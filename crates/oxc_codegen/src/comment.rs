use std::borrow::Cow;

use rustc_hash::FxHashSet;
use smallvec::SmallVec;

use oxc_ast::{
    Comment, CommentContent, CommentKind,
    ast::{Expression, Program},
};
use oxc_span::GetSpan;
use oxc_syntax::line_terminator::LineTerminatorSplitter;

use crate::{Codegen, LegalComment, options::CommentOptions};

type CommentList = SmallVec<[Comment; 1]>;

#[derive(Default)]
pub struct CommentStore {
    groups: Vec<CommentGroup>,
}

struct CommentGroup {
    anchor: u32,
    leading: CommentList,
    trailing: CommentList,
}

impl CommentStore {
    fn build(comments: &mut Vec<Comment>) -> Self {
        comments.sort_unstable_by_key(|comment| (comment.attached_to, comment.span.start));
        let mut groups = Vec::<CommentGroup>::new();
        for comment in comments.drain(..) {
            if groups.last().is_none_or(|group| group.anchor != comment.attached_to) {
                groups.push(CommentGroup {
                    anchor: comment.attached_to,
                    leading: CommentList::new(),
                    trailing: CommentList::new(),
                });
            }
            let group = groups.last_mut().unwrap();
            if comment.is_leading() {
                group.leading.push(comment);
            } else {
                group.trailing.push(comment);
            }
        }
        Self { groups }
    }

    #[inline]
    fn index(&self, anchor: u32) -> Result<usize, usize> {
        self.groups.binary_search_by_key(&anchor, |group| group.anchor)
    }

    fn has_non_semantic_at(&self, anchor: u32) -> bool {
        self.index(anchor).is_ok_and(|index| {
            let group = &self.groups[index];
            group
                .leading
                .iter()
                .chain(&group.trailing)
                .any(|comment| !comment.is_pure() && !comment.is_no_side_effects())
        })
    }

    #[inline]
    fn leading_at(&self, anchor: u32) -> Option<&CommentList> {
        let group = self.index(anchor).ok().map(|index| &self.groups[index])?;
        (!group.leading.is_empty()).then_some(&group.leading)
    }

    #[inline]
    fn trailing_at(&self, anchor: u32) -> Option<&CommentList> {
        let group = self.index(anchor).ok().map(|index| &self.groups[index])?;
        (!group.trailing.is_empty()).then_some(&group.trailing)
    }

    fn take_leading_at(&mut self, anchor: u32) -> Option<CommentList> {
        let index = self.index(anchor).ok()?;
        (!self.groups[index].leading.is_empty())
            .then(|| std::mem::take(&mut self.groups[index].leading))
    }

    fn take_trailing_at(&mut self, anchor: u32) -> Option<CommentList> {
        let index = self.index(anchor).ok()?;
        (!self.groups[index].trailing.is_empty())
            .then(|| std::mem::take(&mut self.groups[index].trailing))
    }

    fn take_matching_at(
        &mut self,
        anchor: u32,
        predicate: impl Fn(&Comment) -> bool + Copy,
    ) -> CommentList {
        let Ok(index) = self.index(anchor) else { return CommentList::new() };
        let group = &mut self.groups[index];
        let mut comments = take_matching(&mut group.leading, predicate);
        comments.extend(take_matching(&mut group.trailing, predicate));
        comments.sort_unstable_by_key(|comment| comment.span.start);
        comments
    }

    fn take_matching_leading_at(
        &mut self,
        anchor: u32,
        predicate: impl Fn(&Comment) -> bool,
    ) -> CommentList {
        let Ok(index) = self.index(anchor) else { return CommentList::new() };
        take_matching(&mut self.groups[index].leading, predicate)
    }

    fn nearest_matching_leading_anchor(
        &self,
        anchor: u32,
        predicate: impl Fn(&Comment) -> bool,
    ) -> Option<u32> {
        let end = self.groups.partition_point(|group| group.anchor <= anchor);
        self.groups[..end]
            .iter()
            .rev()
            .find(|group| group.leading.iter().any(&predicate))
            .map(|group| group.anchor)
    }

    fn take_matching_trailing_at(
        &mut self,
        anchor: u32,
        predicate: impl Fn(&Comment) -> bool,
    ) -> CommentList {
        let Ok(index) = self.index(anchor) else { return CommentList::new() };
        take_matching(&mut self.groups[index].trailing, predicate)
    }

    #[inline]
    fn bounds(&self, start: u32, end: u32, inclusive: bool) -> (usize, usize) {
        let first = self.groups.partition_point(|group| group.anchor < start);
        let last = if inclusive {
            self.groups.partition_point(|group| group.anchor <= end)
        } else {
            self.groups.partition_point(|group| group.anchor < end)
        };
        (first, last)
    }

    fn has_between(&self, start: u32, end: u32) -> bool {
        if start >= end {
            return false;
        }
        let (first, last) = self.bounds(start.saturating_add(1), end, false);
        self.groups[first..last]
            .iter()
            .any(|group| !group.leading.is_empty() || !group.trailing.is_empty())
    }

    fn take_between(
        &mut self,
        start: u32,
        end: u32,
        predicate: impl Fn(&Comment) -> bool + Copy,
    ) -> CommentList {
        if start >= end {
            return CommentList::new();
        }
        let (first, last) = self.bounds(start.saturating_add(1), end, false);
        let mut comments = CommentList::new();
        for group in &mut self.groups[first..last] {
            comments.extend(take_matching(&mut group.leading, predicate));
            comments.extend(take_matching(&mut group.trailing, predicate));
        }
        comments.sort_unstable_by_key(|comment| comment.span.start);
        comments
    }

    fn take_remaining_in(&mut self, start: u32, end: u32) -> CommentList {
        if start > end {
            return CommentList::new();
        }
        let (first, last) = self.bounds(start, end, true);
        take_groups(&mut self.groups[first..last])
    }

    fn has_remaining_in(&self, start: u32, end: u32) -> bool {
        if start > end {
            return false;
        }
        let (first, last) = self.bounds(start, end, true);
        self.groups[first..last]
            .iter()
            .any(|group| !group.leading.is_empty() || !group.trailing.is_empty())
    }

    fn take_all_remaining(&mut self) -> CommentList {
        take_groups(&mut self.groups)
    }

    fn has_matching_before(&self, end: u32, predicate: impl Fn(&Comment) -> bool) -> bool {
        let last = self.groups.partition_point(|group| group.anchor < end);
        self.groups[..last]
            .iter()
            .any(|group| group.leading.iter().chain(&group.trailing).any(&predicate))
    }

    fn take_matching_before(
        &mut self,
        end: u32,
        predicate: impl Fn(&Comment) -> bool + Copy,
    ) -> CommentList {
        let last = self.groups.partition_point(|group| group.anchor < end);
        let mut comments = CommentList::new();
        for group in &mut self.groups[..last] {
            comments.extend(take_matching(&mut group.leading, predicate));
            comments.extend(take_matching(&mut group.trailing, predicate));
        }
        comments.sort_unstable_by_key(|comment| comment.span.start);
        comments
    }
}

fn take_matching(comments: &mut CommentList, predicate: impl Fn(&Comment) -> bool) -> CommentList {
    let mut taken = CommentList::new();
    comments.retain(|comment| {
        if predicate(comment) {
            taken.push(*comment);
            false
        } else {
            true
        }
    });
    taken
}

fn take_groups(groups: &mut [CommentGroup]) -> CommentList {
    let mut comments = CommentList::new();
    for group in groups {
        comments.extend(std::mem::take(&mut group.leading));
        comments.extend(std::mem::take(&mut group.trailing));
    }
    comments.sort_unstable_by_key(|comment| comment.span.start);
    comments
}

/// Whether a comment remains meaningful if its original AST anchor is removed.
fn preserve_when_orphaned(comment: Comment) -> bool {
    comment.is_legal() || comment.is_coverage_ignore_file()
}

fn is_html_comment(comment: Comment, source_text: Option<&str>) -> bool {
    comment.is_line()
        && source_text.is_some_and(|source_text| {
            let value = comment.span.source_text(source_text);
            value.starts_with("<!--") || value.starts_with("-->")
        })
}

/// A `pife`-marked arrow or function expression prints its leading comments
/// inside its own `(` wrap, so operand emission sites must not consume them.
pub(crate) fn is_pife_function(expression: &Expression<'_>) -> bool {
    match expression {
        Expression::ArrowFunctionExpression(arrow) => arrow.pife,
        Expression::FunctionExpression(function) => function.pife,
        Expression::ParenthesizedExpression(paren) => is_pife_function(&paren.expression),
        _ => false,
    }
}

/// Which annotation kind an emission site expects to recover from
/// [`Codegen::comments`].
///
/// `@__PURE__` / `#__PURE__` on a `CallExpression` or `NewExpression`, and
/// `@__NO_SIDE_EFFECTS__` / `#__NO_SIDE_EFFECTS__` on a function declaration or
/// expression, are not interchangeable: downstream tree-shakers only honor
/// each on its corresponding node kind. The filter prevents
/// [`Codegen::print_annotation_comment`] from emitting one kind where the
/// other was expected when both share an `attached_to`.
#[derive(Clone, Copy)]
pub enum AnnotationKind {
    Pure,
    NoSideEffects,
}

impl AnnotationKind {
    #[inline]
    fn matches(self, comment: &Comment) -> bool {
        match self {
            Self::Pure => comment.is_pure(),
            Self::NoSideEffects => comment.is_no_side_effects(),
        }
    }

    /// Canonical literal to emit when no verbatim source is available.
    /// `newline_after = true` is used at statement-level emission sites
    /// (function declarations, exports), `false` at inline emission sites
    /// (call / new / function expressions).
    #[inline]
    fn canonical(self, newline_after: bool) -> &'static str {
        match (self, newline_after) {
            (Self::Pure, false) => "/* @__PURE__ */ ",
            (Self::Pure, true) => "/* @__PURE__ */\n",
            (Self::NoSideEffects, false) => "/* @__NO_SIDE_EFFECTS__ */ ",
            (Self::NoSideEffects, true) => "/* @__NO_SIDE_EFFECTS__ */\n",
        }
    }
}

impl Codegen<'_> {
    pub(crate) fn build_comments(&mut self, comments: &[Comment]) {
        if self.options.comments == CommentOptions::disabled() {
            return;
        }
        let mut retained = Vec::with_capacity(comments.len());
        for comment in comments {
            if comment.is_pure() || comment.is_no_side_effects() {
                if comment.is_leading() && self.options.print_annotation_comment() {
                    retained.push(*comment);
                }
                continue;
            }

            let add = (comment.is_legal() && self.options.print_legal_comment())
                || (comment.is_jsdoc() && self.options.print_jsdoc_comment())
                || (comment.is_annotation() && self.options.print_annotation_comment())
                || (comment.is_normal() && self.options.print_normal_comment());

            if add {
                self.has_property_key_annotations |= comment.is_property_key_annotation();
                retained.push(*comment);
            }
        }
        self.comments = CommentStore::build(&mut retained);
    }

    pub(crate) fn has_comment(&self, start: u32) -> bool {
        self.comments.has_non_semantic_at(start)
    }

    /// Emit a pure / no-side-effects annotation comment for the AST node at
    /// `start`, falling back to the canonical literal when no verbatim source
    /// can be recovered.
    ///
    /// The fallback covers four cases:
    /// - no annotation comment is stashed at `start`,
    /// - the stashed comment's kind doesn't match the emission site (e.g. a
    ///   `@__NO_SIDE_EFFECTS__` slot being queried by a `CallExpression`
    ///   site that needs `@__PURE__`),
    /// - the comment is a line comment but the site can't break the line, or
    /// - source text is unavailable (e.g. the [`Codegen::print_expression`]
    ///   path that skips [`Codegen::build_comments`]).
    ///
    /// Export sites pass `self.span.start` and only recover verbatim when the
    /// annotation precedes the `export` keyword. The rarer
    /// `export /* @__NO_SIDE_EFFECTS__ */ function …` form (annotation between
    /// `export` and `function`) attaches to the inner function's span and
    /// falls back to canonical here.
    pub(crate) fn print_annotation_comment(
        &mut self,
        start: u32,
        kind: AnnotationKind,
        newline_after: bool,
    ) {
        let source_anchor = self.comments.nearest_matching_leading_anchor(start, |comment| {
            kind.matches(comment) && (newline_after || !comment.is_line())
        });
        if self.source_text.is_some()
            && let Some(source_anchor) = source_anchor
        {
            let mut comments = self.comments.take_matching_leading_at(source_anchor, |comment| {
                kind.matches(comment) && (newline_after || !comment.is_line())
            });
            // The semantic claim above remains kind-specific. Once its source
            // anchor is owned, retain compatible sibling comments at that
            // exact boundary instead of relocating them to statement fallback.
            comments.extend(self.comments.take_matching_leading_at(source_anchor, |comment| {
                newline_after || !comment.is_line()
            }));
            comments.sort_unstable_by_key(|comment| comment.span.start);
            for (index, comment) in comments.iter().enumerate() {
                if index != 0 {
                    self.print_str(" ");
                }
                self.print_comment(comment);
            }
            if newline_after {
                self.print_hard_newline();
            } else {
                self.print_str(" ");
            }
            return;
        }
        self.print_str(kind.canonical(newline_after));
    }

    pub(crate) fn print_leading_comments(&mut self, start: u32) {
        if let Some(comments) = self.comments.take_leading_at(start) {
            self.print_comments(&comments);
        }
    }

    pub(crate) fn get_comments(&mut self, start: u32) -> Option<CommentList> {
        let comments = self
            .comments
            .take_matching_at(start, |comment| !comment.is_pure() && !comment.is_no_side_effects());
        (!comments.is_empty()).then_some(comments)
    }

    #[inline]
    pub(crate) fn print_comments_at(&mut self, start: u32) {
        if let Some(comments) = self.get_comments(start) {
            self.print_comments(&comments);
        }
    }

    /// Print parser-attached annotations and JSDoc at a surviving AST node.
    /// Normal comments keep using their existing syntax-specific emitters,
    /// which preserve punctuation-sensitive spacing and transformed-AST
    /// behavior. Invalid pure annotations and property-key annotations also
    /// have dedicated emission sites.
    fn has_attached_comments_at(&self, start: u32) -> bool {
        self.comments.leading_at(start).is_some_and(|comments| {
            comments.iter().any(|comment| {
                (!self.suppress_normal_comments && comment.is_normal())
                    || comment.is_jsdoc()
                    || (comment.is_annotation()
                        && comment.content != CommentContent::PureNotApplied
                        && !comment.is_pure()
                        && !comment.is_no_side_effects()
                        && !comment.is_property_key_annotation())
            })
        })
    }

    pub(crate) fn print_attached_comments_at(&mut self, start: u32) {
        if self.has_attached_comments_at(start) {
            let comments = self.comments.take_matching_leading_at(start, |comment| {
                (!self.suppress_normal_comments && comment.is_normal())
                    || comment.is_jsdoc()
                    || (comment.is_annotation()
                        && comment.content != CommentContent::PureNotApplied
                        && !comment.is_pure()
                        && !comment.is_no_side_effects()
                        && !comment.is_property_key_annotation())
            });
            self.print_comments(&comments);
            if self.last_byte() != Some(b'\n') {
                self.consume_pending_indent_space();
            }
        }
    }

    pub(crate) fn print_normal_comments_at(&mut self, start: u32) {
        let should_print = self
            .comments
            .leading_at(start)
            .is_some_and(|comments| comments.iter().any(|comment| comment.is_normal()));
        if should_print {
            let comments =
                self.comments.take_matching_leading_at(start, |comment| comment.is_normal());
            self.print_comments(&comments);
            if self.last_byte() != Some(b'\n') {
                self.consume_pending_indent_space();
            }
        }
    }

    pub(crate) fn print_trailing_normal_comments_at(&mut self, end: u32) {
        let should_print = self
            .comments
            .trailing_at(end)
            .is_some_and(|comments| comments.iter().any(|comment| comment.is_normal()));
        if should_print {
            self.print_soft_space();
            let comments =
                self.comments.take_matching_trailing_at(end, |comment| comment.is_normal());
            self.print_comments(&comments);
            self.clear_pending_indent_space();
        }
    }

    pub(crate) fn print_trailing_attached_comments_at(&mut self, end: u32) {
        let source_text = self.source_text;
        let should_print = self.comments.trailing_at(end).is_some_and(|comments| {
            comments.iter().any(|comment| {
                !is_html_comment(*comment, source_text)
                    && (comment.is_normal()
                        || comment.is_jsdoc()
                        || (comment.is_annotation() && !comment.is_property_key_annotation()))
            })
        });
        if should_print {
            self.print_soft_space();
            let has_html = self.comments.trailing_at(end).is_some_and(|comments| {
                comments.iter().any(|comment| is_html_comment(*comment, source_text))
            });
            let comments = if has_html {
                self.comments.take_matching_trailing_at(end, |comment| {
                    !is_html_comment(*comment, source_text)
                })
            } else {
                self.comments.take_trailing_at(end).unwrap()
            };
            self.print_comments(&comments);
            self.clear_pending_indent_space();
        }
    }

    pub(crate) fn print_attached_comments_before_expression(
        &mut self,
        expression: &Expression<'_>,
    ) {
        if is_pife_function(expression) || matches!(expression, Expression::ObjectExpression(_)) {
            return;
        }
        let start = expression.span().start;
        if self.has_attached_comments_at(start) {
            self.print_leading_comments_anchored_to_self(start);
        }
        if let Expression::ParenthesizedExpression(paren) = expression {
            self.print_attached_comments_before_expression(&paren.expression);
        }
    }

    /// Print leading comments at `start` and glue the next token to them: after a
    /// group ending in a newline (line comment / `followed_by_newline`), print the
    /// indent — mid-expression callers have no statement machinery to do it, and an
    /// unindented next token renders differently once the parser re-anchors the
    /// comments to it (codegen would no longer be idempotent). Otherwise consume the
    /// pending indent-as-space so the token glues with a single space.
    #[inline]
    pub(crate) fn print_leading_comments_anchored_to_self(&mut self, start: u32) {
        if let Some(comments) = self.comments.take_leading_at(start) {
            self.print_comments(&comments);
            if self.last_byte() == Some(b'\n') {
                self.print_indent();
            } else {
                self.consume_pending_indent_space();
            }
        }
    }

    /// Print a property-key annotation attached directly to a string or template literal.
    #[inline]
    pub(crate) fn print_property_key_annotation(&mut self, start: u32) {
        if !self.has_property_key_annotations {
            return;
        }
        if self.comments.leading_at(start).is_some_and(|comments| {
            comments.iter().any(|comment| comment.is_property_key_annotation())
        }) {
            self.print_leading_comments_anchored_to_self(start);
        }
    }

    /// Print comments attached to an expression that survives codegen.
    ///
    /// Probes the parenthesized layers too: `a || /* c */ (x)` anchors the
    /// comment at the `(`, `a || (/* c */ x)` at `x` — an operand printer only
    /// sees one node, so the walk happens here for every emission site.
    pub(crate) fn print_leading_comments_before_expression(&mut self, expression: &Expression<'_>) {
        if is_pife_function(expression) {
            return;
        }
        let start = expression.span().start;
        let comments = self.comments.take_matching_leading_at(start, |comment| {
            !comment.is_pure() && !comment.is_no_side_effects()
        });
        if !comments.is_empty() {
            self.print_comments(&comments);
            if self.last_byte() == Some(b'\n') {
                self.print_indent();
            } else {
                self.consume_pending_indent_space();
            }
        }
        if let Expression::ParenthesizedExpression(paren) = expression {
            self.print_leading_comments_before_expression(&paren.expression);
        }
    }

    /// Print an expression's comment group only when it contains an annotation
    /// comment, probing parenthesized layers like
    /// [`Self::print_leading_comments_before_expression`].
    ///
    /// This is the variant for emission sites that mutating consumers move
    /// statements into (the minifier merges `if(a)x;if(b)x;` into
    /// `if(a||(b,..))x`; rolldown finalizes moved nodes with their original
    /// spans). Comments are anchored by source position, so a dissolved
    /// statement's leading normal-comment group can coincide with the moved
    /// operand's span start — printing it there misplaces statement-level
    /// trivia inside an expression and is not idempotent
    /// (`test_normal_comment_before_logical_rhs_not_printed` documents the
    /// falsifier). Annotations are the one comment kind with expression-level
    /// meaning, so they still pass through.
    pub(crate) fn print_annotation_comments_before_expression(
        &mut self,
        expression: &Expression<'_>,
    ) {
        if is_pife_function(expression) {
            return;
        }
        let start = expression.span().start;
        let has_annotation = self.comments.leading_at(start).is_some_and(|comments| {
            comments.iter().any(|comment| {
                comment.is_annotation()
                    && !comment.is_pure()
                    && !comment.is_no_side_effects()
                    && !comment.is_property_key_annotation()
            })
        });
        if has_annotation {
            let comments = self.comments.take_matching_leading_at(start, |comment| {
                comment.is_annotation()
                    && !comment.is_pure()
                    && !comment.is_no_side_effects()
                    && !comment.is_property_key_annotation()
            });
            self.print_comments(&comments);
            if self.last_byte() == Some(b'\n') {
                self.print_indent();
            } else {
                self.consume_pending_indent_space();
            }
        }
        if let Expression::ParenthesizedExpression(paren) = expression {
            self.print_annotation_comments_before_expression(&paren.expression);
        }
    }

    /// Whether an orphan comment with `attached_to < end` is still pending.
    /// Used by block emitters to keep an empty body multi-line.
    #[inline]
    pub(crate) fn has_orphan_comments_before(&self, end: u32) -> bool {
        self.comments.has_matching_before(end, |comment| preserve_when_orphaned(*comment))
    }

    /// Drain pending orphan comments with `attached_to < end` and emit them in
    /// source order. Called at every statement boundary so legal and file-level
    /// coverage comments survive when their original anchor was removed by an
    /// upstream pass.
    #[inline]
    pub(crate) fn print_orphan_comments_before(&mut self, end: u32) {
        let mut orphans =
            self.comments.take_matching_before(end, |comment| preserve_when_orphaned(*comment));
        if let Some(last) = orphans.last_mut() {
            // Orphans aren't in their original position, so the source's
            // `followed_by_newline` hint no longer applies. Force it on so
            // `print_comments` emits a trailing newline instead of setting
            // `print_next_indent_as_space` — otherwise the next indent (often
            // before `}`) collapses to a space and pass 2 stops matching.
            last.set_followed_by_newline(true);
            self.print_comments(&orphans);
        }
    }

    /// Print comments attached to any position in the given range `(start, end)` (exclusive).
    /// Returns `true` if any comments were printed.
    pub(crate) fn print_comments_in_range(&mut self, start: u32, end: u32) -> bool {
        let comments = self.comments.take_between(start, end, |comment| {
            !comment.is_pure() && !comment.is_no_side_effects()
        });
        if comments.is_empty() {
            return false;
        }
        self.print_comments(&comments);
        true
    }

    pub(crate) fn has_comments_in_range(&self, start: u32, end: u32) -> bool {
        self.comments.has_between(start, end)
    }

    pub(crate) fn has_remaining_comments_in_span(&self, span: oxc_span::Span) -> bool {
        self.comments.has_remaining_in(span.start, span.end)
    }

    pub(crate) fn print_remaining_comments_in_span(&mut self, span: oxc_span::Span) {
        let mut comments = self.comments.take_remaining_in(span.start, span.end);
        if comments.is_empty() {
            return;
        }
        if self.last_byte() != Some(b'\n')
            && comments.first().is_some_and(|comment| !comment.preceded_by_newline())
        {
            self.print_soft_space();
        }
        comments.last_mut().unwrap().set_followed_by_newline(true);
        self.print_comments(&comments);
    }

    pub(crate) fn print_all_remaining_comments(&mut self) {
        let mut comments = self.comments.take_all_remaining();
        if comments.is_empty() {
            return;
        }
        if self.last_byte() != Some(b'\n')
            && comments.first().is_some_and(|comment| !comment.preceded_by_newline())
        {
            self.print_soft_space();
        }
        comments.last_mut().unwrap().set_followed_by_newline(true);
        self.print_comments(&comments);
    }

    pub(crate) fn print_expr_comments(&mut self, start: u32) -> bool {
        let comments = self
            .comments
            .take_matching_at(start, |comment| !comment.is_pure() && !comment.is_no_side_effects());
        if comments.is_empty() {
            return false;
        }

        for comment in &comments {
            self.print_hard_newline();
            self.print_indent();
            self.print_comment(comment);
        }

        if comments.is_empty() {
            false
        } else {
            self.print_hard_newline();
            true
        }
    }

    pub(crate) fn print_comments(&mut self, comments: &[Comment]) {
        let Some((first, rest)) = comments.split_first() else {
            return;
        };

        if first.preceded_by_newline() {
            // Skip printing newline if this comment is already on a newline.
            if let Some(b) = self.last_byte() {
                match b {
                    b'\n' => self.print_indent(),
                    b'\t' => { /* noop */ }
                    _ => {
                        self.print_hard_newline();
                        self.print_indent();
                    }
                }
            }
        } else if !self.consume_pending_indent_space()
            && matches!(self.last_byte(), None | Some(b'\n'))
        {
            // Only indent at a line start. Mid-line emission sites (`a ?? /* c */ b`,
            // `key: /* c */ value`, `${/* c */ expr}`) would otherwise get a full
            // indent injected mid-line, growing indentation on every codegen pass.
            self.print_indent();
        }
        self.print_comment(first);

        if let Some((last, middle)) = rest.split_last() {
            for comment in middle {
                if comment.preceded_by_newline() {
                    self.print_hard_newline();
                    self.print_indent();
                } else if comment.is_legal() {
                    self.print_hard_newline();
                } else {
                    self.print_soft_space();
                }
                self.print_comment(comment);
            }

            if last.preceded_by_newline() {
                self.print_hard_newline();
                self.print_indent();
            } else if last.is_legal() {
                self.print_hard_newline();
            } else {
                self.print_soft_space();
            }
            self.print_comment(last);

            if last.is_line() || last.followed_by_newline() {
                self.print_hard_newline();
            } else {
                self.print_next_indent_as_space = true;
            }
        } else if first.is_line() || first.followed_by_newline() {
            self.print_hard_newline();
        } else {
            self.print_next_indent_as_space = true;
        }
    }

    fn print_comment(&mut self, comment: &Comment) {
        let Some(source_text) = self.source_text else {
            return;
        };
        let comment_source = comment.span.source_text(source_text);
        match comment.kind {
            CommentKind::Line | CommentKind::SingleLineBlock => {
                self.print_str_escaping_script_close_tag(comment_source);
            }
            CommentKind::MultiLineBlock => {
                for line in LineTerminatorSplitter::new(comment_source) {
                    if !line.starts_with("/*") {
                        self.print_indent();
                    }
                    self.print_str_escaping_script_close_tag(line.trim_start());
                    if !line.ends_with("*/") {
                        self.print_hard_newline();
                    }
                }
            }
        }
    }

    /// Handle Eof / Linked / External Comments.
    /// Return a list of comments of linked or external.
    pub(crate) fn handle_eof_linked_or_external_comments(
        &mut self,
        program: &Program<'_>,
    ) -> Vec<Comment> {
        let legal_comments = &self.options.comments.legal;
        if matches!(legal_comments, LegalComment::None | LegalComment::Inline) {
            return vec![];
        }

        // Dedupe legal comments for smaller output size.
        let mut set = FxHashSet::default();
        let mut comments = vec![];

        let source_text = program.source_text;
        for comment in program.comments.iter().filter(|c| c.is_legal()) {
            let mut text = Cow::Borrowed(comment.span.source_text(source_text));
            if comment.is_multiline_block() {
                let mut buffer = String::with_capacity(text.len());
                // Print block comments with our own indentation.
                for line in LineTerminatorSplitter::new(&text) {
                    if !line.starts_with("/*") {
                        buffer.push('\t');
                    }
                    buffer.push_str(line.trim_start());
                    if !line.ends_with("*/") {
                        buffer.push('\n');
                    }
                }
                text = Cow::Owned(buffer);
            }
            if set.insert(text) {
                comments.push(*comment);
            }
        }

        if comments.is_empty() {
            return vec![];
        }

        match legal_comments {
            LegalComment::Eof => {
                self.print_hard_newline();
                // Clear the flag to ensure consistent formatting for all EOF comments
                self.print_next_indent_as_space = false;
                for c in comments {
                    self.print_comment(&c);
                    self.print_hard_newline();
                }
                vec![]
            }
            LegalComment::Linked(path) => {
                let path = path.clone();
                self.print_hard_newline();
                self.print_str("/*! For license information please see ");
                self.print_str(&path);
                self.print_str(" */");
                comments
            }
            LegalComment::External => comments,
            LegalComment::None | LegalComment::Inline => unreachable!(),
        }
    }
}
