//! Post-parse source-comment attachment.

use std::cmp::Reverse;

use oxc_allocator::{Address, Allocator, GetAddress, Vec as ArenaVec};
use oxc_ast::{
    AstKind, AstType, AttachedComment, AttachedCommentPosition, CommentAttachmentHost,
    CommentAttachments, CommentContent, ast::Program,
};
use oxc_span::{GetSpan, Span};
use oxc_syntax::line_terminator::is_line_terminator;

use crate::Visit;

#[derive(Debug)]
struct NodeRecord {
    address: Address,
    kind: AstType,
    parent: Option<usize>,
    span: Span,
    depth: u32,
    children: std::vec::Vec<usize>,
}

#[derive(Default)]
struct Collector {
    nodes: std::vec::Vec<NodeRecord>,
    stack: std::vec::Vec<usize>,
}

impl<'a> Visit<'a> for Collector {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        let index = self.nodes.len();
        let parent = self.stack.last().copied();
        if let Some(parent) = parent {
            self.nodes[parent].children.push(index);
        }
        self.nodes.push(NodeRecord {
            // `Program` is returned by value and therefore moves after parsing.
            // Use the reserved dummy address as its durable parser-only key.
            address: if self.stack.is_empty() { Address::DUMMY } else { kind.address() },
            kind: kind.ty(),
            parent,
            span: kind.span(),
            depth: u32::try_from(self.stack.len()).unwrap(),
            children: std::vec::Vec::new(),
        });
        self.stack.push(index);
    }

    fn leave_node(&mut self, _kind: AstKind<'a>) {
        self.stack.pop();
    }
}

#[derive(Clone, Copy)]
struct Assignment {
    host: usize,
    position: AttachedCommentPosition,
    same_line: bool,
    force_newline_after: bool,
}

struct Attacher<'a> {
    source_text: &'a str,
    nodes: &'a [NodeRecord],
    comments: &'a [oxc_ast::Comment],
    assignments: std::vec::Vec<Option<Assignment>>,
    cursor: usize,
}

impl<'a> Attacher<'a> {
    fn new(
        source_text: &'a str,
        nodes: &'a [NodeRecord],
        comments: &'a [oxc_ast::Comment],
    ) -> Self {
        Self { source_text, nodes, comments, assignments: vec![None; comments.len()], cursor: 0 }
    }

    fn attach(mut self) -> std::vec::Vec<Assignment> {
        self.attach_pure_not_applied();
        if !self.nodes.is_empty() {
            self.walk_at(0);
        }
        while self.cursor < self.comments.len() {
            if self.assignments[self.cursor].is_none() {
                self.assignments[self.cursor] = Some(Assignment {
                    host: 0,
                    position: AttachedCommentPosition::Inside,
                    same_line: false,
                    force_newline_after: false,
                });
            }
            self.cursor += 1;
        }
        self.assignments.into_iter().map(Option::unwrap).collect()
    }

    /// `PureNotApplied` is the one deliberate parser-attachment override. It
    /// remains trailing on the deepest node ending at the parser's token
    /// boundary, e.g. `foo /* PURE */ = call()`.
    fn attach_pure_not_applied(&mut self) {
        for (comment_index, comment) in self.comments.iter().enumerate() {
            if comment.content != CommentContent::PureNotApplied {
                continue;
            }
            let host = self
                .nodes
                .iter()
                .enumerate()
                .filter(|(_, node)| node.span.end == comment.attached_to)
                .max_by_key(|(_, node)| (node.depth, Reverse(node.span.size())))
                .map_or(0, |(index, _)| index);
            self.assignments[comment_index] = Some(Assignment {
                host,
                position: AttachedCommentPosition::After,
                same_line: self.same_line(self.nodes[host].span.end, comment.span.start),
                force_newline_after: false,
            });
        }
    }

    fn walk_at(&mut self, node_index: usize) {
        if self.cursor >= self.comments.len() {
            return;
        }
        let node = &self.nodes[node_index];
        if self.comments[self.cursor].span.start >= node.span.end {
            return;
        }

        let mut children = node.children.clone();
        children.sort_unstable_by_key(|&index| {
            let child = &self.nodes[index];
            (child.span.start, child.span.end, index)
        });

        let mut previous = None;
        let mut previous_end = node.span.start;
        for child in children {
            let child_start = self.nodes[child].span.start;
            self.consume_between(node_index, previous, previous_end, Some(child), child_start);
            self.walk_at(child);
            previous = Some(child);
            previous_end = self.nodes[child].span.end;
        }
        self.consume_between(node_index, previous, previous_end, None, node.span.end);
    }

    fn consume_between(
        &mut self,
        host: usize,
        previous: Option<usize>,
        previous_end: u32,
        next: Option<usize>,
        next_start: u32,
    ) {
        while self.cursor < self.comments.len() {
            if self.assignments[self.cursor].is_some() {
                self.cursor += 1;
                continue;
            }
            let comment = self.comments[self.cursor];
            if comment.span.start >= next_start {
                return;
            }

            let assignment = match (previous, next) {
                (Some(previous), Some(next)) => {
                    if self.same_line(comment.span.end, next_start) {
                        Assignment {
                            host: next,
                            position: AttachedCommentPosition::Before,
                            same_line: true,
                            force_newline_after: false,
                        }
                    } else if self.same_line(previous_end, comment.span.start) {
                        Assignment {
                            host: previous,
                            position: AttachedCommentPosition::After,
                            same_line: true,
                            force_newline_after: true,
                        }
                    } else {
                        Assignment {
                            host: next,
                            position: AttachedCommentPosition::Before,
                            same_line: false,
                            force_newline_after: false,
                        }
                    }
                }
                (None, Some(next)) => Assignment {
                    host: next,
                    position: AttachedCommentPosition::Before,
                    same_line: self.same_line(comment.span.end, next_start),
                    force_newline_after: false,
                },
                (Some(previous), None) => Assignment {
                    host: previous,
                    position: AttachedCommentPosition::After,
                    same_line: self.same_line(previous_end, comment.span.start),
                    force_newline_after: false,
                },
                (None, None) => Assignment {
                    host,
                    position: AttachedCommentPosition::Inside,
                    same_line: false,
                    force_newline_after: false,
                },
            };
            self.assignments[self.cursor] = Some(assignment);
            self.cursor += 1;
        }
    }

    fn same_line(&self, a: u32, b: u32) -> bool {
        let (start, end) = if a <= b { (a, b) } else { (b, a) };
        let Ok(start) = usize::try_from(start) else { return false };
        let Ok(end) = usize::try_from(end) else { return false };
        self.source_text.get(start..end).is_some_and(|text| !text.chars().any(is_line_terminator))
    }
}

/// Assign every parser comment to an AST host.
pub fn attach_comments<'a>(
    allocator: &'a Allocator,
    program: &Program<'a>,
) -> CommentAttachments<'a> {
    if program.comments.is_empty() {
        return CommentAttachments::new_in(allocator);
    }

    let mut collector = Collector::default();
    collector.visit_program(program);
    let assignments =
        Attacher::new(program.source_text, &collector.nodes, &program.comments).attach();

    let mut counts = vec![0_u32; collector.nodes.len()];
    for assignment in &assignments {
        counts[assignment.host] += 1;
    }
    let mut offsets = vec![0_u32; collector.nodes.len() + 1];
    for index in 0..collector.nodes.len() {
        offsets[index + 1] = offsets[index] + counts[index];
    }
    let mut used = vec![0_u32; collector.nodes.len()];
    let mut sorted = vec![AttachedComment::default(); program.comments.len()];
    for (mut comment, assignment) in program.comments.iter().copied().zip(assignments) {
        if assignment.force_newline_after {
            comment.set_followed_by_newline(true);
        }
        let target = offsets[assignment.host] + used[assignment.host];
        sorted[target as usize] = AttachedComment {
            comment,
            position: assignment.position,
            same_line: assignment.same_line,
        };
        used[assignment.host] += 1;
    }

    let mut hosts = ArenaVec::new_in(&allocator);
    for (index, node) in collector.nodes.iter().enumerate() {
        if counts[index] == 0 {
            continue;
        }
        hosts.push(CommentAttachmentHost {
            address: node.address,
            node_id: std::cell::Cell::new(None),
            kind: node.kind,
            parent_kind: node.parent.map(|parent| collector.nodes[parent].kind),
            span_start: node.span.start,
            start: offsets[index],
            len: counts[index],
        });
    }
    let comments = ArenaVec::from_iter_in(sorted, &allocator);
    CommentAttachments { hosts, comments }
}
