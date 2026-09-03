use crate::{CompressOptions, test, test_options_with_iterations, test_same};

#[test]
fn conflate_identifier_assignments() {
    test(
        "export let x, y; export function setVars(value) { x = value; y = value; }",
        "export let x, y; export function setVars(value) { y = x = value; }",
    );
    test(
        "export let x, y, z; export function setVars(value) { x = value, y = value, z = value; }",
        "export let x, y, z; export function setVars(value) { z = y = x = value; }",
    );
    test(
        "export let x, y; export function setVars() { x = 1 + 2, y = 1 + 2; }",
        "export let x, y; export function setVars() { y = x = 3; }",
    );
    test(
        "export let x, y, z, w; export function f(value) { x = value, y = value, sideEffect(), z = value, w = value; }",
        "export let x, y, z, w; export function f(value) { y = x = value, sideEffect(), w = z = value; }",
    );
    test(
        "export let x, y; export function f(value) { x = typeof value, y = typeof value; }",
        "export let x, y; export function f(value) { y = x = typeof value; }",
    );
}

#[test]
fn statement_fusion_does_not_add_an_iteration() {
    test_options_with_iterations(
        "export let x, y; export function setVars(value) { x = value; y = value; }",
        "export let x, y; export function setVars(value) { y = x = value; }",
        1,
        &CompressOptions::smallest(),
    );
}

#[test]
fn conflate_static_member_assignments() {
    test(
        "export const obj = {}; export function setProps(value) { obj.x = value; obj.y = value; }",
        "export const obj = {}; export function setProps(value) { obj.y = obj.x = value; }",
    );
    test(
        "export const obj = {}; export function setProps(value) { obj.x = value, obj.y = value, obj.z = value; }",
        "export const obj = {}; export function setProps(value) { obj.z = obj.y = obj.x = value; }",
    );
    test(
        "export function setProps(value) { this.x = value, this.y = value; }",
        "export function setProps(value) { this.y = this.x = value; }",
    );
}

#[test]
fn do_not_conflate_unsafe_assignments() {
    // The assignment targets must be resolved bindings.
    test_same("function setVars(value) { x = value, y = value; }");

    // Only plain assignments with structurally equal right-hand sides qualify.
    test_same("export let x, y; export function f(value) { x += value, y = value; }");
    test_same("export let x, y; export function f(a, b) { x = a, y = b; }");

    // Re-evaluation must not allocate a distinct value or run user code.
    test_same("export let x, y; export function f() { x = {}, y = {}; }");
    test_same("export let x, y; export function f() { x = value(), y = value(); }");

    // A mutable RHS binding could change between the original evaluations.
    test_same(
        "export let x, y, value; export function setValue(v) { value = v; } export function f() { x = value, y = value; }",
    );

    // Static member targets must use the same stable object binding.
    test_same(
        "export let obj = {}, other = {}; export function f(value) { obj.x = value, other.y = value; }",
    );
    test_same(
        "export let obj = {}; export function replace(value) { obj = value; } export function f(value) { obj.x = value, obj.y = value; }",
    );
}

#[test]
fn setter_cannot_change_repeated_rhs() {
    test_same(
        "export const obj = { set x(_) { value = 2; } }; export let value = 1; export function f() { obj.x = value, obj.y = value; }",
    );
}
