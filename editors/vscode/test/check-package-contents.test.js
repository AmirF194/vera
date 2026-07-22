// Behavioural tests for the VSIX contents guard.
//
// The guard's whole value is failing when the package drifts, so what
// needs pinning is the failure branches — a check that only ever
// passes is indistinguishable from no check. Every case below is one
// the first version of the guard let through.
//
// These drive `analyse()` on fixture entry lists, so they need neither
// a built VSIX nor `npm ci`. The live end-to-end path is covered by
// `npm run check:package` in CI.

"use strict";

const test = require("node:test");
const assert = require("node:assert");

const {
    analyse, EXPECTED,
} = require("../check-package-contents.js");

/** The expected set, as the reader would return it: all inert, 0644. */
function cleanEntries() {
    return EXPECTED.map((name) => ({ name, mode: 0o644 }));
}

function messages(entries, expected = EXPECTED) {
    return analyse(entries, expected);
}

test("a clean archive reports no problems", () => {
    assert.deepStrictEqual(messages(cleanEntries()), []);
});

test("an unexpected file is reported", () => {
    const entries = [...cleanEntries(), { name: "extension/stray.js", mode: 0o644 }];
    const problems = messages(entries);
    assert.ok(problems.some((p) => p.includes("unexpected file")), problems);
});

test("a missing expected file is reported", () => {
    const entries = cleanEntries().filter(
        (e) => e.name !== "extension/syntaxes/vera.tmLanguage.json",
    );
    const problems = messages(entries);
    assert.ok(
        problems.some((p) => p.includes("expected file missing")), problems,
    );
});

// The cases below all defeated the original extension denylist.

test("an extensionless file is not allowlisted", () => {
    const entries = [...cleanEntries(), { name: "extension/dist/helper", mode: 0o644 }];
    const problems = messages(entries);
    assert.ok(
        problems.some((p) => p.includes("non-allowlisted") && p.includes("no extension")),
        problems,
    );
});

test("a dotfile is not allowlisted (extname returns empty for it)", () => {
    const entries = [...cleanEntries(), { name: "extension/dist/.sh", mode: 0o644 }];
    const problems = messages(entries);
    assert.ok(problems.some((p) => p.includes("non-allowlisted")), problems);
});

test("a .wasm is not allowlisted", () => {
    const entries = [...cleanEntries(), { name: "extension/dist/core.wasm", mode: 0o644 }];
    const problems = messages(entries);
    assert.ok(problems.some((p) => p.includes("non-allowlisted")), problems);
});

test("an executable mode is reported even with an inert extension", () => {
    // The case no extension check can see: .json is allowlisted, and
    // the file is still runnable.
    const entries = cleanEntries().map((e) =>
        e.name === "extension/package.json" ? { ...e, mode: 0o755 } : e,
    );
    const problems = messages(entries);
    assert.ok(problems.some((p) => p.includes("executable file")), problems);
    assert.ok(
        !problems.some((p) => p.includes("non-allowlisted")),
        "extension is allowlisted; only the mode should fail",
    );
});

test("adding a bad file to EXPECTED does not silence the other assertions", () => {
    // The escape hatch the failure message itself offers. The set
    // comparison goes quiet; extension and mode must not.
    const bad = { name: "extension/dist/install.sh", mode: 0o755 };
    const entries = [...cleanEntries(), bad];
    const problems = messages(entries, [...EXPECTED, bad.name]);
    assert.ok(
        !problems.some((p) => p.includes("unexpected file")),
        "set comparison should be satisfied by the widened list",
    );
    assert.ok(problems.some((p) => p.includes("non-allowlisted")), problems);
    assert.ok(problems.some((p) => p.includes("executable file")), problems);
});

test("an empty archive is a failure, not a vacuous pass", () => {
    const problems = messages([]);
    assert.deepStrictEqual(problems, ["archive contains no entries at all"]);
});

test("an empty EXPECTED cannot make an empty archive pass", () => {
    // Both lists empty would otherwise agree trivially.
    const problems = analyse([], []);
    assert.ok(problems.length > 0, "empty vs empty must still fail");
});
