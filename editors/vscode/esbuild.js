"use strict";

const fs = require("node:fs");
const path = require("node:path");
const esbuild = require("esbuild");

const extensionRoot = __dirname;
const distDir = path.join(extensionRoot, "dist");

async function main() {
    fs.rmSync(distDir, { recursive: true, force: true });

    await esbuild.build({
        entryPoints: [path.join(extensionRoot, "extension.js")],
        bundle: true,
        external: ["vscode"],
        format: "cjs",
        legalComments: "eof",
        minify: true,
        outfile: path.join(distDir, "extension.js"),
        platform: "node",
        target: "node16",
    });
    // Nothing is copied alongside the bundle. Up to
    // vscode-languageclient 9 the client shelled out to a packaged
    // `terminateProcess.sh`, so the build resolved that file out of
    // node_modules, copied it here and marked it executable. Version 10
    // inlines the same process-tree walk as a string in
    // lib/node/processes.js and pipes it to /bin/sh, so the helper no
    // longer exists upstream and esbuild carries it into the bundle
    // like any other code. The VSIX is now pure JSON, JS and assets.
}

main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
});
