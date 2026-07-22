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
    // Nothing is copied alongside the bundle, and nothing should be:
    // vscode-languageclient keeps its process-tree kill script inline
    // and esbuild carries that string into the bundle like any other
    // code, so there is no asset to stage here. Earlier versions of
    // the client shelled out to a packaged `terminateProcess.sh` and
    // this build staged it; re-adding a copy step would put an
    // executable back in the VSIX for nothing. See the CHANGELOG for
    // the version history.
}

main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
});
