// Driver for markdown-render-speed-02.
// Reads every case from the input dir, renders each one alone with
// parse() from ./parse.js, and writes the HTML array to the output dir.
// Outside a container MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR stand in
// for /input and /output.
import { readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { join } from "node:path";
import { parse } from "./parse.js";

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";

const cases = JSON.parse(readFileSync(join(INPUT_DIR, "cases.json"), "utf8"));
const html = [];
for (const c of cases) html.push(parse(c.markdown));
mkdirSync(OUTPUT_DIR, { recursive: true });
writeFileSync(join(OUTPUT_DIR, "html.json"), JSON.stringify(html));
