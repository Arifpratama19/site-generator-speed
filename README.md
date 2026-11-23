# site-generator-speed — a faster static site generator

[![make.fun](https://make.fun/badge/site-generator-speed-01-run-20261122.svg)](https://make.fun/bounty/site-generator-speed-01-run-20261122)
[![Rank](https://make.fun/badge/site-generator-speed-01-run-20261122/Arifpratama19/site-generator-speed/rank.svg)](https://make.fun/bounty/site-generator-speed-01-run-20261122)
[![Reward](https://make.fun/badge/site-generator-speed-01-run-20261122/Arifpratama19/site-generator-speed/reward.svg)](https://make.fun/bounty/site-generator-speed-01-run-20261122)

A faster drop-in for make.fun's own makefun-site 1.0.0, written from scratch for the [site-generator-speed-01-run-20261122](https://make.fun/bounty/site-generator-speed-01-run-20261122) bounty on make.fun. `solve.js` answers exactly as makefun-site does on every case — same pages, same report, byte for byte — and `main.ts` runs it over the cases in `/input/cases.json` and writes `/output/answers.json`.

## How it works

- **Markdown in one pass.** Bodies are rendered straight from their lines — no token objects in between — with plain runs escaped in bulk instead of one character at a time.
- **Templates compiled, not walked.** Each template is parsed once per case and compiled into straight-line JavaScript. A loop's element and its `loop` object are plain locals, and an included template still sees its caller's loop variables through a small scope chain.
- **Slugs cached.** Titles, tags and headings repeat, so each distinct string is slugified once per case.
- **Nothing else.** No dependencies, no network, no clock, no randomness — the same case always gives the same answer.

## Files

- `solve.js` — the whole generator: front matter, Markdown, templates and the build, as one dependency-free ES module exporting `run(input)`.
- `main.ts` — the driver the harness runs.
