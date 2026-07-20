# Plan: commonsense reasoner tab for logictools.org

Status: ready for implementation
Written: 2026-07-20. Paths, binary behavior, and example results were checked
against the local repositories on this date.

## 0. Goal

Add a new page `commonsense.html` to logictools.org, working like the current
predicate-logic page (`index.html`): a text box, example menus, a solve
button, and a solver compiled to WebAssembly running in the browser. The
solver is GK, which extends classical predicate logic with
confidences, defaults with exceptions, negative evidence and contradiction
tolerance.

The page content (which examples, their order, all note and help texts) is
already decided and written:

- `commonsense_plan/examples_content.md` — 22 examples with inputs, note
  texts, per-example UI presets, and expected outputs for verification.
- `commonsense_plan/help_texts.md` — page intro, syntax box, four modals,
  Advanced-panel labels and argument mapping, footer, about/download
  additions, navbar item.

Use these texts as the page content. The navbar label is "Commonsense" and the
page is `commonsense.html`.

## 1. Verified facts to build on

- `index.html` is the predicate-logic page. Its machinery to clone:
  - a global `var Module = {noInitialRun: true, print: f, printErr: f, ...}`
    is declared BEFORE `<script async src="gkcjs.js">`; output is collected by
    appending to a string in `Module.print` and shown after `callMain`
    returns (`useGkc()` around line 122, `gkc()` at 215, Module at 360,
    script tag at 3762).
  - examples are hidden divs: `example_<N>_input_code` (inside
    `<pre><code>`), `example_<N>_input_notes`, `example_<N>_proof_notes`;
    `selectExample()` (line 290) copies the code into the textarea
    (unescaping `&amp; &gt; &lt;`) and the notes into visible
    `input_notes` / `proof_notes` divs.
  - two example dropdowns: `select_example`, `select_advanced_example`.
  - Advanced panel: seconds, print level, show derived, strategy text.
  - Bootstrap 3.3.4 from CDN, `wdb.css`, WebFont Roboto/Inconsolata, navbar
    shared across pages.
- gk's WebAssembly build (`/opt/gkreasoner/bin/gkjs.js` + `gkjs.wasm`,
  rebuilt 2026-07-20 from gk master) uses Emscripten's global `Module` form:
  `var Module=typeof Module!=="undefined"?Module:{}`. A pre-declared
  page-global Module works exactly as with gkcjs. Exported:
  `callMain`, `FS`, `cwrap`, `ccall`; `FORCE_FILESYSTEM=1`. Built by
  `/opt/gk/compile_wasm.sh`.
- gk does not accept general input through `-text`; `-jstext` accepts JSON
  only.
  Input must therefore go through the in-memory filesystem:
  `Module.FS.writeFile("input", text)` then
  `Module.callMain(["input", ...args])`. A file named `input` with no
  suffix triggers gk's content sniffer, which auto-detects JSON / GKP / GKS /
  TPTP (`Main/gk.c` `gk_suffix_format` / sniffing around line 2483+). This is
  the mechanism that lets one text box accept all four notations.
- Multi-file input works the same way: write two files, pass both names.
  Needed for the two English examples (background KB `axioms_std.js`, 55 KB).
- gk searches sequentially by default. Do not pass `-parallel`; WebAssembly
  must remain single-process.
- The WebAssembly binary was compared with native gk this month (10/10
  byte-identical outputs) using the harness
  `/opt/gk/experiments/wasm_parity/wasmrun.js`. Reuse its module setup and
  argument handling for Node.js tests. A direct
  `node gkjs.js file.gkp` command does not work; the wrapper must write the
  input with `FS.writeFile` before calling gk. Emscripten's Node.js binary is:
  `/opt/gkcjs/emsdk/node/12.18.1_64bit/bin/node`.
- Memory: `compile_wasm.sh` sets `-s TOTAL_MEMORY=2000MB`. Its build note says
  an older Firefox failed at 2000 MB but worked at 1000 MB. Recheck this with
  the current Firefox version; see task 2.
- All 22 example inputs run correctly on the current native gk; expected
  outputs are recorded per example in `examples_content.md`.

## 2. WebAssembly files

1. Copy `/opt/gkreasoner/bin/gkjs.js` and `gkjs.wasm` to `/opt/logictools/`.
   Test this 2000 MB build in current Firefox. If allocation fails, make a
   temporary copy of `/opt/gk/compile_wasm.sh`, change that copy to
   `TOTAL_MEMORY=1000MB` and change its output to
   `/tmp/gkjs-site.html`. Run it from `/opt/gk`, then copy
   `/tmp/gkjs-site.js` and `/tmp/gkjs-site.wasm` to `/opt/logictools/` as
   `gkjs.js` and `gkjs.wasm`. This leaves `/opt/gk` unchanged. Check the
   selected build with the comparison script on `net_direct.gkp`,
   `penguin.gkp`, and `blocks.gkp`.
2. Copy `/opt/gkreasoner/Examples/language/axioms_std.js` to
   `/opt/logictools/gk_axioms_std.js`. It is fetched on demand (see 4.4),
   not embedded in the page.

## 3. Page structure (`commonsense.html`)

Start from a copy of `index.html` and strip it down; keep the head block
(meta, fonts, styles), navbar, footer structure, and the general layout of
input area / buttons / result area. Then:

- title/meta per `help_texts.md` section 1; navbar per section 2 (also add
  the new navbar item to `index.html`, `prop.html`, `json.html`, `about.html`,
  and `download.html`). The redirect pages `predicate.html` and
  `propositional.html` have no navbar and need no change.
- intro paragraphs per section 3; syntax box per section 4 (collapsible,
  like the predicate page's `syntax` div).
- modals per sections 5–8 ("what is this", "reading the output",
  "confidences", "defaults"), linked from the intro and from the notes area
  headers.
- two dropdowns: `examples` (12 entries) and `more examples` (10 entries),
  names exactly as in `examples_content.md`.
- Advanced panel per section 9: seconds, detail report, print level, show
  derived, strategy, max answers, confidence limit. The argument mapping is
  in the build note of section 9.
- footer per section 10; `about.html` / `download.html` additions per
  sections 11–12; add `commonsense.html` to `sitemap.txt`.

## 4. Browser integration (differences from `useGkc`)

Replace `useGkc()` with `useGk()`:

1. No `seemsJson`/`-text`/`-jstext` branch. Instead:
   `Module.FS.writeFile("input", inputText)` and start
   `arglist = ["input"]`. gk detects the notation from the content.
2. Append arguments from the Advanced controls per the mapping in
   `help_texts.md` section 9. Always append `-seconds N` (default 5).
   Never append `-parallel`.
3. Capture output as on the predicate page (`Module.print` into a string,
   displayed after `callMain` returns). Keep the `printErr` out-of-memory
   reload guard from `index.html`.
4. English examples (21, 22): on first use, `fetch("gk_axioms_std.js")`,
   cache the text in a JS variable, `FS.writeFile("axioms_std.js", kbText)`,
   and call with `["axioms_std.js", "input", ...]`. Show a brief
   "loading background knowledge..." note during the fetch. Handle fetch
   failure with a visible error message.
5. Per-example presets: `selectExample()` additionally reads a small JS
   table `examplePresets[N]` (fields: `detail`, `strategy`, `seconds`,
   `confidence`, `background`) and sets the Advanced controls accordingly;
   selecting an example without presets resets the controls to defaults. The
   presets are
   listed per example in `examples_content.md` (arithmetic prefills the
   strategy field; 4, 7, 11, 15 switch detail on; 20 sets seconds 30; 21-22
   set strategy + confidence limit 0.1 + `background`).
6. Repeated `callMain` calls on one page load: the predicate page relies on
   this and it works with the same emscripten era/settings; verify once for
   gk in the browser (solve two different examples in a row, then the same
   one twice). If state leaks between runs (answers from the previous run,
   error state), fall back to reloading the wasm module per solve or
   `location.reload()`-style reinit, but only if actually needed.

## 5. Example content embedding

For each of the 22 examples in `examples_content.md`:

- hidden div `example_cs<N>_input_code` inside `<pre><code>`: the input
  text. For the 8 examples marked "the full text of ...", copy the file
  verbatim from `/opt/gkreasoner/Examples/` (people_room.js, algebra.js,
  negation_conflict.js, bird_penguin.p, gbirds.js, blocks.gkp,
  penguin_default.js, which_cannot_fly.js). HTML-escape
  `& < >` when embedding (selectExample unescapes them).
- hidden divs `example_cs<N>_input_notes` and `example_cs<N>_proof_notes`:
  the note HTML from the content file, verbatim.
- the `cs` prefix keeps ids disjoint from the predicate page's numbering
  convention in case of future merging; adjust `selectExample()` for it.

## 6. Verification (do all before committing)

1. Node-level: adapt `/opt/gk/experiments/wasm_parity/wasmrun.js` into a
   small script that, for each of the 22 examples, writes the exact input
   text the page will embed, calls the site copy of gkjs with the exact
   arglist the page will build, and compares against the expected outputs in
   `examples_content.md` (match on the quoted key lines: answers,
   confidences, flags — not byte equality). All 22 must pass. Keep the
   script as `/opt/logictools/commonsense_check.js` (committed; it documents
   the page's expected behavior).
2. Browser-level (use the Chrome automation tools if available, otherwise
   ask the user to click through): load the page from a local file or a
   quick `python3 -m http.server`, run at least examples 1, 4, 10, 12
   (JSON output), 13 (strategy preset), 18 (TPTP), 21 (fetched KB), and 20
   (verify that the 30-second preset is applied). Verify example switching
   resets notes and presets, Clear works,
   and solving twice in a row works.
3. Firefox: load once and run example 1 (the memory-size check).
4. Mobile-width sanity: the layout is bootstrap-responsive already; check
   the textarea and dropdowns at narrow width.

## 7. Commit, push, deploy

- Commit to /opt/logictools (branch master): `commonsense.html`, `gkjs.js`,
  `gkjs.wasm`, `gk_axioms_std.js`, `commonsense_check.js`, the navbar edits
  to the other pages, `about.html` + `download.html` additions,
  `sitemap.txt`, and the `commonsense_plan/` folder itself.
- `/opt/logictools` currently has unrelated untracked files (`cadical/`,
  `confer/`, `demo2/`, and tarballs). Leave them unchanged and untracked.
- Push to origin master.
- Deployment is a `git pull` on the logictools server. The server address /
  access is not recorded in this repo: ask the user whether to run the pull
  (and how to reach the server) or whether they do it themselves. Do not
  guess.

## 8. Phase 2 (only on request, not part of this build)

- Taxonomy example 23 (`classify.gkp` + `-defaults`): needs
  `gk_name_number.txt` (1.9 MB) + `gk_taxonomy_packed.txt` (1.4 MB) fetched
  on demand into the in-memory filesystem (`-datafolder` is unnecessary if
  they are written to the current directory). Texts are prepared in
  `examples_content.md` #23.
- Web Worker wrapper so long searches do not freeze the tab.
- A "show clauses" button (`-clausify`). Note: `-clausify` currently drops
  `@confidence` from its output (observed 2026-07-20 on a
  confidence-annotated GKP input); check whether that is intended before
  exposing it.
- Renaming the tab if "commonsense" changes.

## 9. Known risks / open questions

- The checked-in build reserves 2000 MB. Test it in current Firefox before
  deciding whether the site needs the 1000 MB build.
- Long searches block the UI thread (as on the predicate page). Example 20
  is the only slow one and its notes warn about it.
- Reusing `callMain` after gk calls `exit()` under `noInitialRun` works for
  gkcjs on the live site; verify once for gkjs (task 4.6).
- The English examples' JSON output contains internal clauses (`$ctxt` and
  Skolem terms). Keep the actual output unchanged.
