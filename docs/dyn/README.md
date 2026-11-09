# Introduction to Dyn

A guide for anyone bringing a new source language to Strata: from a parser's AST, through
the DDM, an environment and a translator, to a checked Dyn module. It is a
[Verso](https://github.com/leanprover/verso) document, and a Lake project of its own that
depends only on Verso, so it adds nothing to the package's build.

## Building

From this directory:

```
./generate.sh                 # one page per chapter, in _out/html-multi/
./generate.sh --single        # one page, in _out/html-single/
./build-one-page.sh [OUT]     # one self-contained file, _out/dyn-intro.html by default
```

The first build fetches and builds Verso, which takes a few minutes; later builds take
seconds. `LEAN_WRAPPER`, if set, is a command that each `lake` run is wrapped in, for
instance one that caps its memory.

The output works offline and from `file://`: open `_out/html-multi/index.html` in a
browser. To preview over HTTP instead:

```
python3 -m http.server 8000 --bind 127.0.0.1 -d _out/html-multi
```

The Style menu, at the top right of every page, chooses the theme (system, light, dark or
high contrast), the palette, the fonts and the text size. The fonts are under the SIL Open
Font License; each family's `OFL.txt` is beside it in `themes/fonts/`.

## Layout

- `DynIntro/Doc.lean` is the text, and `DynIntro/Blocks.lean` its custom blocks.
  `DynIntroMain.lean` renders it.
- `widgets/` holds the interactive panels, `themes/` the styles and the Style menu.
- `data/` holds the running example's texts: its source, its printed module in both forms,
  its cell-style module before and after ref-to-reg, and the stepper's, trace's, environment
  panel's and interpreter's data.  The While environment and its rules are read from the
  package itself.
- `scripts/export-data.py` copies those texts, and the excerpts of the package's own
  sources, into the listings of `Doc.lean`, the panels' data `widgets/intro-data.js` and the
  panels' static copies. Run it after editing `data/`. With `--check`, which `generate.sh`
  runs first, it changes nothing and fails if any copy differs from its source, or if a
  quoted excerpt is no longer in the package. A line `…` in a quoted listing stands for
  lines left out.
- `checks/` holds Lean files that check the guide against the package. `TypedMean.lean`,
  `RefToReg.lean` and `Exec.lean` compile the builder, ref-to-reg and execution listings and
  pin their output with `#guard_msgs`. `Lowering.lean` lowers the two programs of `data/` with
  While's lowering, and checks that their folded and full prints are the four `.dyn` files of
  `data/`, byte for byte, and that each run in `data/outcomes.json` gives its result and
  output.  `checks/run.sh` elaborates them from the package root; it needs a built package, the
  one three directories up or `DYN_PACKAGE`, and honours `LEAN_WRAPPER`.  The package's
  `lake test` runs both checks, `export-data.py --check` and every file of `checks/`, in
  `StrataPythonTestExtra/DynGuideTest.lean`, so a change to the package that breaks a checked
  listing, a pinned output, or a printed module or an outcome of `data/`, fails its tests.
  `export-data.py --check` checks that each listing whose title names a file is still in that
  file.
- Not checked: the guide's prose; the AST outline in "Your AST"; the templates of appendix D;
  the panels' captions, the stepper's source ranges, the calls that the builder trace lists,
  and the environment panel's notes on types and its list of the base's declarations (of the
  panels' data, only the stepper's line patterns and the trace's value names are checked
  against the folded print); and the static listings of work under development.
- Section 3 of the chapter "Proofs about runs" and the four chapters on abstract
  interpretation, with appendix E and the glossary's section on it, describe work that is not
  yet in the package.
  Their listings are static: neither `checks/` nor `export-data.py` checks them. A title
  says "under development", and names the file the code is in where it has one, in a form
  that `export-data.py` does not read as a quote. The excerpts of that code, and the outputs
  of its tests and commands, are inlined as written when the code was last compared with the
  guide. Only the few listings whose code is already in the package, with a title that ends
  in its path, are checked. Nothing in `checks/` needs code that is not in the package.
- `scripts/postprocess.py` makes Verso's output work offline, and `scripts/inline.py` makes
  the one-page build self-contained.

## Markup

Besides Verso's own, the text uses the blocks listed at the top of `DynIntro/Blocks.lean`.
One of them controls line breaks in tables. Inline code in a table cell wraps at its spaces,
which keeps a table of long signatures or programs within the text column but can split a
short form such as `[l, h]` or `#dyn_transfer_obligation D o τ` across lines. Code marked as
follows stays on one line:

- `::::nowrap` around a `:::table` marks all of the table's code; `::::nowrap 2 3` marks the
  code in columns 2 and 3 only, counting from 1.
- `{nowrap}` before a code span, as in ``{nowrap}`[l, h]` ``, marks that span alone.

Mark a whole table, or the columns, whose code is all short: symbols, forms, intervals. In a
column that also holds signatures or programs, which must keep wrapping, mark the short spans
one by one. Code without a space has nowhere to break and needs no mark. After a change, check
in a browser that no table scrolls.
