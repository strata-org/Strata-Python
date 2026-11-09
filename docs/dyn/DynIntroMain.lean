/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import DynIntro
open Verso.Genre.Manual
open Verso.Output.Html

/-!
`dynintro [--single] [Verso options]` renders "Introduction to Dyn".

The defaults are palette D, IBM Plex Sans and IBM Plex Mono, with the theme following the
system; the Style menu offers the rest. Output is one HTML page per top-level section;
`--single` renders one page instead. The theme's CSS and JavaScript are read at run time from
`themes/`, so restyling needs no rebuild.
-/

def readIfExists (p : System.FilePath) : IO (Option String) := do
  if ← p.pathExists then return some (← IO.FS.readFile p) else return none

def main (args : List String) : IO UInt32 := do
  let single := args.contains "--single"
  let rest := args.filter (· != "--single")
  let read (f : String) : IO String := do return (← readIfExists s!"themes/{f}").getD ""
  let some layoutCss ← readIfExists "themes/layout.css"
    | IO.eprintln "no themes/layout.css; run from the directory of this project"; return 1
  let common ← read "common.css"
  let layoutJs ← read "layout.js"
  let fontsCss ← read "fonts.css"
  let palettes ← read "palettes.css"
  let switcherCss ← read "switcher.css"
  let switcherJs ← read "switcher.js"
  let defaults := "{key: 'dyn-intro-style', palette: 'd', theme: 'system', font: 'plex-sans', code: 'plex-mono', size: 'm'}"
  let preload := (← read "preload.js").replace "__DEFAULTS__" defaults
  let preload := if single then preload ++ "\ndocument.documentElement.classList.add('single-page');" else preload
  -- Theme CSS goes in `extraHead`, which follows every `extraCss` entry: `extraCss` is a
  -- `HashSet`, so its order (and so the cascade between entries) is unspecified.
  let css := "\n".intercalate [fontsCss, palettes, common, layoutCss, switcherCss]
  -- Vendored fonts ship as Verso data files when the theme refers to them.
  let mut fonts : Std.HashSet DataFile := {}
  if (css.splitOn "-verso-data/fonts/").length > 1 then
    for path in ← System.FilePath.walkDir "themes/fonts" do
      if ← path.isDir then continue
      let rel := (path.toString.drop "themes/".length).toString
      fonts := fonts.insert { filename := rel, contents := ← IO.FS.readBinFile path }
  let config : RenderConfig := {
    emitTeX := false
    emitHtmlSingle := if single then .immediately else .no
    emitHtmlMulti := if single then .no else .immediately
    htmlDepth := 1
    features := HtmlFeatures.empty
    extraDataFiles := fonts
    extraJs := ({} : Std.HashSet JS).insert ⟨switcherJs ++ "\n" ++ layoutJs⟩
    extraHead := #[{{<meta name="color-scheme" content="light dark"/>}},
                   {{<link rel="icon" href="data:,"/>}},
                   .tag "script" #[("id", "style-preload")] (.text false preload),
                   .tag "style" #[("id", "theme-css")] (.text false css)]
    extraContents := #[.tag "footer" #[("class", "doc-footer")] (.tag "p" #[] (.text true
      "Introduction to Dyn. Strata is open source; this page uses no network resources. Interactive panels are reading aids over the same texts the static listings show."))]
  }
  manualMain (%doc DynIntro.Doc) (options := rest) (config := config)
