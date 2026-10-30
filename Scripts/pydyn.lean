/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Cli
import StrataPython.Dyn.Cli

/-! # `pydyn`: the Python-on-Dyn command-line tool

`pydyn SUBCOMMAND ARG` runs one of:

* `dyn FILE`: the Dyn translation of a `.py` or Python Ion file, from
  `StrataPython.Dyn.Cli`.
* `read FILE`: a printed Dyn module read back and printed again, from
  `StrataPython.Dyn.Cli`.
* `pyspec SEARCH_PATH MODULE`: the IR modules of a PySpec model module and the model modules it
  imports, from `StrataPython.Dyn.Cli`.
* `features FILE`: the Python features a Python Ion file uses, from
  `StrataPython.Cli`.

`--help` and `SUBCOMMAND --help` print usage. -/

def commands : List Command :=
  [ StrataPython.Dyn.Cli.dynCommand,
    StrataPython.Dyn.Cli.readCommand,
    StrataPython.Dyn.Cli.pyspecCommand,
    StrataPython.Cli.pyFeaturesCommand ]

def commandMap : Std.HashMap String Command :=
  commands.foldl (init := {}) fun m c => m.insert c.name c

public def main (args : List String) : IO Unit :=
  runCommandMap commandMap [{ name := "pydyn", commands }] args
