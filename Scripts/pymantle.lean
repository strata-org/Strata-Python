/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Cli
import StrataPython.Mantle.Cli

/-! # `pymantle`: the Python-on-Mantle command-line tool

`pymantle SUBCOMMAND ARG` runs one of:

* `mantle FILE`: the Mantle translation of a `.py` or Python Ion file, from
  `StrataPython.Mantle.Cli`.
* `features FILE`: the Python features a Python Ion file uses, from
  `StrataPython.Cli`.

`--help` and `SUBCOMMAND --help` print usage. -/

def commands : List Command :=
  [ StrataPython.Mantle.Cli.mantleCommand,
    StrataPython.Cli.pyFeaturesCommand ]

def commandMap : Std.HashMap String Command :=
  commands.foldl (init := {}) fun m c => m.insert c.name c

public def main (args : List String) : IO Unit :=
  runCommandMap commandMap [{ name := "pymantle", commands }] args
