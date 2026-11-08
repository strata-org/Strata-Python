/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- The `strataPy` executable: Strata's Core commands and the Python
-- commands, built from `pythonFrontend` with Strata's command builders.
import StrataPython.Cli

def main (args : List String) : IO Unit :=
  runCommandMap (Strata.Cli.buildCommandMap [] {} [StrataPython.Cli.pythonFrontend])
    (Strata.Cli.buildCommandGroups [] {} [StrataPython.Cli.pythonFrontend]) args
    (progName := "strataPy")
