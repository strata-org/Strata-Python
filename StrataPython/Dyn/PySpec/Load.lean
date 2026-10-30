/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Module
public import StrataPython.Specs
import StrataPython.Specs.DDM
import StrataPython.PythonDialect
import StrataDDM.Ion

set_option autoImplicit false

/-!
# Reading a model set

`loadModels` reads a PySpec model module and every model module it imports: PySpec translates
the module's source, and writes an Ion file for each module that it imports into a cache
directory, which is fresh for each call. The imported modules are read back from there, with
their format versions, so that `translateModels` refuses a file that an older PySpec wrote.
-/

namespace StrataPython.Dyn.PySpec

open StrataPython.Specs

public section

/-- The model set of the module `module`, whose source is `file`, under `searchPath`. PySpec
runs with the Python command `pythonCmd`, and its warnings are returned. -/
def loadModels (pythonCmd : String) (searchPath file : System.FilePath) (module : String) :
    IO (Array ModelInput × Array String) := do
  let some modName := ModuleName.ofString? module
    | throw <| IO.userError s!"'{module}' is not a module name"
  IO.FS.withTempFile fun _ dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun cache => do
      let (sigs, warnings) ← IO.ofExcept (← (translateFile (pythonCmd := pythonCmd)
        (dialectFile := dialectFile) (strataDir := cache) (pythonFile := file)
        (searchPath := searchPath) modName).toBaseIO)
      let first : ModelInput := { module := modName, version := some formatVersion, sigs }
      let mut out := #[first]
      let mut seen := #[module]
      -- The modules to read, each with whether PySpec must have written it: a module that
      -- `m` imports from must exist; one that only a type names, as `M.C` after `import M`,
      -- may not, and then its classes stay unknown.
      let mut todo : Array (String × Bool) :=
        (importsOf first).map (·, true) ++ (typeReferences first).map (·, false)
      -- Each round reads one module that PySpec wrote, and no module twice.
      for _ in [0:4096] do
        let some (m, required) := todo[0]? | break
        todo := todo.extract 1
        seen := seen.push m
        let some mn := ModuleName.ofString? m
          | if required then throw <| IO.userError s!"'{m}' is not a module name" else continue
        let some path ← mn.specIonPath cache
          | if required then
              throw <| IO.userError s!"PySpec wrote no Ion file for the imported module '{m}'"
            else continue
        let (version, sigs) ← IO.ofExcept (← (readDDMVersioned path).toBaseIO)
        let input : ModelInput := { module := mn, version, sigs }
        out := out.push input
        let next := (importsOf input).map (·, true) ++ (typeReferences input).map (·, false)
        for (i, r) in next do
          unless seen.contains i || todo.any (·.1 == i) do todo := todo.push (i, r)
      unless todo.isEmpty do
        throw <| IO.userError s!"the model set of '{module}' imports more than 4096 modules"
      return (out, warnings)

end -- public section

end StrataPython.Dyn.PySpec
