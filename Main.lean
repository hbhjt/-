import MiniCompiler

open MiniCompiler

def main : IO Unit := do

  IO.println "=== Counter Program ==="

  match
    runStmt
      100
      counterProgram
      emptyEnv
  with

  | .ok env =>

      let x :=
        env "x"

      IO.println s!"x = {x}"

  | .error message =>

      IO.println s!"Error: {message}"


  IO.println ""

  IO.println "=== If Program ==="

  match
    runStmt
      100
      ifProgram
      emptyEnv
  with

  | .ok env =>

      let x :=
        env "x"

      let y :=
        env "y"

      IO.println s!"x = {x}"

      IO.println s!"y = {y}"

  | .error message =>

      IO.println s!"Error: {message}"


  IO.println ""

  IO.println "=== Infinite Loop ==="

  match
    runStmt
      10
      infiniteLoop
      emptyEnv
  with

  | .ok _ =>

      IO.println
        "Unexpected termination"

  | .error message =>

      IO.println s!"Error: {message}"
