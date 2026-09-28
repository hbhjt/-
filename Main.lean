import MiniCompiler

open MiniCompiler

def env : Env :=
  update
    (update emptyEnv "x" 10)
    "y" 3


def main : IO Unit := do

  IO.println "===== Expression Evaluation ====="

  IO.println s!"
exampleA1 = {evalA exampleA1 env}"

  IO.println s!"
exampleA2 = {evalA exampleA2 env}"

  IO.println s!"
exampleA3 = {evalA exampleA3 env}"


  IO.println ""
  IO.println "===== Boolean Evaluation ====="

  IO.println s!"
exampleB1 = {evalB exampleB1 env}"

  IO.println s!"
exampleB2 = {evalB exampleB2 env}"


  IO.println ""
  IO.println "===== Optimization ====="

  IO.println s!"
before optimization =
{evalA optimizeExample1 env}"

  IO.println s!"
after optimization =
{evalA (optimize optimizeExample1) env}"
