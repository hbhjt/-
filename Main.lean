import MiniCompiler

open MiniCompiler

def env1 : Env :=
  update
    (update emptyEnv "x" 10)
    "y" 3

def main : IO Unit := do
  IO.println s!"example1 = {evalA example1 env1}"

  IO.println s!"x = {env1 "x"}"
  IO.println s!"y = {env1 "y"}"
  IO.println s!"z = {env1 "z"}"

  IO.println s!"x * 2 + y = {evalA example2 env1}"

  IO.println s!"x < y = {evalB exampleBool1 env1}"

  IO.println s!"(x < y) && !(x = 0) = {evalB exampleBool2 env1}"
