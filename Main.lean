import MiniCompiler

open MiniCompiler

def main : IO Unit := do
  IO.println s!"example1 = {eval example1}"
  IO.println s!"example2 = {eval example2}"
  IO.println s!"example3 = {eval example3}"
