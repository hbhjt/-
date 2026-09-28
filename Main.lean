import MiniCompiler

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"


def x : Int := 10

#check x
#eval x

def addOne (x : Int) : Int :=
  x + 1

#eval addOne 5
#check addOne
