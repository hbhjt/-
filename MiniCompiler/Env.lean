namespace MiniCompiler

/--
变量环境。

变量名 String -> 变量值 Int
-/
abbrev Env := String → Int


/--
初始环境。

所有没有赋值的变量默认为 0。
-/
def emptyEnv : Env :=
  fun _ => 0


/--
更新环境。

注意：
这里没有修改原来的 env，
而是创建一个新的 Env。
-/
def update
    (env : Env)
    (name : String)
    (value : Int) : Env :=
  fun x =>
    if x = name then
      value
    else
      env x

end MiniCompiler
