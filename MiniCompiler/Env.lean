namespace MiniCompiler

/--
Env 表示变量环境：
给定一个变量名，返回它当前保存的整数值。
-/
abbrev Env := String → Int

/--
空环境：
所有变量默认值都是 0。
-/
def emptyEnv : Env :=
  fun _ => 0

/--
更新环境。

update env "x" 10

得到一个新环境，其中：
x = 10

其他变量保持原来的值。
-/
def update (env : Env) (name : String) (value : Int) : Env :=
  fun x =>
    if x = name then
      value
    else
      env x

end MiniCompiler
