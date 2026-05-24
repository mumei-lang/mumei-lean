def usage : String :=
  "simple-cli commands:\n  greet <name>\n  add <n> <m>\n  echo <args...>"

def joinWithSpace : List String → String
  | [] => ""
  | first :: rest => rest.foldl (fun acc part => acc ++ " " ++ part) first

def addArgs (left : String) (right : String) : Except String Nat := do
  let some l := left.toNat? | throw s!"not a natural number: {left}"
  let some r := right.toNat? | throw s!"not a natural number: {right}"
  pure (l + r)

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.println usage
      pure 0
  | ["--help"] =>
      IO.println usage
      pure 0
  | ["greet", name] =>
      IO.println s!"hello, {name}"
      pure 0
  | ["add", left, right] =>
      match addArgs left right with
      | .ok result =>
          IO.println result
          pure 0
      | .error message =>
          IO.eprintln message
          pure 2
  | "echo" :: rest =>
      IO.println (joinWithSpace rest)
      pure 0
  | _ =>
      IO.eprintln usage
      pure 2
