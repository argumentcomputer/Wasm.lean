def go : Nat := "beep".length

def main : IO Unit :=
  let _ := go
  return ()
