def go : Nat := Id.run $ do
  "beep".length

def main : IO Unit :=
  let _ := go
  return ()
