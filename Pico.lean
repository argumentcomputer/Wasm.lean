def go : Int := Id.run $ do

  let i := "(module
        (func $main (export \"main\")
            (result i32)

            (i32.add
                (i32.const 1499550000)
                (i32.add (i32.const 9000) (i32.const 17))
            )
        )
    )"

  pure $ i.length

def main := IO.println s!"{go}"
