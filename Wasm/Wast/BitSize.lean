import Megaparsec
import Megaparsec.Char
import Megaparsec.Common
import Megaparsec.String
import Megaparsec.Parsec

open Megaparsec
open Megaparsec.Char
open Megaparsec.Common
open Megaparsec.String
open Megaparsec.Parsec


/- Webassembly works on 32 and 64 bit ints and floats.
We define BitSize inductive to then combine it with respective constructors. -/
inductive BitSize :=
| thirtyTwo
| sixtyFour
deriving BEq

inductive BitSizeSIMD :=
| hundredTwentyEight
deriving BEq

-- Boring instances

/- 32 *is* .thirtyTwo -/
instance : OfNat BitSize 32 where
  ofNat := .thirtyTwo

/- 64 *is* .sixtyFour -/
instance : OfNat BitSize 64 where
  ofNat := .sixtyFour

/- 128 *is* .hundredTwentyEight -/
instance : OfNat BitSizeSIMD 128 where
  ofNat := .hundredTwentyEight

/- For something to depend on .thirtyTwo means that it can just as well depend on 32. -/
instance : CoeDep BitSize BitSize.thirtyTwo Nat where
  coe := 32

/- For something to depend on .sixtyFour means that it can just as well depend on 64. -/
instance : CoeDep BitSize BitSize.sixtyFour Nat where
  coe := 64

/- For something to depend on .hundredTwentyEight means that it can just as well depend on 128. -/
instance : CoeDep BitSizeSIMD BitSizeSIMD.hundredTwentyEight Nat where
  coe := 128

/- 32 *is* .thirtyTwo and 64 *is* .sixtyFour -/
instance : Coe BitSize Nat where
  coe x := match x with
  | .thirtyTwo => 32
  | .sixtyFour => 64

/- 128 *is* .hundredTwentyEight. -/
instance : Coe BitSizeSIMD Nat where
  coe x := match x with
  | .hundredTwentyEight => 128

/- We rely on numeric ordering rather than on derived ordering based on the order of constructors. -/
instance : Ord BitSize where
  compare x y := Ord.compare (x : Nat) (y : Nat)

/- We rely on numeric ordering rather than on derived ordering based on the order of constructors. -/
instance : Ord BitSizeSIMD where
  compare x y := Ord.compare (x : Nat) (y : Nat)

-- End of boring instances

def bitSizeP : Parsec Char String Unit BitSize :=
  (string "32" *> pure BitSize.thirtyTwo) <|> (string "64" *> pure BitSize.sixtyFour)
