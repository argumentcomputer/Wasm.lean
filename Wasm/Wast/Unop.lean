import Wasm.Wast.BitSize

/- Unary Operations: consume one operand and produce one result of the respective type. -/
namespace Wasm.Wast.Unop

namespace Unop.Int

/- There are three unary operations on ints:
 1. Count leading zeroes.
 2. Count trailing zeroes.
 3. Count the amount of bits set to 1.
 Semantics: https://bug1271972.bmoattachments.org/attachment.cgi?id=8751373 -/
inductive Op (x : BitSize) :=
-- TODO: https://zulip.yatima.io/#narrow/stream/20-meta/topic/WAST.20pair.20prog/near/27516
| clz : Nat' → Op x
| ctz : Nat' → Op x
| popcnt : Nat' → Op x

end Unop.Int

namespace Unop.Float

/- There are seven unary operations on floats:
 1. Get absolute value of a float.
 2. neg?
 3. sqrt?
 4. ceil?
 5. floor?
 6. trunc?
 7. nearest? -/
inductive Op (x : BitSize) :=
-- TODO: https://zulip.yatima.io/#narrow/stream/20-meta/topic/WAST.20pair.20prog/near/27516
| abs : Float' → Op x
| neg : Float' → Op x
| sqrt : Float' → Op x
| ceil : Float' → Op x
| floor : Float' → Op x
| trunc : Float' → Op x
| nearest : Float' → Op x

end Unop.Float

end Wasm.Wast.Unop