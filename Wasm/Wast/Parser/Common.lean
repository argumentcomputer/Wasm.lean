import Straume.Iterator
import Straume.Zeptoparsec

open Straume.Iterator
open Zeptoparsec

namespace Wasm.Wast.Parser.Common

def sepEndBy' (p : Parsec α γ) (sep : Parsec α ψ) : Parsec α $ List γ :=
  sorry

def parses? (p : Parsec α γ) (x : α) : Bool :=
  match p (Iterator.mk x 0) with
  | ParseResult.success _ _ => true
  | ParseResult.error _ _ => false

def option (p : Parsec α γ) : Parsec α $ Option γ := fun it =>
  let x := p it
  match x with
  | .success it' y => .success it' $ .some y
  | .error it' _ => .success it' .none

def ione (it : Iterator String) (p : Char → Bool) : (Option Char × Iterator String) :=
  if hasNext it then
    let c := curr it
    if p c then
      (.some c, next it)
    else
      (.none, it)
  else
    (.none, it)

partial def imanyGo (csit : List Char × Iterator String) (p : Char → Bool) : List Char × Iterator String :=
  let (cs, it) := csit
  if hasNext it then
    let c := curr it
    if p c then
      imanyGo (c :: cs, (next it)) p
    else
      (cs, it)
  else
    (cs, it)

partial def imany (it : Iterator String) (p : Char → Bool) : String × Iterator String :=
  let (cs, it') := imanyGo ([], it) p
  (String.mk ∘ List.reverse $ cs, it')

def progressing (p : Parsec String α) : Parsec String α := fun it =>
  match p it with
  | .success it' y =>
    if it'.i > it.i then
      .success it' y
    else
      .error it "The parser should have progressed, but didn't."
  | e => e

def xinxs [BEq α] (haystack : List α) (needle : α) : Bool :=
  haystack.any $ fun x => x == needle

def oneOf (includes : List Char) : Parsec String Char := progressing $ fun it =>
  .success
    (ione it $ xinxs includes).2
    (curr it)

def noneOf (excludes : List Char) : Parsec String Char := progressing $ fun it =>
  .success
    (ione it $ not ∘ xinxs excludes).2
    (curr it)

def single (c : Char) :=
  oneOf [c]

def cbetween (l : Char) (r : Char) (p : Parsec String β) : Parsec String β :=
  single l *> p <* single r

/- Obligatorily ignore some whitespace tokens. -/
def ignoreP : Parsec String Unit :=
  progressing ws

/- Optional whitespace parser. -/
def owP : Parsec String Unit :=
  ws

def specials : List Char := " ()".data

def notSpecialP : Parsec String Char := noneOf specials

def optional (x : Option α) (d : α) : α :=
    match x with
    | .none => d
    | .some y => y
