import Megaparsec.MonadParsec
import Megaparsec.Common
import Megaparsec.Errors
import YatimaStdLib.Seq

open MonadParsec
open Megaparsec
open Megaparsec.Parsec
open Megaparsec.Common
open Megaparsec.Errors

namespace Wasm.Wast.Parser.Common

def formatP : Parsec Char String Unit Char :=
  oneOf "\n\t\r".data

/-- Parse a line comment. A line comment starts with a double semicolon `;;`
and extends to the end of the line or EOF. -/
def lineCommentP : Parsec Char String Unit String := do
  let comment ← string ";;" *> takeWhileP "non-newline character" (·≠'\n')
  eof <|> discard (single '\n')
  pure s!";;{comment}"

/-- Parse a block comment. A block comment is enclosed in delimiters `(;`…`;)`.
Block comments can be nested.

Per spec, only well-bracketed uses of block comment delimiters are allowed. This means that e.g. `(;(;;)` will fail to parse. -/
partial def blockCommentP : Parsec Char String Unit String := Seq.between (string "(;") (string ";)") do
  let charP := String.mk <$> flip List.cons [] <$> noneOf "(;".data
  let semicolonP := attempt $ string ";" <* notFollowedBy (single ')')
  let bracketP := attempt $ string "(" <* notFollowedBy (single ';')
  let nestedP := charP <|> semicolonP <|> bracketP <|> blockCommentP
  let comment ← many' nestedP
  pure $ s!"(;{String.join comment};)"

/-- Parse a WAST comment, which can either be a line or a block comment. -/
def commentP : Parsec Char String Unit String :=
  lineCommentP <|> blockCommentP

def spaceP : Parsec Char String Unit String :=
  string " " <|> Char.toString <$> formatP <|> commentP

def ignoreP : Parsec Char String Unit Unit :=
  discard $ some' spaceP

def owP : Parsec Char String Unit Unit :=
  discard $ many' spaceP

def specials : List Char := " ()".data

def notSpecialP : Parsec Char String Unit Char :=
  noneOf specials

def hints0 (β : Type u) [Ord β] : Std.RBSet (ErrorItem β) Ord.compare :=
  Std.mkRBSet (ErrorItem β) Ord.compare

def optional (x : Option α) (d : α) : α := x.getD d
