import Megaparsec.MonadParsec
import Megaparsec.Common

open Megaparsec.Parsec
open Megaparsec.Common

namespace Wasm.Wast.Parser.Common

def ignoreP : Parsec Char String Unit Unit :=
  void $ some' $ oneOf " \t\n".data

def owP : Parsec Char String Unit Unit :=
  void $ option' $ some' $ oneOf " \t\n".data

def specials : List Char := " ()".data

def notSpecialP : Parsec Char String Unit Char :=
  noneOf specials
