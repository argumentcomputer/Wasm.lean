import Megaparsec.MonadParsec
import Megaparsec.Common

open Megaparsec.Parsec
open Megaparsec.Common

namespace Wasm.Wast.Parser.Common

def ignoreP : Parsec Char String Unit Unit :=
  discard $ some' $ oneOf " \t\n".data
