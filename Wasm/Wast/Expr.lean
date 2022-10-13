/- WAST expressions as seen in the official test suite. -/

import Wasm.Wast.BitSize
import Wasm.Wast.Name
import Wasm.Wast.Num

import Megaparsec.Common
import Megaparsec.Errors
import Megaparsec.Errors.Bundle
import Megaparsec.Parsec
import Megaparsec.MonadParsec
import YatimaStdLib.NonEmpty

open Wasm.Wast.Name
open Wasm.Wast.Num

open Megaparsec
open Megaparsec.Common
open Megaparsec.Errors
open Megaparsec.Errors.Bundle
open Megaparsec.Parsec
open MonadParsec
open Cached

namespace Wasm.Wast.Expr
