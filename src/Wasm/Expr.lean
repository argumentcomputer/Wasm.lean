
namespace Wasm

def U32 := UInt32
  deriving BEq
def F32 := Float
  deriving BEq
def F64 := Float
  deriving BEq
def I32 := Int
  deriving BEq
def I64 := Int
  deriving BEq


def Address := UInt64
  deriving BEq
def Size := UInt64
  deriving BEq
def Offset := Address
  deriving BEq

inductive Value
  | VI32 : I32 → Value
  | VI64 : I32 → Value
  | VF32 : I32 → Value
  | VF64 : I32 → Value
  deriving BEq

inductive Name 
  | name : String → Name
  -- | UnName Word32
  deriving BEq, Ord

inductive UnOp
  -- Integer
  | clz
  | ctz
  | popcnt

  -- Floating Point
  | neg
  | abs
  | ceil
  | floor
  | trunc
  | nearest
  | sqrt
  deriving BEq

inductive BinOp
  | add
  | sub
  | mul
  | divS
  | divU
  | remS
  | remU
  | and
  | or
  | xor
  | shl
  | shrU
  | shrS
  | rotR
  | rotL
  | div
  | copySign
  | min
  | max
  deriving BEq

inductive SelOp
  | select
  deriving BEq

inductive RelOp
  | eqz
  | eq
  | ne
  | ltS
  | ltU
  | gtS
  | gtU
  | leS
  | leU
  | geS
  | geU
  | lt
  | gt
  | le
  | ge
  deriving BEq

inductive ConvertOp
  | wrapI64
  | truncSF32
  | truncUF32
  | truncSF64
  | truncUF64
  | extendSI32
  | extendUI32
  | convertSI32
  | convertUI32
  | convertSI64
  | convertUI64
  | demoteF64
  | promoteF32

  | reinterpretF32
  | reinterpretF64
  | reinterpretI32
  | reinterpretI64
  deriving BEq

inductive Memop
 | Memop : (ty : Value) → (offset : Offset) → (align : Option Int) → Memop
 deriving BEq

inductive MemSize
  | mem8
  | mem16
  | mem32
  deriving BEq

inductive Extension
  | SX
  | ZX
  deriving BEq

inductive Extop
  | extop : Memop → MemSize → Extension → Extop 
  deriving BEq

inductive Wrapop
  | wrapop : Memop → MemSize → Wrapop
  deriving BEq

inductive Hostop
  | memorySize
  | growMemory
  | hasFeature : Name → Hostop
  deriving BEq

inductive Typ
  | I32
  | I64
  | F32
  | F64
  | FuncType
  deriving BEq

inductive Expr
  | nop
  | unreachable
  | block : (optName : Option Name) → (List Expr) → Expr
  | if_ : Expr → Expr
  | ifElse : Expr → Expr → Expr
  | brIf : Expr → Name → Expr
  | loop : (Option Name) → (Option Name) → (List Expr) → Expr
  | br : Name → (Option Expr) → Expr
  | return_ : Expr → Expr
  | call : Name → (List Expr) → Expr
  | const_ : Typ → Value → Expr
  | lit : Value → Expr
  | load : Memop → Expr → Expr
  | store : Memop → Expr → Expr
  | getLocal : Name → Expr
  | setLocal : Name → Expr → Expr
  | loadExtend : Extop → Expr → Expr
  | storeWrap : Wrapop → Expr → Expr → Expr
  | bin : BinOp → Typ → Expr → Expr → Expr
  | un : UnOp → Typ → Expr → Expr
  | rel : RelOp → Typ → Expr → Expr → Expr
  | sel : SelOp → Expr → Expr → Expr → Expr
  | convert : ConvertOp → Typ → Expr → Expr
  | host : Hostop → (List Expr) → Expr
  deriving BEq 

inductive Param
  | param : (Option Name) → Typ → Param 
  | result : Typ → Typ → Param
  | body : Expr → Param
  deriving BEq

inductive Func
  | func : (ftype : Option Name) → (params : List Param) → (body : List Expr) → (params : List Param) → Func
  | export_ : String → Value → Func
  | import : Name → Int → Func
  deriving BEq

inductive Module 
 | module : (funcs : List Func) → Module
 deriving BEq

inductive Decl
  | modDecl : Module → Decl
  | exprDecl : Expr → Decl
  deriving BEq
end Wasm
