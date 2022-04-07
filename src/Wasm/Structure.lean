namespace Wasm

universe u v

instance : Repr ByteArray where
  reprPrec bs p := reprPrec bs.toList p

instance : BEq ByteArray where
  beq a b := a.toList == b.toList

inductive BitSize := | BS32 | BS64 deriving Repr, BEq

open BitSize

def Word32 := UInt32
  deriving Repr, BEq

instance : OfNat Word32 n := ⟨UInt32.ofNat n⟩

def Word64 := UInt64
  deriving Repr, BEq

instance : OfNat Word64 n := ⟨UInt64.ofNat n⟩

def Float := UInt32
  deriving Repr, BEq

instance : OfNat Float n := ⟨UInt32.ofNat n⟩

def Double := UInt64
  deriving Repr, BEq

instance : OfNat Double n := ⟨UInt64.ofNat n⟩

inductive IUnOp :=

    | IClz
    | ICtz
    | IPopcnt
    | IExtend8S
    | IExtend16S
    | IExtend32S
    deriving Repr, BEq

inductive IBinOp :=
    | IAdd
    | ISub
    | IMul
    | IDivU
    | IDivS
    | IRemU
    | IRemS
    | IAnd
    | IOr
    | IXor
    | IShl
    | IShrU
    | IShrS
    | IRotl
    | IRotr
    deriving Repr, BEq

open IBinOp

inductive IRelOp := | IEq | INe | ILtU | ILtS | IGtU | IGtS | ILeU | ILeS | IGeU | IGeS deriving Repr, BEq

inductive FUnOp := | FAbs | FNeg | FCeil | FFloor | FTrunc | FNearest | FSqrt deriving Repr, BEq

inductive FBinOp := | FAdd | FSub | FMul | FDiv | FMin | FMax | FCopySign deriving Repr, BEq

inductive FRelOp := | FEq | FNe | FLt | FGt | FLe | FGe deriving Repr, BEq

structure MemArg := (offset : Nat) (align : Nat) deriving Repr, BEq

def LabelIndex := Nat
  deriving Repr, BEq
def FuncIndex := Nat
  deriving Repr, BEq
def TypeIndex := Nat
  deriving Repr, BEq
def LocalIndex := Nat
  deriving Repr, BEq
def GlobalIndex := Nat
  deriving Repr, BEq
def MemoryIndex := Nat
  deriving Repr, BEq
def TableIndex := Nat
  deriving Repr, BEq

inductive ValueType :=
    | I32
    | I64
    | F32
    | F64
    deriving Inhabited, Repr, BEq

def ResultType := ValueType
  deriving Repr, BEq
def ParamsType := ValueType
  deriving Repr, BEq
def LocalsType := ValueType
  deriving Repr, BEq

structure FuncType := (params : ParamsType) (results : ResultType) deriving Repr, BEq

inductive BlockType :=
    | inline : (Option ValueType) → BlockType
    | typeIndex : TypeIndex → BlockType
    deriving Repr, BEq

inductive Instruction :=
    -- Control instructions
    | Unreachable : Instruction
    | Nop : Instruction
    | Block : (blockType : BlockType) → (body : Instruction) → Instruction
    | Loop : (blockType : BlockType) → (body : Instruction) → Instruction
    | If : (blockType : BlockType) → (true : Instruction) → (false : Instruction) → Instruction
    | Br : Nat → Instruction
    | BrIf : Nat → Instruction
    | BrTable : Nat → Instruction
    | Return : Instruction
    | Call : Nat → Instruction
    | CallIndirect : Nat → Instruction
    -- Parametric instructions
    | Drop : Instruction
    | Select : Instruction
    -- Variable instructions
    | GetLocal : Nat → Instruction
    | SetLocal : Nat → Instruction
    | TeeLocal : Nat → Instruction
    | GetGlobal : Nat → Instruction
    | SetGlobal : Nat → Instruction
    -- -- Memory instructions
    | I32Load : MemArg → Instruction
    | I64Load : MemArg → Instruction
    | F32Load : MemArg → Instruction
    | F64Load : MemArg → Instruction
    | I32Load8S : MemArg → Instruction
    | I32Load8U : MemArg → Instruction
    | I32Load16S : MemArg → Instruction
    | I32Load16U : MemArg → Instruction
    | I64Load8S : MemArg → Instruction
    | I64Load8U : MemArg → Instruction
    | I64Load16S : MemArg → Instruction
    | I64Load16U : MemArg → Instruction
    | I64Load32S : MemArg → Instruction
    | I64Load32U : MemArg → Instruction
    | I32Store : MemArg → Instruction
    | I64Store : MemArg → Instruction
    | F32Store : MemArg → Instruction
    | F64Store : MemArg → Instruction
    | I32Store8 : MemArg → Instruction
    | I32Store16 : MemArg → Instruction
    | I64Store8 : MemArg → Instruction
    | I64Store16 : MemArg → Instruction
    | I64Store32 : MemArg → Instruction
    | CurrentMemory : Instruction
    | GrowMemory : Instruction
    -- Numeric instructions
    | I32Const : Word32 → Instruction
    | I64Const : Word64 → Instruction
    | F32Const : Float → Instruction
    | F64Const : Double → Instruction
    | IUnOp : BitSize → IUnOp → Instruction
    | IBinOp : BitSize → IBinOp → Instruction
    | I32Eqz : Instruction
    | I64Eqz : Instruction
    | IRelOp : BitSize → IRelOp → Instruction
    | FUnOp : BitSize → FUnOp → Instruction
    | FBinOp : BitSize → FBinOp → Instruction
    | FRelOp : BitSize → FRelOp → Instruction
    | I32WrapI64 : Instruction
    | ITruncFU : /- Int Size -/ BitSize → /- Float Size -/ BitSize → Instruction
    | ITruncFS : /- Int Size -/ BitSize → /- Float Size -/ BitSize → Instruction
    | ITruncSatFU : /- Int Size -/ BitSize → /- Float Size -/ BitSize → Instruction
    | ITruncSatFS : /- Int Size -/ BitSize → /- Float Size -/ BitSize → Instruction
    | I64ExtendSI32 : Instruction
    | I64ExtendUI32 : Instruction
    | FConvertIU : /- Float Size -/ BitSize → /- Int Size -/ BitSize → Instruction
    | FConvertIS : /- Float Size -/ BitSize → /- Int Size -/ BitSize → Instruction
    | F32DemoteF64 : Instruction
    | F64PromoteF32 : Instruction
    | IReinterpretF : BitSize → Instruction
    | FReinterpretI : BitSize → Instruction
    deriving Repr, BEq

open Instruction

def Expression := Instruction
  deriving Repr, BEq

structure Function where
  funcType : TypeIndex
  localTypes : LocalsType
  body : Expression
  deriving Repr, BEq

structure Limit := (n : Nat) (l : Option Nat) deriving Repr, BEq

inductive ElemType :=
  | FuncRef
  deriving Repr, BEq

structure TableType := (limit : Limit) (elemType : ElemType)
 deriving Repr, BEq

structure Table := (type : TableType)
  deriving Repr, BEq

structure Memory := (limit : Limit)
 deriving Repr, BEq

inductive GlobalType :=
  | Const : ValueType → GlobalType
  | Mut : ValueType → GlobalType
  deriving Repr, BEq

structure Global :=
  globalType : GlobalType
  initializer : Expression
  deriving Repr, BEq

structure ElemSegment :=
  tableIndex : TableIndex
  offset : Expression
  funcIndexes : List FuncIndex
  deriving Repr, BEq

structure DataSegment :=
  memIndex : MemoryIndex
  offset : Expression
  chunk : ByteArray
  deriving Repr, BEq

structure StartFunction :=
  funcIndex : FuncIndex
  deriving Repr, BEq

inductive ExportDesc :=
    | ExportFunc : FuncIndex → ExportDesc
    | ExportTable : TableIndex → ExportDesc
    | ExportMemory : MemoryIndex → ExportDesc
    | ExportGlobal : GlobalIndex → ExportDesc
    deriving Repr, BEq

structure Export :=
    name : String
    desc : ExportDesc
    deriving Repr, BEq

inductive ImportDesc :=
    | ImportFunc : TypeIndex → ImportDesc
    | ImportTable : TableType → ImportDesc
    | ImportMemory : Limit → ImportDesc
    | ImportGlobal : GlobalType → ImportDesc
    deriving Repr, BEq

structure Import :=
    sourceModule : String
    name : String
    desc : ImportDesc
    deriving Repr, BEq

namespace Import
open ImportDesc
def isFuncImport (imp : Import) : Bool :=
  match imp.desc with
  | ImportFunc _ => true
  | _ => false

def isTableImport (imp : Import) : Bool :=
  match imp.desc with
  | ImportTable _ => true
  | _ => false

def isMemImport (imp : Import) : Bool :=
  match imp.desc with
  | ImportMemory _ => true
  | _ => false

def isGlobalImport (imp : Import) : Bool :=
  match imp.desc with
  | ImportGlobal _ => true
  | _ => false
end Import

structure Module :=
    types : List FuncType
    functions : List Function
    tables : List Table
    mems : List Memory
    globals : List Global
    elems : List ElemSegment
    datas : List DataSegment
    start : Option StartFunction
    imports : List Import
    exports : List Export
    deriving Repr, BEq

def Module.empty : Module := {
    types := [],
    functions := [],
    tables := [],
    mems := [],
    globals := [],
    elems := [],
    datas := [],
    start := none,
    imports := [],
    exports := []
  }

end Wasm
