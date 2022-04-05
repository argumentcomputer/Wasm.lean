namespace Wasm

universe u v

instance : Repr ByteArray where
  reprPrec bs p := reprPrec bs.toList p

instance : BEq ByteArray where
  beq a b := a.toList == b.toList

inductive BitSize := | BS32 | BS64 deriving Repr, BEq

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

inductive IRelOp := | IEq | INe | ILtU | ILtS | IGtU | IGtS | ILeU | ILeS | IGeU | IGeS deriving BEq

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
    deriving Repr, BEq

def ResultType := ValueType
  deriving Repr, BEq
def ParamsType := ValueType
  deriving Repr, BEq
def LocalsType := ValueType
  deriving Repr, BEq

structure FuncType := (params : ParamsType) (results : ResultType) deriving Repr, BEq

inductive BlockType :=
    | inline (Option ValueType)
    | typeIndex TypeIndex
    deriving Repr, BEq

inductive InstructionNat :=
    -- Control instructions
    | Unreachable
    | Nop
    | Block (blockType : BlockType) (body : InstructionNat) : InstructionNat
    | Loop (blockType : BlockType) (body : InstructionNat) : InstructionNat
    | If (blockType : BlockType) (true : InstructionNat) (false : InstructionNat) : InstructionNat
    | Br Nat
    | BrIf Nat
    | BrTable Nat
    | Return
    | Call Nat
    | CallIndirect Nat
    -- Parametric instructions
    | Drop
    | Select
    -- Variable instructions
    | GetLocal Nat
    | SetLocal Nat
    | TeeLocal Nat
    | GetGlobal Nat
    | SetGlobal Nat
    -- Memory instructions
    | I32Load MemArg
    | I64Load MemArg
    | F32Load MemArg
    | F64Load MemArg
    | I32Load8S MemArg
    | I32Load8U MemArg
    | I32Load16S MemArg
    | I32Load16U MemArg
    | I64Load8S MemArg
    | I64Load8U MemArg
    | I64Load16S MemArg
    | I64Load16U MemArg
    | I64Load32S MemArg
    | I64Load32U MemArg
    | I32Store MemArg
    | I64Store MemArg
    | F32Store MemArg
    | F64Store MemArg
    | I32Store8 MemArg
    | I32Store16 MemArg
    | I64Store8 MemArg
    | I64Store16 MemArg
    | I64Store32 MemArg
    | CurrentMemory
    | GrowMemory
    -- Numeric instructions
    | I32Const Word32
    | I64Const Word64
    | F32Const Float
    | F64Const Double
    | IUnOp BitSize IUnOp
    | IBinOp BitSize IBinOp
    | I32Eqz
    | I64Eqz
    | IRelOp BitSize IRelOp
    | FUnOp BitSize FUnOp
    | FBinOp BitSize FBinOp
    | FRelOp BitSize FRelOp
    | I32WrapI64
    | ITruncFU /- Int Size -/ BitSize /- Float Size -/ BitSize
    | ITruncFS /- Int Size -/ BitSize /- Float Size -/ BitSize
    | ITruncSatFU /- Int Size -/ BitSize /- Float Size -/ BitSize
    | ITruncSatFS /- Int Size -/ BitSize /- Float Size -/ BitSize
    | I64ExtendSI32
    | I64ExtendUI32
    | FConvertIU /- Float Size -/ BitSize /- Int Size -/ BitSize
    | FConvertIS /- Float Size -/ BitSize /- Int Size -/ BitSize
    | F32DemoteF64
    | F64PromoteF32
    | IReinterpretF BitSize
    | FReinterpretI BitSize
    -- deriving Repr, BEq


inductive Instruction (index : Type) [BEq index] [Repr index] :=
    -- Control instructions
    | Unreachable
    | Nop
    | Block (blockType : BlockType) (body : InstructionNat)
    | Loop (blockType : BlockType) (body : InstructionNat)
    | If (blockType : BlockType) (true : InstructionNat) (false : InstructionNat)
    | Br index
    | BrIf index
    | BrTable /-[index]-/ index
    | Return
    | Call index
    | CallIndirect index
    -- Parametric instructions
    | Drop
    | Select
    -- Variable instructions
    | GetLocal index
    | SetLocal index
    | TeeLocal index
    | GetGlobal index
    | SetGlobal index
    -- Memory instructions
    | I32Load MemArg
    | I64Load MemArg
    | F32Load MemArg
    | F64Load MemArg
    | I32Load8S MemArg
    | I32Load8U MemArg
    | I32Load16S MemArg
    | I32Load16U MemArg
    | I64Load8S MemArg
    | I64Load8U MemArg
    | I64Load16S MemArg
    | I64Load16U MemArg
    | I64Load32S MemArg
    | I64Load32U MemArg
    | I32Store MemArg
    | I64Store MemArg
    | F32Store MemArg
    | F64Store MemArg
    | I32Store8 MemArg
    | I32Store16 MemArg
    | I64Store8 MemArg
    | I64Store16 MemArg
    | I64Store32 MemArg
    | CurrentMemory
    | GrowMemory
    -- Numeric instructions
    | I32Const Word32
    | I64Const Word64
    | F32Const Float
    | F64Const Double
    | IUnOp BitSize IUnOp
    | IBinOp BitSize IBinOp
    | I32Eqz
    | I64Eqz
    | IRelOp BitSize IRelOp
    | FUnOp BitSize FUnOp
    | FBinOp BitSize FBinOp
    | FRelOp BitSize FRelOp
    | I32WrapI64
    | ITruncFU /- Int Size -/ BitSize /- Float Size -/ BitSize
    | ITruncFS /- Int Size -/ BitSize /- Float Size -/ BitSize
    | ITruncSatFU /- Int Size -/ BitSize /- Float Size -/ BitSize
    | ITruncSatFS /- Int Size -/ BitSize /- Float Size -/ BitSize
    | I64ExtendSI32
    | I64ExtendUI32
    | FConvertIU /- Float Size -/ BitSize /- Int Size -/ BitSize
    | FConvertIS /- Float Size -/ BitSize /- Int Size -/ BitSize
    | F32DemoteF64
    | F64PromoteF32
    | IReinterpretF BitSize
    | FReinterpretI BitSize
    deriving Repr, BEq

def Expression := Instruction Nat
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

structure TableType := (limit : Limit) (elemType : ElemType) deriving Repr, BEq

structure Table := (type : TableType) deriving Repr, BEq

structure Memory := (limit : Limit) deriving Repr, BEq

inductive GlobalType :=
  | Const ValueType
  | Mut ValueType
  deriving Repr, BEq

inductive Global :=
    globalType : GlobalType
    initializer : Expression
    deriving Repr, BEq

inductive ElemSegment :=
    tableIndex : TableIndex
    offset : Expression
    funcIndexes : List FuncIndex
    deriving Repr, BEq

structure DataSegment :=
    memIndex : MemoryIndex
    offset : Expression
    chunk : ByteArray
    deriving Repr, BEq

structure StartFunction := (funcIndex : FuncIndex) deriving Repr, BEq

inductive ExportDesc :=
    | ExportFunc FuncIndex
    | ExportTable TableIndex
    | ExportMemory MemoryIndex
    | ExportGlobal GlobalIndex
    deriving Repr, BEq

structure Export :=
    name : String
    desc : ExportDesc
    deriving Repr, BEq

inductive ImportDesc :=
    | ImportFunc TypeIndex
    | ImportTable TableType
    | ImportMemory Limit
    | ImportGlobal GlobalType
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
    elems : List Elem
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
