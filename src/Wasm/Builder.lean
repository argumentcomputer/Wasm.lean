import Wasm.Structure

namespace Wasm

structure FuncDef :=
  args : List ValueType
  returns : List ValueType
  locals : List ValueType
  instrs : Expression
  deriving Repr, BEq

def GenFun := ReaderT Nat (EStateM String FuncDef)
  deriving Monad, MonadExcept, MonadReader, MonadState

def genExpr (deep : Nat) (gen : GenFun A) : Expression :=
  instrs $ flip execState (FuncDef [] [] [] []) $ runReaderT gen deep

def Loc (T : Type) := Nat
  deriving Repr, BEq

def param [ValueTypeable T] (t : Proxy T) : GenFun (Loc T) := do
    let f@{ args } <- get
    put { f with args := args ++ [getValueType t] }
    return args.size

def local [ValueTypeable T] (t : Proxy T) : GenFun (Loc T) := do
    let f@{ args, locals } <- get
    put $ f { locals := locals ++ [getValueType t]}
    return $ Loc $ fromIntegral $ length args + length locals

def appendExpr (expr : Expression) : GenFun Unit := do
    modify λ de => { de with instrs := de.instrs ++ expr }
    return ()

def after (instr : Expression) (expr : GenFun a) : GenFun a := do
    let res <- expr
    modify λ de => { de with instrs := de.instrs ++ instr }
    return res

inductive TypedExpr := 
  | ExprI32 (g : GenFun (Proxy I32))
  | ExprI64 (g : GenFun (Proxy I64))
  | ExprF32 (g : GenFun (Proxy F32))
  | ExprF64 (g : GenFun (Proxy F64))

class Producer (expr : Type) where
    OutType : Type -> Type 
    asTypedExpr : expr -> TypedExpr
    asValueType : expr -> ValueType
    produce : expr -> GenFun (OutType expr)

open Producer

instance (t : Type) [ValueTypeable t] : Producer (Loc t) where
    type OutType (Loc t) := Proxy t
    asTypedExpr e :=
      let t : Loc t -> Proxy t := Proxy.mk
      match getValueType (t e) with
      | I32 -> ExprI32 (produce e >> return Proxy)
      | I64 -> ExprI64 (produce e >> return Proxy)
      | F32 -> ExprF32 (produce e >> return Proxy)
      | F64 -> ExprF64 (produce e >> return Proxy)
    asValueType e := getValueType (t e)
        where
            t :: Loc t -> Proxy t
            t _ := Proxy
    produce (Loc i) := appendExpr [GetLocal i] >> return Proxy

instance [ValueTypeable t] : Producer (Glob t) where
    type OutType (Glob t) := Proxy t
    asTypedExpr e := match getValueType (t e) with
        | I32 -> ExprI32 (produce e >> return Proxy)
        | I64 -> ExprI64 (produce e >> return Proxy)
        | F32 -> ExprF32 (produce e >> return Proxy)
        | F64 -> ExprF64 (produce e >> return Proxy)
        where
            t :: Glob t -> Proxy t
            t _ := Proxy
    asValueType e := getValueType (t e)
        where
            t :: Glob t -> Proxy t
            t _ := Proxy
    produce (Glob i) := appendExpr [GetGlobal i] >> return Proxy

instance [ValueTypeable t] : Producer (GenFun (Proxy t)) where
    OutType (GenFun (Proxy t)) := Proxy t
    asTypedExpr e := match getValueType (Proxy.mk e) with
        | I32 => ExprI32 (produce e >> return Proxy)
        | I64 => ExprI64 (produce e >> return Proxy)
        | F32 => ExprF32 (produce e >> return Proxy)
        | F64 => ExprF64 (produce e >> return Proxy)
        where
            t :: GenFun (Proxy t) -> Proxy t
            t _ := Proxy
    asValueType e := getValueType (Proxy.mk e)
        where
            t :: GenFun (Proxy t) -> Proxy t
            t _ := Proxy
    produce := id

def ret [Producer Expr] (expr : Expr) : GenFun (OutType expr) := Producer.produce

def arg [Producer Expr] (e : Expr) : GenFun Unit := Producer.produce e >> return ()

def ValueType.size : ValueType -> BitSize
  | I32 => BS32
  | I64 => BS64
  | F32 => BS32
  | F64 => BS64

def IsInt (i : Type) : Prop :=
    if i = Proxy I32 then True
    else if i = (Proxy I64) then True
    else False

type family IsFloat i :: Bool where
    IsFloat (Proxy F32) := True
    IsFloat (Proxy F64) := True
    IsFloat any         := False

def nop : GenFun () := appendExpr [Nop]

def drop [Producer Val] (val : Val) : GenFun Unit := do
    Producer.produce val
    appendExpr [Drop]

def select [Producer A] [Producer B] OutType A ~ OutType B, Producer Pred, OutType Pred ~ Proxy I32) => (pred : Pred) (a : A)  (b : B) : GenFun (OutType a) :=
  let select' := λ (pred : GenFun Pred)  (a : GenFun Val) (b : GenFun Val) -> GenFun Val => do
      a
      res <- b
      pred
      appendExpr [Select]
      return res
   select' (produce pred) (produce a) (produce b)

def iBinOp [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A))  (op : IBinOp) (a : A) (b : B) : GenFun (OutType A) :=
  produce a >> after [(getSize $ asValueType a) op] (produce b)

def iUnOp [Producer A] (h : IsInt (OutType A)) (op : IUnOp) (a : A) : GenFun (OutType A) :=
  after [IUnOp (getSize $ asValueType a) op] (produce a)

def iRelOp [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (op : IRelOp) (a : A) (b : B) : GenFun (Proxy I32) := do
  produce a
  produce b
  appendExpr [IRelOp (getSize $ asValueType a) op]
  return Proxy

def add [Producer A] [Producer B] (h : OutType A = OutType B) (a : A) (b : B) : GenFun (OutType A) := do
    produce a
    match asValueType a with
    | I32 => after [IBinOp BS32 IAdd] (produce b)
    | I64 => after [IBinOp BS64 IAdd] (produce b)
    | F32 => after [FBinOp BS32 FAdd] (produce b)
    | F64 => after [FBinOp BS64 FAdd] (produce b)

def inc [Consumer A] [Producer A] [Integral I] (i : I) (a : A) : GenFun Unit :=
  match asTypedExpr a with
  | ExprI32 e => a .= (add e i32c i)
  | ExprI64 e => a .= (add e i64c i)
  | ExprF32 e => a .= (add e f32c i)
  | ExprF64 e => a .= (add e f64c i)

def sub [Producer A] [Producer B] (h : OutType A = OutType B) (a : A) (b : B) : GenFun (OutType A) := do
    produce a
    match asValueType a with
    | I32 => after [IBinOp BS32 ISub] (produce b)
    | I64 => after [IBinOp BS64 ISub] (produce b)
    | F32 => after [FBinOp BS32 FSub] (produce b)
    | F64 => after [FBinOp BS64 FSub] (produce b)

def dec [Consumer A] [Producer A] [Integral I] (i : I) (a : A) : GenFun Unit :=
  match asTypedExpr a with
  | ExprI32 e => a .= (sub e i32c i)
  | ExprI64 e => a .= (sub e i64c i)
  | ExprF32 e => a .= (sub e f32c i)
  | ExprF64 e => a .= (sub e f64c i)

def mul [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) := do
mul a b := do
    produce a
    match asValueType a with
    | I32 => after [IBinOp BS32 IMul] (produce b)
    | I64 => after [IBinOp BS64 IMul] (produce b)
    | F32 => after [FBinOp BS32 FMul] (produce b)
    | F64 => after [FBinOp BS64 FMul] (produce b)

def div_u  [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IDivU

def div_s [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IDivS

def rem_u [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IRemU

def rem_s [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IRemS

def and [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IAnd

def or  [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IOr

def xor  [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IXor

def shl  [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IShl

def shr_u [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IShrU

def shr_s [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IShrS

def rotl [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IRotl

def rotr [Producer A] [Producer B] (h : OutType A = OutType B) (h2 : IsInt (OutType A)) (a : A) (b : B) : GenFun (OutType A) :=
  iBinOp IRotr 

def clz [Producer A] (h : IsInt (OutType A)) (a : A) : GenFun (OutType A) :=
  iUnOp IClz

def ctz [Producer A] (h : IsInt (OutType A)) (a : A) : GenFun (OutType A) :=
  iUnOp ICtz

def popcnt [Producer A] (h : IsInt (OutType A)) (a : A) : GenFun (OutType A) :=
  iUnOp IPopcnt

def eq [Producer A] [Producer B] (h : OutType A = OutType B) (a : A) (b : B) : GenFun (Proxy I32) := do
  produce a
  produce b
  match asValueType a with
  | I32 => appendExpr [IRelOp BS32 IEq]
  | I64 => appendExpr [IRelOp BS64 IEq]
  | F32 => appendExpr [FRelOp BS32 FEq]
  | F64 => appendExpr [FRelOp BS64 FEq]
  return Proxy

ne :: (Producer a, Producer b, OutType a ~ OutType b) => a -> b -> GenFun (Proxy I32)
ne a b := do
    produce a
    produce b
|     =atch asValueType a with
|     =   I32 -> appendExpr [IRelOp BS32 INe]
|     =   I64 -> appendExpr [IRelOp BS64 INe]
|     =   F32 -> appendExpr [FRelOp BS32 FNe]
        F64 -> appendExpr [FRelOp BS64 FNe]
    return Proxy

lt_s :: (Producer a, Producer b, OutType a ~ OutType b, IsInt (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
lt_s := iRelOp ILtS

lt_u :: (Producer a, Producer b, OutType a ~ OutType b, IsInt (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
lt_u := iRelOp ILtU

gt_s :: (Producer a, Producer b, OutType a ~ OutType b, IsInt (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
gt_s := iRelOp IGtS

gt_u :: (Producer a, Producer b, OutType a ~ OutType b, IsInt (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
gt_u := iRelOp IGtU

le_s :: (Producer a, Producer b, OutType a ~ OutType b, IsInt (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
le_s := iRelOp ILeS

le_u :: (Producer a, Producer b, OutType a ~ OutType b, IsInt (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
le_u := iRelOp ILeU

ge_s :: (Producer a, Producer b, OutType a ~ OutType b, IsInt (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
ge_s := iRelOp IGeS

ge_u :: (Producer a, Producer b, OutType a ~ OutType b, IsInt (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
ge_u := iRelOp IGeU

eqz :: (Producer a, IsInt (OutType a) ~ True) => a -> GenFun (Proxy I32)
eqz a := do
    produce a
    match asValueType a with
    | I32 => appendExpr [I32Eqz]
    | I64 => appendExpr [I64Eqz]
    | _ => error "Impossible by type constraint"
    return Proxy

fBinOp :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => FBinOp -> a -> b -> GenFun (OutType a)
fBinOp op a b := produce a >> after [FBinOp (getSize $ asValueType a) op] (produce b)

fUnOp :: (Producer a, IsFloat (OutType a) ~ True) => FUnOp -> a -> GenFun (OutType a)
fUnOp op a := after [FUnOp (getSize $ asValueType a) op] (produce a)

fRelOp :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => FRelOp -> a -> b -> GenFun (Proxy I32)
fRelOp op a b := do
    produce a
    produce b
    appendExpr [FRelOp (getSize $ asValueType a) op]
    return Proxy

div_f :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => a -> b -> GenFun (OutType a)
div_f := fBinOp FDiv

min_f :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => a -> b -> GenFun (OutType a)
min_f := fBinOp FMin

max_f :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => a -> b -> GenFun (OutType a)
max_f := fBinOp FMax

copySign :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => a -> b -> GenFun (OutType a)
copySign := fBinOp FCopySign

abs_f :: (Producer a, IsFloat (OutType a) ~ True) => a -> GenFun (OutType a)
abs_f := fUnOp FAbs

neg_f :: (Producer a, IsFloat (OutType a) ~ True) => a -> GenFun (OutType a)
neg_f := fUnOp FNeg

ceil_f :: (Producer a, IsFloat (OutType a) ~ True) => a -> GenFun (OutType a)
ceil_f := fUnOp FCeil

floor_f :: (Producer a, IsFloat (OutType a) ~ True) => a -> GenFun (OutType a)
floor_f := fUnOp FFloor

trunc_f :: (Producer a, IsFloat (OutType a) ~ True) => a -> GenFun (OutType a)
trunc_f := fUnOp FTrunc

nearest_f :: (Producer a, IsFloat (OutType a) ~ True) => a -> GenFun (OutType a)
nearest_f := fUnOp FAbs

sqrt_f :: (Producer a, IsFloat (OutType a) ~ True) => a -> GenFun (OutType a)
sqrt_f := fUnOp FAbs

lt_f :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
lt_f := fRelOp FLt

gt_f :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
gt_f := fRelOp FGt

le_f :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
le_f := fRelOp FLe

ge_f :: (Producer a, Producer b, OutType a ~ OutType b, IsFloat (OutType a) ~ True) => a -> b -> GenFun (Proxy I32)
ge_f := fRelOp FGe

i32c :: (Integral i) => i -> GenFun (Proxy I32)
i32c i := appendExpr [I32Const $ asWord32 $ fromIntegral i] >> return Proxy

i64c :: (Integral i) => i -> GenFun (Proxy I64)
i64c i := appendExpr [I64Const $ asWord64 $ fromIntegral i] >> return Proxy

f32c :: Float -> GenFun (Proxy F32)
f32c f := appendExpr [F32Const f] >> return Proxy

f64c :: Double -> GenFun (Proxy F64)
f64c d := appendExpr [F64Const d] >> return Proxy

wrap :: (Producer i, OutType i ~ Proxy I64) => i -> GenFun (Proxy I32)
wrap big := do
    produce big
    appendExpr [I32WrapI64]
    return Proxy

trunc_u :: (Producer f, IsFloat (OutType f) ~ True, IsInt (Proxy t) ~ True, ValueTypeable t) => Proxy t -> f -> GenFun (Proxy t)
trunc_u t float := do
    produce float
    appendExpr [ITruncFU (getSize $ getValueType t) (getSize $ asValueType float)]
    return Proxy

trunc_s :: (Producer f, IsFloat (OutType f) ~ True, IsInt (Proxy t) ~ True, ValueTypeable t) => Proxy t -> f -> GenFun (Proxy t)
trunc_s t float := do
    produce float
    appendExpr [ITruncFS (getSize $ getValueType t) (getSize $ asValueType float)]
    return Proxy

extend_u :: (Producer i, OutType i ~ Proxy I32) => i -> GenFun (Proxy I64)
extend_u small := do
    produce small
    appendExpr [I64ExtendUI32]
    return Proxy

extend_s :: (Producer i, OutType i ~ Proxy I32) => i -> GenFun (Proxy I64)
extend_s small := do
    produce small
    appendExpr [I64ExtendSI32]
    return Proxy

convert_u :: (Producer i, IsInt (OutType i) ~ True, IsFloat (Proxy t) ~ True, ValueTypeable t) => Proxy t -> i -> GenFun (Proxy t)
convert_u t int := do
    produce int
    appendExpr [FConvertIU (getSize $ getValueType t) (getSize $ asValueType int)]
    return Proxy

convert_s :: (Producer i, IsInt (OutType i) ~ True, IsFloat (Proxy t) ~ True, ValueTypeable t) => Proxy t -> i -> GenFun (Proxy t)
convert_s t int := do
    produce int
    appendExpr [FConvertIS (getSize $ getValueType t) (getSize $ asValueType int)]
    return Proxy

demote :: (Producer f, OutType f ~ Proxy F64) => f -> GenFun (Proxy F32)
demote f := do
    produce f
    appendExpr [F32DemoteF64]
    return Proxy

promote :: (Producer f, OutType f ~ Proxy F32) => f -> GenFun (Proxy F64)
promote f := do
    produce f
    appendExpr [F64PromoteF32]
    return Proxy

type family SameSize a b where
    SameSize (Proxy I32) (Proxy F32) := True
    SameSize (Proxy I64) (Proxy F64) := True
    SameSize (Proxy F32) (Proxy I32) := True
    SameSize (Proxy F64) (Proxy I64) := True
    SameSize a           b           := False

reinterpret :: (ValueTypeable t, Producer val, SameSize (Proxy t) (OutType val) ~ True) => Proxy t -> val -> GenFun (Proxy t)
reinterpret t val := do
    match (getValueType t, asValueType val) with
      |   (I=2, F32) -> appendExpr [IReinterpretF BS32]
      |   (I=4, F64) -> appendExpr [IReinterpretF BS64]
      |   (F=2, I32) -> appendExpr [FReinterpretI BS32]
      |   (F=4, I64) -> appendExpr [FReinterpretI BS64]
        _ -> error "Impossible by type constraint"
    return Proxy

load :: (ValueTypeable t, Producer addr, OutType addr ~ Proxy I32, Integral withfset, Integral align)
    => Prox| y t
=   -> addr| 
   =-> with| fset=    -> alig| n
  = -> GenFun (Proxy t| )
lo=d t addr withfset a| lign=:= do
    produce addr
    | matc= getValueType|  t w=th
    |     =32 -> appendE| xpr =I32Load $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     =64 -> appen| dExp= [I64Load $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     =32 -> appen| dExp= [F32Load $ MemArg (fromIntegral withfset) (fromIntegral align)]
        F64 -> appen| dExp= [F64Load $ MemArg (fromIntegral withfset) (fromIntegral align)]
    return Pr| oxy
=load8_u :: (V| alue=yp| eabl= t, IsInt (Proxy t) ~ True, Producer addr, OutType addr ~ Proxy I32, Integral withfset, Integral align)
    => Prox| y | =
  = -> addr| 
   =-> with| fs| =t
 =  -> alig| n
  = -> GenFun (Proxy|  t)
=| oad8=u t addr withf| set =lign := do
 |    p=oduce addr
 |    |=matc= getValueType t with
 |    |=    =32 -> appendExpr [I32Load8U $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     =64 -> appendE| xpr =I64Load8U $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     = -> error "Im| poss=ble by type constraint"
    return Proxy

load8_s :: (ValueTypea| ble =, IsInt (Proxy t) ~ True, Producer addr, OutType addr ~ Proxy I32, Integral withfset, Integral align)
    => Prox| y t
=   -> addr| 
   =-> with| fset=    -> alig| n
  = -> GenFun (Proxy t| )
l|=oad8=s t addr withfse| t al=gn := do
 |    p=oduce addr
 |    |=matc= getValueType t with
 |    |=    =32 -> appendExpr [I32Load8S $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     =64 -> appendE| xpr =I64Load8S $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     = -> error "Im| poss=ble by type constraint"
    return Proxy

load16_u :: (ValueType| able=t, IsInt (Proxy t) ~ True, Producer addr, OutType addr ~ Proxy I32, Integral withfset, Integral align)
    => Prox| y t
=   -> addr| 
   =-> with| fset=    -> alig| n
  = -> GenFun (Proxy t| )
lo= ad16=u t addr withfs| et a=ign := do
  |   pr=duce addr
  |   | =atc= getValueType t with
  |   | =   =32 -> appendExpr [I32Load16U $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     =64 -> appendEx| pr [=64Load16U $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     = -> error "Imp| ossi=le by type constraint"
    return Proxy

load16_s :: (ValueTypea| ble =, IsInt (Proxy t) ~ True, Producer addr, OutType addr ~ Proxy I32, Integral withfset, Integral align)
    => Prox| y t
=   -> addr| 
   =-> with| fset=    -> alig| n
  = -> GenFun (Proxy t)| 
lo|=ad16=s t addr withfse| t al=gn := do
  |   pr=duce addr
  |   | =atc= getValueType t with
  |   | =   =32 -> appendExpr [I32Load16S $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     =64 -> appendEx| pr [=64Load16S $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     = -> error "Imp| ossi=le by type constraint"
    return Proxy

load32_u :: (ValueTypea| ble =, IsInt (Proxy t) ~ True, Producer addr, OutType addr ~ Proxy I32, Integral withfset, Integral align)
    => Prox| y t
=   -> addr| 
   =-> with| fset=    -> alig| n
  = -> GenFun (Proxy t)| 
lo|=ad32=u t addr withfse| t al=gn := do
  |   pr=duce addr
  |   ap=endExpr [I64Load32U $ MemArg (fromIntegral withfset) (fromIntegral align)]
  |   re=urn P| roxy=
load32_s :: | (Val=eTypeable t, IsInt (Proxy t) ~ True, Producer addr, OutType addr ~ Proxy I32, Integral withfset, Integral align)
    => Prox| y|  =
 =  -> addr| 
   =-> with| f| s=t
=   -> alig| n
  = -> GenFun (Proxy t)
lo| ad32=s t addr withfset align := do
  |   pr=duce addr
  |   ap=endExpr [I64Load32S $ MemArg (fromIntegral withfset) (fromIntegral align)]
  |   re=urn P| roxy=
store :: (Pr| oduc=r addr, OutType addr ~ Proxy I32, Producer val, Integral withfset, Integral align)
    => a| ddr
=   -> v| al
 =  -> w| ithf= set
=   -> a| lign= 
   =-> | GenF=n ()
store a| ddr =al withfset align := do
    pro| duce=addr
    pro| duce=val
    | matc= asValueType val with
    |     =32 -> appendExpr [I32Store $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     =64 -> append| Expr=[I64Store $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     =32 -> append| Expr=[F32Store $ MemArg (fromIntegral withfset) (fromIntegral align)]
        F64 -> append| Expr=[F64Store $ MemArg (fromIntegral withfset) (fromIntegral align| )]

=tore8 :: (Producer a| ddr,=OutType addr ~ Proxy I32, Producer val, IsInt (OutType val) ~ | True= Integral withfset, Integral align)
    => a| ddr
=   -> v| al
 =  -> w| ithf=et
    -> a| lign=    -> G| enFu= ()
store8 a| ddr =al withf| set =lign := do
    prod| uce =ddr
    prod| uce =al
    | matc= asValueType|  val=with
    |     =32 -> appendExpr [I32Store8 $ MemArg (fromIntegral withfset) (fromIntegral alig| n)]
=   |     =64 -> appendE| xpr =I64Store8 $ MemArg (fromIntegral withfset) (fromIntegral alig| n)]
=   |     = -> error "Im| poss=ble by type constraint"

store16 :: (Producer a| ddr,=OutType addr ~ Proxy I32, Producer val, IsInt (OutType val) ~ True, Integral withfset, Integral align)
    => a| ddr
=   -> v| al
 =  -> w| ithf=et
    -> a| lign=    -> Ge| nFun=()
store16 a| ddr =al withf| set =lign := do
    produ| ce a=dr
    produ| ce v=l
    | matc= asValueType | val =ith
    |     =32 -> appendExpr [I32Store16 $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     =64 -> appendEx| pr [=64Store16 $ MemArg (fromIntegral withfset) (fromIntegral align)]
    |     = -> error "Imp| ossi=le by type constraint"

store32 :: (Producer ad| dr, =utType addr ~ Proxy I32, Producer val, OutType val ~ Proxy I64, Integral withfset, Integral align)
    => a| ddr
=   -> v| al
 =  -> w| ithf=et
    -> a| lign=    -> Ge| nFun=()
store32 a| ddr =al withfs| et a=ign := do
    produ| ce a=dr
    produ| ce v=l
    appendExpr [I64Stor| e32 = MemArg (fromIntegral withfset) (fromIntegral align| )]

=emorySize :: GenFun (Proxy I32)
memorySize := appendExpr [CurrentMemory] >> return Proxy

growMemory :: (Producer size, OutType size ~ Proxy I32) => size -> GenFun ()
growMemory size := produce size >> appendExpr [GrowMemory]

call :: (Returnable res) => Fn res -> [GenFun a] -> GenFun res
call (Fn idx) args := sequence_ args >> appendExpr [Call idx] >> return returna| bleV=lue

callIndirect :: (Producer index, OutType index ~ Proxy I32, Returnable res) => | Type=ef res -> index -> [GenFun a] -> GenFun res
callIndirect (TypeDef idx) index args := do
    sequence_ args
    produce index
    appendExpr [CallIndirect idx]
    return returnableValue

br :: Label t -> GenFun ()
br (Label labelDeep) := do
    deep <- ask
    appendExpr [Br $ deep - labelDeep]

brIf :: (Producer pred, OutType pred ~ Proxy I32) => pred -> Label t -> GenFun | ()
b=If pred (Label labelDeep) := do
    produce pred
    deep <- ask
    appendExpr [BrIf $ deep - labelDeep]

brTable :: (Producer selector, OutType selector ~ Proxy I32) => selector -> [Label t] -> Label t -> GenFun ()
brTable selector labels (Label labelDeep) := do
    produce selector
    deep <- ask
    appendExpr [BrTable (map (\(Label d) -> deep - d) labels) $ deep - labelDeep]

finish :: (Producer val) => val -> GenFun ()
finish val := do
    produce val
    appendExpr [Return]

newtype Label i := Label Nat deriving Repr, BEq
{-
when :: (Producer pred, OutType pred ~ Proxy I32)
    => pred
    -> GenFun ()
    -> GenFun ()
when pred body := if' () pred body (return ())

for :: (Producer pred, OutType pred ~ Proxy I32) => GenFun () -> pred -> GenFun () -> GenFun () -> GenFun ()
for initer pred after body := do
    initer
    let loopBody := do
            body
            after
            loopLabel <- label
            if' () pred (br loopLabel) (return ())
    if' () pred (loop () loopBody) (return ())

while :: (Producer pred, OutType pred ~ Proxy I32) => pred -> GenFun () -> GenFun ()
while pred body := do
    let loopBody := do
            body
            loopLabel <- label
            if' () pred (br loopLabel) (return ())
    if' () pred (loop () loopBody) (return ())-}

label :: GenFun (Label t)
label := Label <$> ask

-- if' :: (Producer pred, OutType pred ~ Proxy I32, Returnable res)
--     => res
--     -> pred
--     -> GenFun res
--     -> GenFun res
--     -> GenFun res
-- if' res pred true false := do
--     produce pred
--     deep <- (+1) <$> ask
--     appendExpr [If (asResultValue res) (genExpr deep $ true) (genExpr deep $ false)]
--     return returnableValue

-- loop :: (Returnable res) => res -> GenFun res -> GenFun res
-- loop res body := do
--     deep <- (+1) <$> ask
--     appendExpr [Loop (asResultValue res) (genExpr deep $ body)]
--     return returnableValue

-- block :: (Returnable res) => res -> GenFun res -> GenFun res
-- block res body := do
--     deep <- (+1) <$> ask
--     appendExpr [Block (asResultValue res) (genExpr deep $ body)]
--     return returnableValue

trap :: Proxy t -> GenFun (Proxy t)
trap t := do
    appendExpr [Unreachable]
    return t

unreachable :: GenFun ()
unreachable := appendExpr [Unreachable]

class Consumer loc where
    infixr 2 .=
    (.=) :: (Producer expr) => loc -> expr -> GenFun ()

instance Consumer (Loc t) where
    (.=) (Loc i) expr := produce expr >> appendExpr [SetLocal i]

instance Consumer (Glob t) where
    (.=) (Glob i) expr := produce expr >> appendExpr [SetGlobal i]

newtype TypeDef t := TypeDef Nat deriving Repr, BEq

typedef :: (Returnable res) => res -> [ValueType] -> GenMod (TypeDef res)
typedef res args := do
    let t := FuncType args (asResultValue res)
    st@GenModState { target := m@Module { types } } <- get
    let (idx, inserted) := Maybe.fromMaybe (length types, types ++ [t]) $ (\i -> (i, types)) <$> List.findIndex (== t) types
    put $ st { target := m { types := inserted } }
    return $ TypeDef $ fromIntegral idx

newtype Fn a := Fn Nat deriving Repr, BEq

class Returnable a where
    asResultValue :: a -> [ValueType]
    returnableValue :: a

instance (ValueTypeable t) => Returnable (Proxy t) where
    asResultValue t := [getValueType t]
    returnableValue := Proxy

instance Returnable () where
    asResultValue _ := []
    returnableValue := ()

funRec :: (Returnable res) => res -> (Fn res -> GenFun res) -> GenMod (Fn res)
funRec res generator := do
    st@GenModState { target := m@Module { types, functions }, funcIdx } <- get
    let FuncDef { args, locals, instrs } := execState (runReaderT (generator (Fn funcIdx)) 0) $ FuncDef [] [] [] []
    let t := FuncType args (asResultValue res)
    let (idx, inserted) := Maybe.fromMaybe (length types, types ++ [t]) $ (\i -> (i, types)) <$> List.findIndex (== t) types
    put $ st {
        target := m { functions := functions ++ [Function (fromIntegral idx) locals instrs], types := inserted },
        funcIdx := funcIdx + 1
    }
    return $ Fn funcIdx

fun :: (Returnable res) => res -> GenFun res -> GenMod (Fn res)
fun res := funRec res . const

declare :: (Returnable res) => res -> [ValueType] -> GenMod (Fn res)
declare res args := do
    st@GenModState { target := m@Module { types, functions }, funcIdx } <- get
    let t := FuncType args (asResultValue res)
    let (idx, inserted) := Maybe.fromMaybe (length types, types ++ [t]) $ (\i -> (i, types)) <$> List.findIndex (== t) types
    let err := error "Declared function doesn't have implementation"
    put $ st {
        target := m { functions := functions ++ [Function (fromIntegral idx) err err], types := inserted },
        funcIdx := funcIdx + 1
    }
    return $ Fn funcIdx

implement :: (Returnable res) => Fn res -> GenFun res -> GenMod (Fn res)
implement (Fn funcIdx) generator := do
    st@GenModState { target := m@Module { types, functions, imports } } <- get
    let FuncDef { args, locals, instrs } := execState (runReaderT generator 0) $ FuncDef [] [] [] []
    let locIdx := fromIntegral funcIdx - (length $ filter isFuncImport imports)
    let (l, inst : r) := splitAt locIdx functions
    let typeIdx := funcType inst
    let FuncType ps _ := types !! fromIntegral typeIdx
    if args /= ps then error "Arguments list in implementation doesn't match with declared type" else return ()
    put $ st { target := m { functions := l ++ [Function typeIdx locals instrs] ++ r } }
    return $ Fn funcIdx

nextFuncIndex :: GenMod Nat
nextFuncIndex := gets funcIdx

data GenModState := GenModState {
    funcIdx :: Nat,
    globIdx :: Nat,
    target :: Module
} deriving Repr, BEq

type GenMod := State GenModState

genMod :: GenMod a -> Module
genMod := target . flip execState (GenModState 0 0 emptyModule)

importFunction :: (Returnable res) => TL.Text -> TL.Text -> res -> [ValueType] -> GenMod (Fn res)
importFunction mod name res params := do
    st@GenModState { target := m@Module { types, imports }, funcIdx } <- get
    let t := FuncType params (asResultValue res)
    let (idx, inserted) := Maybe.fromMaybe (length types, types ++ [t]) $ (\i -> (i, types)) <$> List.findIndex (== t) types
    put $ st {
        target := m { imports := imports ++ [Import mod name $ ImportFunc $ fromIntegral idx], types := inserted },
        funcIdx := funcIdx + 1
    }
    return (Fn funcIdx)

importGlobal :: (ValueTypeable t) => TL.Text -> TL.Text -> Proxy t -> GenMod (Glob t)
importGlobal mod name t := do
    st@GenModState { target := m@Module { imports }, globIdx } <- get
    put $ st {
        target := m { imports := imports ++ [Import mod name $ ImportGlobal $ Const $ getValueType t] },
        globIdx := globIdx + 1
    }
    return $ Glob globIdx

importMemory :: TL.Text -> TL.Text -> Nat -> Maybe Nat -> GenMod Mem
importMemory mod name min max := do
    modify $ \(st@GenModState { target := m }) -> st {
        target := m { imports := imports m ++ [Import mod name $ ImportMemory $ Limit min max] }
    }
    return $ Mem 0

importTable :: TL.Text -> TL.Text -> Nat -> Maybe Nat -> GenMod Tbl
importTable mod name min max := do
    modify $ \(st@GenModState { target := m }) -> st {
        target := m { imports := imports m ++ [Import mod name $ ImportTable $ TableType (Limit min max) FuncRef] }
    }
    return $ Tbl 0

class Exportable e where
    type AfterExport e
    export :: TL.Text -> e -> GenMod (AfterExport e)

instance (Exportable e) => Exportable (GenMod e) where
    type AfterExport (GenMod e) := AfterExport e
    export name def := do
        ent <- def
        export name ent

instance Exportable (Fn t) where
    type AfterExport (Fn t) := Fn t
    export name (Fn funIdx) := do
        modify $ \(st@GenModState { target := m }) -> st {
            target := m { exports := exports m ++ [Export name $ ExportFunc funIdx] }
        }
        return (Fn funIdx)

instance Exportable (Glob t) where
    type AfterExport (Glob t) := Glob t
    export name g@(Glob idx) := do
        modify $ \(st@GenModState { target := m }) -> st {
            target := m { exports := exports m ++ [Export name $ ExportGlobal idx] }
        }
        return g

instance Exportable Mem where
    type AfterExport Mem := Mem
    export name (Mem memIdx) := do
        modify $ \(st@GenModState { target := m }) -> st {
            target := m { exports := exports m ++ [Export name $ ExportMemory memIdx] }
        }
        return (Mem memIdx)

instance Exportable Tbl where
    type AfterExport Tbl := Tbl
    export name (Tbl tableIdx) := do
        modify $ \(st@GenModState { target := m }) -> st {
            target := m { exports := exports m ++ [Export name $ ExportTable tableIdx] }
        }
        return (Tbl tableIdx)

class ValueTypeable a where
    type ValType a
    getValueType :: (Proxy a) -> ValueType
    initWith :: (Proxy a) -> (ValType a) -> Expression

instance ValueTypeable I32 where
    type ValType I32 := Word32
    getValueType _ := I32
    initWith _ w := [I32Const w]

instance ValueTypeable I64 where
    type ValType I64 := Word64
    getValueType _ := I64
    initWith _ w := [I64Const w]

instance ValueTypeable F32 where
    type ValType F32 := Float
    getValueType _ := F32
    initWith _ f := [F32Const f]

instance ValueTypeable F64 where
    type ValType F64 := Double
    getValueType _ := F64
    initWith _ d := [F64Const d]

i32 := Proxy @I32
i64 := Proxy @I64
f32 := Proxy @F32
f64 := Proxy @F64

newtype Glob t := Glob Nat deriving Repr, BEq

global :: (ValueTypeable t) => (ValueType -> GlobalType) -> Proxy t -> (ValType t) -> GenMod (Glob t)
global mkType t val := do
    idx <- gets globIdx
    modify $ \(st@GenModState { target := m }) -> st {
        target := m { globals := globals m ++ [Global (mkType $ getValueType t) (initWith t val)] },
        globIdx := idx + 1
    }
    return $ Glob idx

setGlobalInitializer :: forall t . (ValueTypeable t) => Glob t -> (ValType t) -> GenMod ()
setGlobalInitializer (Glob idx) val := do
    modify $ \(st@GenModState { target := m }) ->
        let globImpsLen := length $ filter isGlobalImport $ imports m in
        let (h, glob:t) := splitAt (fromIntegral idx - globImpsLen) $ globals m in
        st {
            target := m { globals := h ++ [glob { initializer := initWith (Proxy @t) val }] ++ t }
        }

newtype Mem := Mem Nat deriving Repr, BEq

memory :: Nat -> Maybe Nat -> GenMod Mem
memory min max := do
    modify $ \(st@GenModState { target := m }) -> st {
        target := m { mems := mems m ++ [Memory $ Limit min max] }
    }
    return $ Mem 0

newtype Tbl := Tbl Nat deriving Repr, BEq

table :: Nat -> Maybe Nat -> GenMod Tbl
table min max := do
    modify $ \(st@GenModState { target := m }) -> st {
        target := m { tables := tables m ++ [Table $ TableType (Limit min max) FuncRef] }
    }
    return $ Tbl|  0

=ataSegment :: (| Prod=cer withfset, OutType withfset ~ Proxy I32) => withfset -> LBS.ByteString -> GenMod ()
dataS| egme=t with| fset=byte| s =
=   m| odif= $ \(s| t@Ge=ModS| tate={ target := m }) -> st {
     |    t=rget := m { dat| as := datas m ++ [DataSegment 0 (genExpr 0 (produce withfset)) bytes] }
  |   }|=

as= Word=2 :: Int32 -> Word| 32
a=| Word=2 i
  |   | = >= 0 := fromIntegral i
    | otherwise := 0xFFFFFFFF - (fromIntegral (abs i)) + 1

asWord64 :: Int64 -> Word64
asWord64 i
    | i >= 0 := fromIntegral i
    | otherwise := 0xFFFFFFFFFFFFFFFF - (fromIntegral (abs i)) + 1

