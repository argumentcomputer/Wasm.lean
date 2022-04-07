import Std
import Wasm.Structure

namespace Wasm

inductive Value :=
  | VI32 Word32
  | VI64 Word64
  | VF32 Float
  | VF64 Double
  deriving BEq, Repr

open Value

instance : Inhabited Value := ⟨VI32 0⟩

def Value.type : Value -> ValueType
  | (VI32 _) => I32
  | (VI64 _) => I64
  | (VF32 _) => F32
  | (VF64 _) => F64

/-
TODO -- implement
def asInt32 (w : Word32) : Int32 :=
    if w.toNat < 0x80000000
    then w.toNat
    else -1 * fromIntegral (0xFFFFFFFF - w + 1)

def asInt64 (w : Word64) : Int64 :=
    if w < 0x8000000000000000
    then fromIntegral w
    else -1 * fromIntegral (0xFFFFFFFFFFFFFFFF - w + 1)

def asWord32 : (i : Int32) → Word32
    if i >= 0 then i
    else 0xFFFFFFFF - (fromIntegral (abs i)) + 1

def asWord64 (i : Int64) : Word64 :=
    if i >= 0 then i
    else 0xFFFFFFFFFFFFFFFF - (fromIntegral (abs i)) + 1
-/
/-
def nearest [IEEE F] (f : F) : F :=
    if f.isNan then f
    else if f >= 0 && f <= 0.5 th copySign 0 f
    else if f < 0 && f >= -0.5 then -0
    else
      let i := floor f :: Integer in
      let fi := fromIntegral i in
      let r := abs f - abs fi in
      flip copySign f $ (
          if r == 0.5
          then (
              case (even i, f < 0) of
                  (True, _) -> fi
                  (_, True) -> fi - 1.0
                  (_, False) -> fi + 1.0
          )
          else fromIntegral (round f :: Integer)
      )


def zeroAwareMin [IEEE A]  a -> a -> a
zeroAwareMin a b
    | identicalIEEE a 0 && identicalIEEE b (-0) := b
    | isNaN a := a
    | isNaN b := b
    | otherwise := minNum a b

zeroAwareMax :: IEEE a => a -> a -> a
zeroAwareMax a b
    | identicalIEEE a (-0) && identicalIEEE b 0 := b
    | isNaN a := a
    | isNaN b := b
    | otherwise := maxNum a b

floatFloor :: Float -> Float
floatFloor a
    | isNaN a := a
    | otherwise := copySign (fromIntegral (floor a :: Integer)) a

doubleFloor :: Double -> Double
doubleFloor a
    | isNaN a := a
    | otherwise := copySign (fromIntegral (floor a :: Integer)) a

floatCeil :: Float -> Float
floatCeil a
    | isNaN a := a
    | otherwise := copySign (fromIntegral (ceiling a :: Integer)) a

doubleCeil :: Double -> Double
doubleCeil a
    | isNaN a := a
    | otherwise := copySign (fromIntegral (ceiling a :: Integer)) a

floatTrunc :: Float -> Float
floatTrunc a
    | isNaN a := a
    | otherwise := copySign (fromIntegral (truncate a :: Integer)) a

doubleTrunc :: Double -> Double
doubleTrunc a
    | isNaN a := a
    | otherwise := copySign (fromIntegral (truncate a :: Integer)) a
-/
structure Label :=
  resultType : ResultType
  deriving Repr, BEq

def Address := UInt32
    deriving BEq, Repr, Inhabited

instance : OfNat Address n := ⟨UInt32.ofNat n⟩

structure TableInstance :=
    lim : Limit
    elements : Array (Option Address)

def MemoryStore := ByteArray -- .MutableByteArray (Primitive.PrimState IO)
    deriving Inhabited, BEq, Repr

structure MemoryInstance :=
    limit : Limit
    memory : MemoryStore
    deriving Inhabited, BEq, Repr

inductive GlobalInstance :=
    | const : ValueType → Value → GlobalInstance
    | mutable : ValueType → Value → GlobalInstance
    deriving Inhabited, BEq, Repr

def makeMutGlobal (val: Value) : GlobalInstance :=
  GlobalInstance.mutable (val.type) val

def makeConstGlobal (val : Value) : GlobalInstance := GlobalInstance.const (val.type) val

inductive ExternalValue :=
    | ExternFunction Address
    | ExternTable Address
    | ExternMemory Address
    | ExternGlobal Address
    deriving BEq, Repr, Inhabited

structure ExportInstance :=
  name : String
  value : ExternalValue
  deriving BEq, Repr, Inhabited

structure ModuleInstance :=
    funcTypes : Array FuncType := Array.empty
    funcaddrs : Array Address := Array.empty
    tableaddrs : Array Address := Array.empty
    memaddrs : Array Address := Array.empty
    globaladdrs : Array Address := Array.empty
    exports : Array ExportInstance := Array.empty
    deriving BEq, Repr, Inhabited

def ModuleInstance.empty (_ : Unit) : ModuleInstance := {
    funcTypes := Array.empty,
    funcaddrs := Array.empty,
    tableaddrs := Array.empty,
    memaddrs := Array.empty,
    globaladdrs := Array.empty,
    exports := Array.empty
  : ModuleInstance }

def HostFunction := List Value -> IO (List Value)
  deriving Inhabited

inductive FunctionInstance :=
    | FunctionInstance
        (funcType : FuncType)
        (moduleInstance : ModuleInstance)
        (code : Function)
    | HostInstance
        (funcType : FuncType)
        (hostCode : HostFunction)
    deriving Inhabited

open FunctionInstance


structure Store :=
    funcInstances : Array FunctionInstance := Array.empty
    tableInstances : Array TableInstance := Array.empty
    memInstances : Array MemoryInstance := Array.empty
    globalInstances : Array GlobalInstance := Array.empty
    deriving Inhabited


-- def Store.empty : Store := { funcInstances := #[] : Store }

inductive HostItem :=
  | function : FuncType → HostFunction → HostItem
  | global : GlobalInstance → HostItem
  | memory : Limit → HostItem
  | table : Limit → HostItem
  deriving BEq, Repr, Inhabited

def makeHostModule (st : Store) (items : List (TL.Text × HostItem)) : IO (Store × ModuleInstance) := do
  let makeHostFunctions : (Store, ModuleInstance) -> (Store, ModuleInstance) :=
      (λ (st, inst) =>
            let funcLen := Array.length $ funcInstances st
            let (names, types, instances) := unzip3 <| items.map λ (name, {t, c}) => (name, t, HostInstance.mk t c)
            let exps := Array.fromList $ zipWith (\name i -> ExportInstance name (ExternFunction i)) names [funcLen..]
            let inst' := inst {
                    funcTypes := Array.fromList types,
                    funcaddrs := Array.fromList [funcLen..funcLen + length instances - 1],
                    exports := Wasm.exports inst <> exps
                }
            let st' := st { funcInstances := funcInstances st <> Array.fromList instances }
            (st', inst')
        );
  let makeHostGlobals : (Store, ModuleInstance) -> (Store, ModuleInstance) :=
      (λ (st, inst) =>
            let globLen := Array.length $ globalInstances st in
            let (names, instances) := unzip [(name, g) | (name, (HostGlobal g)) <- items] in
            let exps := Array.fromList $ zipWith (\name i -> ExportInstance name (ExternGlobal i)) names [globLen..] in
            let inst' := inst {
                    globaladdrs := Array.fromList [globLen..globLen + length instances - 1],
                    exports := Language.Wasm.Interpreter.exports inst <> exps
                }
            in
            let st' := st { globalInstances := globalInstances st <> Array.fromList instances } in
            (st', inst')
      );
            
  let makeHostMems : (Store, ModuleInstance) -> IO (Store, ModuleInstance) :=
      (λ (st, inst) => do
            let memLen := Array.length $ memInstances st
            let (names, limits) := unzip [(name, Memory lim) | (name, (HostMemory lim)) <- items]
            instances <- allocMems limits
            let exps := Array.fromList $ zipWith (\name i -> ExportInstance name (ExternMemory i)) names [memLen..]
            let inst' := inst {
                    memaddrs := Array.fromList [memLen..memLen + length instances - 1],
                    exports := Language.Wasm.Interpreter.exports inst <> exps
                }
            let st' := st { memInstances := memInstances st <> instances }
            return (st', inst')
      );
            
  let makeHostTables : (Store, ModuleInstance) -> IO (Store, ModuleInstance) :=
      (λ (st, inst) => do
            let tableLen := Array.length $ tableInstances st
            let (names, tables) := unzip [(name, Table (TableType lim FuncRef)) | (name, (HostTable lim)) <- items]
            let instances := allocTables tables
            let exps := Array.fromList $ zipWith (\name i -> ExportInstance name (ExternTable i)) names [tableLen..]
            let inst' := inst {
                    tableaddrs := Array.fromList [tableLen..tableLen + length instances - 1],
                    exports := Language.Wasm.Interpreter.exports inst <> exps
                }
            let st' := st { tableInstances := tableInstances st <> instances }
            return (st', inst')
      );
  (st, emptyModInstance)
      |> makeHostFunctions
      |> makeHostGlobals
      |> makeHostMems
      >>= makeHostTables


def calcInstance (s : Store) (imports : Imports) (mod : Module) : Initialize ModuleInstance := do
  let getImpIdx : Import -> Initialize ExternalValue :=
    (λ ({ m, n : Import }) =>
      match Map.lookup (m, n) imps with
      | some idx => return idx
      | none => throw $ "Cannot find import from module " ++ show m ++ " with name " ++ show n
    );
  let checkImportType : Import -> Initialize ExternalValue :=
    (λ
    | imp@(Import _ _ (ImportFunc typeIdx)) => do
      idx <- getImpIdx imp
      funcAddr <- case idx of
          ExternFunction funcAddr -> return funcAddr
          other -> throwError "incompatible import type"
      let expectedType := types !! fromIntegral typeIdx
      let actualType := Language.Wasm.Interpreter.funcType $ fs ! funcAddr
      if expectedType == actualType
      then return idx
      else throwError "incompatible import type"
    | imp@(Import _ _ (ImportGlobal globalType)) => do
      let err := throwError "incompatible import type"
      idx <- getImpIdx imp
      globalAddr <- case idx of
          ExternGlobal globalAddr -> return globalAddr
          _ -> err
      let globalInst := gs ! globalAddr
      let typesMatch := case (globalType, globalInst) of
              (Const vt, GIConst vt' _) -> vt == vt'
              (Mut vt, GIMut vt' _) -> vt == vt'
              _ -> False
      if typesMatch then return idx else err
    | imp@(Import _ _ (ImportMemory limit)) => do
      idx <- getImpIdx imp
      memAddr <- case idx of
          ExternMemory memAddr -> return memAddr
          _ -> throwError "incompatible import type"
      let MemoryInstance { lim } := ms ! memAddr
      if limitMatch lim limit
      then return idx
      else throwError "incompatible import type"
    | imp@(Import _ _ (ImportTable (TableType limit _))) => do
      idx <- getImpIdx imp
      tableAddr <- case idx of
          ExternTable tableAddr -> return tableAddr
          _ -> throwError "incompatible import type"
      let TableInstance { lim } := ts ! tableAddr
      if limitMatch lim limit
      then return idx
      else throwError "incompatible import type"
    );

  let limitMatch : Limit -> Limit -> Bool :=
    λ (Limit n1 m1) (Limit n2 m2) => n1 >= n2 && (isNothing m2 || fromOption False ((<=) <$> m1 <*> m2))
  let funLen := s.funcInstances.size
  let tableLen := s.tableInstances.size
  let memLen := s.memoryInstances.size
  let globalLen := s.globalInstances.size
  let funImps <- mapM checkImportType $ filter isFuncImport imports
  let tableImps <- mapM checkImportType $ filter isTableImport imports
  let memImps <- mapM checkImportType $ filter isMemImport imports
  let globalImps <- mapM checkImportType $ filter isGlobalImport imports
  let funs := Array.fromList $ map (λ(ExternFunction i) => i) funImps ++ [funLen:funLen + functions.size - 1]
  let tbls := Array.fromList $ map (λ(ExternTable i) => i) tableImps ++ [tableLen:tableLen + tables.size - 1]
  let memories := Array.fromList $ map (λ(ExternMemory i) => i) memImps ++ [memLen:memLen + mems.size - 1]
  let globs := Array.fromList $ map (λ(ExternGlobal i) => i) globalImps ++ [globalLen:globalLen + globals.size - 1]
  let refExport := (λ 
        | (Export name (ExportFunc idx)) =>
          ExportInstance name $ ExternFunction $ funs ! fromIntegral idx
        | (Export name (ExportTable idx)) =>
          ExportInstance name $ ExternTable $ tbls ! fromIntegral idx
        | (Export name (ExportMemory idx)) =>
          ExportInstance name $ ExternMemory $ memories ! fromIntegral idx
        | (Export name (ExportGlobal idx)) =>
          ExportInstance name $ ExternGlobal $ globs ! fromIntegral idx
  )
  return  {
      funcTypes := Array.fromList types,
      funcaddrs := funs,
      tableaddrs := tbls,
      memaddrs := memories,
      globaladdrs := globs,
      exports := Array.fromList $ map refExport exports
  : ModuleInstance }

def Imports := Std.HashMap (String × String) ExternalValue

def Imports.empty : Imports := Std.HashMap.empty

def allocFunctions (inst : ModuleInstance) (funs : List Function) : Array FunctionInstance :=
    let mkFuncInst f := FunctionInstance (inst.funcTypes ! (fromIntegral f.funcType)) inst f
    Array.fromList $ map mkFuncInst funs

def getGlobalValue (inst : ModuleInstance) (store : Store) (idx : Nat) : IO Value :=
    let addr :=
      match inst.globaladdrs.get! idx with
      | some a => a
      | none => throw "Global index is out of range. It can happen if initializer refs non-import global."
    match store.globalInstances.get! addr with
    | GlobalInstance.const _ v => return v
    | GlobalInstance.mutable _ ref => readIORef ref

-- due the validation there can be only these instructions
def evalConstExpr : ModuleInstance -> Store -> Expression -> IO Value
  | _ _ [I32Const v] => pure $ VI32 v
  | _ _ [I64Const v] => pure $ VI64 v
  | _ _ [F32Const v] => pure $ VF32 v
  | _ _ [F64Const v] => pure $ VF64 v
  | inst store [GetGlobal i] => getGlobalValue inst store i
  | _ _ instrs => throw $ "Global initializer contains unsupported instructions: " ++ show instrs

def allocAndInitGlobals (inst : ModuleInstance) (store : Store) (globs : List Global) : IO (Array GlobalInstance) :=
  let runIniter : Expression -> IO Value
  -- the spec says get global can ref only imported globals
  -- only they are in store for this moment
    := evalConstExpr inst store

  let allocGlob : Global -> IO GlobalInstance := (λ
    | (Global (Const vt) initer) => GIConst vt <$> runIniter initer
    | (Global (Mut vt) initer) => do
      let val <- runIniter initer
      return GlobalInstance.mutable vt val
  Array.fromList <$> mapM allocGlob globs

def allocTables (tables : Array Table) : Array TableInstance :=
  let allocTable : Table -> TableInstance :=
    λ table =>
      {
          lim := table.type.limit,
          elements := List.toArray $ List.replicate table.type.limit.from_ none
      }
  tables.map allocTable

def defaultBudget : Nat := 300

def pageSize : Nat := 64 * 1024

def allocMems (mems : Array Memory) : IO (Array MemoryInstance) :=
    let allocMem : Memory -> IO MemoryInstance := λ memory => do
        let size := memory.limit.from * pageSize
        let mem  := ByteArray.mkEmpty size
        -- ByteArray.setByteArray @Word64 mem 0 (size / 8) 0
        return {
            limit := memory.limit,
            memory := mem
        : MemoryInstance }
    Array.mapM allocMem mems

def Initialize := ExceptT String (StateT Store IO)
    deriving MonadState, MonadExcept

def initialize (inst : ModuleInstance) (module : Module) : Initialize := do
    let checkElem : ElemSegment -> Initialize (Address × Int × List Address) := λ elem do
        let st <- State.get
        let VI32 val <- liftIO $ evalConstExpr inst st elem.offset
        let from := fromIntegral val
        let funcs := map ((funcaddrs inst !) . fromIntegral) funcIndexes
        let idx := tableaddrs inst ! fromIntegral tableIndex
        let last := from + funcs.size
        let TableInstance lim elems := tableInstances st ! idx
        let len := Array.length elems
        Monad.when (last > len) $ throw "elements segment does not fit"
        return (idx, from, funcs)

    let initElem : (Address × Int × List Address) -> Initialize Unit := λ (idx, from, funcs) => 
        State.modify $ λ st =>
            let TableInstance lim elems := tableInstances st ! idx in
            let table := TableInstance lim (elems // zip [from..] (map some funcs)) in
            { st with tableInstances := tableInstances st Array.// [(idx, table)] }

    let checkinductive : InductiveSegment -> Initialize (Int, MemoryStore, LBS.ByteString)
    checkinductive inductiveSegment {memIndex, offset, chunk} := do
        st <- State.get
        VI32 val <- liftIO $ evalConstExpr inst st offset
        let from := fromIntegral val
        let idx := memaddrs inst ! fromIntegral memIndex
        let last := from + (fromIntegral $ LBS.length chunk)
        let MemoryInstance _ memory := memInstances st ! idx
        mem <- liftIO $ readIORef memory
        len <- ByteArray.getSizeofMutableByteArray mem
        Monad.when (last > len) $ throwError "inductive segment does not fit"
        return (from, mem, chunk)

    initinductive :: (Int, MemoryStore, LBS.ByteString) -> Initialize ()
    initinductive (from, mem, chunk) =
        mapM_ (\(i,b) -> ByteArray.writeByteArray mem i b) $ zip [from..] $ LBS.unpack chunk
    let checkedMems <- mapM checkinductive module.inductives
    let checkedTables <- mapM checkElem module.elems
    mapM_ initinductive checkedMems
    mapM_ initElem checkedTables
    let st <- State.get
    match start with
    | some (StartFunction idx) -> do
      let funInst := funcInstances st ! (funcaddrs inst ! fromIntegral idx)
      let mainRes <- liftIO $ eval defaultBudget st funInst []
      match mainRes with
      | some [] => return ()
      |  _ => throw "Start function terminated with trap"
    | none => return ()
    where

def instantiate (st : Store) (imps : Imports) (mod : Valid.ValidModule) : IO (Either String ModuleInstance × Store) := flip State.runStateT st $ runExceptT $ do
    let m := Valid.getModule mod
    let inst <- calcInstance st imps m
    let functions := funcInstances st <|> (allocFunctions inst $ Struct.functions m)
    let globals <- liftIO $ (globalInstances st <|> ·) <$> (allocAndInitGlobals inst st $ Struct.globals m)
    let tables := tableInstances st <|> (allocTables $ Struct.tables m)
    let mems <- liftIO $ (memInstances st <|> ·) <$> (allocMems $ Struct.mems m)
    State.put $ st {
        funcInstances := functions,
        tableInstances := tables,
        memInstances := mems,
        globalInstances := globals
    }
    initialize inst m
    return inst

def Stack := List Value
    deriving Repr, BEq

structure EvalCtx :=
    locals : Array Value
    labels : Array Label
    stack : Stack
    deriving Repr, BEq

inductive EvalResult :=
    | Done EvalCtx
    | Break Int (List Value) EvalCtx
    | Trap
    | ReturnFn (List Value)
    deriving Repr, BEq

def checkValType : ValueType -> Value -> Option Value
    | I32 (VI32 v) => some $ VI32 v
    | I64 (VI64 v) => some $ VI64 v
    | F32 (VF32 v) => some $ VF32 v
    | F64 (VF64 v) => some $ VF64 v
    | _   _        => none

def initLocal : ValueType -> Value
    | I32 => VI32 0
    | I64 => VI64 0
    | F32 => VF32 0
    | F64 => VF64 0


def eval (budget : Nat) (store : Store) (funcInst : FunctionInstance) (args : List Value) : IO (Option (List Value)) := do
-- eval 0 _ _ _ := return Nothing
-- eval budget store FunctionInstance { funcType, moduleInstance, code := Function { localTypes, body} } args := do
    if budget = 0 then return none
    let go : EvalCtx -> Expression -> IO EvalResult := λ
        | ctx [] => pure $ Done ctx
        | ctx (instr :: rest) => do
            let res <- step ctx instr
            match res with
            | Done ctx' => go ctx' rest
            | command => return command
        
    let makeLoadInstr : EvalCtx → Nat → Int → (List Value -> Nat -> EvalResult) → IO EvalResult :=
        λ (ctx : EvalCtx) (offset : Nat) (byteWidth : Int) (cont : List Value -> Nat -> EvalResult) (v : Nat) => do
          let { memory, limit : MemoryInstance } := memInstances store.memInstances ! (memaddrs moduleInstance ! 0)
          -- let memory <- readIORefc memoryRef
          let addr := v + offset
          let readByte idx := do
              let byte <- ByteArray.readByteArray @Word8 memory $ addr + idx
              return $ byte <<< (idx * 8)
          let len := memory.size
          let isAligned := rem addr byteWidth == 0
          if addr + byteWidth > len
          then return Trap
          else (
            if isAligned
            then cont rest <$> ByteArray.readByteArray memory (Nat.quot addr byteWidth)
            else cont rest . sum <$> mapM readByte [0 : byteWidth-1]
          )
        -- makeLoadInstr _ _ _ _ := error "Incorrect value on top of stack for memory instruction"

    let makeStoreInstr (ctx : EvalCtx) (offset : Nat) (byteWith : Int) (v : Nat) : IO EvalResult :=
        λ (ctx : EvalCtx) (offset : Nat) (byteWith : Int) (v : Nat) => do
        let { memory : MemoryInstance } := store.memInstances.get! (moduleInstance.memaddrs.get! 0)
        -- let memory <- readIORef memoryRef
        let addr := fromIntegral $ va + fromIntegral offset
        let writeByte idx := do
            let byte := fromIntegral $ v >>> (idx * 8) && 0xFF
            ByteArray.writeByteArray @Word8 memory (addr + idx) byte
        let len := memory.size
        let isAligned := rem addr byteWidth == 0
        let write := if isAligned
            then ByteArray.writeByteArray memory (Nat.quot addr byteWidth) v
            else (mapM_ writeByte [0 : byteWidth-1] : IO Unit)
        if addr + byteWidth > len
        then return Trap
        else write >> (return $ Done ctx { stack := rest })
        makeStoreInstr _ _ _ _ := error "Incorrect value on top of stack for memory instruction"

    let step : EvalCtx -> Instruction Natural -> IO EvalResult := λ
        | _ Unreachable := return Trap
        | ctx Nop := return $ Done ctx
        | ctx (Block blockType expr) := do
            let FuncType paramType resType := case blockType of
                    Inline Nothing -> FuncType [] []
                    Inline (some valType) -> FuncType [] [valType]
                    TypeIndex typeIdx -> funcTypes moduleInstance ! fromIntegral typeIdx
            res <- go ctx { labels := Label resType : labels ctx } expr
            case res of
                Break 0 r EvalCtx{ locals := ls } -> return $ Done ctx { locals := ls, stack := r ++ (drop (length paramType) $ stack ctx) }
                Break n r ctx' -> return $ Break (n - 1) r ctx'
                Done ctx'@EvalCtx{ labels := (_:rest) } -> return $ Done ctx' { labels := rest }
                command -> return command
        | ctx loop@(Loop blockType expr) := do
            let resType := case blockType of
                    Inline Nothing -> []
                    Inline (some valType) -> [valType]
                    TypeIndex typeIdx -> results $ funcTypes moduleInstance ! fromIntegral typeIdx
            res <- go ctx { labels := Label resType : labels ctx } expr
            case res of
                Break 0 r EvalCtx{ locals := ls, stack := st } -> step ctx { locals := ls, stack := st } loop
                Break n r ctx' -> return $ Break (n - 1) r ctx'
                Done ctx'@EvalCtx{ labels := (_:rest) } -> return $ Done ctx' { labels := rest }
                command -> return command
        | ctx@EvalCtx{ stack := (VI32 v): rest } (If blockType true false) := do
            let FuncType paramType resType := case blockType of
                    Inline Nothing -> FuncType [] []
                    Inline (some valType) -> FuncType [] [valType]
                    TypeIndex typeIdx -> funcTypes moduleInstance ! fromIntegral typeIdx
            let expr := if v /= 0 then true else false
            res <- go ctx { labels := Label resType : labels ctx, stack := rest } expr
            case res of
                Break 0 r EvalCtx{ locals := ls } -> return $ Done ctx { locals := ls, stack := r ++ (drop (length paramType) rest) }
                Break n r ctx' -> return $ Break (n - 1) r ctx'
                Done ctx'@EvalCtx{ labels := (_:rest) } -> return $ Done ctx' { labels := rest }
                command -> return command
        | ctx@EvalCtx{ stack, labels } (Br label) := do
            let idx := fromIntegral label
            let Label resType := labels !! idx
            case sequence $ zipWith checkValType (reverse resType) $ take (length resType) stack of
                some result -> return $ Break idx result ctx
                Nothing -> return Trap
        | ctx@EvalCtx{ stack := (VI32 v): rest } (BrIf label) =
            if v == 0
            then return $ Done ctx { stack := rest }
            else step ctx { stack := rest } (Br label)
        | ctx@EvalCtx{ stack := (VI32 v): rest } (BrTable labels label) =
            let idx := fromIntegral v in
            let lbl := fromIntegral $ if idx < length labels then labels !! idx else label in
            step ctx { stack := rest } (Br lbl)
        | EvalCtx{ stack } Return =
            let resType := results funcType in
            case sequence $ zipWith checkValType (reverse resType) $ take (length resType) stack of
                some result -> return $ ReturnFn $ reverse result
                Nothing -> return Trap
        | ctx (Call fun) := do
            let funInst := funcInstances store ! (funcaddrs moduleInstance ! fromIntegral fun)
            let ft := Language.Wasm.Interpreter.funcType funInst 
            let args := params ft
            case sequence $ zipWith checkValType args $ reverse $ take (length args) $ stack ctx of
                some params -> do
                    res <- eval (budget - 1) store funInst params
                    case res of
                        some res -> return $ Done ctx { stack := reverse res ++ (drop (length args) $ stack ctx) }
                        Nothing -> return Trap
                Nothing -> return Trap
        | ctx@EvalCtx{ stack := (VI32 v): rest } (CallIndirect typeIdx) := do
            let funcType := funcTypes moduleInstance ! fromIntegral typeIdx
            let TableInstance { elements } := tableInstances store ! (tableaddrs moduleInstance ! 0)
            let checks := do
                    addr <- Monad.join $ elements !? fromIntegral v
                    let funcInst := funcInstances store ! addr
                    let targetType := Language.Wasm.Interpreter.funcType funcInst
                    Monad.guard $ targetType == funcType
                    let args := params targetType
                    Monad.guard $ length args <= length rest
                    params <- sequence $ zipWith checkValType args $ reverse $ take (length args) rest
                    return (funcInst, params)
            case checks of
                some (funcInst, params) -> do
                    res <- eval (budget - 1) store funcInst params
                    case res of
                        some res -> return $ Done ctx { stack := reverse res ++ (drop (length params) rest) }
                        Nothing -> return Trap
                Nothing -> return Trap
        | ctx@EvalCtx{ stack := (_:rest) } Drop := return $ Done ctx { stack := rest }
        | ctx@EvalCtx{ stack := (VI32 test:val2:val1:rest) } Select =
            if test == 0
            then return $ Done ctx { stack := val2 : rest }
            else return $ Done ctx { stack := val1 : rest }
        | ctx (GetLocal i) := return $ Done ctx { stack := (locals ctx ! fromIntegral i) : stack ctx }
        | ctx@EvalCtx{ stack := (v:rest) } (SetLocal i) =
            return $ Done ctx { stack := rest, locals := locals ctx // [(fromIntegral i, v)] }
        | ctx@EvalCtx{ locals := ls, stack := (v:rest) } (TeeLocal i) =
            return $ Done ctx {
                stack := v : rest,
                locals := locals ctx // [(fromIntegral i, v)]
            }
        | ctx (GetGlobal i) := do
            let globalInst := globalInstances store ! (globaladdrs moduleInstance ! fromIntegral i)
            val <- case globalInst of
                GIConst _ v -> return v
                GIMut _ ref -> readIORef ref
            return $ Done ctx { stack := val : stack ctx }
        | ctx@EvalCtx{ stack := (v:rest) } (SetGlobal i) := do
            let globalInst := globalInstances store ! (globaladdrs moduleInstance ! fromIntegral i)
            case globalInst of
                GIConst _ v -> error "Attempt of mutation of constant global"
                GIMut _ ref -> writeIORef ref v
            return $ Done ctx { stack := rest }
        | ctx (I32Load MemArg { offset }) =
            makeLoadInstr ctx offset 4 $ (λ rest val => Done ctx { stack := VI32 val : rest })
        | ctx (I64Load MemArg { offset }) =
            makeLoadInstr ctx offset 8 $ (λ rest val => Done ctx { stack := VI64 val : rest })
        | ctx (F32Load MemArg { offset }) =
            makeLoadInstr ctx offset 4 $ (λ rest val => Done ctx { stack := VF32 (wordToFloat val) : rest })
        | ctx (F64Load MemArg { offset }) =
            makeLoadInstr ctx offset 8 $ (λ rest val => Done ctx { stack := VF64 (wordToDouble val) : rest })
        | ctx (I32Load8U MemArg { offset }) =
            makeLoadInstr @Word8 ctx offset 1 $ (λ rest val => Done ctx { stack := VI32 (fromIntegral val) : rest })
        | ctx (I32Load8S MemArg { offset }) =
            makeLoadInstr ctx offset 1 $ (λ rest byte =>
                let val := asWord32 $ if (byte :: Word8) >= 128 then -1 * fromIntegral (0xFF - byte + 1) else fromIntegral byte in
                Done ctx { stack := VI32 val : rest })
        | ctx (I32Load16U MemArg { offset }) := do
            makeLoadInstr @Word16 ctx offset 2 $ (λ rest val => Done ctx { stack := VI32 (fromIntegral val) : rest })
        | ctx (I32Load16S MemArg { offset }) =
            makeLoadInstr ctx offset 2 $ (λ rest val =>
                let signed := asWord32 $ if (val :: Word16) >= 2 ^ 15 then -1 * fromIntegral (0xFFFF - val + 1) else fromIntegral val in
                Done ctx { stack := VI32 signed : rest })
        | ctx (I64Load8U MemArg { offset }) =
            makeLoadInstr @Word8 ctx offset 1 $ (λ rest val => Done ctx { stack := VI64 (fromIntegral val) : rest })
        | ctx (I64Load8S MemArg { offset }) =
            makeLoadInstr ctx offset 1 $ (λ rest byte =>
                let val := asWord64 $ if (byte :: Word8) >= 128 then -1 * fromIntegral (0xFF - byte + 1) else fromIntegral byte in
                Done ctx { stack := VI64 val : rest })
        | ctx (I64Load16U MemArg { offset }) =
            makeLoadInstr @Word16 ctx offset 2 $ (λ rest val => Done ctx { stack := VI64 (fromIntegral val) : rest })
        | ctx (I64Load16S MemArg { offset }) =
            makeLoadInstr ctx offset 2 $ (λ rest val =>
                let signed := asWord64 $ if (val :: Word16) >= 2 ^ 15 then -1 * fromIntegral (0xFFFF - val + 1) else fromIntegral val in
                Done ctx { stack := VI64 signed : rest })
        | ctx (I64Load32U MemArg { offset }) =
            makeLoadInstr @Word32 ctx offset 4 $ (λ rest val => Done ctx { stack := VI64 (fromIntegral val) : rest })
        | ctx (I64Load32S MemArg { offset }) =
            makeLoadInstr ctx offset 4 $ (λ rest val =>
                let signed := asWord64 $ fromIntegral $ asInt32 val in
                Done ctx { stack := VI64 signed : rest })
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (I32Store MemArg { offset }) =
            makeStoreInstr ctx { stack := rest } offset 4 v
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (I64Store MemArg { offset }) =
            makeStoreInstr ctx { stack := rest } offset 8 v
        | ctx@EvalCtx{ stack := (VF32 f:rest) } (F32Store MemArg { offset }) =
            makeStoreInstr ctx { stack := rest } offset 4 $ floatToWord f
        | ctx@EvalCtx{ stack := (VF64 f:rest) } (F64Store MemArg { offset }) =
            makeStoreInstr ctx { stack := rest } offset 8 $ doubleToWord f
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (I32Store8 MemArg { offset }) =
            makeStoreInstr @Word8 ctx { stack := rest } offset 1 $ fromIntegral v
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (I32Store16 MemArg { offset }) =
            makeStoreInstr @Word16 ctx { stack := rest } offset 2 $ fromIntegral v
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (I64Store8 MemArg { offset }) =
            makeStoreInstr @Word8 ctx { stack := rest } offset 1 $ fromIntegral v
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (I64Store16 MemArg { offset }) =
            makeStoreInstr @Word16 ctx { stack := rest } offset 2 $ fromIntegral v
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (I64Store32 MemArg { offset }) =
            makeStoreInstr @Word32 ctx { stack := rest } offset 4 $ fromIntegral v
        | ctx@EvalCtx{ stack := st } CurrentMemory := do
            let MemoryInstance { memory := memoryRef } := memInstances store ! (memaddrs moduleInstance ! 0)
            let memory <- readIORef memoryRef
            let size <- ((`quot` pageSize) . fromIntegral) <$> ByteArray.getSizeofMutableByteArray memory
            return $ Done ctx { stack := VI32 (fromIntegral size) : st }
        | ctx@EvalCtx{ stack := (VI32 n:rest) } GrowMemory := do
            let MemoryInstance { lim := limit@(Limit _ maxLen), memory := memoryRef } := memInstances store ! (memaddrs moduleInstance ! 0)
            let memory <- readIORef memoryRef
            let size <- (`quot` pageSize) <$> ByteArray.getSizeofMutableByteArray memory
            let growTo := size + fromIntegral n
            let w64PageSize := fromIntegral $ pageSize `div` 8
            let result <- (
                if fromOption True ((growTo <=) . fromIntegral <$> maxLen) && growTo <= 0xFFFF
                then (
                    if n == 0 then return size else do
                        mem' <- ByteArray.resizeMutableByteArray memory $ growTo * pageSize
                        ByteArray.setByteArray @Word64 mem' (size * w64PageSize) (fromIntegral n * w64PageSize) 0
                        writeIORef memoryRef mem'
                        return size
                )
                else return $ -1
            )
            return $ Done ctx { stack := VI32 (asWord32 $ fromIntegral result) : rest }
        | ctx (I32Const v) := return $ Done ctx { stack := VI32 v : stack ctx }
        | ctx (I64Const v) := return $ Done ctx { stack := VI64 v : stack ctx }
        | ctx (F32Const v) := return $ Done ctx { stack := VF32 v : stack ctx }
        | ctx (F64Const v) := return $ Done ctx { stack := VF64 v : stack ctx }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IAdd) =
            return $ Done ctx { stack := VI32 (v1 + v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 ISub) =
            return $ Done ctx { stack := VI32 (v1 - v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IMul) =
            return $ Done ctx { stack := VI32 (v1 * v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IDivU) =
            if v2 == 0
            then return Trap
            else return $ Done ctx { stack := VI32 (v1 `quot` v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IDivS) =
            if v2 == 0 || (v1 == 0x80000000 && v2 == 0xFFFFFFFF)
            then return Trap
            else return $ Done ctx { stack := VI32 (asWord32 $ asInt32 v1 `quot` asInt32 v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IRemU) =
            if v2 == 0
            then return Trap
            else return $ Done ctx { stack := VI32 (v1 `rem` v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IRemS) =
            if v2 == 0
            then return Trap
            else return $ Done ctx { stack := VI32 (asWord32 $ asInt32 v1 `rem` asInt32 v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IAnd) =
            return $ Done ctx { stack := VI32 (v1 .&. v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IOr) =
            return $ Done ctx { stack := VI32 (v1 .|. v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IXor) =
            return $ Done ctx { stack := VI32 (v1 `xor` v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IShl) =
            return $ Done ctx { stack := VI32 (v1 `shiftL` (fromIntegral v2 `rem` 32)) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IShrU) =
            return $ Done ctx { stack := VI32 (v1 `shiftR` (fromIntegral v2 `rem` 32)) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IShrS) =
            return $ Done ctx { stack := VI32 (asWord32 $ asInt32 v1 `shiftR` (fromIntegral v2 `rem` 32)) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IRotl) =
            return $ Done ctx { stack := VI32 (v1 `rotateL` fromIntegral v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IBinOp BS32 IRotr) =
            return $ Done ctx { stack := VI32 (v1 `rotateR` fromIntegral v2) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 IBEq) =
            return $ Done ctx { stack := VI32 (if v1 == v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 INe) =
            return $ Done ctx { stack := VI32 (if v1 /= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 ILtU) =
            return $ Done ctx { stack := VI32 (if v1 < v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 ILtS) =
            return $ Done ctx { stack := VI32 (if asInt32 v1 < asInt32 v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 IGtU) =
            return $ Done ctx { stack := VI32 (if v1 > v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 IGtS) =
            return $ Done ctx { stack := VI32 (if asInt32 v1 > asInt32 v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 ILeU) =
            return $ Done ctx { stack := VI32 (if v1 <= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 ILeS) =
            return $ Done ctx { stack := VI32 (if asInt32 v1 <= asInt32 v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 IGeU) =
            return $ Done ctx { stack := VI32 (if v1 >= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v2:VI32 v1:rest) } (IRelOp BS32 IGeS) =
            return $ Done ctx { stack := VI32 (if asInt32 v1 >= asInt32 v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } I32BEqz =
            return $ Done ctx { stack := VI32 (if v == 0 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (IUnOp BS32 IClz) =
            return $ Done ctx { stack := VI32 (fromIntegral $ countLeadingZeros v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (IUnOp BS32 ICtz) =
            return $ Done ctx { stack := VI32 (fromIntegral $ countTrailingZeros v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (IUnOp BS32 IPopcnt) =
            return $ Done ctx { stack := VI32 (fromIntegral $ popCount v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (IUnOp BS32 IExtend8S) =
            let byte := v .&. 0xFF in
            let r := if byte >= 0x80 then asWord32 (fromIntegral byte - 0x100) else byte in
            return $ Done ctx { stack := VI32 r : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (IUnOp BS32 IExtend16S) =
            let half := v .&. 0xFFFF in
            let r := if half >= 0x8000 then asWord32 (fromIntegral half - 0x10000) else half in
            return $ Done ctx { stack := VI32 r : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (IUnOp BS32 IExtend32S) =
            return $ Done ctx { stack := VI32 v : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IAdd) =
            return $ Done ctx { stack := VI64 (v1 + v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 ISub) =
            return $ Done ctx { stack := VI64 (v1 - v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IMul) =
            return $ Done ctx { stack := VI64 (v1 * v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IDivU) =
            if v2 == 0
            then return Trap
            else return $ Done ctx { stack := VI64 (v1 `quot` v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IDivS) =
            if v2 == 0 || (v1 == 0x8000000000000000 && v2 == 0xFFFFFFFFFFFFFFFF)
            then return Trap
            else return $ Done ctx { stack := VI64 (asWord64 $ asInt64 v1 `quot` asInt64 v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IRemU) =
            if v2 == 0
            then return Trap
            else return $ Done ctx { stack := VI64 (v1 `rem` v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IRemS) =
            if v2 == 0
            then return Trap
            else return $ Done ctx { stack := VI64 (asWord64 $ asInt64 v1 `rem` asInt64 v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IAnd) =
            return $ Done ctx { stack := VI64 (v1 .&. v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IOr) =
            return $ Done ctx { stack := VI64 (v1 .|. v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IXor) =
            return $ Done ctx { stack := VI64 (v1 `xor` v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IShl) =
            return $ Done ctx { stack := VI64 (v1 `shiftL` (fromIntegral (v2 `rem` 64))) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IShrU) =
            return $ Done ctx { stack := VI64 (v1 `shiftR` (fromIntegral (v2 `rem` 64))) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IShrS) =
            return $ Done ctx { stack := VI64 (asWord64 $ asInt64 v1 `shiftR` (fromIntegral (v2 `rem` 64))) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IRotl) =
            return $ Done ctx { stack := VI64 (v1 `rotateL` fromIntegral v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IBinOp BS64 IRotr) =
            return $ Done ctx { stack := VI64 (v1 `rotateR` fromIntegral v2) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 IBEq) =
            return $ Done ctx { stack := VI32 (if v1 == v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 INe) =
            return $ Done ctx { stack := VI32 (if v1 /= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 ILtU) =
            return $ Done ctx { stack := VI32 (if v1 < v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 ILtS) =
            return $ Done ctx { stack := VI32 (if asInt64 v1 < asInt64 v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 IGtU) =
            return $ Done ctx { stack := VI32 (if v1 > v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 IGtS) =
            return $ Done ctx { stack := VI32 (if asInt64 v1 > asInt64 v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 ILeU) =
            return $ Done ctx { stack := VI32 (if v1 <= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 ILeS) =
            return $ Done ctx { stack := VI32 (if asInt64 v1 <= asInt64 v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 IGeU) =
            return $ Done ctx { stack := VI32 (if v1 >= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v2:VI64 v1:rest) } (IRelOp BS64 IGeS) =
            return $ Done ctx { stack := VI32 (if asInt64 v1 >= asInt64 v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } I64BEqz =
            return $ Done ctx { stack := VI32 (if v == 0 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (IUnOp BS64 IClz) =
            return $ Done ctx { stack := VI64 (fromIntegral $ countLeadingZeros v) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (IUnOp BS64 ICtz) =
            return $ Done ctx { stack := VI64 (fromIntegral $ countTrailingZeros v) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (IUnOp BS64 IPopcnt) =
            return $ Done ctx { stack := VI64 (fromIntegral $ popCount v) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (IUnOp BS64 IExtend8S) =
            let byte := v .&. 0xFF in
            let r := if byte >= 0x80 then asWord64 (fromIntegral byte - 0x100) else byte in
            return $ Done ctx { stack := VI64 r : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (IUnOp BS64 IExtend16S) =
            let quart := v .&. 0xFFFF in
            let r := if quart >= 0x8000 then asWord64 (fromIntegral quart - 0x10000) else quart in
            return $ Done ctx { stack := VI64 r : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (IUnOp BS64 IExtend32S) =
            let half := v .&. 0xFFFFFFFF in
            let r := if half >= 0x80000000 then asWord64 (fromIntegral half - 0x100000000) else half in
            return $ Done ctx { stack := VI64 r : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (FUnOp BS32 FAbs) =
            return $ Done ctx { stack := VF32 (abs v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (FUnOp BS32 FNeg) =
            return $ Done ctx { stack := VF32 (negate v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (FUnOp BS32 FCeil) =
            return $ Done ctx { stack := VF32 (floatCeil v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (FUnOp BS32 FFloor) =
            return $ Done ctx { stack := VF32 (floatFloor v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (FUnOp BS32 FTrunc) =
            return $ Done ctx { stack := VF32 (floatTrunc v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (FUnOp BS32 FNearest) =
            return $ Done ctx { stack := VF32 (nearest v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (FUnOp BS32 FSqrt) =
            return $ Done ctx { stack := VF32 (sqrt v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (FUnOp BS64 FAbs) =
            return $ Done ctx { stack := VF64 (abs v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (FUnOp BS64 FNeg) =
            return $ Done ctx { stack := VF64 (negate v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (FUnOp BS64 FCeil) =
            return $ Done ctx { stack := VF64 (doubleCeil v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (FUnOp BS64 FFloor) =
            return $ Done ctx { stack := VF64 (doubleFloor v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (FUnOp BS64 FTrunc) =
            return $ Done ctx { stack := VF64 (doubleTrunc v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (FUnOp BS64 FNearest) =
            return $ Done ctx { stack := VF64 (nearest v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (FUnOp BS64 FSqrt) =
            return $ Done ctx { stack := VF64 (sqrt v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FBinOp BS32 FAdd) =
            return $ Done ctx { stack := VF32 (v1 + v2) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FBinOp BS32 FSub) =
            return $ Done ctx { stack := VF32 (v1 - v2) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FBinOp BS32 FMul) =
            return $ Done ctx { stack := VF32 (v1 * v2) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FBinOp BS32 FDiv) =
            return $ Done ctx { stack := VF32 (v1 / v2) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FBinOp BS32 FMin) =
            return $ Done ctx { stack := VF32 (zeroAwareMin v1 v2) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FBinOp BS32 FMax) =
            return $ Done ctx { stack := VF32 (zeroAwareMax v1 v2) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FBinOp BS32 FCopySign) =
            return $ Done ctx { stack := VF32 (copySign v1 v2) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FBinOp BS64 FAdd) =
            return $ Done ctx { stack := VF64 (v1 + v2) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FBinOp BS64 FSub) =
            return $ Done ctx { stack := VF64 (v1 - v2) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FBinOp BS64 FMul) =
            return $ Done ctx { stack := VF64 (v1 * v2) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FBinOp BS64 FDiv) =
            return $ Done ctx { stack := VF64 (v1 / v2) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FBinOp BS64 FMin) =
            return $ Done ctx { stack := VF64 (zeroAwareMin v1 v2) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FBinOp BS64 FMax) =
            return $ Done ctx { stack := VF64 (zeroAwareMax v1 v2) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FBinOp BS64 FCopySign) =
            return $ Done ctx { stack := VF64 (copySign v1 v2) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FRelOp BS32 FBEq) =
            return $ Done ctx { stack := VI32 (if v1 == v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FRelOp BS32 FNe) =
            return $ Done ctx { stack := VI32 (if v1 /= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FRelOp BS32 FLt) =
            return $ Done ctx { stack := VI32 (if v1 < v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FRelOp BS32 FGt) =
            return $ Done ctx { stack := VI32 (if v1 > v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FRelOp BS32 FLe) =
            return $ Done ctx { stack := VI32 (if v1 <= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF32 v2:VF32 v1:rest) } (FRelOp BS32 FGe) =
            return $ Done ctx { stack := VI32 (if v1 >= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FRelOp BS64 FBEq) =
            return $ Done ctx { stack := VI32 (if v1 == v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FRelOp BS64 FNe) =
            return $ Done ctx { stack := VI32 (if v1 /= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FRelOp BS64 FLt) =
            return $ Done ctx { stack := VI32 (if v1 < v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FRelOp BS64 FGt) =
            return $ Done ctx { stack := VI32 (if v1 > v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FRelOp BS64 FLe) =
            return $ Done ctx { stack := VI32 (if v1 <= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VF64 v2:VF64 v1:rest) } (FRelOp BS64 FGe) =
            return $ Done ctx { stack := VI32 (if v1 >= v2 then 1 else 0) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } I32WrapI64 =
            return $ Done ctx { stack := VI32 (fromIntegral $ v .&. 0xFFFFFFFF) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncFU BS32 BS32) =
            if isNaN v || isInfinite v || v >= 2^32 || v <= -1
            then return Trap
            else return $ Done ctx { stack := VI32 (truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncFU BS32 BS64) =
            if isNaN v || isInfinite v || v >= 2^32 || v <= -1
            then return Trap
            else return $ Done ctx { stack := VI32 (truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncFU BS64 BS32) =
            if isNaN v || isInfinite v || v >= 2^64 || v <= -1
            then return Trap
            else return $ Done ctx { stack := VI64 (truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncFU BS64 BS64) =
            if isNaN v || isInfinite v || v >= 2^64 || v <= -1
            then return Trap
            else return $ Done ctx { stack := VI64 (truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncFS BS32 BS32) =
            if isNaN v || isInfinite v || v >= 2^31 || v < -2^31 - 1
            then return Trap
            else return $ Done ctx { stack := VI32 (asWord32 $ truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncFS BS32 BS64) =
            if isNaN v || isInfinite v || v >= 2^31 || v <= -2^31 - 1
            then return Trap
            else return $ Done ctx { stack := VI32 (asWord32 $ truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncFS BS64 BS32) =
            if isNaN v || isInfinite v || v >= 2^63 || v < -2^63 - 1
            then return Trap
            else return $ Done ctx { stack := VI64 (asWord64 $ truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncFS BS64 BS64) =
            if isNaN v || isInfinite v || v >= 2^63 || v < -2^63 - 1
            then return Trap
            else return $ Done ctx { stack := VI64 (asWord64 $ truncate v) : rest }

        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFS BS32 BS32) | isNaN v =
            return $ Done ctx { stack := VI32 0 : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFS BS32 BS64) | isNaN v =
            return $ Done ctx { stack := VI32 0 : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFS BS64 BS32) | isNaN v =
            return $ Done ctx { stack := VI64 0 : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFS BS64 BS64) | isNaN v =
            return $ Done ctx { stack := VI64 0 : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFU BS32 BS32) | v <= -1 || isNaN v =
            return $ Done ctx { stack := VI32 0 : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFU BS32 BS64) | v <= -1 || isNaN v =
            return $ Done ctx { stack := VI32 0 : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFU BS64 BS32) | v <= -1 || isNaN v =
            return $ Done ctx { stack := VI64 0 : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFU BS64 BS64) | v <= -1 || isNaN v =
            return $ Done ctx { stack := VI64 0 : rest }

        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFS BS32 BS32) | v >= 2^31 =
            return $ Done ctx { stack := VI32 0x7fffffff : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFS BS32 BS64) | v >= 2^31 =
            return $ Done ctx { stack := VI32 0x7fffffff : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFS BS64 BS32) | v >= 2^63 =
            return $ Done ctx { stack := VI64 0x7fffffffffffffff : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFS BS64 BS64) | v >= 2^63 =
            return $ Done ctx { stack := VI64 0x7fffffffffffffff : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFU BS32 BS32) | v >= 2^32 =
            return $ Done ctx { stack := VI32 0xffffffff : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFU BS32 BS64) | v >= 2^32 =
            return $ Done ctx { stack := VI32 0xffffffff : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFU BS64 BS32) | v >= 2^64 =
            return $ Done ctx { stack := VI64 0xffffffffffffffff : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFU BS64 BS64) | v >= 2^64 =
            return $ Done ctx { stack := VI64 0xffffffffffffffff : rest }
        
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFS BS32 BS32) | v <= -2^31 - 1 =
            return $ Done ctx { stack := VI32 0x80000000 : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFS BS32 BS64) | v <= -2^31 - 1 =
            return $ Done ctx { stack := VI32 0x80000000 : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFS BS64 BS32) | v <= -2^63 - 1 =
            return $ Done ctx { stack := VI64 0x8000000000000000 : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFS BS64 BS64) | v <= -2^63 - 1 =
            return $ Done ctx { stack := VI64 0x8000000000000000 : rest }

        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFU BS32 BS32) =
            return $ Done ctx { stack := VI32 (truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFU BS32 BS64) =
            return $ Done ctx { stack := VI32 (truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFU BS64 BS32) =
            return $ Done ctx { stack := VI64 (truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFU BS64 BS64) =
            return $ Done ctx { stack := VI64 (truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFS BS32 BS32) =
            return $ Done ctx { stack := VI32 (asWord32 $ truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFS BS32 BS64) =
            return $ Done ctx { stack := VI32 (asWord32 $ truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (ITruncSatFS BS64 BS32) =
            return $ Done ctx { stack := VI64 (asWord64 $ truncate v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (ITruncSatFS BS64 BS64) =
            return $ Done ctx { stack := VI64 (asWord64 $ truncate v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } I64ExtendUI32 =
            return $ Done ctx { stack := VI64 (fromIntegral v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } I64ExtendSI32 =
            return $ Done ctx { stack := VI64 (asWord64 $ fromIntegral $ asInt32 v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (FConvertIU BS32 BS32) =
            return $ Done ctx { stack := VF32 (realToFrac v) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (FConvertIU BS32 BS64) =
            return $ Done ctx { stack := VF32 (realToFrac v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (FConvertIU BS64 BS32) =
            return $ Done ctx { stack := VF64 (realToFrac v) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (FConvertIU BS64 BS64) =
            return $ Done ctx { stack := VF64 (realToFrac v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (FConvertIS BS32 BS32) =
            return $ Done ctx { stack := VF32 (realToFrac $ asInt32 v) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (FConvertIS BS32 BS64) =
            return $ Done ctx { stack := VF32 (realToFrac $ asInt64 v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (FConvertIS BS64 BS32) =
            return $ Done ctx { stack := VF64 (realToFrac $ asInt32 v) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (FConvertIS BS64 BS64) =
            return $ Done ctx { stack := VF64 (realToFrac $ asInt64 v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } F32DemoteF64 =
            return $ Done ctx { stack := VF32 (realToFrac v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } F64PromoteF32 =
            return $ Done ctx { stack := VF64 (realToFrac v) : rest }
        | ctx@EvalCtx{ stack := (VF32 v:rest) } (IReinterpretF BS32) =
            return $ Done ctx { stack := VI32 (floatToWord v) : rest }
        | ctx@EvalCtx{ stack := (VF64 v:rest) } (IReinterpretF BS64) =
            return $ Done ctx { stack := VI64 (doubleToWord v) : rest }
        | ctx@EvalCtx{ stack := (VI32 v:rest) } (FReinterpretI BS32) =
            return $ Done ctx { stack := VF32 (wordToFloat v) : rest }
        | ctx@EvalCtx{ stack := (VI64 v:rest) } (FReinterpretI BS64) =
            return $ Done ctx { stack := VF64 (wordToDouble v) : rest }
        | EvalCtx{ stack } instr := error $ "Error during evaluation of instruction: " ++ show instr ++ ". Stack " ++ show stack
    match sequence $ zipWith checkValType (params funcType) args with
    | some checkedArgs => do
        let initialContext := {
              locals := Array.fromList $ checkedArgs ++ map initLocal localTypes,
              labels := [Label $ results funcType],
              stack := []
            }
        let res <- go initialContext body
        match res with
        | Done ctx => pure $ some $ reverse $ stack ctx
        | ReturnFn r => pure $ some r
        | Break 0 r _ => pure $ some $ reverse r
        | Break _ _ _ => throw "Break is out of range"
        | Trap => return none
    | none => return none
-- eval _ _ HostInstance { funcType, hostCode } args := some <$> hostCode args

def invoke (st : Store) (funcIdx : Address) (args : List Value) : IO (Option (List Value)) :=
    eval defaultBudget st $ st.funcInstances.get! funcIdx.toNat

def invokeExport (st : Store) (inst : ModuleInstance) (name : String) (args : List Value) : IO (Option (List Value)) :=
    match Array.find (λ (ExportInstance n _) => n == name) inst.exports with
    | some (ExportInstance _ (ExternFunction addr)) => invoke st addr args
    | none => throw $ "Function with name " ++ show name ++ " was not found in module's exports"

def getGlobalValueByName (store : Store) (inst : ModuleInstance) (name : String) : IO Value :=
    match Array.find (λ (ExportInstance n _) => n == name) inst.exports with
    | some (ExportInstance _ (ExternGlobal addr)) =>
        let globalInst := store.globalInstances.get! addr.toNat
        match globalInst with
        | GlobalInstance.const _ v => return v
        | GlobalInstance.mut _ ref => readIORef ref
    | none => throw $ "Function with name " ++ show name ++ " was not found in module's exports"
---/