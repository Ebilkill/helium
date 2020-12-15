module Helium.CodeGeneration.LLVM.Builtins
  ( builtinDefinitions
  , eval, alloc, unpackString
  , newCursor, freeCursor, writeCursor, finishCursor, memdumpCursor, writeCursorSize
  )
where

import Helium.CodeGeneration.Iridium.Data as Iridium
import Helium.CodeGeneration.LLVM.Utils
import LLVM.AST
import LLVM.AST.Type
import LLVM.AST.Constant
import qualified LLVM.AST.Global as Global
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import Lvm.Common.Id(Id, stringFromId, idFromString)

data Builtin = Builtin Id [Type] Type

builtin :: String -> [Type] -> Type -> Builtin
builtin = Builtin . idFromString

eval', alloc', memcpy', unpackString', newCursor', freeCursor', writeCursor', finishCursor', memdumpCursor', writeCursorSize' :: Builtin
eval' = builtin "_$helium_runtime_eval" [voidPointer, IntegerType 64] voidPointer
-- Alignment, size (number of bytes)
alloc' = builtin "helium_global_alloc" [IntegerType 32] voidPointer
memcpy' = builtin "memcpy" [voidPointer, voidPointer, IntegerType 32] voidPointer
-- Size, pointer to character (i32) array
-- TODO: use target pointer size
unpackString' = builtin "_$helium_runtime_unpack_string" [IntegerType 64, pointer $ IntegerType 8] voidPointer

-- All voidPointers in the Cursor functions are actually cursor*, EXCEPT the
-- voidPointer in the return type of the functions other than newCursor' (where
-- they're actually 'void'), and the last argument to write_cursor (where it's
-- actually 'void*').
newCursor'        = builtin "helium_new_cursor"         [] voidPointer
freeCursor'       = builtin "helium_free_cursor"        [voidPointer] voidPointer
writeCursor'      = builtin "helium_write_cursor"       [voidPointer, IntegerType 64, voidPointer] voidPointer
finishCursor'     = builtin "helium_finish_cursor"      [voidPointer, voidPointer] voidPointer
memdumpCursor'    = builtin "helium_memdump_cursor"     [voidPointer] voidPointer
writeCursorSize'  = builtin "helium_write_cursor_size"  [IntegerType 32, IntegerType 32, voidPointer] voidPointer

builtins :: Iridium.Module -> [Builtin]
builtins iridium = filter (\(Builtin name _ _) -> not $ Iridium.declaresFunction iridium name) allBuiltins
  
allBuiltins :: [Builtin]
allBuiltins =
  [ -- Cursor builtins:
    newCursor', freeCursor', writeCursor', finishCursor', memdumpCursor', writeCursorSize'
    -- Other builtins:
  , eval', alloc', memcpy', unpackString'
  ]

builtinDefinitions :: Iridium.Module -> [Definition]
builtinDefinitions iridium = map definition $ builtins iridium

eval, alloc, unpackString, newCursor, freeCursor, writeCursor, finishCursor, memdumpCursor, writeCursorSize :: Operand
eval = operand eval'
alloc = operand alloc'
unpackString = operand unpackString'

newCursor       = operand newCursor'
freeCursor      = operand freeCursor'
writeCursor     = operand writeCursor'
finishCursor    = operand finishCursor'
memdumpCursor   = operand memdumpCursor'
writeCursorSize = operand writeCursorSize'

operand :: Builtin -> Operand
operand (Builtin name args ret) = ConstantOperand $ GlobalReference (pointer t) $ toName name
  where
    t = FunctionType ret args False

definition :: Builtin -> Definition
definition (Builtin name args ret) = GlobalDefinition $ Function
  { Global.linkage = External
  , Global.visibility = Default
  , Global.dllStorageClass = Nothing
  , Global.callingConvention = C
  , Global.returnAttributes = []
  , Global.returnType = ret
  , Global.name = toName name
  , Global.parameters = (parameters, {- varargs: -} False)
  , Global.functionAttributes = []
  , Global.section = Nothing
  , Global.comdat = Nothing
  , Global.alignment = 0
  , Global.garbageCollectorName = Nothing
  , Global.prefix = Nothing
  , Global.basicBlocks = []
  , Global.personalityFunction = Nothing
  , Global.metadata = []
  }
  where
    parameters :: [Parameter]
    parameters = map (\t -> Parameter t (mkName "_") []) args
