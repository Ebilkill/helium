module Helium.CodeGeneration.LLVM.Struct where

import Helium.CodeGeneration.Iridium.Show ()
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import LLVM.AST (Name)
import qualified Lvm.Core.Type as Core

data Struct
  = Struct
      { typeName :: Maybe Name,
        tagSize :: Int,
        tagValue :: Int,
        fields :: [StructField]
      }
  deriving (Eq, Ord, Show)

data StructField
  = StructField
      { fieldType :: Core.Type,
        fieldFlagIndex :: Maybe Int
      }
  deriving (Eq, Ord, Show)

tupleStruct :: Int -> Struct
tupleStruct arity = Struct Nothing 0 0 $ map field [0 .. arity - 1]
  where
    field index = StructField (Core.TVar index) (Just index)
