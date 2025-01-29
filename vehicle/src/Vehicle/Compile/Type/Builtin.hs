module Vehicle.Compile.Type.Builtin where

import Data.Proxy (Proxy)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (PrintableBuiltin)
import Vehicle.Data.Builtin.Linearity (LinearityBuiltin)
import Vehicle.Data.Builtin.Linearity.Type (isLinearityBuiltinConstructor, typeLinearityBuiltin)
import Vehicle.Data.Builtin.Polarity (PolarityBuiltin)
import Vehicle.Data.Builtin.Polarity.Type (isPolarityBuiltinConstructor, typePolarityBuiltin)
import Vehicle.Data.Builtin.Standard (Builtin (..))
import Vehicle.Data.Builtin.Standard.Type (isStandardConstructor, typeStandardBuiltin)

class (PrintableBuiltin builtin) => TypableBuiltin builtin where
  -- | Construct a type for the builtin
  typeBuiltin :: Provenance -> builtin -> Type builtin

  -- | Can meta variables depend on other values in the scope?
  -- Efficiency hack for polarity/linearity subsystems.
  useDependentMetas :: Proxy builtin -> Bool

  -- | Could the constructors end up the same if applied to some
  -- suitable set of arguments.
  couldBeEqual :: builtin -> builtin -> Bool

instance TypableBuiltin LinearityBuiltin where
  typeBuiltin = typeLinearityBuiltin
  useDependentMetas _ = False
  couldBeEqual b1 b2 =
    not (isLinearityBuiltinConstructor b1 && isLinearityBuiltinConstructor b2)

instance TypableBuiltin PolarityBuiltin where
  typeBuiltin = typePolarityBuiltin
  useDependentMetas _ = False
  couldBeEqual b1 b2 =
    not (isPolarityBuiltinConstructor b1 && isPolarityBuiltinConstructor b2)

instance TypableBuiltin Builtin where
  typeBuiltin = typeStandardBuiltin
  useDependentMetas _ = True
  couldBeEqual b1 b2 =
    not (isStandardConstructor b1 && isStandardConstructor b2)
