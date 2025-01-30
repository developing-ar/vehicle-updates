module Vehicle.Compile.Type.System where

import Data.Hashable (Hashable)
import Vehicle.Compile.Context.Free (MonadFreeContext)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (PrintableBuiltin, prettyVerbose)
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Monad.Class (MonadTypeChecker)
import Vehicle.Data.Builtin.Interface.Normalise (NormalisableBuiltin)
import Vehicle.Data.Builtin.Interface.Type (TypableBuiltin)
import Vehicle.Data.Builtin.Standard (Builtin (..))

-- | The type-checking monad.
type TCM builtin m =
  ( MonadTypeChecker builtin m,
    HasTypeSystem builtin
  )

-- | A class that provides an abstract interface for a set of builtins.
class (Eq builtin, Hashable builtin, NormalisableBuiltin builtin, TypableBuiltin builtin) => HasTypeSystem builtin where
  convertFromStandardBuiltins ::
    (MonadTypeChecker builtin m) =>
    BuiltinUpdate m Builtin builtin

  restrictDeclType ::
    (MonadTypeChecker builtin m) =>
    RestrictedDecl ->
    DeclProvenance ->
    Type builtin ->
    m (Type builtin)

  addAuxiliaryInputOutputConstraints ::
    (MonadTypeChecker builtin m) => Decl builtin -> m (Decl builtin)

  generateDefaultAuxiliaryConstraint ::
    (MonadTypeChecker builtin m) =>
    Maybe (Decl builtin) ->
    m Bool

  isAuxiliaryConstraint ::
    Expr builtin -> Bool

  -- | Is the constraint a casting operation (e.g. of literals, tensors etc.)
  isCastConstraint ::
    builtin -> Bool

  -- | Solves an auxiliary instance constraint (i.e. a constraint that is
  -- not solvable by the default instance mechanism)
  solveAuxiliaryInstanceConstraint ::
    (MonadTypeChecker builtin m, MonadFreeContext builtin m) =>
    WithContext (InstanceConstraint builtin) ->
    m ()

-----------------------------------------------------------------------------
-- Standard builtins
-----------------------------------------------------------------------------

extractElementType :: (PrintableBuiltin builtin1, PrintableBuiltin builtin2) => builtin1 -> [Arg builtin2] -> Expr builtin2
extractElementType b args = case args of
  [tElem] -> argExpr tElem
  _ -> monomorphisationError b args

monomorphisationError :: (PrintableBuiltin builtin1, PrintableBuiltin builtin2) => builtin1 -> [Arg builtin2] -> a
monomorphisationError b args = do
  let exprDoc = prettyVerbose args
  developerError $
    "Monomorphisation should have got rid of" <+> quotePretty (show b) <> "s but found applied to args" <+> squotes exprDoc
