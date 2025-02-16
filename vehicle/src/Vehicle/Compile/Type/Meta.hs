module Vehicle.Compile.Type.Meta
  ( MetaSet,
    MetaVariableContext,
    MetaInfo (..),
    extendMetaCtx,
    HasMetas (..),
    makeMetaType,
    makeMetaExpr,
    getMetaDependencies,
    getNormMetaDependencies,
    findMetaInfo,
  )
where

import Vehicle.Compile.Type.Meta.Set (MetaSet)
import Vehicle.Compile.Type.Meta.Variable
