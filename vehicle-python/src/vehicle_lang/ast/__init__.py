import json
from abc import ABCMeta, abstractmethod
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import Any, Generic, Iterable, Optional, Sequence, Tuple, Union

from typing_extensions import Literal, Self, TypeAlias, TypeVar, override

from .. import session
from ..error import VehicleError
from ..typing import DeclarationName, Explicit, Target
from ._decode import JsonValue, decode

Name: TypeAlias = str
UniverseLevel: TypeAlias = int


@dataclass(frozen=True, init=False)
class AST(metaclass=ABCMeta):
    def __init__(self) -> None:
        raise TypeError("Cannot instantiate abstract class AST")

    @classmethod
    def from_dict(cls, value: JsonValue) -> Self:
        return decode(cls, value)

    @classmethod
    def from_json(cls, value: str) -> Self:
        return cls.from_dict(json.loads(value))


################################################################################
# Provenance
################################################################################


@dataclass(frozen=True)
class Provenance(AST):
    lineno: int
    col_offset: int
    end_lineno: Optional[int] = None
    end_col_offset: Optional[int] = None


MISSING: Provenance = Provenance(0, 0)

################################################################################
# Values
################################################################################


DType = TypeVar("DType", bool, float, int, Fraction)


@dataclass(frozen=True)
class Tensor(Generic[DType]):
    shape: Tuple[int, ...]
    value: Tuple[DType, ...]


################################################################################
# Expression
################################################################################


@dataclass(frozen=True, init=False)
class Expression(AST):
    # Abstract base for expression nodes
    def __init__(self) -> None:
        raise TypeError("Cannot instantiate abstract class Expression")


#################################################################################
# Dimensions
#################################################################################


@dataclass(frozen=True)
class Dimension(Expression):
    value: int


@dataclass(frozen=True)
class DimensionNil(Expression):
    pass


@dataclass(frozen=True)
class DimensionCons(Expression):
    head: Dimension
    tail: Union["DimensionCons", DimensionNil]


@dataclass(frozen=True)
class DimensionIndex(Expression):
    value: int


################################################################################
# Builtin Literals
################################################################################


@dataclass(frozen=True)
class Index(Expression):
    value: int


@dataclass(frozen=True)
class BoolTensor(Expression):
    value: Tensor[bool]


@dataclass(frozen=True)
class NatTensor(Expression):
    value: Tensor[int]


@dataclass(frozen=True)
class IntTensor(Expression):
    value: Tensor[int]


@dataclass(frozen=True)
class RatTensor(Expression):
    value: Tensor[Fraction]


@dataclass(frozen=True)
class RatLiteral(Expression):
    value: Fraction


################################################################################
# Builtin Constants
################################################################################


@dataclass(frozen=True)
class ConstTensor(Expression):
    body: Expression
    dimension: Expression


################################################################################
# Builtin Types
################################################################################


@dataclass(frozen=True)
class TensorType(Expression):
    body: Expression


@dataclass(frozen=True)
class IndexType(Expression):
    pass


@dataclass(frozen=True)
class IndexTensorType(Expression):
    pass


@dataclass(frozen=True)
class BoolType(Expression):
    pass


@dataclass(frozen=True)
class NatType(Expression):
    pass


@dataclass(frozen=True)
class IntType(Expression):
    pass


@dataclass(frozen=True)
class RatType(Expression):
    pass


@dataclass(frozen=True)
class ListType(Expression):
    pass


@dataclass(frozen=True)
class UnitType(Expression):
    pass


################################################################################
# Builtin Functions
################################################################################


@dataclass(frozen=True)
class ConsList(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class NotBoolTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class AndBoolTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class OrBoolTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class NegRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class AddRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class SubRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class MulRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class DivRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class EqRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class NeRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class LeRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class LtRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class GeRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class GtRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class PowRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class MinRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class MaxRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class ReduceAndBoolTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class ReduceOrBoolTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class ReduceSumRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class ReduceRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class ReduceMulRatTensor(Expression):
    body: Expression


@dataclass(frozen=True)
class EqIndex(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class NeIndex(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class LeIndex(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class LtIndex(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class GeIndex(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class GtIndex(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class LookupRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class StackTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class ConstRatTensor(Expression):
    body: Fraction


@dataclass(frozen=True)
class FoldList(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class MapList(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class MapRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class ZipWithRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class IndicesIndexTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class MinimiseRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class MaximiseRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class If(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class SearchRatTensor(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class DimensionLookup(Expression):
    body: Expression
    index: DimensionIndex


################################################################################
# Variables
################################################################################


@dataclass(frozen=True)
class Binder(AST):
    provenance: Provenance = field(repr=False)
    name: Optional[Name]
    type: Union[Expression, Expression]


@dataclass(frozen=True)
class Pi(Expression):
    body: Sequence[Expression]


@dataclass(frozen=True)
class Lam(Expression):
    binder: Binder
    body: Expression


@dataclass(frozen=True)
class App(Expression):
    provenance: Provenance = field(repr=False)
    body: Expression
    arguments: Sequence[Expression]


@dataclass(frozen=True)
class PartialApp(Expression):
    provenance: Provenance = field(repr=False)
    arity: int
    body: Expression
    arguments: Sequence[Expression]


@dataclass(frozen=True)
class Var(Expression):
    name: Name
    body: Sequence[Expression]


################################################################################
# Declarations
################################################################################


@dataclass(frozen=True, init=False)
class Declaration(AST, metaclass=ABCMeta):
    # Abstract base for top-level declarations
    def __init__(self) -> None:
        raise TypeError("Cannot instantiate abstract class Declaration")

    def get_name(self) -> Name:
        # Abstract method to get the name of the declaration
        raise NotImplementedError("Subclasses must implement get_name()")


@dataclass(frozen=True)
class DefFunction(Declaration):
    provenance: Provenance = field(repr=False)
    name: Name
    type: Expression
    body: Expression

    @override
    def get_name(self) -> Name:
        return self.name


@dataclass(frozen=True)
class DefPostulate(Declaration):
    provenance: Provenance = field(repr=False)
    name: Name
    body: Expression

    @override
    def get_name(self) -> Name:
        return self.name


################################################################################
# Modules
################################################################################


@dataclass(frozen=True, init=False)
class Program(AST):
    def __init__(self) -> None:
        raise TypeError("Cannot instantiate abstract class Program")

    @override
    @classmethod
    def from_dict(cls, value: JsonValue) -> Self:
        return decode(Program, value)


@dataclass(frozen=True)
class Main(Program):
    declarations: Sequence[Declaration]


def load(
    path: Union[str, Path],
    *,
    declarations: Iterable[DeclarationName] = (),
    target: Target = Explicit.Explicit,
) -> Program:
    exc, out, err, log = session.check_output(
        [
            "compile",
            "--target",
            target._vehicle_option_name,
            "--json",
            f"--specification={path}",
            *[f"--declaration={declaration_name}" for declaration_name in declarations],
        ]
    )
    if exc != 0:
        msg: str = err or out or log or "unknown error"
        raise VehicleError(msg)
    if out is None:
        raise VehicleError("no output")
    return Program.from_json(out)
