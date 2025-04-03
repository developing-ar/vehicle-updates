from pathlib import Path
from typing import Union

from .. import session
from ..error import VehicleError
from ..typing import TypeSystem


def check(
    specification: Union[str, Path], typeSystem: TypeSystem = TypeSystem.Standard
) -> None:
    """
    Type-check a .vcl specification file.

    :param specification: The path to the Vehicle specification file to verify.
    :param typeSystem: The typing system that should be used.
    """
    args = ["check", "--check", str(specification)]
    args.extend(["--typeSystem", typeSystem._vehicle_option_name])

    # Call Vehicle
    exc, out, err, log = session.check_output(args)

    # Check for errors
    if exc != 0:
        # TODO: Change this to return JSON
        raise VehicleError(err or out or log or "unknown error")

    else:  # if out is none, then the specification is correct
        return None
