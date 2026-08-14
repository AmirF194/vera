"""Reading the `VERA_*` diagnostic flags.

One predicate, so the knobs catalogued in `ENVIRONMENT.md` agree about
what "set" means.  Two of them are read from opposite ends of the
compiler — `VERA_EAGER_GC` in `vera/codegen/assembly.py` at emit time,
`VERA_DEBUG_HOST_ERRORS` in `vera/codegen/api.py` at execution time —
and a second copy of the parsing rule is how one of them quietly starts
accepting a spelling the other rejects, in a variable a user only ever
sets while something is already going wrong.

Deliberately a leaf: this module imports `os` and nothing from `vera`,
so any layer can read a flag without an import cycle.
"""

from __future__ import annotations

import os

# The spellings that mean "on".  Compared after stripping surrounding
# whitespace and lowercasing, so ` TRUE ` counts.  Anything else —
# including `0`, `no`, `false` and the empty string — means off, so a
# variable left set to `0` in a shell profile does not silently enable a
# debugging mode.
#
# The set is the UNION of what the two read sites accepted before they
# were unified: `VERA_EAGER_GC` took `on` and `VERA_DEBUG_HOST_ERRORS`
# did not, and neither ENVIRONMENT.md section mentioned it.  Widening
# the narrower knob is safe; narrowing the wider one would quietly stop
# honouring `VERA_EAGER_GC=on` for whoever is already typing it.
_TRUTHY = ("1", "true", "yes", "on")


def flag_enabled(name: str) -> bool:
    """Is the `VERA_*` diagnostic flag ``name`` set to a truthy value?"""
    return os.environ.get(name, "").strip().lower() in _TRUTHY
