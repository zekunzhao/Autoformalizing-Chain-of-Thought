"""Resolve the PropBank frames directory without hardcoded machine paths."""
from __future__ import annotations

import os
from pathlib import Path

_PKG = Path(__file__).resolve().parent


def resolve_frames_dir(cli_value: str | None = None) -> str:
    """Return a directory of PropBank ``*.xml`` frame files.

    Order: ``--frames`` / explicit argument, then ``PROPBANK_FRAMES``,
    then the bundled ``frames/`` stub shipped with this archive.
    """
    candidates = []
    if cli_value:
        candidates.append(Path(cli_value).expanduser())
    env = os.environ.get("PROPBANK_FRAMES")
    if env:
        candidates.append(Path(env).expanduser())
    candidates.append(_PKG / "frames")

    for path in candidates:
        if path.is_dir() and any(path.glob("*.xml")):
            return str(path.resolve())

    raise FileNotFoundError(
        "No PropBank frames found. Pass --frames, set PROPBANK_FRAMES, "
        "or clone https://github.com/propbank/propbank-frames and point "
        "at its frames/ directory. A tiny bake.xml stub is bundled for the sample."
    )
