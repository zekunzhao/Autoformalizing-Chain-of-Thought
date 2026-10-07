#!/usr/bin/env python3
"""AMR -> Lean 4. Input: PIT-tagged AMR JSON. Output: .lean templates."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from frames_util import resolve_frames_dir
from propbank_interface import PropbankCatalogue


def _load_rationales(path: Path):
    data = json.loads(path.read_text(encoding="utf-8"))
    if not data:
        return []
    if isinstance(data, dict):
        data = [data]
    first = data[0]
    if isinstance(first, dict) and "amr" in first:
        return [data]
    return data


def _items(rationale):
    if isinstance(rationale, list) and rationale and isinstance(rationale[0], list):
        return rationale[0]
    return rationale


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Translate PIT-tagged AMR graphs to Lean 4 templates."
    )
    ap.add_argument("-i", "--input", required=True, help="JSON file of AMR items or rationales")
    ap.add_argument("-o", "--output", default="./out", help="Directory for .lean files")
    ap.add_argument(
        "--encoding",
        choices=("role", "frame"),
        default="role",
        help="AMR-Role (default) or AMR-Frame encoding",
    )
    ap.add_argument("--frames", default=None, help="Directory of PropBank frame XML files")
    ap.add_argument(
        "--short",
        action="store_true",
        help="Role encoding only: shorter Lean variant (lean_snippets3)",
    )
    args = ap.parse_args()

    frames_dir = resolve_frames_dir(args.frames)
    pb = PropbankCatalogue(frames_dir)

    if args.encoding == "role":
        from amr2lean_batch_role_centric import AMR2LeanBatch
        make_batch = lambda: AMR2LeanBatch(
            pb,
            import_semantic_gadgets=False,
            shorter_variant=args.short,
            include_nl_comment=True,
        )
    else:
        from amr2lean_batch_frame_centric import AMR2LeanBatch
        make_batch = lambda: AMR2LeanBatch(
            pb, import_semantic_gadgets=False, include_nl_comment=True
        )

    out_dir = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)

    rationales = _load_rationales(Path(args.input))
    if not rationales:
        raise SystemExit(f"No AMR items in {args.input}")

    for idx, rationale in enumerate(rationales):
        batch = make_batch()
        lean = batch.translate_many(_items(rationale))
        dest = out_dir / f"rationale-{idx}.lean"
        dest.write_text(lean, encoding="utf-8")
        print(dest)


if __name__ == "__main__":
    main()
