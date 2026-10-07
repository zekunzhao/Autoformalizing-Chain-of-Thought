
# frame centric approach for CoT translation
from propbank_interface import PropbankCatalogue
import json
import os
from typing import Dict, List, Tuple
from amr2lean import AMR2LeanSequenceTranslator

class AMR2LeanBatch:
    """
    Multi-AMR driver:
      - preserves order,
      - shares boilerplate,
      - maps human labels -> {axiom | lemma | theorem},
      - optional negation per item (or inferred if label is 'contradiction').
    """
    def __init__(self, propbank_catalog: PropbankCatalogue, import_semantic_gadgets: bool = False,
                 label_map: Dict[str, str] = None, include_nl_comment: bool = False):
        self.pb = propbank_catalog
        self.import_semantic_gadgets = import_semantic_gadgets
        # default mapping (you can override by passing label_map)
        self.label_map = (label_map or {
            "premise": "axiom",
            "new definition": "axiom",
            "question": "question",
            "implicit-assumption": "axiom",
            "lemma": "lemma",
            "rule/explicit-knowledge-claim": "axiom",
            "conclusion": "theorem",
            "implicit assumption resurfacing": "axiom",
            "axiom": "axiom",
            "theorem": "theorem",
        })
        self.include_nl_comment = include_nl_comment

    def _to_kind_and_neg(self, label: str) -> Tuple[str, bool]:
        lab = (label or "").strip().lower()
        negate = lab in {"contradiction", "negated", "neg"}
        base = lab.replace("contradiction", "conclusion").replace("negated", "conclusion").strip()
        kind = self.label_map.get(base, "axiom")
        return kind, negate

    def translate_many(self, items: List[Dict[str, str]]) -> str:
        """
        items: list of dicts with keys:
          - "amr" (str)     : required AMR string
          - "label" (str)   : e.g., 'premise', 'conclusion'
          - "name"  (str)   : desired Lean identifier (optional but recommended)
          - "negate"(bool)  : optional explicit negation
          - "sid"   (str)   : optional sentence id/stable tag
        """
        seq = AMR2LeanSequenceTranslator(self.pb, import_semantic_gadgets=self.import_semantic_gadgets, include_nl_comment=self.include_nl_comment)

        for idx, item in enumerate(items, start=1):
            amr = item["amr"]
            label = item.get("PIT", "premise")
            name = item.get("name", None)
            sid  = item.get("sid", f"s{idx}")
            nl_body = item.get("text", '')
            kind, inferred_neg = self._to_kind_and_neg(label)
            negate = bool(item.get("negate", inferred_neg))

            seq.add(amr_str=amr, kind=kind, name=name, negate=negate, sid=sid, nl_body=nl_body)

        code = seq.render()

        return code


if __name__ == "__main__":
    import argparse
    from pathlib import Path
    from frames_util import resolve_frames_dir

    ap = argparse.ArgumentParser(description="AMR -> Lean 4")
    ap.add_argument("-i", "--input", required=True, help="JSON file of PIT-tagged AMR")
    ap.add_argument("-o", "--output", default="./out", help="Output directory for Lean files")
    ap.add_argument("--frames", default=None, help="Directory of PropBank frame XML files")
    args = ap.parse_args()

    pb_catalog = PropbankCatalogue(resolve_frames_dir(args.frames))
    data = json.loads(Path(args.input).read_text(encoding="utf-8"))
    if data and isinstance(data[0], dict) and "amr" in data[0]:
        rationales = [data]
    else:
        rationales = data
    out_dir = Path(args.output)
    out_dir.mkdir(parents=True, exist_ok=True)
    for idx, rationale in enumerate(rationales):
        items = rationale
        if isinstance(rationale, list) and rationale and isinstance(rationale[0], list):
            items = rationale[0]
        batch = AMR2LeanBatch(pb_catalog, import_semantic_gadgets=False, include_nl_comment=True)
        lean_code = batch.translate_many(items)
        (out_dir / f"rationale-{idx}.lean").write_text(lean_code, encoding="utf-8")
