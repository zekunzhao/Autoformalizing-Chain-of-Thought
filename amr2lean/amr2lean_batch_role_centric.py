# role centric translation
import argparse
from amr2lean2 import AMR2LeanTranslator
from propbank_interface import PropbankCatalogue
import json
import os 
from typing import Dict, List, Tuple, Set 

class AMR2LeanBatch:
    def __init__(self, propbank_catalog: PropbankCatalogue,
                 import_semantic_gadgets: bool = False,
                 label_map: Dict[str,str] = None,
                 shorter_variant: bool = False,
                 include_nl_comment: bool = False ):
        self.tr = AMR2LeanTranslator(propbank_catalog, import_semantic_gadgets, shorter_variant, include_nl_comment)
        self.label_map = label_map or {
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
        }

    def _kind(self, label: str) -> str:
        return self.label_map.get(label.lower().strip(), "axiom")

    def translate_many(self, items: List[Dict[str, str]]) -> str:
        """
        items in desired order; each item supports:
          { "amr": <penman>,
            "label": <string>,         # maps to axiom/lemma/theorem
            "name": Optional[str],     # lean identifier suffix
            "sid": Optional[str],      # AMR sentence id (if used by your loader)
            "negate": Optional[bool],  # only used when kind == "theorem"
          }
        """
        for it in items:
            kind   = self._kind(it.get("PIT", "axiom"))
            negate = bool(it.get("negate", False)) and (kind == "theorem")
            v = str(it.get("index", ""))
            sid_str = (v and f"s{v}") or v
            self.tr.translate_one_as(
                amr_str = it["amr"],
                kind    = kind,
                name    = it.get("name"),
                sid     = sid_str,
                nl_body = it.get("text", ""),
                negate  = negate
            )
        return self.tr.M.render()



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
