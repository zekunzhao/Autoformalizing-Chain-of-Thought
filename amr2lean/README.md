# AMR2Lean

Deterministic translator from Abstract Meaning Representation (AMR) to Lean 4 templates. This archive is anonymized for double-blind review.

Two encodings are supported:

- **role** (`AMR-Role`): uniform role-assignment triples.
- **frame** (`AMR-Frame`): predicate records with optional core roles `arg0`–`arg4`.

Input is PIT-tagged AMR (premise / lemma / conclusion, etc.). Output is Lean 4 with `sorry` on theorems — a *template*, not a finished proof. Use the companion **agentic_prover** archive to attempt those proofs.

## Requirements

- Python 3.10+
- `pip install -r requirements.txt` (`penman`)
- Optional: `nltk` plus WordNet (`python -c "import nltk; nltk.download('wordnet')"`) for lemma POS tags. Without it, unknown terminals are treated as nouns.
- PropBank frame XML. A one-frame stub (`frames/bake.xml`) is bundled for the sample. For real CoT graphs, clone [propbank-frames](https://github.com/propbank/propbank-frames) and pass its `frames/` directory.

## Quick start

```bash
pip install -r requirements.txt
python translate.py \
  --encoding role \
  --input samples/cake.json \
  --output ./out \
  --frames ./frames
# expected Lean is also checked in as samples/cake_role.lean
```

Frame encoding:

```bash
python translate.py --encoding frame --input samples/cake.json --output ./out --frames ./frames
```

Optional: `export PROPBANK_FRAMES=/path/to/propbank-frames/frames` instead of `--frames`.

## JSON format

Top-level JSON is a list of *rationales*. Each rationale is a list of items:

```json
[
  [
    {
      "index": 0,
      "PIT": "premise",
      "text": "Someone baked a cake.",
      "amr": "(b / bake-01 :ARG0 (p / person) :ARG1 (c / cake))"
    },
    {
      "index": 1,
      "PIT": "conclusion",
      "text": "A cake was baked.",
      "amr": "(b / bake-01 :ARG1 (c / cake))"
    }
  ]
]
```

`PIT` is mapped to Lean `axiom` / `lemma` / `theorem`. A bare list of items (no extra nesting) is also accepted.

## Layout

| Path | Role |
| --- | --- |
| `translate.py` | CLI |
| `amr2lean2.py` + `amr2lean_batch_role_centric.py` | AMR-Role |
| `amr2lean.py` + `amr2lean_batch_frame_centric.py` | AMR-Frame |
| `amr_toolbox/` | AMR graph + PropBank XML loader |
| `frames/` | bundled PropBank stub |
| `special_*.json` | special entities, frames, prepositions |

Run commands from this directory so Python can import the local packages (`PYTHONPATH=.` if you invoke the CLI from elsewhere).

## Notes

- Translation does not call an LLM.
- Unknown PropBank senses fall back to default numbered roles.
- Full-scale experiments need the complete PropBank frames release, not only `bake.xml`.
