
Two self-contained packages:

| Archive | Input | Output |
| --- | --- | --- |
| [`amr2lean/`](amr2lean/) (`amr2lean.zip`) | PIT-tagged AMR JSON | Lean 4 templates |
| [`agentic_prover/`](agentic_prover/) (`agentic_prover.zip`) | Lean 4 templates (`sorry`) | attempted proofs + JSON logs |

Each folder has its own `README.md`, `LICENSE`, and `requirements.txt`. Identifiers, machine paths, and API keys have been stripped.

Typical pipeline: AMR JSON → `amr2lean/translate.py` → `.lean` templates → `agentic_prover/langgraph_cot_auto.py`.
