# Agentic prover

LangGraph agent that takes Lean 4 *templates* (axioms plus theorems with `sorry`) and attempts proofs via an LLM + Lean REPL loop. This archive is anonymized for double-blind review.

The agent may insert extra axioms and replace `sorry` with tactics. Type-check success is not a faithfulness guarantee; see the accompanying paper.

## Requirements

- Python 3.10+
- `pip install -r requirements.txt`
- An OpenAI API key in `OPENAI_API_KEY` (never commit keys)
- Lean 4 via `lean-interact`. This archive pins `leanprover/lean4:v4.26.0` in `lean-toolchain`. The first run may download a Lean toolchain.

## Quick start

```bash
export OPENAI_API_KEY=sk-...
# optional: export OPENAI_MODEL=gpt-5-mini
pip install -r requirements.txt
python langgraph_cot_auto.py \
  --inputs samples \
  --pattern tweety.lean \
  --out ./out \
  --rounds 3 \
  --style autof
```

AMR-style templates (comments `-- natural language description` / `-- NL` before each declaration):

```bash
python langgraph_cot_auto.py \
  --inputs samples \
  --pattern tweety_amr.lean \
  --out ./out \
  --rounds 3 \
  --style AMR-Role
```

`--style` is one of `autof`, `AMR-Frame`, `AMR-Role`.

## CLI

| Flag | Meaning |
| --- | --- |
| `--inputs` | Directory of `.lean` templates |
| `--pattern` | Glob (default `*.lean`) |
| `--out` | JSON logs per file |
| `--rounds` | Max LLM/Lean rounds |
| `--style` | Template encoding (cheat-sheet + parser) |
| `--model` | OpenAI chat model (else `OPENAI_MODEL` or `gpt-5-mini`) |
| `--exclude-processed` | Skip stems that already have an output JSON |

## Layout

| Path | Role |
| --- | --- |
| `langgraph_cot_auto.py` | Agent graph and CLI |
| `langgraph_cot_amr_ms.py` | AMR template parser and encoding cheat-sheets |
| `samples/` | Tiny type-checking templates |
| `lean-toolchain` | Lean 4.26.0 pin |

## Notes

- Templates must type-check *with* `sorry` before the loop starts; otherwise the file is skipped.
- Extra axioms that restate the goal or reverse given implications are filtered (bridge-only rule).
- Do not hard-code API keys. Use `OPENAI_API_KEY`.
