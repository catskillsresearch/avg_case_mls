#!/usr/bin/env python3
"""Run PalomarPolicy editorial rubric via Cursor SDK."""

from __future__ import annotations

import argparse
import json
import os
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
PRIMARY_MODEL = "gpt-5.6-sol"
ECONOMY_MODEL = "composer-2.5"
PRIMARY_STEPS = frozenset({
    "statement_alignment", "definition_fidelity", "literature_notability", "synthesis",
})
ECONOMY_STEPS = frozenset({"classification", "metadata", "proof_account"})
TOKENS_CANDIDATES = (ROOT.parent / "tokens_ssto.yaml", ROOT / "tokens_ssto.yaml")
PROOF_ACCOUNT_TRIGGER = re.compile(
    r"informal proof|proof account|proof architecture|proof strategy", re.IGNORECASE
)


def load_json(path: Path) -> Any:
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def read_text(path: Path, limit: int | None = None) -> str:
    text = path.read_text(encoding="utf-8")
    if limit is not None and len(text) > limit:
        return text[:limit] + f"\n\n[truncated at {limit} characters]"
    return text


def parse_model_json(raw: str) -> dict:
    text = raw.strip()
    if text.startswith("```"):
        text = re.sub(r"^```(?:json)?\s*", "", text)
        text = re.sub(r"\s*```$", "", text)
    start, end = text.find("{"), text.rfind("}")
    if start == -1 or end == -1 or end <= start:
        raise ValueError("model output is not a JSON object")
    return json.loads(text[start : end + 1])


def _read_key_from_tokens_file(path: Path) -> str | None:
    if not path.is_file():
        return None
    text = path.read_text(encoding="utf-8")
    for pattern in (
        r"(?m)^CURSOR_API_KEY:\s*(\S+)",
        r"(?m)^cursor_api_key:\s*(\S+)",
    ):
        match = re.search(pattern, text)
        if match:
            return match.group(1).strip().strip("'\"")
    try:
        import yaml
        data = yaml.safe_load(text)
        if isinstance(data, dict):
            key = (data.get("CURSOR_API_KEY") or data.get("cursor_api_key") or "").strip()
            return key or None
    except Exception:
        pass
    return None


def load_cursor_api_key() -> str:
    for name in ("CURSOR_API_KEY", "PALOMAR_CURSOR_API_KEY"):
        value = os.environ.get(name, "").strip()
        if value:
            return value
    for path in TOKENS_CANDIDATES:
        key = _read_key_from_tokens_file(path)
        if key:
            return key
    tried = ", ".join(str(p) for p in TOKENS_CANDIDATES)
    raise SystemExit(
        "FAIL: set CURSOR_API_KEY or add it to ../tokens_ssto.yaml for editorial audit.\n"
        f"Looked for token files: {tried}\n"
        f"Primary model: {PRIMARY_MODEL}; economy model: {ECONOMY_MODEL}."
    )


def model_for_step(step_id: str) -> str:
    if step_id in PRIMARY_STEPS:
        return os.environ.get(
            "PALOMAR_EDITORIAL_PRIMARY_MODEL", PRIMARY_MODEL
        ).strip() or PRIMARY_MODEL
    if step_id in ECONOMY_STEPS:
        return os.environ.get(
            "PALOMAR_EDITORIAL_ECONOMY_MODEL", ECONOMY_MODEL
        ).strip() or ECONOMY_MODEL
    return PRIMARY_MODEL


def cursor_prompt(api_key: str, model: str, system: str, user: str) -> str:
    from cursor_sdk import Agent, AgentOptions, CursorAgentError, LocalAgentOptions

    prompt = (
        f"{system.strip()}\n\n---\n\n{user.strip()}\n\n"
        "Respond with one bare JSON object only. No markdown fences or surrounding prose."
    )
    try:
        result = Agent.prompt(
            prompt,
            AgentOptions(
                api_key=api_key,
                model=model,
                local=LocalAgentOptions(cwd=str(ROOT)),
            ),
        )
    except CursorAgentError as err:
        raise SystemExit(f"FAIL: Cursor API error ({model}): {err.message}") from err
    if result.status != "finished":
        detail = getattr(result, "result", None) or getattr(result, "error", None) or result.status
        raise SystemExit(f"FAIL: Cursor run did not finish ({model}): {detail}")
    body = (result.result or "").strip()
    if not body:
        raise SystemExit(f"FAIL: empty Cursor response ({model})")
    return body


def expected_declarations(cfg: dict) -> list[str]:
    return list(cfg["theorem_names"]) + list(cfg.get("definition_names", []))


def expected_codes(formalization_yaml: str) -> list[str]:
    try:
        import yaml
        doc = yaml.safe_load(formalization_yaml)
        classification = doc.get("classification", {}) if isinstance(doc, dict) else {}
        return (
            [f"arxiv:{item}" for item in classification.get("arxiv", []) or []]
            + [f"msc2020:{item}" for item in classification.get("msc2020", []) or []]
        )
    except Exception:
        codes: list[str] = []
        for field in ("arxiv", "msc2020"):
            for match in re.finditer(
                rf"{field}:\s*\[(.*?)\]", formalization_yaml, re.DOTALL
            ):
                codes.extend(
                    f"{field}:{item}"
                    for item in re.findall(r"[\w.\-]+", match.group(1))
                )
        return codes


def assemble_evidence(
    step_id: str, cfg: dict, policy_dir: Path, mechanical: dict, prior: list[dict]
) -> dict:
    evidence: dict[str, Any] = {
        "step": step_id,
        "repository_commit": mechanical.get("repository", {}).get("commit") or "unknown",
        "comparator": cfg,
        "mechanical_report": mechanical,
        "previous_findings": [
            finding for result in prior for finding in result.get("findings", [])
        ],
    }
    files = {
        "formalization_metadata": ROOT / "formalization.yaml",
        "challenge_source": ROOT / "Challenge.lean",
        "solution_source": ROOT / "Solution.lean",
        "project_readme": ROOT / "README.md",
        "comparator_config": ROOT / "comparator.json",
        "lakefile": (
            ROOT / "lakefile.toml"
            if (ROOT / "lakefile.toml").is_file() else ROOT / "lakefile.lean"
        ),
        "lean_toolchain": ROOT / "lean-toolchain",
        "provenance": ROOT / "PROVENANCE.md",
    }
    for key, path in files.items():
        if path.is_file():
            evidence[key] = read_text(
                path, limit=120_000 if key == "challenge_source" else 80_000
            )
    guide = policy_dir / "taxonomies/classification-guide.md"
    if guide.is_file():
        evidence["classification_guide"] = read_text(guide, 40_000)
    evidence["declarations_checked_order"] = expected_declarations(cfg)
    return evidence


def validate_step_result(
    result: dict, step: dict, cfg: dict, formalization_yaml: str
) -> list[str]:
    errors: list[str] = []
    step_id = step["id"]
    required = {
        "step", "outcome", "summary", "findings", "scores", "trust_level",
        "sources_checked", "declarations_checked", "codes_checked", "internal_notes",
    }
    if missing := required - set(result):
        errors.append(f"{step_id}: missing fields {sorted(missing)}")
    if result.get("step") != step_id:
        errors.append(f"{step_id}: step field mismatch {result.get('step')!r}")
    outcome = result.get("outcome")
    if outcome not in {"neutral", "warning", "failure"}:
        errors.append(f"{step_id}: invalid outcome {outcome!r}")
    if step.get("requires_declaration_coverage"):
        if result.get("declarations_checked") != expected_declarations(cfg):
            errors.append(f"{step_id}: declarations_checked mismatch")
    if step.get("requires_classification_coverage"):
        expected = expected_codes(formalization_yaml)
        if result.get("codes_checked") != expected:
            errors.append(
                f"{step_id}: codes_checked mismatch "
                f"(expected {expected}, got {result.get('codes_checked')})"
            )
    findings = result.get("findings", [])
    if outcome == "neutral" and findings:
        errors.append(f"{step_id}: neutral outcome must have empty findings")
    if outcome in {"warning", "failure"} and not findings:
        errors.append(f"{step_id}: {outcome} outcome requires at least one finding")
    for key in step.get("score_keys", []):
        score = result.get("scores", {}).get(key)
        if score is not None and not (isinstance(score, int) and 1 <= score <= 5):
            errors.append(f"{step_id}: score {key}={score!r} not integer 1-5")
    return errors


def validate_synthesis(synthesis: dict, results: list[dict], rubric: dict) -> list[str]:
    errors: list[str] = []
    required = {"outcome", "summary", "scores", "warnings", "requested_changes"}
    if missing := required - set(synthesis):
        errors.append(f"synthesis: missing fields {sorted(missing)}")
    outcome = synthesis.get("outcome")
    if outcome not in {"neutral", "revision_required", "rejected"}:
        errors.append(f"synthesis: invalid outcome {outcome!r}")
    for key in rubric.get("registry_scores", []):
        expected = next(
            (r.get("scores", {}).get(key) for r in results
             if r.get("scores", {}).get(key) is not None),
            None,
        )
        actual = synthesis.get("scores", {}).get(key)
        if expected is not None and actual != expected:
            errors.append(
                f"synthesis: score {key} must copy evidence check ({expected} != {actual})"
            )
    notability = synthesis.get("scores", {}).get("notability")
    if notability is not None and notability < rubric.get("minimum_score", 4):
        if outcome != "rejected":
            errors.append("synthesis: notability below minimum requires rejected outcome")
    if any(r.get("outcome") == "failure" for r in results) and outcome == "neutral":
        errors.append("synthesis: cannot be neutral when a check failed")
    if outcome == "revision_required" and not synthesis.get("requested_changes"):
        errors.append("synthesis: revision_required needs requested_changes")
    all_findings = [f for r in results for f in r.get("findings", [])]
    if outcome == "neutral" and all_findings:
        errors.append("synthesis: neutral outcome cannot have material findings")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run Palomar editorial audit using vendored PalomarPolicy prompts."
    )
    parser.add_argument("--policy-dir", type=Path, default=Path("vendor/palomar-policy"))
    parser.add_argument("--policy-pin", required=True)
    parser.add_argument("--mechanical-report", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    api_key = load_cursor_api_key()
    policy_dir = args.policy_dir
    rubric = load_json(policy_dir / "rubric.json")
    materiality = read_text(policy_dir / "prompts/materiality.md")
    mechanical = load_json(args.mechanical_report)
    cfg = load_json(ROOT / "comparator.json")
    formalization_yaml = read_text(ROOT / "formalization.yaml")
    proof_texts = [
        read_text(path, 40_000)
        for path in (ROOT / "Challenge.lean", ROOT / "README.md", ROOT / "Solution.lean")
        if path.is_file()
    ] + [formalization_yaml]

    results: list[dict] = []
    models: dict[str, str] = {}
    for step in rubric["steps"]:
        step_id = step["id"]
        if step_id == "synthesis":
            continue
        if step_id == "proof_account" and not any(
            PROOF_ACCOUNT_TRIGGER.search(text) for text in proof_texts
        ):
            print(f"SKIP: {step_id} (no informal proof account detected)")
            continue
        model = model_for_step(step_id)
        print(f"RUN: editorial step {step_id} ({model}) …")
        system = materiality + "\n\n---\n\n" + read_text(policy_dir / step["prompt"])
        evidence = assemble_evidence(step_id, cfg, policy_dir, mechanical, results)
        raw = cursor_prompt(
            api_key, model, system,
            "Evaluate the submission evidence below. Return one bare JSON object only.\n\n"
            + json.dumps(evidence, indent=2),
        )
        result = parse_model_json(raw)
        errors = validate_step_result(result, step, cfg, formalization_yaml)
        if errors:
            raise SystemExit("FAIL: step validation errors:\n  " + "\n  ".join(errors))
        results.append(result)
        models[step_id] = model
        print(f"  outcome={result['outcome']} summary={result['summary'][:120]}")

    model = model_for_step("synthesis")
    print(f"RUN: editorial synthesis ({model}) …")
    system = materiality + "\n\n---\n\n" + read_text(
        policy_dir / "prompts/06-synthesis.md"
    )
    raw = cursor_prompt(
        api_key, model, system,
        json.dumps({
            "mechanical_report": mechanical,
            "all_previous_results": results,
            "submission": formalization_yaml,
        }, indent=2),
    )
    synthesis = parse_model_json(raw)
    models["synthesis"] = model
    errors = validate_synthesis(synthesis, results, rubric)
    if errors:
        raise SystemExit("FAIL: synthesis validation errors:\n  " + "\n  ".join(errors))

    packet = {
        "policy_commit": args.policy_pin,
        "provider": "cursor_sdk",
        "models": {
            "primary_default": PRIMARY_MODEL,
            "economy_default": ECONOMY_MODEL,
            "by_step": models,
        },
        "checks": results,
        "synthesis": synthesis,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(packet, indent=2) + "\n", encoding="utf-8")
    outcome = synthesis.get("outcome")
    print(f"OK: editorial audit written to {args.out}")
    print(f"Synthesis outcome: {outcome}")
    if outcome != "neutral":
        print("Findings / warnings:")
        for warning in synthesis.get("warnings", []):
            print(f"  - {warning}")
        for change in synthesis.get("requested_changes", []):
            print(f"  * {change}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
