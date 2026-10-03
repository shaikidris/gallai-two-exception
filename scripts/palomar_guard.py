"""Bind a clean release snapshot to the pinned Palomar input/metadata contract.

Adapted from the tested guard in CollatzConvergencePositiveDensity. This
preparation check does not run Comparator, kernels or any registry action.
"""

import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys


PIPELINE = "65f0154ed776cd26c224254aa57b379137f28b0d"
WORKFLOW = ".github/workflows/palomar-rehearsal.yml"
PROFILE = "palomar-standard-v1"


def git(root, *args):
    return subprocess.check_output(
        ["git", "-C", str(root), *args], text=True, stderr=subprocess.PIPE
    ).strip()


def require_snapshot(root, commit):
    if Path(git(root, "rev-parse", "--show-toplevel")).resolve() != root.resolve():
        raise ValueError("Source must be the selected Git repository root")
    if git(root, "rev-parse", "HEAD") != commit:
        raise ValueError("Checkout does not match the requested commit")
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError("Checkout is dirty; validate a clean immutable snapshot")


def validate_inputs(contract, inputs):
    values, request_id = contract.submission_request({"inputs": inputs})
    if not contract.SHA_RE.fullmatch(values["commit_sha"]):
        raise ValueError("Invalid source commit")
    if values.get("authorization_relationship") not in contract.AUTHORIZATION_RELATIONSHIPS:
        raise ValueError("Missing or invalid authorization relationship")
    if inputs.get("pipeline_commit") != PIPELINE:
        raise ValueError("Request pipeline pin differs from the approved verifier")
    if inputs.get("mode") != "full" or inputs.get("execution_profile") != PROFILE:
        raise ValueError("Request must use full mode and the approved execution profile")
    return request_id


def validate_workflow(workflow):
    job = workflow["jobs"]["verify"]
    expected = {
        "repository": "${{ needs.guard.outputs.repository }}",
        "commit": "${{ needs.guard.outputs.commit }}",
        "pipeline_commit": "${{ needs.guard.outputs.pipeline }}",
        "request_id": "${{ needs.guard.outputs.request_id }}",
        "options": "${{ needs.guard.outputs.options }}",
        "mode": "full",
        "execution_profile": PROFILE,
    }
    if job.get("needs") != "guard":
        raise ValueError("Full replay must depend on guard success")
    expected_uses = "PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@" + PIPELINE
    if job.get("uses") != expected_uses or job.get("with") != expected:
        raise ValueError("Workflow and validated input/pipeline bindings differ")


def validate_selection(source, metadata):
    config = json.loads((source / "comparator.json").read_text())
    selected = [r["declaration"] for r in metadata["status"]["main_results"]]
    if config["theorem_names"] != selected:
        raise ValueError("Metadata and Comparator theorem selections differ")
    if set(config["permitted_axioms"]) != {"propext", "Classical.choice", "Quot.sound"}:
        raise ValueError("Comparator must permit exactly the approved standard axioms")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--pipeline", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--request-id", required=True)
    parser.add_argument("--authorization-relationship", required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    source, pipeline = args.source.resolve(), args.pipeline.resolve()
    receipt_path = args.receipt.resolve()
    if receipt_path.is_relative_to(source) or receipt_path.is_relative_to(pipeline):
        raise ValueError("Receipt must be outside both immutable checkouts")
    require_snapshot(source, args.commit)
    require_snapshot(pipeline, PIPELINE)
    sys.path.insert(0, str(pipeline))
    contract = importlib.import_module("scripts.submission_contract")
    options = json.dumps({"comparator_config_path": "comparator.json",
                          "authorization_relationship": args.authorization_relationship})
    inputs = dict(repository=args.repository, commit=args.commit,
                  pipeline_commit=PIPELINE, request_id=args.request_id,
                  mode="full", execution_profile=PROFILE, options=options)
    validate_inputs(contract, inputs)
    metadata = contract.load_formalization_metadata(source / "formalization.yaml")
    validate_selection(source, metadata)
    import yaml
    validate_workflow(yaml.safe_load((source / WORKFLOW).read_text()))
    receipt = {
        "status": "pass",
        "scope": "pinned request/metadata and immutable binding guard; no proof verification",
        "inputs": inputs,
        "metadata_sha256": hashlib.sha256((source / "formalization.yaml").read_bytes()).hexdigest(),
        "workflow_sha256": hashlib.sha256((source / WORKFLOW).read_bytes()).hexdigest(),
        "comparator_sha256": hashlib.sha256((source / "comparator.json").read_bytes()).hexdigest(),
    }
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as out:
            for key, value in [("repository", args.repository), ("commit", args.commit),
                               ("pipeline", PIPELINE), ("request_id", args.request_id),
                               ("options", options)]:
                out.write(f"{key}={value}\n")
    print("PASS: pinned parser, strict metadata, clean snapshots and replay bindings")


if __name__ == "__main__":
    main()
