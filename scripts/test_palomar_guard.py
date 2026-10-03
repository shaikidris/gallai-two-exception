"""Replay-input regressions against the pinned upstream parser; no Lean build."""

import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import yaml
import palomar_guard as guard


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--pipeline", type=Path, required=True)
parser.add_argument("--scratch-root", type=Path, required=True)
args = parser.parse_args()
sys.path.insert(0, str(args.pipeline.resolve()))
from scripts import submission_contract as contract

SOURCE = Path(__file__).resolve().parents[1]


class GuardRegression(unittest.TestCase):
    def inputs(self):
        return dict(repository="example/project", commit="a" * 40,
                    pipeline_commit=guard.PIPELINE, request_id="abcdef123456",
                    mode="full", execution_profile=guard.PROFILE,
                    options=json.dumps({"comparator_config_path": "comparator.json",
                        "authorization_relationship": "I am a responsible author or maintainer"}))

    def workflow(self):
        return yaml.safe_load((SOURCE / guard.WORKFLOW).read_text())

    def test_valid_request(self):
        self.assertEqual(guard.validate_inputs(contract, self.inputs()), "abcdef123456")

    def test_bad_request_id(self):
        inputs = self.inputs()
        inputs["request_id"] = "c2-release-long-identifier"
        with self.assertRaisesRegex(Exception, "twelve"):
            guard.validate_inputs(contract, inputs)

    def test_missing_authorization(self):
        inputs = self.inputs()
        inputs["options"] = '{"comparator_config_path":"comparator.json"}'
        with self.assertRaisesRegex(ValueError, "authorization"):
            guard.validate_inputs(contract, inputs)

    def test_missing_comparator(self):
        inputs = self.inputs()
        inputs["options"] = '{"authorization_relationship":"I am a responsible author or maintainer"}'
        with self.assertRaisesRegex(Exception, "Comparator configuration path"):
            guard.validate_inputs(contract, inputs)

    def test_pipeline_mismatch(self):
        inputs = self.inputs()
        inputs["pipeline_commit"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "pipeline pin"):
            guard.validate_inputs(contract, inputs)

    def test_invalid_source_commit(self):
        inputs = self.inputs()
        inputs["commit"] = "main"
        with self.assertRaisesRegex(ValueError, "source commit"):
            guard.validate_inputs(contract, inputs)

    def test_wrong_mode_or_profile(self):
        for key, value in [("mode", "preflight"), ("execution_profile", "unknown")]:
            inputs = self.inputs()
            inputs[key] = value
            with self.assertRaisesRegex(ValueError, "full mode"):
                guard.validate_inputs(contract, inputs)

    def test_valid_workflow(self):
        guard.validate_workflow(self.workflow())

    def test_workflow_pin_mismatch(self):
        workflow = self.workflow()
        workflow["jobs"]["verify"]["uses"] = "wrong/workflow@" + "0" * 40
        with self.assertRaisesRegex(ValueError, "bindings"):
            guard.validate_workflow(workflow)

    def test_workflow_must_depend_on_guard(self):
        workflow = self.workflow()
        del workflow["jobs"]["verify"]["needs"]
        with self.assertRaisesRegex(ValueError, "guard success"):
            guard.validate_workflow(workflow)

    def test_workflow_source_binding(self):
        workflow = self.workflow()
        workflow["jobs"]["verify"]["with"]["commit"] = "${{ github.sha }}"
        with self.assertRaisesRegex(ValueError, "bindings"):
            guard.validate_workflow(workflow)

    def test_embedded_orcid_names(self):
        valid = contract.load_formalization_metadata(SOURCE / "formalization.yaml")
        for key in ("authors", "responsible_maintainers"):
            bad = copy.deepcopy(valid)
            bad["project"][key] = ["Researcher (ORCID: 0009-0009-9699-9712)"]
            with tempfile.TemporaryDirectory(dir=args.scratch_root) as tmp:
                path = Path(tmp) / "formalization.yaml"
                path.write_text(yaml.safe_dump(bad))
                with self.assertRaisesRegex(Exception, "ORCID"):
                    contract.load_formalization_metadata(path)

    def test_theorem_selection_mismatch(self):
        metadata = contract.load_formalization_metadata(SOURCE / "formalization.yaml")
        guard.validate_selection(SOURCE, metadata)
        metadata["status"]["main_results"].pop()
        with self.assertRaisesRegex(ValueError, "selections differ"):
            guard.validate_selection(SOURCE, metadata)

    def test_clean_snapshot_and_full_guard(self):
        with tempfile.TemporaryDirectory(dir=args.scratch_root) as tmp:
            root = Path(tmp) / "source"
            root.mkdir()
            def run(*argv):
                return subprocess.check_output(["git", "-C", str(root), *argv],
                                               text=True, stderr=subprocess.DEVNULL).strip()
            run("init")
            for name in ("formalization.yaml", "comparator.json", guard.WORKFLOW):
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((SOURCE / name).read_bytes())
            run("add", ".")
            run("-c", "user.name=Guard Regression", "-c", "user.email=guard@example.invalid",
                "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false",
                "commit", "-m", "temporary guard fixture")
            commit = run("rev-parse", "HEAD")
            guard.require_snapshot(root, commit)
            result = subprocess.run([
                sys.executable, str(SOURCE / "scripts/palomar_guard.py"),
                "--source", str(root), "--pipeline", str(args.pipeline.resolve()),
                "--commit", commit, "--repository", "example/project",
                "--request-id", "abcdef123456",
                "--authorization-relationship", "I am a responsible author or maintainer",
                "--receipt", str(Path(tmp) / "receipt.json"),
            ], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads((Path(tmp) / "receipt.json").read_text())["status"], "pass")
            with self.assertRaisesRegex(ValueError, "match"):
                guard.require_snapshot(root, "0" * 40)
            (root / "comparator.json").write_text("changed")
            with self.assertRaisesRegex(ValueError, "dirty"):
                guard.require_snapshot(root, commit)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0]])
