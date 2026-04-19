# Verification results (auto-populated by CI)


Auto-populated by CI workflows:

- `lean4checker_results.txt` — written by [.github/workflows/lean4checker.yml](../../../.github/workflows/lean4checker.yml) on `workflow_dispatch`. Per-module `leanchecker --fresh` replay over `ZPM.*` + `Verification.*`.
- `print_axioms_results.txt` — written by the same workflow. `#print axioms` over every Solution theorem.
- `comparator_output.txt` — stdout from the `comparator` job in [.gitlab-ci.yml](../../../.gitlab-ci.yml), running on [gitlab.com/Zetetic-Dhruv/zetesis-puremath-verification](https://gitlab.com/Zetetic-Dhruv/zetesis-puremath-verification) under a real Landlock sandbox. Copied from the GitLab job artifact.

Do not edit by hand — these files are overwritten on every CI run.
