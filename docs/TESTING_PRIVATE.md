# Testing submissions while the repository is private

> **Temporary.** This file is for maintainers. Delete it when the repository becomes public,
> and move *As the maintainer* to [`PIPELINE.md`](PIPELINE.md).

[`CONTRIBUTING.md`](CONTRIBUTING.md) describes a submission from a fork.
Forking is disabled while the repository is private, so a test submission comes from a branch
of this repository rather than from a fork. Everything else is as in
`CONTRIBUTING.md`, *Submitting, step by step*, including the placeholders.

## As the submitter

```sh
git clone https://github.com/leansolving/SqueezeBench.git
cd SqueezeBench
lake exe cache get
lake build
lake exe squeeze bootstrap

git checkout -b <branch> origin/main
lake exe squeeze new <Problem> <lower|upper>
# edit Def.lean, Proof.lean, REPORT.md and metadata.toml
lake build SqueezeBench.Problems.<Problem>.Records.<Direction>.V<k>.Proof

git add SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k>
git commit -m "<Problem> <Direction> V<k>"
lake exe squeeze verify SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k> --base origin/main

git push -u origin <branch>
gh pr create --base main
```

Test with the `Tutorial` problem: it exists to exercise the pipeline and is not on the
leaderboard.

## As the maintainer

1. On GitHub, open *Files changed*. The pull request must only add files inside one record
   directory. Check this before you run anything, since building a pull request runs its code.
2. Verify from a fresh clone, so that the record has not been compiled before:

   ```sh
   git clone https://github.com/leansolving/SqueezeBench.git squeezebench-review
   cd squeezebench-review
   gh pr checkout <number>
   lake exe cache get
   lake build
   lake exe squeeze bootstrap
   lake exe squeeze verify SqueezeBench/Problems/<Problem>/Records/<Direction>/V<k> --base origin/main
   ```

3. Read `REPORT.md`, then merge:

   ```sh
   gh pr merge <number> --squash --delete-branch
   ```

4. Open the next Challenge and commit it:

   ```sh
   git checkout main
   git pull
   lake exe squeeze accept <Problem> <lower|upper>
   git add -A
   git commit -m "Accept <Problem> <Direction> V<k>"
   git push
   ```

Also test submissions that must fail: one that changes a file outside its record directory,
and one copied from a fixture under `Fixtures/` that is expected to be rejected.
