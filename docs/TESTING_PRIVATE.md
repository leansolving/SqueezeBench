# Testing submissions while the repository is private

> **Temporary.** This file is for maintainers. When the repository becomes public, remove
> *As the submitter* and keep the rest as the maintainer guide.

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

## Checking the repository

```sh
lake exe squeeze audit                     # re-verify every accepted record; slow
lake exe squeeze audit Golomb upper V000   # or narrow it: a problem, a direction, one version
lake exe squeeze test                      # verify every fixture and check its expected result
```

`audit` judges each record against the Challenge that admitted it. `accept` never edits a
record; it opens the next Challenge and updates the problem README.

The fixtures are in `Fixtures/Tutorial/`:

| fixture | expected |
|---|---|
| `Bob` | accepted |
| `StaleAgainstV001` | rebase: it answers a version already accepted |
| `MacroInDef` | rejected by the `Def.lean` check |
| `TooLarge` | rejected by the size limit |
| `ShadowedF` | rejected by Comparator: a local `f` changes the statement |
| `RecordIsF` | accepted by Comparator, rejected by admissibility |
| `WrongWitness` | rejected by the fuel gate |
| `SearchUnderAnotherName` | rejected by the fuel gate's range check, at `n = 13` |
| `HeartbeatOverride`, `AsyncOverride`, `MetaCommand` | rejected by the computation budget: the file tries to change its limits |
| `SplitSearch` | rejected by the computation budget: every lemma is within its limit, the file is not |
| `BvCheck`, `PlainNativeDecide` | rejected by Comparator's axiom check |

## Maybe in the future: Requiring pull requests

GitHub can refuse every direct push to `main`, so that each change goes through a pull
request. The setting is a branch protection rule, or ruleset, on `main` with *Require a pull
request before merging*, under *Settings → Branches* or *Settings → Rules → Rulesets*.

It is not available yet: GitHub offers it for a private repository only on a paid plan, and
the organization is on the free one. It becomes available when the repository is public.

Until then it is an agreement between the maintainers: nobody pushes to `main` directly,
except for the commit that follows `squeeze accept`.

When the rule is turned on:

- It protects the whole branch, not single directories, so changes to the docs and the tool
  need a pull request too.
- The commit that follows `squeeze accept` needs its own pull request, unless maintainers are
  allowed to bypass the rule, which is an option of the same setting.
- Turn on with it: *Require approvals*, so that a second maintainer approves each pull
  request; *Require branches to be up to date before merging*, so that two pull requests for
  the same version cannot both merge; and *Block force pushes*.
