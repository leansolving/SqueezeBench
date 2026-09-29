# Continuation runs (second phase)

This folder holds the prompt and the notices of the second phase of the evaluation. In it, agents based on Fable 5.1 (nineteen records) and Opus 5.5 (the lower record for Golomb rulers) continued from the records that the baseline left (`../baseline-prompt.md`).

| file | what it is |
|---|---|
| `prompt.md` | the prompt of one track, the upper record of `Ramsey3`; the prompts of the other tracks differ only in the problem, the direction and the submitter name (`trial claude-opus-5.5` for the Opus 5.5 run) |
| `notice-stop.md` | sent after 80 minutes or at 55% context, whichever came first; the first six runs ended by themselves before this rule was in place |
| `notice-continue.md` | sent when an agent stopped working before its stop notice |
| `notice-sources.md` | the rule on outside sources, sent to the runs in progress when it was introduced and part of the prompt afterwards |

The prompt changed slightly over the runs, and `prompt.md` is its final form. Each agent ran in Claude Code at maximum effort (Opus 5.5 at extra-high effort), isolated in its own copy of the project at the records current at its start. It had the shell, the file tools, web search and the `askgpt` tool, which forwards a question to GPT-6 Astra through its API. Every accepted record was re-verified independently with `lake exe squeeze verify --accepted` before it was merged.
