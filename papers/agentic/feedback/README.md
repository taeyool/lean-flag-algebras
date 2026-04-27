# Per-Section Feedback

Write per-section feedback files in this directory.

## File naming convention

Use the lowercase section name with non-alphanumeric characters replaced by `_`.

| Section name | File name |
|---|---|
| Introduction | introduction.md |
| Background: Flag Algebras | background_flag_algebras.md |
| Abstract Formalization | abstract_formalization.md |
| The Reflection Layer | the_reflection_layer.md |
| The Tactic Layer | the_tactic_layer.md |
| Results | results.md |
| Related Work | related_work.md |
| Conclusion | conclusion.md |
| Abstract | abstract.md |

## Example

```markdown
1. The problem statement is too abstract. Show a concrete example before the formal setup.

2. The Contributions paragraph only lists one line for the reflection architecture.
   Please spell out the roles of Sym2Graph and the adequacy theorem.
```

Numbering each item allows RevisionJudge to track whether each point was addressed individually.
