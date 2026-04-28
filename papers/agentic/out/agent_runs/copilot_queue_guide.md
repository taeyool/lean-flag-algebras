# Copilot Queue Guide

Mode: revision

1. For each section directory, run planner_task.md in Copilot chat and save JSON to planner_output.json.
2. Run retriever_task.md and save JSON to retriever_output.json.
3. Run writer_task.md and save text to writer_output.md.
4. Run verifier_task.md and save text to verifier_output.md.
5. (revision mode only) Run revision_judge_task.md and save JSON to revision_judge_output.json.
   If retry_required=true, rerun writer/verifier targeting unaddressed points, then re-run judge.
6. Apply verifier_output.md to the target section in draft using apply_task.md.

Draft target: papers/agentic/out/paper_draft_from_contributions.tex
