# Reproducing the verification

## Requirements

Use the exact Lean release in lean-toolchain, installed through elan, and Git.
Lake reads lake-manifest.json to fetch the exact dependencies. Mathlib's binary
cache avoids rebuilding its entire library. The source-bound native checker
also uses Python 3 and lean-pkg; use the producer version recorded in the
committed receipts. Installing software is separate from verifying a proof.

## Transparent local route

After cloning this repository and entering it, retrieve the pinned cache:

```sh
lake exe cache get
```

Then run the committed checker with a fresh output path outside the source tree:

```sh
bash verify.sh ../verification.log
```

It rebuilds the proof and axiom-report modules, checks the shared Challenge
definition guard, imports the built environment, and audits every
claim declaration. Expected terminal markers include claim-axioms-done: 216,
sorry-count: 0, and only Classical.choice, Quot.sound and propext. Check the exit
code as well as those lines. A successful development build alone is not a
source-bound receipt. On Linux, use capped systemd units for long local builds.

## Receipt-backed route

lean-pkg verify runs schema preflight, the independent comparator, the official
systemd native receipt producer and the registry gate at one committed source.
Use its dry run first and the documented host policy for the installed version.
The lower-level command contracts are shown in verify.sh and lean-pkg help.
Keep failed runs and corrected successors separate. Never edit or rebind a
receipt to a changed source.

The Comparator configuration is comparator/config-chen-dalang-2015.json, with
Challenge and Solution as its statement/proof modules and 16 selected targets.
The native audit covers all 216 listed declarations. These counts describe
different checks, not a percentage of the full paper.

## Palomar preflight

Palomar additionally requires its own complete pinned reusable workflow for the
exact public repository and commit. Local build/Comparator receipts are not a
substitute for that workflow, editorial review or registration. No Palomar
registration is claimed until its immutable entry is available.

## Common failures

A missing lake/lean executable usually means elan's bin directory is absent from
PATH. A wrong dependency revision is not repaired by borrowing an unrelated
olean: restore the manifest's exact pins. A missing Mathlib cache can turn a
short source replay into a much longer library build. An active process is not
a completed pass. Read actual final exit status and source-bound artifacts.

## Meaning of a pass

The checks certify the exact Lean statements at their recorded source and
dependency revisions. They do not prove novelty, certify every result of the
paper, turn L2 continuity into sample-path continuity, or replace the author's
responsibility for the statement-to-paper correspondence.


## Audit escape control

The exact Core-Lean audit executable extracted from the committed verify.sh
was exercised on two separately compiled fixtures. A theorem of True proved
by True.intro was accepted. A theorem of True proved by a named custom axiom
was detected as depending on GuardBad.forbidden and rejected by the installed
axiom policy. Both fixture compilations and both environment probes exited
successfully; rejection occurred at the intended forbidden-axiom policy, not
an import or syntax failure.

The separate positive and negative logs and documentary result are retained
under .lean-receipts/controls/. That result is explicitly not a source-bound
receipt and is not mixed into the accepted 216-claim audit transcript. It tests
the audit executable, not another mathematical result of the paper.
