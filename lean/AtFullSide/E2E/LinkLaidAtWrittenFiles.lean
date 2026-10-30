-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/LinkLaidAtWrittenFiles.lean

What this file has. The theorems of E2E/LinkLaidPrivacy.lean and E2E/LinkLaidAllAtOnce.lean ask that
the public files Z are in scope, and two of them that Z has a live description. This file proves all
four at the library's two named sets of public files, VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap, so that no
premise on the public files is left (open_zFull, open_zGap, AtFullSide/E2E/AtWrittenFiles.lean). So
these theorems are not vacuous for want of public files. The first is linkLaidEight_zFull, at homeR
b storedPublicFiles, the input at one fixed digest. With one explicit and two placeholder provers it has index
privacy, error at most 2 ^ -135 (one request, 2 ^ 64 oracle queries), with proofs produced under the
same search limits.

Where this stands (in full: E2E/ZetaAtCaps.lean): the step through hashing is proved, with an error
bound; the link's prover is explicit; the two that carry the first table's proof and the inference
are placeholders.

The index: in the release's use, the model's weights (Terms: E2E/HidingTerms.lean).

Theorems, for Z := storedPublicFiles and for Z := zGap, at `homeR b Z`. None has a premise on the public files.
  `linkLaidEight_zFull`, `linkLaidEight_zGap`: `LinkLaidEight`: the nine clauses of
    E2E/LinkLaidAllAtOnce.lean.
  `linkLaidAtOnce_zFull`, `linkLaidAtOnce_zGap`: `LinkLaidAtOnce`: clauses 1, 2 and 9 of these.
  `linkLaidWithBound_zFull`, `linkLaidWithBound_zGap`: `LinkLaidWithBound`: index privacy with the
    general bound on the error.
  `linkLaidStrings_zFull`, `linkLaidStrings_zGap`: `LinkLaidStrings`: the proofs are produced, for
    any number of copies, except with the probability stated there.

Limits, the weightiest first.
- Each theorem keeps all its own limits, told in the headers of its file; the first of them: two of
  the three provers are placeholders that send fixed messages.
- These theorems are at the parameters with an all-zero digest. Up to the field coinBound, which the
  verifier does not read, these are the verifier's parameters at that digest and one m
  (home_is_reBound, home_is_own, E2E/HomeInputTie.lean). They are not tied to the digest that
  VerifierAndGoals.verify computes from the files, so the limit on the digest stands.
- storedPublicFiles and zGap are terms written in this library. No theorem ties them to any file on a disk.
- The file builds on the side library lean/AtFullSide/.

Tests and notes.
- A theorem at two named values adds only that its premises on Z are met there.
- No statement here uses E2E/HomeInputTie.lean's two equations, and none depends on b.
- Nothing in these statements says that any verifier accepts. For the link's interactive verifier,
  also at these two sets of public files, see AtFullSide/E2E/LinkLaidAccepted.lean.

Terms: E2E/HidingTerms.lean.

This file lies in the side library AtFullSide, which is built with a larger thread stack
(lake build AtFullSide).


-/
import E2E.LinkLaidAllAtOnce
import AtFullSide.E2E.AtWrittenFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.LinkLaid
open VerifierAndGoals (PublicFiles storedPublicFiles zGap)
open AtPublicFiles.AtWritten (open_zFull open_zGap)

variable (b : PublicFiles → ℕ)

/-! ## At storedPublicFiles -/

theorem linkLaidEight_zFull : LinkLaidEight b storedPublicFiles :=
  linkLaidEight b storedPublicFiles open_zFull.1 open_zFull.2

theorem linkLaidAtOnce_zFull : LinkLaidAtOnce b storedPublicFiles :=
  linkLaidAtOnce b storedPublicFiles open_zFull.1 open_zFull.2

theorem linkLaidWithBound_zFull : LinkLaidWithBound b storedPublicFiles :=
  linkLaidWithBound b storedPublicFiles open_zFull.1

theorem linkLaidStrings_zFull : LinkLaidStrings b storedPublicFiles :=
  linkLaidStrings b storedPublicFiles open_zFull.1

/-! ## At zGap -/

theorem linkLaidEight_zGap : LinkLaidEight b zGap :=
  linkLaidEight b zGap open_zGap.1 open_zGap.2

theorem linkLaidAtOnce_zGap : LinkLaidAtOnce b zGap :=
  linkLaidAtOnce b zGap open_zGap.1 open_zGap.2

theorem linkLaidWithBound_zGap : LinkLaidWithBound b zGap :=
  linkLaidWithBound b zGap open_zGap.1

theorem linkLaidStrings_zGap : LinkLaidStrings b zGap :=
  linkLaidStrings b zGap open_zGap.1

end AtPublicFiles.LinkLaid

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.linkLaidEight_zFull
#print axioms AtPublicFiles.LinkLaid.linkLaidAtOnce_zFull
#print axioms AtPublicFiles.LinkLaid.linkLaidWithBound_zFull
#print axioms AtPublicFiles.LinkLaid.linkLaidStrings_zFull
#print axioms AtPublicFiles.LinkLaid.linkLaidEight_zGap
#print axioms AtPublicFiles.LinkLaid.linkLaidAtOnce_zGap
#print axioms AtPublicFiles.LinkLaid.linkLaidWithBound_zGap
#print axioms AtPublicFiles.LinkLaid.linkLaidStrings_zGap
