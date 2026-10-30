-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/LengthsOkWritten.lean: the test `Codes.lengthsOk` (OnBytes/Iop/Ground.lean: every
code's message length is a power of two), which the law on the sub-protocol K13 asks as
`PlanM3.hlen` and the shared chain's law as `hl`: that it accepts at the written codes of the proof
file at the full size; a negative test; and that it accepts at the public part of the IOP as written
in Lean.

Row or tool. Closed facts on a written value, and two laws on the public part. They are examples and
payers for a premise of other laws. No law on a sub-protocol is named.

The test's one argument, its written term and its tie.
  `Z.first.codes`: the written term is `Johnson.G.codesFull2` (Johnson/G/PackLit.lean). The tie is
    `first_in_scope` (Johnson/Goal/Numbers/KeyInScope.lean) with `codes_written`
    (Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean): both through Lean.

What is here.
  `lengthsOk_written`: the test accepts at `codesFull2`, which has 17 codes for main rows and 14 for
    mask rows: so it does not accept for want of a code.
  `codesBaseTurned`, `codesMaskTurned`, `lengthsOk_rejects`: the negative test: with 1 added to the
    message length of the first code for main rows, and likewise of the last code for mask rows, the
    test rejects. One for each of its two clauses.
  `lengthsOk_in_scope`: in scope, where the public part Z is made and the test on the first chain's
    parameters accepts: the test accepts at `Z.first.codes`. By rewriting through the tie; nothing
    is evaluated.
  `lengthsOk_of_pub`: the same with no scope and no further test: `ProofFile.pubBy`
    (Johnson/Desc/ProofFile/Pub.lean) itself refuses unless `first.codes.lengthsOk`. So wherever a
    public part is made at all, at every function for the planner's output and every way to the
    first state, the test accepts there.
By evaluations in Lean's kernel (`decide +kernel`): `lengthsOk_written`, `lengthsOk_rejects`.

Limits. Nothing on any other test. Nothing says that a public part is made at any files. Nothing on
soundness.


-/
import Johnson.Goal.Numbers.KeyInScope
import Johnson.G.DataEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes Johnson.G Johnson.G.OfPlan
open VerifiableInference.PlanWritten (first_in_scope codes_written firstPinnedAt)

/-- **The test accepts at the written codes**, of which there are 17 and 14. -/
theorem lengthsOk_written :
    codesFull2.lengthsOk = true ∧ codesFull2.base.size = 17 ∧ codesFull2.mask.size = 14 := by
  decide +kernel

/-- The written codes with 1 added to the message length of the first code for main rows. -/
def codesBaseTurned : Codes :=
  { codesFull2 with base := codesFull2.base.modify 0 fun x => { x with ell := x.ell + 1 } }

/-- The written codes with 1 added to the message length of the last code for mask rows. -/
def codesMaskTurned : Codes :=
  { codesFull2 with mask := codesFull2.mask.modify 13 fun x => { x with ell := x.ell + 1 } }

/-- **The negative test**: it rejects at each. -/
theorem lengthsOk_rejects :
    codesBaseTurned.lengthsOk = false ∧ codesMaskTurned.lengthsOk = false := by decide +kernel

/-- **In scope it accepts at the public part's codes.** -/
theorem lengthsOk_in_scope {o : _root_.ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : _root_.ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : _root_.ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : firstPinnedAt Z.p.X.P Z.first = true) : Z.first.codes.lengthsOk = true := by
  rw [(first_in_scope hW h hy).1, codes_written]
  exact lengthsOk_written.1

/-- **Wherever a public part is made, it accepts there**: the maker refuses otherwise. -/
theorem lengthsOk_of_pub
    {made : ByteArray → ByteArray → ByteArray → Except String Made} {st : _root_.ProofFile.Starts}
    {pol lay KL : ByteArray} {Z : _root_.ProofFile.Pub}
    (h : _root_.ProofFile.pubBy made st pol lay KL = .ok Z) : Z.first.codes.lengthsOk = true := by
  unfold _root_.ProofFile.pubBy at h
  obtain ⟨m, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, h', _⟩ := bind_ok h
    exact absurd h' (throw_ne _ _)
  · rename_i hc
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨D, _, h⟩ := bind_ok h
    obtain ⟨told, _, h⟩ := bind_ok h
    obtain ⟨depth, _, h⟩ := bind_ok h
    obtain ⟨cuts, _, h⟩ := bind_ok h
    obtain ⟨s₀, _, h⟩ := bind_ok h
    obtain rfl := Except.ok.inj h
    show m.p.chains.proof.first.codes.lengthsOk = true
    simpa using hc

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.lengthsOk_written
#print axioms VerifiableInference.Desc.K13.Law.lengthsOk_rejects
#print axioms VerifiableInference.Desc.K13.Law.lengthsOk_in_scope
#print axioms VerifiableInference.Desc.K13.Law.lengthsOk_of_pub
