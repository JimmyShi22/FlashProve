-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/TableOne.lean: IN THE GOALS' SCOPE, WHERE THE PROOF FILE's TEST ON WHAT THE
PLANNER MADE ACCEPTS (madePinnedAt): THE CODE SWITCH's TYPED TABLE (K2Caller.tableOf) HAS ONE VALUE,
WHEREVER IT RETURNS. No evaluation. A law file; no running text imports it.

Why. The sentence «tableOf Zp.pol lay Zp.KL = .ok tableFullLit» is a named test on the three public
files (tableWrittenB, Johnson/Top/H0/K2Caller/TableWritten.lean) that no test of the sealed verifier
asks. tableOf reads the files anew, by the library's planner and by the rows of the sendings. With
this file the sentence is asked ONCE, at one closed set of files, not at every set in scope.

  tableFrom_sub       of the sub-proofs the table reads the open rows alone.
  table_one_in_scope  two sets of files W, W' in scope, each with its public part made and its
                      test accepting: tableOf W… = .ok t · tableOf W'… = .ok t' ⟹ t = t'.
  table_written_of_one   so: where at ONE such set W₀ the table is the written one, it is the
                      written one at every such W at which it returns.
  table_written_of_stored   the same at W₀ := the stored full-size set (VerifierAndGoals.storedPublicFiles): its four
                      facts (in scope · the public part is made · the test accepts · the table is
                      the written one) are CLOSED sentences, and stay NAMED PREMISES here.
BY: TableFrom.lean's tableOf_iff · made_tie (the two planners' sizes are one,
Johnson/Desc/First/Link/Law/RowsOfMade.lean) and rows_one_in_scope
(Johnson/LPFE1R/RowsOneInScope.lean) · made_in_scope
(Johnson/Goal/Numbers/MadeInScope.lean).
NOT SAID: that tableOf returns at any set of files · any of the four closed sentences: Lean's
kernel does not reduce the rows of the sendings at the full size; they have been evaluated.
Limits. The full size alone. Nothing on soundness.

-/
import Johnson.Top.H0.Opts.TableFrom
import Johnson.LPFE1R.RowsOneInScope
import Johnson.Top.H0.K2Caller.LitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params OnBytes.Plan
open Johnson.G.MadeFree (Free)
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.PlanWritten.Joined (writtenMade made_in_scope)
open VerifiableInference.Desc.LinkJoin (made_tie rows_one_in_scope)

theorem tableFrom_sub (z : ProofSized) {sub sub' : Subproofs} (h : sub.openRows = sub'.openRows)
    (R : List Johnson.G.SendRow) : tableFrom z sub R = tableFrom z sub' R := by
  unfold tableFrom framesOf
  rw [h]

/-- Under the test the library's planner's sizes are the written ones. -/
theorem older_sized_written {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {p : OnBytes.Model.Verify.Planned}
    (hp : OnBytes.Model.Verify.planned W.pol W.KL (some W.lay) = .ok p) :
    p.chains.made.sized = writtenMade.sized :=
  (made_tie h hp).2.1.trans (congrArg Free.sized (made_in_scope hW
    (show ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z from h) hy))

/-- **One typed table over the scope, under the test.** -/
theorem table_one_in_scope {W W' : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true)
    (hW' : VerifierAndGoals.InScope W' = true) {Z Z' : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (h' : ProofFile.pubPlain OnBytes.secondHashFunction W'.pol W'.lay W'.KL = .ok Z')
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hy' : madePinnedAt Z'.p.X.P Z'.p.chains.made Z'.first Z'.made = true)
    {t t' : List SwRow} (ht : tableOf W.pol W.lay W.KL = .ok t)
    (ht' : tableOf W'.pol W'.lay W'.KL = .ok t') : t = t' := by
  obtain ⟨p, R, hp, hR, rfl⟩ := tableOf_iff.1 ht
  obtain ⟨p', R', hp', hR', rfl⟩ := tableOf_iff.1 ht'
  have e : p.chains.made.sized.proof = p'.chains.made.sized.proof := by
    rw [older_sized_written hW h hy hp, older_sized_written hW' h' hy' hp']
  rw [rows_one_in_scope hW hW' h h' hy hy' hR hR', e]
  exact tableFrom_sub _ rfl _

/-- **Asked once.** -/
theorem table_written_of_one {W₀ : VerifierAndGoals.PublicFiles} (hW₀ : VerifierAndGoals.InScope W₀ = true) {Z₀ : ProofFile.Pub}
    (h₀ : ProofFile.pubPlain OnBytes.secondHashFunction W₀.pol W₀.lay W₀.KL = .ok Z₀)
    (hy₀ : madePinnedAt Z₀.p.X.P Z₀.p.chains.made Z₀.first Z₀.made = true)
    (hT : tableOf W₀.pol W₀.lay W₀.KL = .ok tableFullLit)
    {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {t : List SwRow} (ht : tableOf W.pol W.lay W.KL = .ok t) : t = tableFullLit :=
  table_one_in_scope hW hW₀ h h₀ hy hy₀ ht hT

/-- The same, at the stored full-size set. -/
theorem table_written_of_stored (hW₀ : VerifierAndGoals.InScope VerifierAndGoals.storedPublicFiles = true) {Z₀ : ProofFile.Pub}
    (h₀ : ProofFile.pubPlain OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = .ok Z₀)
    (hy₀ : madePinnedAt Z₀.p.X.P Z₀.p.chains.made Z₀.first Z₀.made = true)
    (hT : tableOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = .ok tableFullLit)
    {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true) {Z : ProofFile.Pub}
    (h : ProofFile.pubPlain OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {t : List SwRow} (ht : tableOf W.pol W.lay W.KL = .ok t) : t = tableFullLit :=
  table_written_of_one hW₀ h₀ hy₀ hT hW h hy ht

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.table_one_in_scope
#print axioms VerifiableInference.Desc.First.K2Caller.table_written_of_stored
