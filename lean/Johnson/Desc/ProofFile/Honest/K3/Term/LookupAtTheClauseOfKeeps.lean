-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY PROVER: nothing of a prover's sides is read.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupAtTheClauseOfKeeps.lean: the kind "lookup" (K3): what the
lookups' laws read of the first chain's "keeps" at the kind K3, as ONE sentence on the letter f
(`LookupClauseOfKeepsIs`), and the two laws that stand on it, at the thread of `lettersHead`
(Honest/Thread/FirstHead.lean) with "keeps" by f (`kpBy f`), every other letter a variable. One
definition, three theorems.

  `LookupClauseOfKeepsIs Zp publicData f`   at the kind K3 the clause f is: the lookups' own clause
        `k3KeepsAt`; `formsBehind` (Honest/Thread/FHeadF.lean): behind the step the public tests on the
        open claims on linear forms accept; and, at the pieces 7 and 8, which are the lookups on the
        digits, `readersStayAt` (Honest/Thread/FHeadG.lean): the readers of the forms that stay open
        answer the same behind the step
  `clauseOfKeepsGivesTheLookupClause`       the projection
  `lookupStepPaysTheClauseOfKeeps`          behind a lookup's accepted step the whole clause holds:
        `StepPaysTheWholeKeepsClause` (Honest/K3/Term/LookupBehindAndRidesPast.lean) at all fifty
  `lookupOpenItemsRidePastAtTheClauseOfKeeps`   `RidesPastS` at all fifty

Why one sentence. The value of f in the first thread is a tower of layers that grows; each new layer is
"True" at the kind K3. The laws here are general in f; the file that names the first thread shows the
sentence at its f, in one line.

By what. `formsBehind_of_form` (Honest/Thread/FHeadF.lean); `readersStayBehindTheDigitsStep`
(Honest/K3/Term/LookupReadersStay.lean); at the calls the piece is 2 or 3, at the digits 7 or 8;
`lookupOpenItemsRidePastTheCallsOfALink`, `lookupOpenItemsRidePastTheDigits`.

Hypotheses that remain. The head `P5J.AtMgA`; a Said that gives `SaidOk`; the sentence on f.

Limits. Implications from the thread's relation. Nothing shows that the relation holds at a run. The
full size alone: that limit comes with the head. It stands over Honest/Thread/FHead.lean,
FHeadF.lean and FHeadG.lean.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBehindAndRidesPast
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupReadersStay
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupOpenItemsRidePastTheCalls
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupOpenItemsRidePastTheDigits
import Johnson.Desc.ProofFile.Honest.Thread.FHeadG

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place Strs KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf places_are_k3)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF formsBehind readersStayAt formsBehind_of_form)
open ProofFile.Honest.K3.Law.AtThr

/-- **What the clause of "keeps" is at the kind K3.** A definition, meant as a hypothesis on the letter
f. -/
def LookupClauseOfKeepsIs (Zp : ProofFile.Pub) (publicData : VerifiableInference.Desc.First.PubData)
    (f : KindName → Place → TS → TS → Prop) : Prop :=
  ∀ p s s', f .K3 p s s' ↔
    (k3KeepsAt Zp p s s' ∧ formsBehind publicData p s') ∧
      (p.piece = 7 ∨ p.piece = 8 → readersStayAt publicData p s s')

/-- **The clause gives the lookups' own clause.** -/
theorem clauseOfKeepsGivesTheLookupClause {Zp : ProofFile.Pub}
    {publicData : VerifiableInference.Desc.First.PubData} {f : KindName → Place → TS → TS → Prop}
    (clauseIs : LookupClauseOfKeepsIs Zp publicData f) (p : Place) (t t' : TS)
    (clause : f .K3 p t t') : k3KeepsAt Zp p t t' :=
  ((clauseIs p t t').1 clause).1.1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **Behind a lookup's accepted step the whole clause of "keeps" at the kind K3 holds**, at all fifty
borders. Conditional on the head, the sentence on f, and a Said that gives `SaidOk`. -/
theorem lookupStepPaysTheClauseOfKeeps (clauseIs : LookupClauseOfKeepsIs Zp h.𝔇.pubD f)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat}
    (linkBelow : l < 25) (d : Bool) :
    StepPaysTheWholeKeepsClause
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
      Said (borderOf l d) (k3KeepsAt Zp (IM.k3Place l d)) (f .K3 (IM.k3Place l d)) := by
  intro blk hblk k s m E ds y cols s' hA _ hS hk hForm
  refine (clauseIs _ _ _).2 ⟨⟨hk, ?_⟩, ?_⟩
  · exact formsBehind_of_form h H Q test carryX item n₁ n₂ b₀ Vd Rd _ w (places_are_k3 linkBelow d)
      hForm
  · intro hpiece
    cases d with
    | true =>
      exact readersStayBehindTheDigitsStep h H Q test carryX item n₁ n₂ b₀ Vd Rd _ w Said
        saidGivesWordsBelowThePrime linkBelow hblk hA hS
    | false =>
      exfalso
      have hp : (IM.k3Place l false).piece = 2 ∨ (IM.k3Place l false).piece = 3 := by
        by_cases e : l = 24
        · right
          simp [IM.k3Ix, e]
        · left
          simp [IM.k3Ix, e]
      omega

/-- **`RidesPastS` at all fifty borders.** Conditional on the head, the sentence on f, and a Said that
gives `SaidOk`. -/
theorem lookupOpenItemsRidePastAtTheClauseOfKeeps
    (clauseIs : LookupClauseOfKeepsIs Zp h.𝔇.pubD f)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat}
    (linkBelow : l < 25) (d : Bool) :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
      (borderOf l d) := by
  have lookupClause := clauseOfKeepsGivesTheLookupClause clauseIs
  cases d with
  | false =>
    exact lookupOpenItemsRidePastTheCallsOfALink h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
      linkBelow lookupClause Said
  | true =>
    have pieceIs : (IM.k3Place l true).piece = 7 ∨ (IM.k3Place l true).piece = 8 := by
      by_cases e : l = 24
      · right
        simp [IM.k3Ix, e]
      · left
        simp [IM.k3Ix, e]
    exact lookupOpenItemsRidePastTheDigits h H Q test carryX item n₁ n₂ b₀ Vd Rd f w Said
      saidGivesWordsBelowThePrime linkBelow lookupClause
      (fun _ _ clause => ((clauseIs _ _ _).1 clause).1.2)
      (fun _ _ clause => ((clauseIs _ _ _).1 clause).2 pieceIs)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.clauseOfKeepsGivesTheLookupClause
#print axioms ProofFile.Honest.K3.Term.lookupStepPaysTheClauseOfKeeps
#print axioms ProofFile.Honest.K3.Term.lookupOpenItemsRidePastAtTheClauseOfKeeps
