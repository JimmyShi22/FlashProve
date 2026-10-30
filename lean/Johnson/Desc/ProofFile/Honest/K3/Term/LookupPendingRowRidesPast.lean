-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY PROVER: the prover H is a letter of the thread and is not read: the law is on the verifier's
states in front of and behind a lookup on the digits, at the first chain's letters at the library's
head.

Johnson/Desc/ProofFile/Honest/K3/Term/LookupPendingRowRidesPast.lean: the kind "lookup" (K3): the
item "wo" (the sentence on the pending row that the open link's sub-protocols have left) rides past
each of the 25 lookups on the digits. Theorems; no definition; nothing is evaluated.

What is shown.
  `digitsLeaveWhatIsLeftForThePendingRow`, `headsDigitsLeaveWhatIsLeftForThePendingRow`: on states
    alone: the lookups' two clauses of "keeps" at the digits leave `leftOf`
    (Johnson/Top/H0/Walk/FrameRow.lean) as it was.
  `pendingRowSentenceGoesOn`: at the composed meaning `mgAll Dm Mg`, at every Dm and Mg: where the
    two states are `SameBut` and `leftOf` is one, what "wo" says in front it says behind. The mirror
    of the library's `mgAll_wo_back` (Johnson/Desc/Sound/MgAt/K3RidesDig.lean), without the third
    clause of that law's relation, which its proof does not spend.
  `pendingRowSentenceRidesPastTheDigits`: **`RidesPastAtS` at the item `Item.wo segment`, at every
    segment's number, at the border of the lookup on the digits of every link below 25.**

Hypotheses that remain. `h`: `P5J.AtMgA`. `keepsGivesTheLookupClause`: the letter f at the kind K3
implies `k3KeepsAt`. `linkBelow`: l < 25. Every other letter of the thread is free, and so is
`Said`.

Limits. `RidesPastAtS` is a step law from the invariant `ThrS`: nothing here shows that the
invariant holds at any run; the invariant is not spent. The full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBehindAndRidesPast
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.Sound.MgAt.K3RidesDig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place Strs KindName Wit)
open VerifiableInference.Desc.First (Item Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_wo CellsQ)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (SameBut)
open Johnson.Desc.First.Walk.Law (leftOf rowAt rowBy)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.K3.Law.AtThr

/-! ## 1 On states alone -/

/-- The clause of "keeps" at the digits of a layers' or an attention link leaves what the link's
sub-protocols have left for the pending row. -/
theorem digitsLeaveWhatIsLeftForThePendingRow {shape : OnBytes.Model.Forest.Shape} {claims : Nat}
    {s s' : TS} (kept : K3KeepsDigits shape claims s s') : leftOf s' = leftOf s := by
  obtain ⟨-, tl, F, H, G, -, -, arms, -⟩ := kept
  rcases arms with ⟨a, here, rfl⟩ | ⟨a, here, rfl⟩ | ⟨a, here, -, rfl⟩ <;>
    simp [leftOf, Johnson.Desc.First.Walk.leftLay, VerifiableInference.Desc.First.Close.leftHead,
      here]

/-- The clause of "keeps" at the digits of the head's link leaves it too. -/
theorem headsDigitsLeaveWhatIsLeftForThePendingRow {shape : OnBytes.Model.Forest.Shape}
    {s s' : TS} (kept : K3KeepsHead shape s s') : leftOf s' = leftOf s := by
  obtain ⟨-, tl, F, H, G, a₀, claim, -, -, here, -, rfl, -⟩ := kept
  simp [leftOf, Johnson.Desc.First.Walk.leftLay, VerifiableInference.Desc.First.Close.leftHead,
    here]

/-! ## 2 At the composed meaning -/

section
variable {Xi Pp Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi Pp Tok rows cols nR X) (Mg : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT))

/-- **"wo" GOES ON**: it reads what is left for the pending row, "out", the statement and the book.
-/
theorem pendingRowSentenceGoesOn (segment : Nat) {front behind : Pp × TS}
    (same : SameBut front.2 behind.2) (left : leftOf behind.2 = leftOf front.2) (y y' : Strs)
    (v : Wit (CellsQ rows cols) Tok MsgT) (said : (mgAll Dm Mg).wo segment front y v) :
    (mgAll Dm Mg).wo segment behind y' v := by
  rw [mgAll_wo] at said ⊢
  have sameRow : rowAt Dm.d1.lay (Dm.d1.ncl segment) Dm.d1.lin behind.2 =
      rowAt Dm.d1.lay (Dm.d1.ncl segment) Dm.d1.lin front.2 := by
    unfold rowAt rowBy
    rw [left, same.out, same.st]
  have sameReader : Dm.rw13 behind = Dm.rw13 front := by
    funext w'
    unfold MgData.rw13 VerifiableInference.Desc.K13.Law.rwBook
    rw [same.st, same.book]
  unfold VerifiableInference.Desc.First.FillP1.woAt at said ⊢
  intro row rowIs
  have one := said row (by rw [← sameRow]; exact rowIs)
  rw [← sameReader] at one
  exact one

end

/-! ## 3 At the thread -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

/-- The thread's "keeps" at the border of a lookup on the digits leaves what is left for the pending
row. -/
theorem keepsLeaveWhatIsLeftForThePendingRow
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t') {l : Nat}
    (linkBelow : l < 25) {s s' : TS} (kept : (LK).thread.keeps (borderOf l true) s s') :
    leftOf s' = leftOf s := by
  have clause := keepsGiveTheLookupClauseAtTheBorder h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
    keepsGivesTheLookupClause linkBelow true kept
  by_cases head : l = 24
  · subst head
    obtain ⟨shape, atHead⟩ := lookupClauseAtTheHeadsDigits h clause
    exact headsDigitsLeaveWhatIsLeftForThePendingRow atHead
  · obtain ⟨shape, claims, atLink⟩ := lookupClauseAtTheDigits h (by omega) clause
    exact digitsLeaveWhatIsLeftForThePendingRow atLink

/-- **THE ITEM "wo" RIDES PAST EVERY LOOKUP ON THE DIGITS**, at every segment's number.
Conditional on the head and on the arrow from the letter f at the kind K3. -/
theorem pendingRowSentenceRidesPastTheDigits
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t') {l : Nat}
    (linkBelow : l < 25) (segment : Nat) :
    RidesPastAtS (LK).thread Said (borderOf l true) (Item.wo segment) := by
  intro k s m E s' ps v _ kept said
  have same : SameBut s s' := lookupClauseGivesSameBut h linkBelow true
    (keepsGiveTheLookupClauseAtTheBorder h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
      keepsGivesTheLookupClause linkBelow true kept)
  have left := keepsLeaveWhatIsLeftForThePendingRow h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
    keepsGivesTheLookupClause linkBelow kept
  exact pendingRowSentenceGoesOn
    { h.𝔇 with decT := fun _ _ => some (Q.cells m.st.input), cr1 := carryX } mgBase segment
    (front := ((LK).thread.seat k m s)) (behind := ((LK).thread.seat k m s')) same left
    ((LK).thread.strs E) ((LK).thread.strs (E.add ps)) v said

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.digitsLeaveWhatIsLeftForThePendingRow
#print axioms ProofFile.Honest.K3.Term.headsDigitsLeaveWhatIsLeftForThePendingRow
#print axioms ProofFile.Honest.K3.Term.pendingRowSentenceGoesOn
#print axioms ProofFile.Honest.K3.Term.keepsLeaveWhatIsLeftForThePendingRow
#print axioms ProofFile.Honest.K3.Term.pendingRowSentenceRidesPastTheDigits
