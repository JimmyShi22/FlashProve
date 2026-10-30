-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchSwitchPub.lean: the closing of a segment (K10): under the head, at a place p of the code
switch out of the written list, of link l: the number fx at which the laws on the first chain's script speak of the switch
(the rounds in front of the switch's border), and three things that the records `TieBySwitch` and `FreshBySwitch`
(Pay/XchTieBySwitch.lean, Pay/XchFreshField.lean) ask of it and of the switch's codes.

  `borderTest`, `border_written`   by Lean's kernel, at links 1 to 24: the switch's place stands in the written list of places in
                    front of the closing's border 14 l + nAt l + 5; the switch's codes are the written codes
  `fxAt`              the number: 0 + the rounds of the blocks in front of the switch's border
  **`fx_heard`**        at a stand in front of the closing, of a thread over the head's blocks in front of which no round was heard:
                    no fewer challenges have been heard than fxAt
  **`fx_gam`**          the folds' challenges of the segments in front of l have numbers below fxAt: the field gam
  **`switch_codes_at`**   at a reached state that has not failed, the statement's codes are the switch's

By: `step_heard_le` (Pay/XchStand.lean); `gam_written` (Pay/XchPublic.lean); `declared_in_front` (Pay/MadeStand.lean);
`borderNo_written` (Honest/K1/Law/MembersByBorder.lean); `facts_reached` (Pay/AtReach.lean); `AtMg.codes_full`
(Johnson/P5J/CodesFullAtMg.lean).

Limits. The head is a premise. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchPublic
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchStand
import Johnson.Desc.ProofFile.Honest.K1.Law.MembersByBorder
import Johnson.P5J.CodesFullAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K2 (SegmentPub SwitchPlace)
open ProofFile.Honest.K2.Law (segsW placesW)

/-- The test at link l. -/
def borderTest (l : Nat) : Bool :=
  match placesW.find? (·.link == l) with
  | some p => decide (P5J.At.ps.findIdx (· == p.place) ≤ 14 * l + IM.nAt l + 5) &&
      decide (p.sizes.codes = Johnson.G.codesFull2)
  | none => false

set_option maxRecDepth 1000000 in
theorem border_written : ((List.range 24).all fun i => borderTest (i + 1)) = true := by decide +kernel

/-- What it says at one link. -/
theorem border_at {l : Nat} (h1 : 1 ≤ l) (h2 : l < 25) {p : SwitchPlace} (hp : placesW.find? (·.link == l) = some p) :
    P5J.At.ps.findIdx (· == p.place) ≤ 14 * l + IM.nAt l + 5 ∧ p.sizes.codes = Johnson.G.codesFull2 := by
  have h := List.all_eq_true.1 border_written (l - 1) (List.mem_range.2 (by omega))
  have e : l - 1 + 1 = l := by omega
  rw [e] at h
  unfold borderTest at h
  rw [hp] at h
  obtain ⟨a1, a2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact ⟨of_decide_eq_true a1, of_decide_eq_true a2⟩

/-- The rounds in front of the switch's border, in the form in which the laws on the script have the number. -/
def fxAt (cF : Chain TS ProofFile.Cl) (p : SwitchPlace) : Nat := 0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a stand in front of the closing no fewer challenges have been heard.** -/
theorem fx_heard (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (h1 : 1 ≤ l) (h2 : l < 25) {p : SwitchPlace}
    (hp : placesW.find? (·.link == l) = some p) {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk TS ProofFile.Cl V W X Pb}
    (ha : T.ahead = []) (hbs : T.bs = cF.blocksInOrder) {Said : Nat → Coins Bk → Mid W X → Prop} {blk : Block TS ProofFile.Cl}
    {k : Coins Bk} {s : TS} {m : Mid W X} {En : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    {s' : TS} (St : StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s') :
    fxAt cF p ≤ m.st.heard.length := by
  have hb : borderNo cF.blocksInOrder p.place ≤ 14 * l + IM.nAt l + 5 := by
    rw [K1.borderNo_written h]
    exact (border_at h1 h2 hp).1
  have e := step_heard_le ha St hb
  rw [hbs] at e
  exact e

/-- **The folds' challenges of the segments in front have numbers below it.** -/
theorem fx_gam (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (h1 : 1 ≤ l) (h2 : l < 25) {p : SwitchPlace}
    (hp : placesW.find? (·.link == l) = some p) : ∀ S ∈ segsW.take l, ∀ i ∈ S.gamma, i < fxAt cF p := by
  intro S hS i hi
  have hg := List.all_eq_true.1 gam_written (l - 1) (List.mem_range.2 (by omega))
  have e : l - 1 + 1 = l := by omega
  rw [e] at hg
  unfold gamTest at hg
  rw [hp] at hg
  have h3 := of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 hg S hS) i hi)
  unfold fxAt roundsTo
  rw [Nat.zero_add, (declared_in_front h _).2, K1.borderNo_written h]
  exact h3

/-- **At a reached state that has not failed, the statement's codes are the switch's.** -/
theorem switch_codes_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (h1 : 1 ≤ l) (h2 : l < 25)
    {p : SwitchPlace} (hp : placesW.find? (·.link == l) = some p) {b : Nat} {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) (hf : s.failed = none) : s.st.codes = p.sizes.codes := by
  rw [(facts_reached h hr hf).2.1, P5J.AtMg.codes_full h.toAtMg, (border_at h1 h2 hp).2]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.border_written
#print axioms ProofFile.Honest.K10.border_at
#print axioms ProofFile.Honest.K10.fxAt
#print axioms ProofFile.Honest.K10.fx_heard
#print axioms ProofFile.Honest.K10.fx_gam
#print axioms ProofFile.Honest.K10.switch_codes_at
