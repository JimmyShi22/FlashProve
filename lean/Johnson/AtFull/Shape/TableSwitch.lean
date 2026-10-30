-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TableSwitch.lean: THE TABLE MEETS THE FRAMES: THE CODE SWITCH AT ALL ITS 25
PLACES, AND THE PROXIMITY TEST. Under the head P5J.AtMgA. Nothing is evaluated.

  `tab_switch_att` (k < 12: at 14 (2 k + 1) + 2), `tab_switch_lay` (1 ≤ k < 12: at 14 (2 k) + 2):
    Both (TableFrames.lean): over switch_att_both and switch_lay_both (SwitchReturns.lean). The
    cell's step has a guard on the shape in front (linkGd: no mark; linkB; linkP); its test on
    values is switchW (the pairs at written-out variables are (1, 1)).
  `tab_switch_head` (339), `tab_finish` (353): Both: over switch_head_both and switch_finish_both
    (SwitchEndsBoth.lean). Guards: headGd, finGd. Tests on values: headW (the pairs; what the quiet
    step behind the switch asks of the state itself); switchW.
  `tab_test` (354): Both: "carries" over test_frame (TestFrame.lean) through carries_behind_guard
    (FrameNarrow.lean); "returns" over test_returns_guarded (TestReturnsFrame.lean). The cell's
    step has the guard testGuardB in front; its test on values is testV.

Limits. As the frames': two premises of the rule for acceptance. THAT A GUARD OR A TEST ACCEPTS AT
ANY STATE IS NOT SHOWN: where a guard refuses, the step refuses, and both premises say nothing. At
354 all the algebra of the proximity test lies in testV. "Returns" at 354 rests on the guard and on
testV alone; testV is true where the entering of the chain's end refuses. That the head has a member
is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TableSites

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)
open ProofFile.Honest (Carries Returns)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

theorem tab_switch_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (k : Nat)
    (hk : k < 12) : Both cF Zp Bs.G₀ (14 * (2 * k + 1) + 2) := fun ft => by
  obtain ⟨B', P, n, HP, Y, p, e1, e2, e3, e4, e5, e6, hf⟩ :=
    switch_att_both h (2 * k + 1) (by omega) (by omega) (sub_odd k)
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * k + 1) + 2) = Tab.switch Zp Bs.G₀ (2 * k + 1) := by
    rw [cells_link Zp Bs.G₀ (2 * k + 1) 1 (by omega) (by omega) rfl]
    show (if (2 * k + 1 == 0) = true then Tab.opening Zp Bs.G₀
      else Tab.switch Zp Bs.G₀ (2 * k + 1)) = _
    rw [if_neg (by simp)]
  unfold Tab.switch at hc
  rw [e2] at hc
  simp only [Option.bind_some, e3, e4, e5, e6,
    show ((2 * k + 1) % 2 == 1) = true from beq_iff_eq.2 (by omega), if_true] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]

theorem tab_switch_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (k : Nat)
    (h1 : 1 ≤ k) (hk : k < 12) : Both cF Zp Bs.G₀ (14 * (2 * k) + 2) := fun ft => by
  obtain ⟨B', P, n, HP, Y, hp, e1, e2, e3, e4, e5, e6, hf⟩ :=
    switch_lay_both h (2 * k) (by omega) (by omega) (sub_even k hk)
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * k) + 2) = Tab.switch Zp Bs.G₀ (2 * k) := by
    rw [cells_link Zp Bs.G₀ (2 * k) 1 (by omega) (by omega) rfl]
    show (if (2 * k == 0) = true then Tab.opening Zp Bs.G₀ else Tab.switch Zp Bs.G₀ (2 * k)) = _
    rw [if_neg (by simp; omega)]
  unfold Tab.switch at hc
  rw [e2] at hc
  simp only [Option.bind_some, e3, e4, e5, e6,
    show ((2 * k) % 2 == 1) = false from beq_eq_false_iff_ne.2 (by omega), Bool.false_eq_true,
    if_false] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]

theorem tab_switch_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Both cF Zp Bs.G₀ 339 := fun ft => by
  obtain ⟨B', P, n, HP, e1, e2, e3, e4, hf⟩ := switch_head_both h
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ 339 = Tab.switchHead Zp Bs.G₀ :=
    cells_head Zp Bs.G₀ 2 (by omega) rfl
  unfold Tab.switchHead at hc
  rw [e2] at hc
  simp only [Option.bind_some, e3, e4] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]

theorem tab_finish (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Both cF Zp Bs.G₀ 353 := fun ft => by
  obtain ⟨B', P, n, e1, e2, e3, hf⟩ := switch_finish_both h
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ 353 = Tab.finish Zp Bs.G₀ := cells_back Zp Bs.G₀ 0 rfl
  unfold Tab.finish at hc
  rw [e2] at hc
  simp only [Option.bind_some, e3] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]

theorem tab_test (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 354 := fun ft => by
  have hc : Tab.cells Zp G 354 = (Tab.backRow Zp G).at 1 := cells_back Zp G 1 rfl
  refine ⟨?_, test_returns_guarded h ft _ _ (testA (H2U.p12OfMade Zp.made)) (cell_g hc) ?_⟩
  · exact carries_behind_guard (G' := fun _ => optE (testA (H2U.p12OfMade Zp.made)))
      (vals' := Tab.vals Zp G) (fun y => testGuardB (H2U.p12OfMade Zp.made) y.1)
      (testA (H2U.p12OfMade Zp.made)) (cell_g hc) rfl (test_frame h ft _ _ rfl)
  · funext s rs gs
    rw [cell_v hc]
    rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.tab_switch_att
#print axioms Johnson.AtFull.Shape.tab_switch_lay
#print axioms Johnson.AtFull.Shape.tab_switch_head
#print axioms Johnson.AtFull.Shape.tab_finish
#print axioms Johnson.AtFull.Shape.tab_test
