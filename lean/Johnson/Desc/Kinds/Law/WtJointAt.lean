-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WtJointAt.lean (WaK6's fourth clause is the weaker KeptWFo: the
ledger later in the lookups' sense alone): THE JOINING LEMMA ON THE CLAIM ON THE WEIGHTS, WHOLE, IN
THE
FORM THAT THE MERGE'S FOURTH TIE SPENDS: at the state in front of the merge: WaK6 → wtP1 → wtK6:
from the merge's files' sentence (Johnson/Top/H0/Fill/FillP1.lean: wtP1) to the sentence that
stands in the composed meaning's parameter wt (Law/WtK6.lean: wtK6: WeightAt under the guard on the
witness).

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  WaK6 W V' sF: WHAT IS ASKED OF THE STATE IN FRONT OF THE MERGE: there are an accepting step s to
      s' of the sub-protocol at the output head (its ledger well laid in front; canonical rounds),
      covered positions cov and tables t with: sF goes on from s' as far as WeightAt reads (
          KeptWFo: Law/WeightAtFo.lean) · cov is what sF's own routine makes · the claim that
          lies at sF is what the
      quiet step's text returns at what was heard, cov and t · the two ties of the top digit's key
          against the layout's segment (LeftTies), AT WHAT LIES HEARD AT sF, at the call number and
          the segment that the layout gives for the name "HD0".
  wtK6_of_wtP1: THE LEMMA.

How. Law/WtJoint.lean's weightAt_of_wtP1 gives WeightAt at s'; weightAt_keptFo
(Law/WeightAtFo.lean) carries it to sF; weightSlot_filled (Law/WeightAtSame.lean) and
hidden_keptFo give that the hidden
value under the one slot is the same at both ledgers.
Every letter under "there is", and what pins it. In WaK6: s, s', rv, gs: NOT PINNED by sF: any
accepting step from which sF goes on serves · cov: by sF's own routine · t: not pinned here (the
quiet step reads it off sF's own part).
PREMISES BESIDE WaK6, ALL ON PARAMETERS: the tests on the plan accept · W.T = W.hS.T · rows ≤ hRef ·
cols ≤ 2 ^ kRef · the merge's layout is the public parameters' · the reference layout · lamS = 13 ·
V = 202048 · d = 5120 · hcellOf: the merge's reader of a cell gives the witness's cell, 0 outside ·
hmaskOf: AT EVERY STATE WITH WaK6, at every witness, compCut's mask row is the merge's maskOf
below the merge's number of slots (asked at every state it would be false: the merge's files' reader
maskRowAt gives 0 where no segment's part is open): NOT PAID: it wants, of the state, the open
segment's part and the mask row's seat in it: an eighth clause for WaK6 when its payer is typed.
What it does not say. THAT WaK6 HOLDS AT A REACHED STATE: four facts along the fold, shown by
nobody. LeftTies: open since Law/WeightTwinAt.lean. THE REFERENCE SIZES ALONE. No
example. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.WtJoint
import Johnson.Desc.Kinds.Law.WeightAtFo
import Johnson.Desc.Kinds.Law.WtK6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes (E zeroE)
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout)
open OnBytes.Model (Fork)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.Head (nV nD)
open VerifiableInference.OnPublicFiles.Flat (GE InRange Holds)
open VerifiableInference.Desc.First (S HeadOwn Numbers)
open VerifiableInference.Desc.First.K11Caller (ewAt)
open VerifiableInference.Desc.First.FillP1 (wtP1)
open VerifiableInference.Desc.Sound (Mem MsgT)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- **What is asked of the state in front of the merge.** -/
def WaK6 (W : OnBytes.Model.Verify.Public) (V' : Nat) (sF : S) : Prop :=
  ∃ (s s' : S) (rv : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (cov : OnBytes.Model.Head.Covered) (t : OnBytes.Model.Head.Tables),
    (blockAt W.hS (readsOf W) (workOf W) 24).decide s rv gs = .ok s' ∧
    WellLaid ((seatAt W.hS (readsOf W)).ledger s) ∧ Canonical rv ∧ KeptWFo s' sF ∧
    sF.covered W.T V' = .ok cov ∧
    (∀ o' x claim, sF.here = .head o' → o'.x = some x → o'.claim = some claim →
      First.Look.weightsClaim (runAt W cov x t) W.layers.wsLay = .ok claim) ∧
    ∀ (g : Given) o' x q sg,
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g →
      sF.here = .head o' → o'.x = some x → OnBytes.Model.Head.callNo W.HLy "HD0" = some q →
      (W.HLy.calls.getD q default).seg? "HD0" = some sg →
      LeftTies W g cov x t (ewAt (runAt W cov x t) q sg)

/-- **THE JOINING LEMMA.** -/
theorem wtK6_of_wtP1 {rows cols : Nat} {P Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
    (msR : List Mem) (N : Numbers) (W : OnBytes.Model.Verify.Public) (lay6 : ReqLayout)
    (num : ℕ → ℕ → ℕ) (n rb : ℕ) (hplan : (parOf W.hS (workOf W)).ok = true)
    (hTT : W.T = W.hS.T) (V' : Nat) (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef)
    (Pm : HeadMergeP) (hlay : Pm.lay = W.layers.wsLay) (ni : ℕ)
    (cellOf : Wit (Fin rows → Fin cols → GE) Tok MsgT → ℕ → ℕ → K)
    (maskOf : P × S → Wit (Fin rows → Fin cols → GE) Tok MsgT → ℕ → K)
    (hcellOf : ∀ w r c, cellOf w r c =
      if h : r < rows ∧ c < cols then w.cells ⟨r, h.1⟩ ⟨c, h.2⟩ else 0)
    (hmaskOf : ∀ (a : P × S) w, WaK6 W V' a.2 → ∀ j, j < Pm.nMsg →
      rd ((compCut cs arr msR N (Meaning.sizesOf W) (seatLay W lay6 num) W (plAt n rb) w).2 j) =
        maskOf a w j)
    {sh : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW sh ppref)
    (hl : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (hlam : W.H.lamS = 13)
    (hV2 : W.hS.V = 202048) (hd5 : W.hS.d = 5120) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hWa : WaK6 W V' a.2)
    (hw : wtP1 Pm ni cellOf maskOf a y w) :
    wtK6 cs arr msR N W lay6 num n rb 24 a y w := by
  intro _ hR
  obtain ⟨i, hi⟩ := hR
  have hmk := hmaskOf a w hWa
  obtain ⟨s, s', rv, gs, cov, t, hd, hWL, hcan, hK, hcov, hclaim, hLT⟩ := hWa
  have hst : SameHeard s' a.2 := by
    obtain ⟨o, o', ho, ho', e1, _, e3, e4, e5, e6, _⟩ := hK
    refine ⟨e6, e5, fun o1 h1 => ?_⟩
    rw [ho] at h1
    obtain rfl := First.Here.head.inj h1
    exact ⟨o', ho', e3, e1, e4⟩
  have hcell : ∀ r c, cellOf w r c = ((i.mat r c : Int) : K) := by
    intro r c
    rw [hcellOf]
    by_cases h : r < rows ∧ c < cols
    · rw [dif_pos h]
      exact hi.1 ⟨r, h.1⟩ ⟨c, h.2⟩
    · rw [dif_neg h, hi.2 r c h]
      simp
  obtain ⟨g, H, F1, a0, gk, o', claim, p1, p2, p3, p4, p5, p6, p7, p8, J⟩ :=
    Came.weightAt_of_wtP1 W 24 hd hWL hcan hplan hst hTT hcov hr hc hi Pm hlay ni cellOf maskOf a.1
      y w hw hcell
  obtain ⟨q, sg, hq, hsg, J2⟩ := J t Z hl hlam (hclaim o' _ claim p5 p6 p7)
  obtain ⟨g2, H2, F2, a2, gk2, Q, b1, b2, b3, b4, b5, _, b7, b8, _, b10⟩ :=
    Came.behind_all W 24 hd hWL hcan
  obtain rfl : g = g2 := Except.ok.inj (p1.symm.trans b1)
  have e2 := Option.some.inj (p2.symm.trans b2)
  obtain rfl : H = H2 := congrArg Prod.fst e2
  obtain rfl : F1 = F2 := congrArg (fun p => p.2.1) e2
  rw [p3] at b3
  obtain rfl := First.Here.head.inj b3
  obtain rfl : gk = gk2 := Option.some.inj (p4.symm.trans b4)
  have hsz := Came.runAt_sizes W p1 cov (heardOf gk H) t
  have hV : V = nV := hsz.2.symm.trans hV2
  have hd' : Norm.d = nD := by
    obtain ⟨_, _, _, _, _, rfl⟩ := Came.given_ok _ _ _ _ p1
    exact hd5
  -- the hidden value under the one slot
  have hhid : hidden F1 (compCut cs arr msR N (Meaning.sizesOf W) (seatLay W lay6 num) W
      (plAt n rb) w).2 (heardOf gk H).sV = hidden o'.F (compCut cs arr msR N (Meaning.sizesOf W)
      (seatLay W lay6 num) W (plAt n rb) w).2 (heardOf gk H).sV := by
    obtain ⟨o1, o2, ho1, ho2, _, _, _, _, _, _, hL⟩ := hK
    rw [p5] at ho2
    obtain rfl := First.Here.head.inj ho2
    obtain ⟨x, hx, hv, hf⟩ := weightSlot_filled W.hS (readsOf W) ho1 b7
    have ho1' : o1 = { a0 with F := F1, x := some (heardOf gk H), squaresP := some Q } := by
      rw [b5] at ho1
      exact (First.Here.head.inj ho1).symm
    have eslot : OnBytes.Model.Aff.slot (heardOf gk H).sV =
        OnBytes.Model.Aff.slot (x.tH.sEnd + 1) := b10.symm.trans hv
    have ej : (heardOf gk H).sV = x.tH.sEnd + 1 := by
      have := congrArg (fun f : OnBytes.Model.Aff => (f.slots.getD 0 (0, zeroE)).1) eslot
      exact this
    have eF : o1.F = F1 := by rw [ho1']
    rw [ej, ← eF]
    exact (hidden_keptFo _ hL hf).symm
  have hW' := J2 (hLT g o' _ q sg p1 p5 p6 hq hsg) (compCut cs arr msR N (Meaning.sizesOf W)
      (seatLay W lay6 num) W
    (plAt n rb) w).1.toCells rfl hV hd' (compCut cs arr msR N (Meaning.sizesOf W)
    (seatLay W lay6 num) W (plAt n rb) w).2 hhid hmk
  exact (weightAt_keptFo W hK ⟨H, b7⟩ _ _).mpr hW'

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6_of_wtP1
