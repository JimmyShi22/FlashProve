-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WtJoint.lean: FROM THE MERGE'S FILES' SENTENCE ON THE CLAIM ON THE WEIGHTS
(Johnson/Top/H0/Fill/FillP1.lean: wtP1), AT THE STATE IN FRONT OF THE MERGE, TO K6's
(Law/MergeClaimAt.lean: WeightAt), AT THE STATE BEHIND THE SUB-PROTOCOL AT THE OUTPUT HEAD: the
first of two steps of the joining lemma that the merge's fourth tie is to spend.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.Came).
  claimVal_cellsIn: the head's claim's value over the cells within the committed table, where these
      are the casts of an index's digits, is its value over the index's digit matrix (by
      claimVal_head and Hof_Wof).
  rd_atWorld_slot: the hidden value under one slot, read in the field: what was shown there less the
      factor there times the mask row's entry there.
  weightAt_of_wtP1: s, s': the states in front of and behind the sub-protocol at the output head;
      sF: the state in front of the merge. FROM wtP1 AT sF: WeightAt W s' c mask at every c whose
      weights are whOf w.cells.

How. wtP1_plain (Johnson/Top/H0/Fill/WtPlain.lean) unfolds wtP1; weightAt_at_quiet
(Law/WeightJoint.lean) is the rest.
Every letter under "there is": none in the conclusions.
PREMISES THAT NOBODY PAYS HERE, ALL IN THE STATEMENT. On states: the accepting step s to s' with its
ledger well laid and canonical rounds · SameHeard s' sF · the covered positions at sF · hclaim: the
claim that lies at sF is what the quiet step's text returns at what was heard, the covered positions
and the tables t · hhid: the hidden value under the value's slot is the same at the ledger behind
the sub-protocol and at sF's. On parameters: the merge's layout is the public parameters' · the
reference
layout · lamS = 13 · W.T = W.hS.T · V = nV · d = nD · LeftTies (two) · hcell: the merge's reader of
a cell gives the witness's cell, 0 outside · hmask: the merge's and K6's mask rows are one below the
merge's number of slots.
On the witness: its cells hold the index i.
What it does not say. WeightAt AT sF: the second step (that sentence's footprint: other files').
THE REFERENCE SIZES ALONE. No example. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.WeightJoint
import Johnson.Top.H0.Fill.WtPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE okE)
open OnBytes.Model (Reading eqTab Fork)
open OnBytes.Road (eqR claimVal Wm)
open OnBytes.Road.Hd (avOf facKK)
open Norm (lt ls d lPd T S2)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.Head (Hof nV nD)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K11Caller (headClaim cellsIn Wof Hof_Wof head_rows ewAt)
open VerifiableInference.Desc.First.FillP1 (wtP1 wtP1_plain)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

namespace Came

/-- **The head's claim's value over the cells within the committed table.** -/
theorem claimVal_cellsIn {sh : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW sh ppref)
    (P : First.K11Caller.Place) (hl : OnBytes.Model.wsLayOf sh true kRef = .ok P.lay)
    (cell : ℕ → ℕ → K) (i : Cm.Idx) (hcell : ∀ r c, cell r c = ((i.mat r c : Int) : K))
    (AV rs' : Array E) (hs : 13 ≤ rs'.size) :
    claimVal Reading.gl P.lay (cellsIn P cell) (headClaim P.lay AV rs') =
      claimVal Reading.gl P.lay (fun r c' => ((i.mat r c' : Int) : K)) (headClaim P.lay AV rs') :=
          by
  obtain ⟨hm, hk⟩ := head_rows Z hl
  unfold headClaim
  rw [OnBytes.Road.Hd.claimVal_head Reading.gl Z hl _ AV rs' hs,
    OnBytes.Road.Hd.claimVal_head Reading.gl Z hl _ AV rs' hs]
  refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun k hk' => ?_
  unfold cellsIn
  rw [Hof_Wof P _ i.mat (fun rc => hcell _ _) hm hk (Finset.mem_range.mp hk')
    (Finset.mem_range.mp hv)]

/-- The hidden value under one slot. -/
theorem rd_atWorld_hidden (F : Fork) (mask : Nat → E) (j : Nat) :
    rd (atWorld F mask noEnt (OnBytes.Model.Aff.slot j)) = rd (hidden F mask j) := by
  have e : atWorld F mask noEnt (OnBytes.Model.Aff.slot j) =
      (0 : E) + OnBytes.oneE * hidden F mask j := rfl
  have h1 : rd OnBytes.oneE = 1 := OnBytes.Model.Reading.gl.one
  rw [e, rd_add, rd_mul, rd_zero, h1]
  ring

/-- **The hidden value under one slot, read in the field.** -/
theorem rd_atWorld_slot (F : Fork) (mask : Nat → E) (j : Nat) :
    rd (atWorld F mask noEnt (OnBytes.Model.Aff.slot j)) =
      rd (F.vp.getD j 0) - rd (F.mf.getD j 0) * rd (mask j) := by
  have e : atWorld F mask noEnt (OnBytes.Model.Aff.slot j) =
      (0 : E) + OnBytes.oneE * hidden F mask j := rfl
  rw [e, rd_add, rd_mul]
  unfold hidden
  rw [rd_sub, rd_mul, rd_zero]
  have h1 : rd OnBytes.oneE = 1 := OnBytes.Model.Reading.gl.one
  rw [h1]
  ring

/-- **From the merge's sentence at the state in front of the merge to WeightAt behind the
sub-protocol at the output head.** -/
theorem weightAt_of_wtP1 (W : OnBytes.Model.Verify.Public) (l : Nat) {s s' sF : S}
    {rv : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) l).decide s rv gs = .ok s')
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rv)
    (hplan : (parOf W.hS (workOf W)).ok = true) (hst : SameHeard s' sF) (hTT : W.T = W.hS.T)
    {V' : Nat} {cov : OnBytes.Model.Head.Covered} (hcov : sF.covered W.T V' = .ok cov)
    {rows cols : Nat} (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef)
    {M : Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE} {i : Cm.Idx}
    (hH : VerifiableInference.OnPublicFiles.Flat.Holds M i)
    {P Wt : Type} (Pm : HeadMergeP) (hlay : Pm.lay = W.layers.wsLay) (ni : ℕ)
    (cellOf : Wt → ℕ → ℕ → K) (maskOf : P × S → Wt → ℕ → K) (z : P) (y : Strs) (w : Wt)
    (hw : wtP1 Pm ni cellOf maskOf (z, sF) y w)
    (hcell : ∀ r c, cellOf w r c = ((i.mat r c : Int) : K)) :
    ∃ (g : Given) (H : HeardAll) (F1 : Fork) (a : HeadOwn) (gk : OnBytes.Model.Forest.Heard)
      (o' : HeadOwn) (claim : OnBytes.Model.WsClaim),
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g ∧
      hear ((seatAt W.hS (readsOf W)).ledger s) rv = some (H, F1, []) ∧
      s.here = .head a ∧ a.lookHeard = some gk ∧
      sF.here = .head o' ∧ o'.x = some (heardOf gk H) ∧ o'.claim = some claim ∧
      (seatAt W.hS (readsOf W)).ledger s' = F1 ∧
      ∀ (t : OnBytes.Model.Head.Tables)
        {sh : OnBytes.Model.WsShape} (_ : OnBytes.Road.SizedW sh ppref)
        (_ : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (_ : W.H.lamS = 13)
        (_ : First.Look.weightsClaim (runAt W cov (heardOf gk H) t) W.layers.wsLay = .ok claim),
        ∃ q sg, OnBytes.Model.Head.callNo W.HLy "HD0" = some q ∧
          (W.HLy.calls.getD q default).seg? "HD0" = some sg ∧
          (LeftTies W g cov (heardOf gk H) t (ewAt (runAt W cov (heardOf gk H) t) q sg) →
            ∀ c : Cells, c.Wh = whOf M → V = nV → d = nD → ∀ mask : Nat → E,
              hidden F1 mask (heardOf gk H).sV = hidden o'.F mask (heardOf gk H).sV →
              (∀ j, j < Pm.nMsg → rd (mask j) = maskOf (z, sF) w j) →
              WeightAt W s' c mask) := by
  obtain ⟨g, H, F1, a, gk, o', p1, p2, p3, p4, p5, p6, p7, J⟩ :=
    weightAt_at_quiet W l hd hWL hcan hplan hst hTT hcov hr hc hH
  obtain ⟨s₀, p3', lkW, h, hd2, claim, x0, hu, e1, e2, e3, hsv, heq⟩ :=
    wtP1_plain Pm ni cellOf maskOf (z, sF) y w hw
  have e1' : sF.here = .head hd2 := e1
  rw [p5] at e1'
  obtain rfl := First.Here.head.inj e1'
  obtain rfl : heardOf gk H = x0 := Option.some.inj (p6.symm.trans e3)
  refine ⟨g, H, F1, a, gk, o', claim, p1, p2, p3, p4, p5, p6, e2, p7,
    fun t sh Z hl hlam hk => ?_⟩
  obtain ⟨q, sg, hq, hsg, hcl, J2⟩ := J t Z hl hlam hk
  refine ⟨q, sg, hq, hsg, fun hL c hWh hV hd' mask hhid hmask => J2 hL c hWh hV hd' mask ?_⟩
  have hs : 13 ≤ (heardOf gk H).rs.size := by
    have e := (rs_size hWL p2 (zt_size_at W p1 hplan)).trans (lPd_ref hd')
    show 13 ≤ ((H.2.2.logits.r.extract lt (lt + lPd)).reverse).size
    rw [Array.size_reverse]
    exact Nat.le_of_eq e.symm
  have hlP : OnBytes.Model.wsLayOf sh true kRef =
      .ok (First.MergeLaw.planPlace Pm h ⟨claim.ui, hu⟩).lay := by
    show OnBytes.Model.wsLayOf sh true kRef = .ok Pm.lay
    rw [hlay]
    exact hl
  have hcv := claimVal_cellsIn Z (First.MergeLaw.planPlace Pm h ⟨claim.ui, hu⟩) hlP (cellOf w) i
    hcell (avOf (runAt W cov (heardOf gk H) t) (ewAt (runAt W cov (heardOf gk H) t) q sg))
    (heardOf gk H).rs hs
  have hcl' : claim = headClaim (First.MergeLaw.planPlace Pm h ⟨claim.ui, hu⟩).lay
      (avOf (runAt W cov (heardOf gk H) t) (ewAt (runAt W cov (heardOf gk H) t) q sg))
      (heardOf gk H).rs := by
    show claim = headClaim Pm.lay _ _
    rw [hlay]
    exact hcl
  rw [← hcl'] at hcv
  have hcv' : claimVal Reading.gl Pm.lay
      (cellsIn (First.MergeLaw.planPlace Pm h ⟨claim.ui, hu⟩) (cellOf w)) claim =
      claimVal Reading.gl Pm.lay (fun r c' => ((i.mat r c' : Int) : K)) claim := hcv
  rw [rd_atWorld_hidden, hhid]
  unfold hidden
  rw [rd_sub, rd_mul, hmask _ hsv, ← hlay, ← hcv', heq]
  rfl

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.claimVal_cellsIn
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rd_atWorld_slot
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.weightAt_of_wtP1
