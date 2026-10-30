-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/Decide.lean: the proof of `HeadMergeDecideReturns`
(Johnson/Desc/K11/Returns/Statement.lean), to the letter: the decision of the merge of the claims on
the weights returns, and the state behind is written out. Lemmas; none of the library's goals.

How. The rounds have the merge's form (`headMergeRoundsFit`, RoundsFit.lean of this folder); so the
kind's maker of the tape returns (`mergeTape_of_form`, Tape.lean); the claimed form names one slot,
which is filled, so its public part is given (the library's `publicPart_returns_filled`,
OnBytes/Tie/Pv/Psc/PscRoom.lean); the end value goes under its slot, which is free; so the library's
flat text of the merge returns (`headMerge_flatEnd`, FlatEnd.lean), and the kind's hearing with it
(the library's `hear_of_flat`, Johnson/Top/H0/MergeLaw/Flat.lean).

The chief names:
  `start_one`        the claimed form at one slot: which slot it names; it names no entry of a row
  `hideRun_one`, `hide_free_eq`   one value under a free slot: the ledger behind, written out
  `claimFits_ui`     a claim that fits names a unit of the layout
  `ledgerLaid`           a ledger with another next slot and one value laid
  `headMergeDecideReturns`

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.Tape
import Johnson.Desc.K11.Returns.RoundsFit
import Johnson.Top.H0.MergeLaw.Flat
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes (E mulE zeroE oneE)
open OnBytes.Psc (Weight)
open OnBytes.Model (Fork Aff WsLay WsClaim WsForkOut wsForkStart wsRowPart wsEpsT powers)
open OnBytes.PscRun (Sized Filled getD_set_self publicPart_returns_filled)
open OnBytes.Desc.First.P1 (endP endP_spec endP_row_ready)
open VerifiableInference.Desc (need named roundsFit noDigest)
open VerifiableInference.Desc.First.MergeLaw (hear_of_flat)

/-- One power: 1. -/
theorem powers_one (x : E) : powers x 1 = #[oneE] := rfl

/-- The claimed form at one slot names that slot, and no entry of a row. -/
theorem start_one (sv : Nat) (x : E) :
    (wsForkStart #[sv] (powers x 1)).slots.toList.map (·.1) = [sv] ∧
      (wsForkStart #[sv] (powers x 1)).ents = #[] := by
  rw [powers_one]
  constructor <;> simp [wsForkStart, Aff.addMul, Aff.slot]

/-- A run of one value is one step. -/
theorem hideRun_one (F : Fork) (j : Nat) (v f : E) : F.hideRun j #[v] f = F.hide j v f := by
  unfold Fork.hideRun
  rw [← Array.foldlM_toList]
  cases h : F.hide j v f with
  | none => simp [Fork.hideStep, h]
  | some H => simp [Fork.hideStep, h]

/-- One value under a slot that is there and free: the ledger behind, written out. -/
theorem hide_free_eq (F : Fork) (j : Nat) (v f : E) (h1 : j < F.ns) (h2 : F.gotF.size = F.ns)
    (h3 : ¬ Filled F j) :
    F.hide j v f =
      some { F with gotF := F.gotF.set! j true, vp := F.vp.set! j v, mf := F.mf.set! j f } := by
  have hj : j < F.gotF.size := by rw [h2]; exact h1
  have e : F.gotF.getD j true = F.gotF.getD j false := by
    simp [Array.getD_eq_getD_getElem?, hj]
  have h3' : F.gotF.getD j true = false := by
    rw [e]
    unfold Filled at h3
    simpa using h3
  unfold Fork.hide
  rw [if_pos (by simp [h1, h2, h3'])]

/-- A claim that fits names a unit of the layout. -/
theorem claimFits_ui {lay : WsLay} {c : WsClaim} (h : claimFits lay c = true) :
    c.ui < lay.U.size := by
  by_contra hn
  unfold claimFits at h
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
  cases h

/-- The ledger F with nx as its next slot and one value laid under slot j. -/
def ledgerLaid (F : Fork) (nx j : Nat) (v f : E) : Fork :=
  { F with next := nx, gotF := F.gotF.set! j true, vp := F.vp.set! j v, mf := F.mf.set! j f }

/-- **The decision returns, and the state behind is written out.** -/
theorem headMergeDecideReturns : HeadMergeDecideReturns := by
  intro P s a claim x rs hhere hop hnw hcl hx hfit hS hFl hlt hfree hn hrf
  obtain ⟨xb, mu, eps, c, beta, v, xs, hxl, hx2, htape⟩ :=
    mergeTape_of_form P.lay.lk 1 P.work _ (headMergeRoundsFit P rs hrf)
  obtain ⟨st1, st2⟩ := start_one x.sV xb
  obtain ⟨T, hT⟩ := publicPart_returns_filled a.F (wsForkStart #[x.sV] (powers xb 1)) hS.2.2
    (by
      intro y hy
      have hm : y.1 ∈ [x.sV] := by
        rw [← st1]
        exact List.mem_map_of_mem hy
      rw [List.mem_singleton.1 hm]
      exact hFl)
  have hj : a.F.next + 1 + 2 * P.lay.lk + 1 = mergeEndSlot P.lay.lk a.F := by
    unfold mergeEndSlot
    omega
  have hnx : a.F.next + 1 + 2 * P.lay.lk + 1 + 1 = a.F.next + 2 * P.lay.lk + 3 := by omega
  have hG : ({ a.F with next := a.F.next + 1 + 2 * P.lay.lk + 1 + 1 } : Fork).hideRun
      (a.F.next + 1 + 2 * P.lay.lk + 1) #[v] beta =
      some (ledgerLaid a.F (a.F.next + 1 + 2 * P.lay.lk + 1 + 1) (a.F.next + 1 + 2 * P.lay.lk + 1) v
        beta) := by
    have h0 := hide_free_eq ({ a.F with next := a.F.next + 1 + 2 * P.lay.lk + 1 + 1 } : Fork)
      (mergeEndSlot P.lay.lk a.F) v beta hlt hS.2.2 hfree
    rw [← hj] at h0
    rw [hideRun_one]
    exact h0
  have hsh : (ledgerLaid a.F (a.F.next + 1 + 2 * P.lay.lk + 1 + 1)
      (a.F.next + 1 + 2 * P.lay.lk + 1) v beta).shown (a.F.next + 1 + 2 * P.lay.lk + 1) =
      some v := by
    have hl : a.F.next + 1 + 2 * P.lay.lk + 1 < a.F.ns := by rw [hj]; exact hlt
    unfold Fork.shown ledgerLaid
    rw [if_pos (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl, getD_set_self _ _ _ _ (by rw [hS.2.2]; exact hl)⟩)]
    exact congrArg some (getD_set_self _ _ _ _ (by rw [hS.1]; exact hl))
  obtain ⟨wo, hfl, hp, hsF, hrm, _, _, hrec⟩ := headMerge_flatEnd P.lay #[claim] #[x.sV] a.F _ xb mu
    eps c beta v T v 0 0 0 xs (by simp) (by simp) rfl
    (by
      intro q hq
      have e : q = claim := by simpa using hq
      rw [e]
      exact ⟨claimFits_ui hfit, hfit⟩)
    hxl hx2 hT hG hsh
  have hhear : mergeHear P.lay #[claim] #[x.sV] a.F (mergeTapeOf 1 xb mu eps 0 xs 0 c beta 0 v) =
      .ok (wo, _, []) := hear_of_flat hfl
  obtain ⟨e1, _, _, e4, _, _, e7⟩ := endP_spec (beginP #[x.sV] xb T mu eps a.F.next)
    (xs.map plainRnd) (Weight.atZero 2, [c], beta)
  obtain ⟨r1, r2, _, r4⟩ := endP_row_ready (beginP #[x.sV] xb T mu eps a.F.next)
    (xs.map plainRnd) (Weight.atZero 2, [c], beta) rfl rfl rfl
  have hvars : wo.p.vars.toList =
      List.replicate P.lay.lk (Weight.plain 3) ++ [Weight.atZero 2] := by
    rw [hp, e1]
    show [] ++ _ = _
    rw [List.nil_append, List.map_append, List.map_map, ← hxl]
    congr 1
    show xs.map (fun _ => Weight.plain 3) = _
    exact List.map_const'
  refine ⟨wo, ledgerLaid a.F (a.F.next + 1 + 2 * P.lay.lk + 1 + 1)
    (a.F.next + 1 + 2 * P.lay.lk + 1) v beta, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · have hnext : ((ledgerLaid a.F (a.F.next + 1 + 2 * P.lay.lk + 1 + 1)
        (a.F.next + 1 + 2 * P.lay.lk + 1) v beta).next == P.nMsg) = true := by
      show (a.F.next + 1 + 2 * P.lay.lk + 1 + 1 == P.nMsg) = true
      rw [beq_iff_eq, hnx, hn]
    unfold headMergeDecide
    simp only [hhere, need, named, hop, hnw, htape, hcl, hx, hhear, hnext, bind, Except.bind, pure,
      Except.pure, if_true, List.isEmpty_nil]
  · rw [hnx, hj]
    rfl
  · show (a.F.vp.set! _ v).size = a.F.vp.size
    simp [Array.set!_eq_setIfInBounds]
  · show (a.F.mf.set! _ beta).size = a.F.mf.size
    simp [Array.set!_eq_setIfInBounds]
  · refine ⟨by rw [hp]; exact r2, by rw [hp]; exact r1, by rw [hp]; rfl, by rw [hp, e7]; rfl, hvars,
      ?_, by rw [hp, e4]; exact st1, by rw [hp, e4]; exact st2, ?_, hsF.trans hj,
      ⟨mulE oneE (wsEpsT P.lay claim wo.rm), ?_⟩⟩
    · have h1 : wo.p.r.size = wo.p.vars.size := by rw [hp]; exact r4
      have h2 : wo.p.vars.size = wo.p.vars.toList.length := (Array.length_toList).symm
      rw [h1, h2, hvars]
      simp
    · have h1 : wo.rm.size = wo.rm.toList.length := (Array.length_toList).symm
      rw [h1, hrm, List.length_map, hxl]
    · rw [hrec]
      show ((#[claim].zip (powers xb 1)).toList.map _) = _
      rw [powers_one]
      simp

end Johnson.Desc.First.ForkMerge.Returns

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Returns.powers_one
#print axioms Johnson.Desc.First.ForkMerge.Returns.start_one
#print axioms Johnson.Desc.First.ForkMerge.Returns.hideRun_one
#print axioms Johnson.Desc.First.ForkMerge.Returns.hide_free_eq
#print axioms Johnson.Desc.First.ForkMerge.Returns.claimFits_ui
#print axioms Johnson.Desc.First.ForkMerge.Returns.headMergeDecideReturns
