-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Shape/ClaimRun.lean: the proofs of `MergeRunCarries`, `MergeRunReturns` and
`MergeRunGAt` (Johnson/Desc/K11/Shape/ClaimRunStatement.lean), to the letter; and the record
`mergeRunLaw`: the `RunLaw` (Johnson/Desc/First/Batch/Shape/ClaimShape.lean) of the merge's run of
claims, at the run on shapes `mergeRunG` and at no premise on values. Lemmas and one definition;
none of the library's goals.

How. Where the run on shapes returns, the shape's number 3 says that the state stands in the head's
open link; its components are then written out (`chainSh_head`, Step.lean of this folder). The test
`openB` gives what the sumcheck's row asks (`open_of_B`, Johnson/Desc/First/Shape/Parts.lean): so
the row is made (`pscRowO`, OnBytes/K/Kc/Returns/FlReturns6.lean), and the ledger's shape behind is
the shape in front with the sumcheck's own slots filled (`hide_of_B`). The claim's form's shape:
`affSh_rowForm`. What the run's yes holds: `claim_inv` (Johnson/Top/H0/MergeLaw/Run.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Shape.ClaimRunStatement
import Johnson.Desc.K11.Shape.Step
import Johnson.Top.H0.MergeLaw.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.ShapeStep
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Fork WsForkOut)
open D6.Ret (walk_taken pscRowO)
open VerifiableInference.Desc (Claim named)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open VerifiableInference.Desc.K9.Shape (RunLaw)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim)

/-- What a return of the run on shapes at a state's shape holds. -/
theorem runG_inv {n : Nat} {s : S} {y : List ClaimSh × ChainSh}
    (h : mergeRunG n (chainSh s) = .ok y) :
    ∃ (a : HeadOwn) (wo : WsForkOut), s.here = .head a ∧ a.opened = true ∧ a.wo = some wo ∧
      openB (pscSh wo.p) (ledSh a.F) = true ∧
      y = ([ClaimSh.mk none (rowFormSh wo.p.first (takenSh (pscSh wo.p).degrees)
          (affSh wo.p.start) (AffSh.mk [] [])) []],
        (chainSh s).setLed ((ledSh a.F).setGot
          (fillB (ledSh a.F).got wo.p.first (takenSh (pscSh wo.p).degrees)))) := by
  have h3 : hereNo s.here = 3 := by
    by_contra hc
    have : ((chainSh s).here == 3) = false := by
      show (hereNo s.here == 3) = false
      simpa using hc
    unfold mergeRunG at h
    rw [this] at h
    cases h
  cases hs : s.here with
  | head a =>
    have ho : a.opened = true := by
      rw [hs] at h3
      by_cases ho : a.opened = true
      · exact ho
      · simp [hereNo, ho] at h3
    have hc := chainSh_head s a hs ho
    cases hw : a.wo with
    | none =>
      rw [hc] at h
      simp [mergeRunG, ChainSh.mk, ChainSh.here, ChainSh.led, ChainSh.head, headSh, hw] at h
    | some wo =>
      by_cases hb : openB (pscSh wo.p) (ledSh a.F) = true
      · refine ⟨a, wo, rfl, ho, hw, hb, ?_⟩
        have e : mergeRunG n (chainSh s) = .ok
            ([ClaimSh.mk none (rowFormSh wo.p.first (takenSh (pscSh wo.p).degrees)
              (affSh wo.p.start) (AffSh.mk [] [])) []],
            (chainSh s).setLed ((ledSh a.F).setGot
              (fillB (ledSh a.F).got wo.p.first (takenSh (pscSh wo.p).degrees)))) := by
          rw [hc]
          simp only [mergeRunG, ChainSh.mk, ChainSh.here, ChainSh.led, ChainSh.head, headSh, hw,
            Option.map_some, mergeSh, beq_self_eq_true]
          rw [if_pos hb]
          rfl
        exact (Except.ok.inj (e.symm.trans h)).symm
      · rw [hc] at h
        simp only [mergeRunG, ChainSh.mk, ChainSh.here, ChainSh.led, ChainSh.head, headSh, hw,
          Option.map_some, mergeSh, beq_self_eq_true] at h
        rw [if_neg hb] at h
        cases h
  | between => rw [hs] at h3; cases h3
  | lay _ => rw [hs] at h3; cases h3
  | att _ => rw [hs] at h3; cases h3
  | fin _ => rw [hs] at h3; cases h3
  | mem _ => rw [hs] at h3; cases h3

/-- **"returns".** -/
theorem mergeRunReturns : MergeRunReturns := by
  intro n s y h
  obtain ⟨a, wo, hs, _, hw, hb, _⟩ := runG_inv h
  obtain ⟨H, hH, _⟩ := pscRowO (open_of_B hb) wo.fvp {} []
  refine ⟨([{ form := wo.p.rowForm wo.fvp {} }], { s with here := .head { a with F := H } }), ?_⟩
  unfold headMergeClaim
  simp only [hs, hw, hH, named, bind, Except.bind, pure, Except.pure]

/-- **"carries".** -/
theorem mergeRunCarries : MergeRunCarries := by
  intro n s s' cs y hr hg
  obtain ⟨a, wo, hs, ho, hw, hb, rfl⟩ := runG_inv hg
  obtain ⟨a', wo', G, hs', hw', e', hc, hG⟩ := claim_inv hr
  obtain rfl : a' = a := by
    rw [hs] at hs'
    cases hs'
    rfl
  obtain rfl : wo' = wo := Option.some.inj (hw'.symm.trans hw)
  have hO := open_of_B hb
  have hlen : wo'.p.walk.1.length = takenSh (pscSh wo'.p).degrees := by
    rw [walk_taken hO, taken_sh]
  have hfree : freeB (ledSh a'.F) wo'.p.first
      (Array.replicate wo'.p.walk.1.length zeroE : Array E).size = true := by
    rw [Array.size_replicate, hlen]
    unfold openB at hb
    rw [Bool.and_eq_true] at hb
    exact hb.2
  obtain ⟨H, hH, _, _, hsh⟩ := hide_of_B hfree (subE zeroE oneE)
  obtain rfl : H = G := Option.some.inj (hH.symm.trans hG)
  rw [Array.size_replicate, hlen] at hsh
  refine Prod.ext ?_ ?_
  · show [ClaimSh.mk none _ []] = cs.map claimSh
    rw [hc]
    show _ = [ClaimSh.mk none (affSh (wo'.p.rowForm wo'.fvp {})) []]
    rw [affSh_rowForm, hlen]
    rfl
  · show (chainSh s).setLed _ = chainSh s'
    rw [e', chainSh_head s a' hs ho, chainSh_head _ { a' with F := H } rfl ho, ← hsh]
    simp only [ChainSh.setLed, ChainSh.mk, ChainSh.marked, ChainSh.here, ChainSh.tl, ChainSh.led,
      ChainSh.tables, ChainSh.rowsOwed, ChainSh.core, ChainSh.reply, ChainSh.indexMasks,
      ChainSh.pile, ChainSh.atEnd, ChainSh.check, ChainSh.link, ChainSh.look, ChainSh.lookHeard,
      ChainSh.own, ChainSh.head, ChainSh.att, ChainSh.fin, Option.map_some, headSh, if_pos ho]

/-- **The record.** The run on shapes is `mergeRunG`; there is no premise on values. -/
def mergeRunLaw : RunLaw headMergeClaim where
  runG := mergeRunG
  pre := fun _ _ => True
  carries := fun n s s' cs y _ hr hg => mergeRunCarries n s s' cs y hr hg
  returns := fun n s y hg _ => mergeRunReturns n s y hg

/-- Marks that are free over n + 1 places stay free over the first n where the last is laid. -/
theorem free_set (l : List Bool) (f n : Nat) (h : ((l.drop f).take (n + 1)).all (!·) = true) :
    (((l.set (f + n) true).drop f).take n).all (!·) = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hi' : i < n ∧ f + i < l.length := by
    simp only [List.length_take, List.length_drop, List.length_set] at hi
    omega
  have k := free_get l f (n + 1) h i (by omega)
  rw [List.getElem?_eq_getElem hi'.2] at k
  simp only [List.getElem_take, List.getElem_drop, List.getElem_set]
  rw [if_neg (by omega)]
  simpa using k

theorem taken_merge : ∀ lk : Nat, takenSh (List.replicate lk 3 ++ [2]) = 2 * lk + 2
  | 0 => rfl
  | lk + 1 => by
    have ih := taken_merge lk
    unfold takenSh at ih ⊢
    show 1 + ((3 - 1) + ((List.replicate lk 3 ++ [2]).map (· - 1)).sum) = _
    omega

/-- **The run on shapes returns behind the kind's update.** -/
theorem mergeRunGAt : MergeRunGAt := by
  intro P n a L hg hL hfree
  unfold mergeGuardB at hg
  rw [hL] at hg
  cases hh : a.head with
  | none => simp [hh] at hg
  | some h =>
    cases hc : h.claim with
    | none => simp [hh, hc] at hg
    | some c =>
      cases hx : h.xEnd with
      | none => simp [hh, hc, hx] at hg
      | some e =>
        simp only [hh, hc, hx, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
        obtain ⟨⟨⟨_, g2⟩, _⟩, ⟨⟨⟨⟨_, g5⟩, _⟩, g7⟩, _⟩, _⟩ := hg
        have hb : openB (mergeShOf P L c e).p (ledUpd P L) = true := by
          unfold freeB at hfree
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hfree
          have hs : sizedB (ledUpd P L) = true := by
            have := g5
            simpa [sizedB, ledUpd, LedSh.mk, LedSh.shown, LedSh.ns, LedSh.factors, LedSh.got]
              using this
          unfold openB freeB
          simp only [mergeShOf, PscSh.mk, PscSh.rowMade, PscSh.started, PscSh.degrees,
            PscSh.challenges, PscSh.first, taken_merge, hs, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨⟨⟨rfl, by trivial⟩, by simp⟩, by simp⟩, by simp⟩, ⟨by trivial, ?_⟩, ?_⟩
          · show L.next + (2 * P.lay.lk + 2) ≤ L.ns
            omega
          · have e : L.next + 2 * P.lay.lk + 2 = L.next + (2 * P.lay.lk + 2) := by omega
            show (((L.got.set (L.next + 2 * P.lay.lk + 2) true).drop L.next).take
              (2 * P.lay.lk + 2)).all (!·) = true
            rw [e]
            exact free_set L.got L.next (2 * P.lay.lk + 2) hfree.2
        have e3 : ∀ (X : LedSh) (Y : HeadSh),
            ((((a.setRowsOwed none).setLed X).setHead Y).here == 3) = true := by
          intro X Y
          show (a.here == 3) = true
          rw [g2]
          rfl
        have e4 : ∀ (X : LedSh) (Y : HeadSh),
            (((a.setRowsOwed none).setLed X).setHead Y).led = some X := by
          intro X Y
          show a.led.map (fun _ => X) = some X
          rw [hL]
          rfl
        have e5 : ∀ (X : LedSh) (Y : HeadSh),
            (((a.setRowsOwed none).setLed X).setHead Y).head = some Y := by
          intro X Y
          show a.head.map (fun _ => Y) = some Y
          rw [hh]
          rfl
        cases hres : mergeRunG n (mergeUpd P a) with
        | ok y => exact ⟨y, rfl⟩
        | error msg =>
          exfalso
          unfold mergeUpd at hres
          simp only [hL, hh, hc, hx] at hres
          unfold mergeRunG at hres
          rw [e3, e4, e5] at hres
          have hres' : (if openB (mergeShOf P L c e).p (ledUpd P L) = true then
              (Except.ok _ : Except String (List ClaimSh × ChainSh)) else .error _) =
              .error msg := hres
          rw [if_pos hb] at hres'
          cases hres'

end Johnson.Desc.First.ForkMerge.ShapeStep

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeRunReturns
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeRunCarries
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeRunLaw
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeRunGAt
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.runG_inv
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.free_set
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.taken_merge
