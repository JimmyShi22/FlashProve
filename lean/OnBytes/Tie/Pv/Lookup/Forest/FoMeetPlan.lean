-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoMeetPlan.lean.
The spec of the sub-proofs' lookup is what the byte-level verifier's planner's entries ask.

Main names:
  `spEnt e`: what a plan entry asks of a round's plain data: bytes / 24 scalars, drawE elements; all
    drawn are other than 0 where the entry says so of all of them.
  `ent_spec`: the closed form of the planner's list (TwPlan.entN, the shift's entry in front if
    there is one), read by spEnt, is the shift's round and Fo.specN: for all v', d, n and w ≠ 0.
  `plan_spec`: if the planner finishes Params.planForest at the shape's v, d and shift, its rounds'
    entries, read by spEnt, are Fo.specF h. From TwLaw.finish_forest.
  `meet_view`: the rounds of a view whose sizes are Fo.planF h, read by a reading ρ in a field, are
    the reading of a typed transcript, if no 0 is read where a further variable's challenge stands.
Under: 1 ≤ h.v; in meet_view also Fo.YNonZero, a premise on the view.
Does not say: that the planner does not refuse. Nor that the routine that reads a round by its entry
asks what spEnt says: spEnt is this file's own reading of an entry.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoMeet
import OnBytes.Tie.Pv.Lookup.Port.FoHeard
import OnBytes.Tie.Pv.Lookup.Lists.TwPlanOne

set_option autoImplicit false

namespace Fo
open Tw TwV TwPlan OnBytes OnBytes.Params OnBytes.Model OnBytes.PscRun

/-- What a plan entry asks of a round's plain data. -/
def spEnt (e : Fmt.Entry) : RSp := ⟨e.msg / 24, e.drawE, e.drawE != 0 && e.drawNZ == e.drawE⟩

theorem spEnt_rd (wk : ℕ) (name : String) (s k : ℕ) (hk : k ≠ 0) :
    spEnt (rd wk name s k) = ⟨s, k, false⟩ := by
  have h0 : (0 == k) = false := by simpa using fun h : 0 = k => hk h.symm
  simp [spEnt, rd, h0]

theorem spEnt_y (wk : ℕ) (name : String) (s : ℕ) : spEnt (rd wk name s 1 1) = ⟨s, 1, true⟩ := by
  simp [spEnt, rd]

theorem spEnt_none (name : String) (s : ℕ) : spEnt (rdNone name s) = ⟨s, 0, false⟩ := by
  simp [spEnt, rdNone]

/-- A sumcheck with the round of the further variable. -/
theorem psc_spec (wk k g gY a : ℕ) :
    (pscN wk (List.replicate k g) true gY a).map spEnt = spSc k g gY a := by
  simp [pscN, spSc, spEnt_rd, spEnt_y, spEnt_none]

/-- A sumcheck without it. -/
theorem psc_specC (wk : ℕ) (degs : List ℕ) :
    (pscN wk degs false 0 0).map spEnt = ⟨1, 1, false⟩ :: degs.map fun n => ⟨n, 1, false⟩ := by
  simp [pscN, spEnt_rd, Function.comp_def]

theorem ent_specN (wk v' d w n : ℕ) (hw : w ≠ 0) :
    (entN wk v' d w n).map spEnt = specN v' d w n := by
  have hwd : w + d ≠ 0 := by omega
  have h0 : (pscN wk [] true 3 3).map spEnt = spStep 0 := psc_spec wk 0 0 3 3
  have h1 : ∀ l, (pscN wk [] true 3 2).map spEnt = spStep (l + 1) := fun _ => psc_spec wk 0 0 3 2
  unfold entN specN
  rw [TwLaw.flat_succ spStep n]
  have e1 : (fun _ : ℕ => (pscN wk [] true 3 2).map spEnt) = fun l => spStep (l + 1) := funext h1
  have e2 : spLev 0 = fun a => spSc a 2 2 2 ++ [⟨0, 1, false⟩] := funext fun a => by
    unfold spLev
    rw [Nat.zero_add]
  have e3 : spLev w = fun a => spSc (w + a) 2 2 2 ++ [⟨0, 1, false⟩] := rfl
  simp only [List.map_append, List.map_flatMap, List.map_cons, List.map_nil, h0, psc_spec,
    psc_specC, spEnt_rd _ _ _ _ one_ne_zero, spEnt_rd _ _ _ _ hw, spEnt_rd _ _ _ _ hwd,
    List.append_assoc]
  rw [e1, e2, e3]

theorem ent_spec (wk v' d w n : ℕ) (hw : w ≠ 0) (sh : Bool) :
    ((if sh then [shiftN wk] else []) ++ entN wk v' d w n).map spEnt =
      spShift sh ++ specN v' d w n := by
  rw [List.map_append, ent_specN wk v' d w n hw]
  cases sh
  · rfl
  · show [spEnt (rd wk "LKP shift" 0 1)] ++ _ = _
    rw [spEnt_rd _ _ _ _ one_ne_zero]
    rfl

/-- The planner's own entries, read, are the spec. -/
theorem plan_spec {s : Setting} {sc : Scope} (h : FoNums.Sh) (hv : 1 ≤ h.v) {P : Planned}
    (hf : finish s sc (planForest ⟨h.v, h.d, FoNums.several h⟩) = .ok P) :
    (P.rounds.map (·.entry)).map spEnt = specF h := by
  have hv' : FoNums.v' h + 1 = h.v := by unfold FoNums.v'; omega
  rw [← hv'] at hf
  rw [(TwLaw.finish_forest (FoNums.v' h) h.d (FoNums.several h) hf).1]
  exact ent_spec _ _ _ 5 30 (by decide) _

open Cb.Fo Iop TWhole in
/-- At the rounds that a run took off a view. -/
theorem meet_view {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    (ρ : Model.Reading E) (h : FoNums.Sh) (L : Lay E St₀ J₀) (Ex : ExtSpec) (rv : List Fmt.RoundView)
    (hv : 1 ≤ h.v)
    (hs : rv.map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF h)
    (hz : YNonZero h (rv.map (rdRV ρ))) :
    ∃ τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape, forFl h L Ex τ = rv.map (rdRV ρ) := by
  refine meet h L Ex _ hv ?_ hz
  rw [← hs, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [sizeOf, rdRV]

end Fo
