-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/BelowOk.lean: CONDITIONAL.

What is here. THE TWO STRUCTURES OF PREMISES ON THE SLOTS THAT K4's TWO LISTS OF CLAIMS NAME
(`FrontOk`, `BackOk`, Johnson/Road/K4/Slots/FrontBack.lean), BEHIND A HEARING OF THE LAYERS' OWN
ROUNDS: `FrontOk` at "below the merge's first slot", `BackOk` at "below sFv" (the slot of the
merge's end value). Statements and proofs.

Why this file. Johnson/Road/K4/Total/NotFree.lean builds these two structures inside the proofs of
`front_below` and `back_below` and spends them at once on a RETURN OF A RUN (`formsFrontWith`,
`formsBack`). Whoever holds the lists without a run's return (`front` at any shown values; `back`)
wants the structures themselves, for `front_slots` and `back_slots`. THE PROOFS OF `frontOk_below`
AND `backOk_below` ARE THAT FILE's OWN LINES, up to the last call: in these two nothing new is
shown. `frontOk_at_y` is not in that file; it is small.

  `frontOk_below`   the structure for "front".
  `backOk_below`    the structure for "back".
  `frontOk_at_y`    the structure reads of the public data P their layout alone: it holds at all
      public data with the same layout.

Limits. PREMISES, as in NotFree.lean, AND NOBODY PAYS THEM HERE: the hearing's return; hF: the
ledger F has arrays of the right sizes; hfree: nothing is filled in F from its next free number on
(the library's `FreeAbove`, OnBytes/Tie/Pv/Psc/PscRoom.lean, written out); of "front" two more, on
the lookup's state: N (`LookFilled`) and hlv (its leaves' sumcheck's window lies below F's next free
number). The structures are premises of `front_slots` and `back_slots`, which go one way. This file
gives no example of the premises together; its writers know of none that has been through Lean.
Nothing on entries. Nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Road.K4.Total.NotFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own nEndT)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Psc (Weight)
open OnBytes.Desc.First.K4.Slots (Fresh win_three merge_next covers_nums stack_fin merge_start
  stretch slotsIn_wsForkStart slotsIn_mono FrontOk BackOk LookFilled)
open VerifiableInference.Desc.First.MergeLaw (hear_of_flat mergeHear_inv)

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {t u : Tape} {rows : Bool}

/-- CONDITIONAL. **The structure for "front", at "below the merge's first slot".** -/
theorem frontOk_below (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (N : LookFilled rows fo F) (hlv : fo.leaves.first + fo.leaves.walk.1.length ≤ F.next)
    (h : hear engFl P hp g fo F t = some (o, G, u)) :
    FrontOk (fun j => j < o.wo.toWsMerged.p.first) rows P g o := by
  obtain ⟨G5, u5, cl, s5, f5, A, hE⟩ := fills_before hF h
  obtain ⟨m1, _⟩ := merge_next s5 hE
  obtain ⟨hc, hy, _⟩ := hear_parts h
  obtain ⟨n9, n7, n4, p3⟩ := covers_nums hc
  obtain ⟨efo, _, hap⟩ := apart_part P hp g fo F G t u o hF h
  have n5 := f5.next
  have up : ∀ j, Filled G5 j → j < o.wo.toWsMerged.p.first := fun j hj => by
    rw [m1]
    exact filled_below hfree f5 j hj
  have lo : ∀ j, Filled F j → j < o.wo.toWsMerged.p.first := fun j hj => by
    have h1 : j < F.next := filled_below hfree (Fresh.refl F) j hj
    omega
  obtain ⟨a, b, c⟩ := N.at_ (U := F) efo fun _ hj => hj
  have hlv' : o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ F.next := by
    rw [efo]
    exact hlv
  have eT : nEndT P.y = P.y.NN * P.y.Lam + P.y.LamM + P.y.LamM * P.y.h.NE := by
    unfold nEndT
    rw [if_pos p3, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  exact
    { k3 := fun hr f hf => slotsIn_mono lo (a hr f hf)
      wplRow := slotsIn_mono up A.wplRow
      wplL := up _ A.wplL
      wplR := up _ A.wplR
      tVCl := up _ A.tVCl
      tVEnd := fun j h1 h2 => up j (stretch A.tVEnd j h1 (by rw [n4, ← hy]; exact h2))
      tVWin := fun i hi => by
        show o.H.tV.p.first + i < o.wo.toWsMerged.p.first
        omega
      tVStart := slotsIn_mono up A.tVStart
      sPvB := fun j h1 h2 => up j (stretch A.sPv j h1 h2)
      sPv7 := fun j h1 h2 => up j (stretch A.sPv j h1 (by rw [n7, ← hy]; exact h2))
      sW := fun j h1 h2 => up j (stretch A.sW j h1 (by rw [n9, ← hy]; exact h2))
      tT := fun tT e j h1 h2 => up j (stretch (A.tT tT e) j h1 (by rw [eT, ← hy]; exact h2))
      hdRow := slotsIn_mono up A.hd.1
      hdL := up _ A.hd.2.1
      hdR := up _ A.hd.2.2
      hd2 := fun x e =>
        ⟨slotsIn_mono up (A.hd2 x e).1, up _ (A.hd2 x e).2.1, up _ (A.hd2 x e).2.2⟩
      sBit := lo _ b
      lvWin := fun i hi => by
        show o.H.fo.leaves.first + i < o.wo.toWsMerged.p.first
        omega
      lvStart := slotsIn_mono lo c
      sVE := fun hg => up _ (A.sVE hg) }

/-- CONDITIONAL. **The structure for "back", at "below the slot of the merge's end value".** -/
theorem backOk_below (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (h : hear engFl P hp g fo F t = some (o, G, u)) :
    BackOk (fun j => j < o.wo.sFv) o := by
  obtain ⟨G5, u5, cl, s5, f5, A, hE⟩ := fills_before hF h
  obtain ⟨m1, _⟩ := merge_next s5 hE
  obtain ⟨_, _, _, _, H1, hd2, cl', G1, G2, G3, G4, G5', u1, u2, u3, u4, u5', _, _, hS, _, _, _,
    _, _, _⟩ := hear_parts h
  obtain ⟨_, _, _, _, beta, v, _, _, _, _, qs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvars,
    _, _⟩ := mergeHear_inv (hear_of_flat hE)
  have e := sFv_at h
  have h3 : ∀ w ∈ List.replicate P.wsLay.lk (Weight.plain 3), w.d = 3 := fun w hw => by
    obtain rfl := List.eq_of_mem_replicate hw
    rfl
  have hw := win_three o.wo.toWsMerged.p _ 1 h3 hvars
  rw [List.length_replicate] at hw
  have up : ∀ j, Filled G5 j → j < o.wo.sFv := fun j hj => by
    have h1 := filled_below hfree f5 j hj
    omega
  obtain ⟨hA, hB⟩ := stack_fin (S := fun j => j < o.wo.sFv) hS
  obtain ⟨rho, hst⟩ := merge_start _ _ _ _ _ _ _ _ hE
  refine
    { rowS := slotsIn_mono up A.rowS
      sA0 := up _ (by simpa using A.stack 0 (by omega))
      sB0 := ?_
      Alin := hA
      Blin := hB
      mWin := fun i hi => by
        show o.wo.toWsMerged.p.first + i < o.wo.sFv
        omega
      mStart := ?_ }
  · rw [A.sB0, Nat.add_assoc]
    exact up _ (A.stack _ (by omega))
  · rw [hst]
    refine slotsIn_wsForkStart _ _ fun j hj => ?_
    unfold mergeSlots at hj
    rw [Array.toList_append, List.mem_append] at hj
    rcases hj with hj | hj
    · simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [A.sV, Nat.add_assoc]
      exact up _ (A.stack _ (by omega))
    · by_cases hg : (g == 0) = true
      · rw [if_pos hg] at hj
        have e' : j = o.sVE := by simpa using hj
        rw [e']
        exact up _ (A.sVE hg)
      · rw [if_neg hg] at hj
        simp at hj

/-- The structure for "front" reads the layout alone of the public data. -/
theorem frontOk_at_y {S : ℕ → Prop} {Q : Pub} (K : FrontOk S rows P g o) (hy : Q.y = P.y) :
    FrontOk S rows Q g o :=
  { K with sPvB := by rw [hy]; exact K.sPvB }

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.frontOk_below
#print axioms OnBytes.Desc.First.K4.Total.backOk_below
#print axioms OnBytes.Desc.First.K4.Total.frontOk_at_y
