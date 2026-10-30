-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/NotFree.lean: NO FORM OF K4's TWO RUNS OF CLAIMS NAMES THE MERGE's SLOT sFv
(the slot of the merge's end value). Behind a hearing of the layers' own rounds: every slot that a
form of "front" names lies below the merge's first slot; every slot that a form of "back" names lies
below sFv. Statements and proofs.

Why not at the ledger G that the hearing leaves: sFv is filled in G, so "filled in G" does not part
it from the others. THE ROAD GOES THROUGH THE LEDGER IN FRONT OF THE MERGE, G5. All that the hearing
has filled for the two runs, but for the merge's own, is filled in G5 already. From a ledger F in
which nothing is filled from its next free number on, what is filled in G5 lies below G5's next free
number; the merge begins just there; sFv is its slot number 2 lk + 2.

  `fills_before`: the list of what is filled (Fills7, Johnson/Road/K4/Slots/HearFills.lean) holds at
    the ledger in front of the merge, which has arrays of the right sizes and is Fresh from F.
  `filled_below`: what is filled in a ledger that is Fresh from F lies below its next free number.
  `sFv_at`: sFv = the merge's first slot + (2 lk + 2).
  `front_below`: every slot of every form of formsFrontWith rows P g o Gr is below the merge's
    first.
  `back_below`: every slot of every form of formsBack o Gr is below sFv.
  `front_not_sFv`, `back_not_sFv`: so none is sFv.
Gr is any ledger: the listings take no new slot, and what they name is fixed by what was heard.
New: the road through G5. fills_before is hear_fills' own walk, stopped one step earlier. The rest:
FrontOk, BackOk, formsFront_slots, formsBack_slots, stack_fin, merge_start, LookFilled;
Fresh, Spares, win_three, merge_next (Slots/HearSpares.lean, RunsSpare.lean); apart_part
(Total/WindowsFit.lean); mergeHear_inv.
**Limits.** PREMISES. Of both: the hearing's return; hF: F has arrays of the right sizes; hfree:
nothing is filled in F from its next free number on. Of "front" two more, ON THE LOOKUP's RECORD: N
(LookFilled: its own claims, if listed, its bit and its leaves' sumcheck's start form name slots
that are filled in F) and hlv (its leaves' sumcheck's window lies below F's next free number).
NOBODY PAYS THESE HERE: hF, hfree and hlv are premises of the part FitBehind too; N is the lookup's
files'. ONE PUBLIC RECORD P: the block hears at its record with the tokens laid in and runs at its
own: the caller carries hr over by formsFrontWith_tokv or run_pub (PubOnly.lean). One direction,
from a return of the listing: it is not said that a listing returns. Of the test on a slot that a
reader of the forms makes, this pays ONE clause (the slot is not the free one): not that the slot is
below the number of slots, not the mask row's seat, not "late or filled". Nothing on soundness.
K04_law, the law of K4's block itself, IS NOT PROVED. Met through Lean at no member; by a run at one
honest proof of each of two sizes both runs of claims return at all 2 and 12 layers' places.


-/
import Johnson.Road.K4.Slots.RunsSpare
import Johnson.Road.K4.Slots.FrontAt
import Johnson.Road.K4.Total.WindowsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Psc (Weight)
open OnBytes.Desc.First.K4.Slots (Spares Fresh SameAt win_three merge_next covers_nums Fills7
  norms_fills terms_fills stack_fills gated_fills front_fills stack_fin merge_start stretch
  slotsIn_wsForkStart SlotsIn slotsIn_mono FrontOk BackOk formsFront_slots formsBack_slots
  LookFilled)
open VerifiableInference.Desc.First.MergeLaw (hear_of_flat mergeHear_inv)

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G Gr F₁ : Fork}
  {t u : Tape} {rows : Bool} {fs : Array Aff}

/-- **What is filled in front of the merge.** -/
theorem fills_before (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    ∃ (G5 : Fork) (u5 : Tape) (cl : Array WsClaim), Sized G5 ∧ Fresh F G5 ∧ Fills7 P hp g o G5 ∧
      flatForkEnd P.wsLay cl (mergeSlots hp g o) G5 u5 = some (o.wo, G, u) := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, hS, hG, e2, hM,
    _, _, hE⟩ := hear_parts h
  obtain ⟨s1, _, a1, a2, a3, a4, a5, a6, a7, a8⟩ := norms_fills hF hN
  obtain ⟨s2, k2, b1⟩ := terms_fills s1 hT
  obtain ⟨s3, k3, c1, _, c3, c4, c2⟩ := stack_fills s2 hS
  obtain ⟨s4, k4, d1, d2⟩ := gated_fills s3 hG
  obtain ⟨s5, k5, e1⟩ := front_fills s4 hM
  have f1 : Fresh F G1 := (Spares.fresh hN hF).2
  have f2 : Fresh G1 G2 := (Spares.fresh hT s1).2
  have f3 : Fresh G2 G3 := (Spares.fresh hS s2).2
  have f4 : Fresh G3 G4 := (Spares.fresh hG s3).2
  have f5 : Fresh G4 G5 := by
    have hM' := hM
    unfold mergeFront at hM'
    by_cases hg : (g == 0) = true
    · rw [if_pos hg] at hM'
      exact (Spares.fresh hM' s4).2
    · rw [if_neg hg] at hM'
      obtain ⟨_, rfl, _⟩ := hM'
      exact Fresh.refl _
  have q4 : ∀ j, Filled G4 j → Filled G5 j := k5
  have q3 : ∀ j, Filled G3 j → Filled G5 j := fun j hj => q4 j (k4 j hj)
  have q2 : ∀ j, Filled G2 j → Filled G5 j := fun j hj => q3 j (k3 j hj)
  have q1 : ∀ j, Filled G1 j → Filled G5 j := fun j hj => q2 j (k2 j hj)
  obtain ⟨_, _, _, _, _, w1, _, w2, w3, _, w4⟩ := hearTerms_keeps hT
  refine ⟨G5, u5, cl, s5, (((f1.trans f2).trans f3).trans f4).trans f5, ?_, hE⟩
  exact
    { sW := fun i hi => by rw [w1]; exact q1 _ (a1 i hi)
      wplL := by rw [w2]; exact q1 _ a2
      wplR := by rw [w2]; exact q1 _ a3
      wplRow := by rw [w2]; exact slotsIn_mono q1 a4
      sPv := fun i hi => by rw [w3]; exact q1 _ (a5 i hi)
      tVCl := by rw [w4]; exact q1 _ a6
      tVEnd := fun i hi => by rw [w4]; exact q1 _ (a7 i hi)
      tVStart := by rw [w4]; exact slotsIn_mono q1 a8
      tT := fun tT e i hi => q2 _ (b1 tT e i hi)
      stack := fun i hi => q3 _ (c1 i hi)
      sB0 := c3
      sV := c4
      rowS := slotsIn_mono q3 c2
      hd := ⟨slotsIn_mono q4 d1.1, q4 _ d1.2.1, q4 _ d1.2.2⟩
      hd2 := fun x e => by
        rw [e2] at e
        obtain rfl := Option.some.inj e
        exact ⟨slotsIn_mono q4 d2.1, q4 _ d2.2.1, q4 _ d2.2.2⟩
      sVE := fun hg => e1 hg }

/-- What is filled in a ledger that is Fresh from F lies below that ledger's next free number, if
nothing is filled in F from its own next free number on. -/
theorem filled_below {F G5 : Fork} (hfree : ∀ j, F.next ≤ j → ¬ Filled F j) (f : Fresh F G5) :
    ∀ j, Filled G5 j → j < G5.next := by
  intro j hj
  by_contra hc
  have hc' : G5.next ≤ j := Nat.le_of_not_lt hc
  exact hfree j (Nat.le_trans f.next hc') ((f.same j (Or.inr hc')).1.mp hj)

/-- The merge's end value's slot is the merge's slot number 2 lk + 2. -/
theorem sFv_at (h : hear engFl P hp g fo F t = some (o, G, u)) :
    o.wo.sFv = o.wo.toWsMerged.p.first + (2 * P.wsLay.lk + 2) := by
  obtain ⟨_, _, _, _, H1, hd2, cl, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, _, _, _, _, _, _,
    _, _, hE⟩ := hear_parts h
  obtain ⟨_, _, _, _, beta, v, _, _, _, _, qs, _, _, _, _, _, _, _, _, _, _, hsF, _, _, _, _,
    hfirst, _⟩ := mergeHear_inv (hear_of_flat hE)
  show o.wo.sFv = o.wo.p.first + (2 * P.wsLay.lk + 2)
  rw [hsF, hfirst]
  omega

/-- **Every slot that a form of "front" names lies below the merge's first slot.** -/
theorem front_below (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (N : LookFilled rows fo F) (hlv : fo.leaves.first + fo.leaves.walk.1.length ≤ F.next)
    (h : hear engFl P hp g fo F t = some (o, G, u))
    (hr : formsFrontWith rows P g o Gr = some (fs, F₁)) :
    ∀ f ∈ fs.toList, SlotsIn (fun j => j < o.wo.toWsMerged.p.first) f := by
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
  refine formsFront_slots (S := fun j => j < o.wo.toWsMerged.p.first) ?_ hr
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
      hd2 := fun x e => ⟨slotsIn_mono up (A.hd2 x e).1, up _ (A.hd2 x e).2.1, up _ (A.hd2 x e).2.2⟩
      sBit := lo _ b
      lvWin := fun i hi => by
        show o.H.fo.leaves.first + i < o.wo.toWsMerged.p.first
        omega
      lvStart := slotsIn_mono lo c
      sVE := fun hg => up _ (A.sVE hg) }

/-- **Every slot that a form of "back" names lies below the merge's end value's slot.** -/
theorem back_below (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (h : hear engFl P hp g fo F t = some (o, G, u)) (hr : formsBack o Gr = some (fs, F₁)) :
    ∀ f ∈ fs.toList, SlotsIn (fun j => j < o.wo.sFv) f := by
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
  refine formsBack_slots (S := fun j => j < o.wo.sFv) ?_ hr
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

/-- **No form of "front" names the merge's end value's slot.** -/
theorem front_not_sFv (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (N : LookFilled rows fo F) (hlv : fo.leaves.first + fo.leaves.walk.1.length ≤ F.next)
    (h : hear engFl P hp g fo F t = some (o, G, u))
    (hr : formsFrontWith rows P g o Gr = some (fs, F₁)) :
    ∀ f ∈ fs.toList, SlotsIn (fun j => j ≠ o.wo.sFv) f := fun f hf =>
  slotsIn_mono (fun j (hj : j < o.wo.toWsMerged.p.first) => by
    have e := sFv_at h
    omega) (front_below hF hfree N hlv h hr f hf)

/-- **No form of "back" names the merge's end value's slot.** -/
theorem back_not_sFv (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (h : hear engFl P hp g fo F t = some (o, G, u)) (hr : formsBack o Gr = some (fs, F₁)) :
    ∀ f ∈ fs.toList, SlotsIn (fun j => j ≠ o.wo.sFv) f := fun f hf =>
  slotsIn_mono (fun j (hj : j < o.wo.sFv) => Nat.ne_of_lt hj) (back_below hF hfree h hr f hf)

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.fills_before
#print axioms OnBytes.Desc.First.K4.Total.filled_below
#print axioms OnBytes.Desc.First.K4.Total.sFv_at
#print axioms OnBytes.Desc.First.K4.Total.front_below
#print axioms OnBytes.Desc.First.K4.Total.back_below
#print axioms OnBytes.Desc.First.K4.Total.front_not_sFv
#print axioms OnBytes.Desc.First.K4.Total.back_not_sFv
