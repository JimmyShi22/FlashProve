-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/CourseLeaves.lean: THE
COURSE's CLAIM ON A PART's LEAVES NAMES THE SECOND LEDGER's ENTRIES ALONE: in the typed course of a
key file's lookup (Lk6.Mid.course, Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean: the course that
hear_course names) every mask entry that the claim on the leaves of part i's
key tree names is an entry D.ix n of the second message. (The like at Lk6.PortSim.course, whose text
is the same but for the namespace, goes through by the same proof: not kept here.)

Main names:
  IxOnly D c: every mask entry that the claim c names is some D.ix n.
  ends_ix: the claims that a sumcheck of the product kind hands on, where its last two fresh mask
    entries are the second message's, are IxOnly.
  levels_ix: so is the claim on the leaves that a key tree of at least one level hands on.
  leaves_ix: so is (course D f own idx).leaves i, at i < D.S.m with 1 ≤ D.S.v i.

No premise on the rounds f: where they are too few for a sumcheck no value is shown, and the claims
handed on are none.

Object: Lk6.Mid.course. User: the field r1_15 (the reading of a claim on keys does not move when
the first message's table is laid anew).
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.Course

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.CourseLeaves
open OnBytes OnBytes.Slice
open Lk6.PortSim Lk6.Mid

/-- Every mask entry that the claim names is an entry of the second message. -/
def IxOnly (D : Dt) (c : PscF.PointClaim) : Prop := ∀ q ∈ c.masks, ∃ n, q.1 = D.ix n

theorem ixOnly_no (D : Dt) : IxOnly D noClaim := fun _ hq => by cases hq

theorem ixOnly_scale (D : Dt) (x : GE) (m : PscF.MaskForm) (h : ∀ q ∈ m, ∃ n, q.1 = D.ix n) :
    ∀ q ∈ PscF.scaleForm x m, ∃ n, q.1 = D.ix n := by
  intro q hq
  unfold PscF.scaleForm at hq
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hq
  exact h t ht

theorem ixOnly_line (D : Dt) (rho : GE) (a b : PscF.PointClaim) (ha : IxOnly D a)
    (hb : IxOnly D b) : IxOnly D (lineF rho a b) := by
  intro q hq
  have hq' : q ∈ PscF.scaleForm (1 - rho) a.masks ++ PscF.scaleForm rho b.masks := hq
  rcases List.mem_append.1 hq' with h | h
  · exact ixOnly_scale D _ _ ha q h
  · exact ixOnly_scale D _ _ hb q h

theorem ixOnly_getD (D : Dt) (L : List PscF.PointClaim) (h : ∀ e ∈ L, IxOnly D e) (j : ℕ) :
    IxOnly D (L.getD j noClaim) := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : L[j]? with
  | none => exact ixOnly_no D
  | some e => exact h e (List.mem_of_getElem? hj)

/-- **The claims that a sumcheck of the product kind hands on**, where its last two fresh mask
entries are the second message's. -/
theorem ends_ix (D : Dt) (c : PscF.Claim) (kept : ℕ) (place : List GE → List GE) (s : Cs)
    (hd : ∀ w ∈ c.vars, 1 ≤ w.d) : ∀ e ∈ (pscC D c sProd true kept place s).1.ends, IxOnly D e := by
  intro e he q hq
  have he' : e ∈ ((PscF.outOf c sProd
      (slots D.ms s.own (PscF.masksOf c sProd - 2) ++ slots D.ix s.idx 2)
      (heardF c.vars.length true s.rounds)).ends.map
        fun e => { e with point := place e.point }) := he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he'
  have hq' : q ∈ e0.masks := hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he0
  obtain rfl := List.mem_singleton.1 hq'
  obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
  have hp2' : p.2 ∈ (s.rounds.getD (c.vars.length + 2) ([], [])).1 := hp2
  have hlen : c.vars.length + 2 < s.rounds.length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hp2'
    cases hp2'
  have hvars : PscF.varsOf c sProd = c.vars ++ [PscF.Weight.atZero 3] := rfl
  have hL := PscF.hidingWalk_length (PscF.varsOf c sProd)
    ((heardF c.vars.length true s.rounds).rounds.map (·.2)) (by rw [hvars]; simp)
    (by
      show _ = ((((s.rounds.drop 1).take (c.vars.length + 1)).map _).map _).length
      rw [hvars]
      simp
      omega)
    (by
      intro w hw
      rw [hvars] at hw
      rcases List.mem_append.1 hw with h | h
      · exact hd w h
      · obtain rfl := List.mem_singleton.1 h
        show 1 ≤ 3
        omega)
  rw [hL, List.drop_left' (by
    unfold slots PscF.masksOf
    simp [sProd])] at hp1
  unfold slots at hp1
  obtain ⟨i, -, hi⟩ := List.mem_map.1 hp1
  exact ⟨_, hi.symm⟩

/-- One level's sumcheck. -/
def stepOf (D : Dt) (keys : Bool) (more n l : ℕ) (c : PscF.PointClaim) (s : Cs) : PscF.Out × Cs :=
  pscC D
    ⟨(if (keys && n == 0) then ordFirst D.S.order (more + l) else ordDown (more + l)).map
      fun t => PscF.Weight.equality (c.point.getD t 0) 3, c.masks, c.value⟩ sProd (keys && n == 0) 0
    (byVarF · (if (keys && n == 0) then ordFirst D.S.order (more + l) else ordDown (more + l))) s

theorem levels_succ (D : Dt) (keys : Bool) (more n l : ℕ) (c : PscF.PointClaim) (s : Cs) :
    cLevels D keys more (n + 1) l c s = cLevels D keys more n (l + 1)
      (lineF (stepOf D keys more n l c s).2.draw
        ((stepOf D keys more n l c s).1.ends.getD 0 noClaim)
        ((stepOf D keys more n l c s).1.ends.getD 1 noClaim)) (stepOf D keys more n l c s).2.next :=
  rfl

/-- The levels leave the claims on the leaves as they are. -/
theorem levels_leaves (D : Dt) (keys : Bool) (more : ℕ) :
    ∀ (n l : ℕ) (c : PscF.PointClaim) (s : Cs), (cLevels D keys more n l c s).2.leaves = s.leaves
  | 0, _, _, _ => rfl
  | n + 1, l, c, s => by
    rw [levels_succ, levels_leaves D keys more n]
    rfl

/-- **The claim on the leaves that a key tree of at least one level hands on.** -/
theorem levels_ix (D : Dt) (more : ℕ) :
    ∀ (n l : ℕ) (c : PscF.PointClaim) (s : Cs), IxOnly D (cLevels D true more (n + 1) l c s).1
  | 0, l, c, s => by
    rw [levels_succ]
    have h := ends_ix D
      ⟨(ordFirst D.S.order (more + l)).map fun t => PscF.Weight.equality (c.point.getD t 0) 3,
        c.masks, c.value⟩ 0 (byVarF · (ordFirst D.S.order (more + l))) s (by
        intro w hw
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hw
        show 1 ≤ 3
        omega)
    exact ixOnly_line D _ _ _ (ixOnly_getD D _ h 0) (ixOnly_getD D _ h 1)
  | n + 1, l, c, s => by
    rw [levels_succ]
    exact levels_ix D more n (l + 1) _ _

theorem key_succ (D : Dt) (n i : ℕ) (s : Cs) :
    cKey D (n + 1) i s = cKey D n (i + 1)
      { (cLevels D true 0 (D.S.v i) 0 (s.roots i) s).2 with
        leaves := Function.update (cLevels D true 0 (D.S.v i) 0 (s.roots i) s).2.leaves i
          (cLevels D true 0 (D.S.v i) 0 (s.roots i) s).1 } :=
  rfl

/-- The key trees from part i0 on: the claims on other parts' leaves stay; those on these parts'
leaves name the second message's entries alone. -/
theorem key_leaves (D : Dt) : ∀ (n i0 : ℕ) (s : Cs) (j : ℕ),
    ((j < i0 ∨ i0 + n ≤ j) → (cKey D n i0 s).leaves j = s.leaves j) ∧
      (i0 ≤ j → j < i0 + n → 1 ≤ D.S.v j → IxOnly D ((cKey D n i0 s).leaves j))
  | 0, i0, s, j => ⟨fun _ => rfl, fun h1 h2 _ => absurd h2 (by omega)⟩
  | n + 1, i0, s, j => by
    rw [key_succ]
    obtain ⟨ih1, ih2⟩ := key_leaves D n (i0 + 1)
      { (cLevels D true 0 (D.S.v i0) 0 (s.roots i0) s).2 with
        leaves := Function.update (cLevels D true 0 (D.S.v i0) 0 (s.roots i0) s).2.leaves i0
          (cLevels D true 0 (D.S.v i0) 0 (s.roots i0) s).1 } j
    refine ⟨fun h => ?_, fun h1 h2 hv => ?_⟩
    · rw [ih1 (by omega)]
      show Function.update _ i0 _ j = _
      rw [Function.update_of_ne (by omega), levels_leaves]
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h3
      · rw [ih1 (by omega)]
        show IxOnly D (Function.update (β := fun _ => PscF.PointClaim) _ i0 _ i0)
        rw [Function.update_self]
        obtain ⟨m, hm⟩ : ∃ m, D.S.v i0 = m + 1 := ⟨D.S.v i0 - 1, by omega⟩
        rw [hm]
        exact levels_ix D 0 m 0 _ _
      · exact ih2 (by omega) (by omega) hv

/-- The stretches behind the key trees leave the claims on the leaves as they are. -/
theorem course_leaves (D : Dt) (f : List (Lk6.Flat.RV GE)) (own idx : ℕ) :
    (course D f own idx).leaves =
      (cKeys D (cJoin D (cParts D (cHead D f own idx)))).leaves := by
  show (cTable D (cKeys D (cJoin D (cParts D (cHead D f own idx))))).leaves = _
  exact levels_leaves D false D.S.mu D.S.d 0 _ _

/-- **THE COURSE's CLAIM ON A PART's LEAVES NAMES THE SECOND LEDGER's ENTRIES ALONE.** -/
theorem leaves_ix (D : Dt) (f : List (Lk6.Flat.RV GE)) (own idx i : ℕ) (hi : i < D.S.m)
    (hv : 1 ≤ D.S.v i) : ∀ q ∈ ((course D f own idx).leaves i).masks, ∃ n, q.1 = D.ix n := by
  rw [course_leaves]
  exact (key_leaves D D.S.m 0 _ i).2 (Nat.zero_le _) (by omega) hv

end Johnson.RunOne.Law.CourseLeaves

#print axioms Johnson.RunOne.Law.CourseLeaves.ixOnly_no
#print axioms Johnson.RunOne.Law.CourseLeaves.ixOnly_scale
#print axioms Johnson.RunOne.Law.CourseLeaves.ixOnly_line
#print axioms Johnson.RunOne.Law.CourseLeaves.ixOnly_getD
#print axioms Johnson.RunOne.Law.CourseLeaves.ends_ix
#print axioms Johnson.RunOne.Law.CourseLeaves.levels_succ
#print axioms Johnson.RunOne.Law.CourseLeaves.levels_leaves
#print axioms Johnson.RunOne.Law.CourseLeaves.levels_ix
#print axioms Johnson.RunOne.Law.CourseLeaves.key_succ
#print axioms Johnson.RunOne.Law.CourseLeaves.key_leaves
#print axioms Johnson.RunOne.Law.CourseLeaves.course_leaves
#print axioms Johnson.RunOne.Law.CourseLeaves.leaves_ix
