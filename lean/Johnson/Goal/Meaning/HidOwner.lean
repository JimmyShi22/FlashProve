-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidOwner.lean: in the verifier's plans a label names its owner: every entry of
the 25 lists bears 256 times the identifier of the sub-proof that owns the array, plus the array's
number in the owner's list.

Main names:
  linkOf id   the number of the sub-proof with the identifier id: 1 + g: group g (2 g) · 13: the
    head (24) · 14 + g: the attention sub-proof of group g (2 g + 1).
  ownerK lab, ownerA lab   the owner's sub-proof and the array's number there, off the label:
    linkOf (lab / 256) and lab % 256.
  size_even, size_odd, size_head   in scope the lists have 9, 5 and 8 entries.
  lab_even, lab_odd, lab_head   in scope, the label of every entry.
  owner_cases   IN SCOPE, FOR EVERY ENTRY OF THE 25 LISTS: either the label names the entry itself,
    or the entry is the reader of one of the 24 pairs and the label names that pair's owner.

It rests on the library's labA_tails, plan_labels, plan_sizes, tails_pairs, labH_of_public,
plan_mats, owners_plan, groups_of_public, fill_eq, and on the files on labels and plan sizes beside
this one.

What is not claimed. That an array with a label lies in its owner's commitment. The full size alone.
The program does not import this file.
-/
import Johnson.Goal.Meaning.HidPlanFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model (TMat)
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx tailsOf)

/-- The number of the sub-proof with the identifier id. -/
def linkOf (id : ℕ) : ℕ :=
  if id = 13 then 24 else if id < 13 then 2 * (id - 1) else 2 * (id - 14) + 1

/-- The owner's sub-proof, off the label. -/
def ownerK (lab : ℕ) : ℕ := linkOf (lab / 256)

/-- The array's number in the owner's list, off the label. -/
def ownerA (lab : ℕ) : ℕ := lab % 256

theorem owner_of (id n : ℕ) (hn : n < 256) :
    ownerK (id * 256 + n) = linkOf id ∧ ownerA (id * 256 + n) = n := by
  unfold ownerK ownerA
  exact ⟨by rw [show (id * 256 + n) / 256 = id by omega], by omega⟩

theorem linkOf_group {g : ℕ} (hg : g < 12) : linkOf (1 + g) = 2 * g := by
  unfold linkOf
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem linkOf_att (g : ℕ) : linkOf (14 + g) = 2 * g + 1 := by
  unfold linkOf
  rw [if_neg (by omega), if_neg (by omega)]
  omega

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- The numbers of the three arrays in a group's list, in scope. -/
theorem ix_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    (matIx X.y).iQA = 6 ∧ (matIx X.y).iXO = 7 ∧ (matIx X.y).iXI = 8 := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  refine ⟨?_, ?_, ?_⟩
  · show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 = 6
    rw [p0, p1]
  · show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 = 7
    rw [p0, p1]
  · show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 = 8
    rw [p0, p1]

/-- A group's plan is there. -/
theorem planG_there (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ}
    (hg : g < 12) : ∃ P, X.G[g]? = some P := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
  obtain ⟨hsz, -⟩ := Hd.plan_labels hP hG
  have hgs : g < X.G.size := by
    rw [hsz, B.groups]
    exact hg
  exact ⟨_, Array.getElem?_eq_getElem hgs⟩

theorem size_even (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12) :
    (matsAt X (2 * g)).size = 9 := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
  obtain ⟨P, e⟩ := planG_there h C hg
  have S := congrArg Array.size (plan_sizes hP hG e).1
  rw [Array.size_map] at S
  have R : (matsR X.y g).size = 9 := by
    unfold matsR
    rw [tails_pairs X.y (by rw [B.groups]; exact hg), List.size_toArray, sizesTab_length, p0, p1]
  rw [matsAt_even hg e, S, R]

theorem lab_even (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12)
    {a : ℕ} (ha : a < 9) : labAt X (2 * g) a = labA X.y g a := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨p0, p1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  obtain ⟨P, e⟩ := planG_there h C hg
  have L := labG_eq h C hg (n := a) (by rw [p0, p1]; exact ha)
  unfold labG at L
  rw [e] at L
  have L' : (P.tl.mats[a]?).map (fun M => M.aId) = some (labA X.y g a) := L
  unfold labAt
  rw [matsAt_even hg e]
  cases hM : P.tl.mats[a]? with
  | none =>
    rw [hM] at L'
    cases L'
  | some M =>
    rw [hM] at L'
    rw [getD_of hM]
    exact Option.some.inj L'

/-- The list of an attention sub-proof's plan, with the identifier in its labels. -/
theorem matsAt_att_gid (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ}
    (hg : g < 12) : ∃ i : Attention.In, i.gid = 14 + g ∧ (Hd.shapeA X g).cf.NAs = 1 ∧
      matsAt X (2 * g + 1) = (Attention.matrices (Hd.shapeA X g) i).map fixed := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  obtain ⟨lines, A0, seenG, seenA, hO, H⟩ := Hd.groups_of_public h B.p4
  obtain ⟨Xg, Ag, s, hG, h0, hs, hA, -, -, -, etl, eS⟩ := H g (by rw [B.groups]; exact hg)
  obtain ⟨cf, hf, hp, -⟩ := group_plan hG
  have ei : Xg.inp = Attention.inOf X.P.settings X.y (Hd.midQOf X.y g) g := (plan_shape hp).2
  have Sh := shaped_of_hid (plan_shape hp).1
  have en : Xg.S.cf.NAs = 1 := by
    rw [Sh.cfg, fill_eq hf]
    exact C.num 40
  refine ⟨Xg.inp, ?_, by rw [eS]; exact en, ?_⟩
  · rw [ei]
    show 2 + X.y.NGr + g = 14 + g
    rw [B.groups]
  · rw [matsAt_odd hg hA, etl, owners_plan hO h0 hs, plan_mats hp, eS]

theorem size_odd (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12) :
    (matsAt X (2 * g + 1)).size = 5 := by
  obtain ⟨i, -, n1, e⟩ := matsAt_att_gid h C hg
  rw [e, Array.size_map, matrices_size, n1]

/-- The labels of an attention sub-proof's four own entries. -/
theorem lab_odd (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ} (hg : g < 12)
    {a : ℕ} (ha : a < 4) : labAt X (2 * g + 1) a = (14 + g) * 256 + a := by
  obtain ⟨i, gi, n1, e⟩ := matsAt_att_gid h C hg
  have own : ∀ (nm : String) (m k wp : ℕ),
      (fixed (Attention.ownMatrix i nm m k a wp)).aId = (14 + g) * 256 + a := by
    intro nm m k wp
    unfold fixed Attention.ownMatrix
    rw [← gi]
    rfl
  unfold labAt
  by_cases h0 : a = 0
  · subst h0
    have hq : (0 : ℕ) < (Hd.shapeA X g).cf.NAs := by rw [n1]; exact Nat.one_pos
    have hM : (Attention.matrices (Hd.shapeA X g) i)[0]? = some (Attention.ownMatrix i
        ("as" ++ toString 0) (2 ^ (Hd.shapeA X g).cf.lmS)
        ((Hd.shapeA X g).kAs / (Hd.shapeA X g).cf.NAs) 0 i.wpS) := by
      unfold Attention.matrices
      rw [Array.getElem?_append_left (by simpa using hq)]
      simp [hq]
    rw [getD_of (show (matsAt X (2 * g + 1))[0]? = some _ by
      rw [e, Array.getElem?_map, hM]
      rfl)]
    exact own _ _ _ _
  · have t := matrices_tail (Hd.shapeA X g) i (a - 1)
    rw [n1, show 1 + (a - 1) = a by omega] at t
    have c : a = 1 ∨ a = 2 ∨ a = 3 := by omega
    rcases c with rfl | rfl | rfl
    · have hM : (matsAt X (2 * g + 1))[1]? = some (fixed (Attention.ownMatrix i "ah"
          ((Hd.shapeA X g).cf.wcH * (Hd.shapeA X g).T)
          ((Hd.shapeA X g).fillH / (Hd.shapeA X g).cf.wcH) 1 i.wph)) := by
        rw [e, Array.getElem?_map, t]
        rfl
      rw [getD_of hM]
      exact own _ _ _ _
    · have hM : (matsAt X (2 * g + 1))[2]? = some (fixed (Attention.ownMatrix i "ao"
          ((Hd.shapeA X g).cf.wcO * (Hd.shapeA X g).T)
          ((Hd.shapeA X g).fillO / (Hd.shapeA X g).cf.wcO) 2 i.wpo)) := by
        rw [e, Array.getElem?_map, t]
        rfl
      rw [getD_of hM]
      exact own _ _ _ _
    · have hM : (matsAt X (2 * g + 1))[3]? = some (fixed (Attention.ownMatrix i "bA"
          (2 ^ (Hd.shapeA X g).cf.lmb) (Hd.shapeA X g).kbA 3 i.wpbA)) := by
        rw [e, Array.getElem?_map, t]
        rfl
      rw [getD_of hM]
      exact own _ _ _ _

theorem size_head (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    (matsAt X 24).size = 8 := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
  obtain ⟨stream, -, hm⟩ := Hd.planH2_label hH
  rw [matsAt_head, e]
  show H0.tl.mats.size = 8
  rw [hm]
  unfold Model.Head.matsH
  rw [hN]
  rfl

theorem lab_head (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {a : ℕ} (ha : a < 8) :
    labAt X 24 a = Hd.labH X.hS X.y a := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  unfold labAt
  rw [matsAt_head]
  exact Hd.labH_of_public h hN (by omega)

/-- **In scope, for every entry of the 25 lists: the label names the entry itself, or the entry is
the reader of one of the 24 pairs and the label names that pair's owner.** -/
theorem owner_cases (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {k a : ℕ}
    (hk : k < 25) (ha : a < (matsAt X k).size) :
    (ownerK (labAt X k a) = k ∧ ownerA (labAt X k a) = a) ∨
    (∃ g, 0 < g ∧ g < 12 ∧ k = 2 * g ∧ a = (matIx X.y).iXI ∧
      ownerK (labAt X k a) = 2 * (g - 1) ∧ ownerA (labAt X k a) = (matIx X.y).iXO) ∨
    (∃ g, g < 12 ∧ k = 2 * g + 1 ∧ a = (Hd.shapeA X g).cf.NAs + 3 ∧
      ownerK (labAt X k a) = 2 * g ∧ ownerA (labAt X k a) = (matIx X.y).iQA) ∨
    (k = 24 ∧ a = X.hS.NHf + 3 ∧ ownerK (labAt X k a) = 22 ∧
      ownerA (labAt X k a) = (matIx X.y).iXO) := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  obtain ⟨i6, i7, i8⟩ := ix_of_core h C
  by_cases h24 : k = 24
  · subst h24
    rw [size_head h C] at ha
    by_cases e : a = 7
    · subst e
      have L : labAt X 24 7 = (1 + 11) * 256 + 7 := by
        rw [lab_head h C ha]
        unfold Hd.labH labA
        rw [hN, B.groups, i7, i8, if_pos rfl, if_neg (by omega)]
      obtain ⟨o1, o2⟩ := owner_of (1 + 11) 7 (by norm_num)
      refine Or.inr (Or.inr (Or.inr ⟨rfl, by rw [hN], ?_, ?_⟩))
      · rw [L, o1, linkOf_group (by norm_num)]
      · rw [L, o2, i7]
    · have L : labAt X 24 a = 13 * 256 + a := by
        rw [lab_head h C ha]
        unfold Hd.labH
        rw [hN, B.groups, if_neg (by omega)]
      obtain ⟨o1, o2⟩ := owner_of 13 a (by omega)
      exact Or.inl ⟨by rw [L, o1]; rfl, by rw [L, o2]⟩
  · by_cases hev : k % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g := ⟨k / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [size_even h C hg] at ha
      by_cases e : a = 8 ∧ g ≠ 0
      · have L : labAt X (2 * g) a = (1 + (g - 1)) * 256 + 7 := by
          rw [lab_even h C hg ha]
          unfold labA
          rw [i7, i8, if_pos e, show 1 + (g - 1) = g by omega]
        obtain ⟨o1, o2⟩ := owner_of (1 + (g - 1)) 7 (by norm_num)
        refine Or.inr (Or.inl ⟨g, by omega, hg, rfl, by rw [i8]; exact e.1, ?_, ?_⟩)
        · rw [L, o1, linkOf_group (by omega)]
        · rw [L, o2, i7]
      · have L : labAt X (2 * g) a = (1 + g) * 256 + a := by
          rw [lab_even h C hg ha]
          unfold labA
          rw [i8, if_neg e]
        obtain ⟨o1, o2⟩ := owner_of (1 + g) a (by omega)
        exact Or.inl ⟨by rw [L, o1, linkOf_group hg], by rw [L, o2]⟩
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g + 1 := ⟨k / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [size_odd h C hg] at ha
      obtain ⟨i, -, n1, -⟩ := matsAt_att_gid h C hg
      by_cases e : a = 4
      · subst e
        obtain ⟨M, a1, -, -, a4⟩ := entryA h C hg
        rw [n1] at a1
        have L : labAt X (2 * g + 1) 4 = (1 + g) * 256 + 6 := by
          unfold labAt
          rw [getD_of a1, a4]
          unfold labA
          rw [i6, i8, if_neg (by omega)]
        obtain ⟨o1, o2⟩ := owner_of (1 + g) 6 (by norm_num)
        refine Or.inr (Or.inr (Or.inl ⟨g, hg, rfl, by rw [n1], ?_, ?_⟩))
        · rw [L, o1, linkOf_group hg]
        · rw [L, o2, i6]
      · obtain ⟨o1, o2⟩ := owner_of (14 + g) a (by omega)
        rw [lab_odd h C hg (by omega : a < 4)]
        exact Or.inl ⟨by rw [o1, linkOf_att], o2⟩

end Core

end Meaning

#print axioms Meaning.owner_of
#print axioms Meaning.linkOf_group
#print axioms Meaning.linkOf_att
#print axioms Meaning.ix_of_core
#print axioms Meaning.size_even
#print axioms Meaning.lab_even
#print axioms Meaning.matsAt_att_gid
#print axioms Meaning.size_odd
#print axioms Meaning.lab_odd
#print axioms Meaning.planG_there
#print axioms Meaning.size_head
#print axioms Meaning.lab_head
#print axioms Meaning.owner_cases
