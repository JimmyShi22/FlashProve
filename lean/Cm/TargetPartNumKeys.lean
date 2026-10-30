-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPartNumKeys.lean: book-keeping on the sizes of the model's polynomial conditions: the
model's numbers over p = 2^64 - 2^32 + 1, after gluing: the numbers of variables of the glued
families of `(Cm.Seg.TS.segM s k).glued`, by kind of segment and by size of table; how many families
of keys a glued segment has.

Statements on data only, with their proofs. In a segment the families of identities must be 0 at
every vertex, and the families of keys must take values of their tables (`SegSpec.Holds`,
Cb/Req/ReqSpec.lean). Gluing (`SegSpec.glued`, Cb/Req/ReqGlue.lean) joins all identities into one
family, and the keys of each table into one, with selector variables in front. The numbers before
gluing are in Cm/TargetPartNumSeg.lean.



Main names:
  `Sharp S n16 n8 nI`: every table of S has T = 16 or T = 8; a glued family of keys has at most n16
    variables if its table has T = 16, at most n8 if T = 8; the glued identities have at most nI.
  By kind of segment:
    tables of 2^16 entries    tables of 2^8 entries     the one family of identities      families
                                                                                          of keys
  all of four layers but attention (`ff_sharp`, `ff_keysLen`):
    24 families, 5 + 26 = 31  10 families, 4 + 26 = 30  at most 19 families, 5 + 23 = 28  at most 5
  attention weights (`att_sharp`, `att_keysLen`):
    7 families, 3 + 27 = 30   none                      12 families, 4 + 18 = 22          at most 4
  the head with the identity on y (`headY_sharp`, `headY_keysLen`):
    5 families, 3 + 28 = 31   2 families, 1 + 28 = 29   18 families, 5 + 10 = 15          at most 4
  "c families, a + V = n": at most c families on at most V variables are glued into one on at most
  n = ⌈log₂ c⌉ + V (`v_glued_byT`, `idn_glued_le`). The theorems state n (`Sharp` at 31 30 28, at
  30 0 22, at 31 29 15) and the last column; c and V are arguments in the proofs.
  `segM_sharp`, `segM_gluedKeys`, `segM_keysLen`: every glued segment.
All are upper bounds, but for the tables' sizes.

The generic lemmas (`v_glued_byT`, `idn_glued_le`, `tab_glued`) are Cm/SegNumsKeys.lean's, imported.
`headY_sharp` has 18 identities.
Section 4: `headY_keysLen`: the head's tables are among four (range 2^16; the range table scaled by
2^23; range 2^8; the clamp); `gluedLen_le` is stated for all fields.

Why: which tables are equal is decided classically in the glued form. But equal tables have the same
number of entries: so the families glued with a table of 2^t entries are among the segment's
families whose tables have 2^t entries, and these can be counted.

Limits: No two tables are compared. No number here is a security level.
Terms: lean/GLOSSARY.md.
-/
import Cm.TargetPartNumSeg
import Cm.SegNumsKeys

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All Finset

/-- What is shown of a segment: (bounds on the numbers of variables of glued keys with large tables,
with small tables, of the glued identities). -/
structure Sharp {X : Type} (S : SegSpec X Cb.Gl.F Cb.Gl.E) (n16 n8 nI : ℕ) : Prop where
  tabs : ∀ k ∈ S.keys, k.2.T = 16 ∨ k.2.T = 8
  k16 : ∀ q ∈ S.glued.keys, q.2.T = 16 → q.1.v ≤ n16
  k8 : ∀ q ∈ S.glued.keys, q.2.T = 8 → q.1.v ≤ n8
  idn : ∀ f ∈ S.glued.idn, f.v ≤ nI

/-! ## 2. The three kinds -/

theorem head_sharp (np : NormPar) : Sharp (segHead np) 31 29 15 where
  tabs := fun k hk => by
    obtain ⟨f, _, rfl⟩ := List.mem_map.1 hk
    show tabLog f = 16 ∨ tabLog f = 8
    cases f <;> decide
  k16 := v_glued_byT (segHead np) (t := 16) (c := 5) (V := 28)
    (by
      show ((allFam.map fun f => (keyFam np f, keyTab f)).filter fun k =>
          decide (k.2.T = 16)).length ≤ 5
      rw [List.filter_map, List.length_map]
      exact (by decide : (allFam.filter fun f => decide (tabLog f = 16)).length ≤ 5))
    fun k hk _ => ((head_nums np).1.2 k hk).2
  k8 := v_glued_byT (segHead np) (t := 8) (c := 2) (V := 28)
    (by
      show ((allFam.map fun f => (keyFam np f, keyTab f)).filter fun k =>
          decide (k.2.T = 8)).length ≤ 2
      rw [List.filter_map, List.length_map]
      exact (by decide : (allFam.filter fun f => decide (tabLog f = 8)).length ≤ 2))
    fun k hk _ => ((head_nums np).1.2 k hk).2
  idn := idn_glued_le (segHead np) (c := 17) (V := 10) (le_of_eq (head_nums np).2.1) fun f hf => by
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hf
    exact le_refl 10

/-- The last segment: the head with the identity on y. -/
theorem headY_sharp (np : NormPar) : Sharp (segHeadY np) 31 29 15 where
  tabs := (head_sharp np).tabs
  k16 := (head_sharp np).k16
  k8 := (head_sharp np).k8
  idn := idn_glued_le (segHeadY np) (c := 18) (V := 10) (le_of_eq (headY_nums np).2.1) fun f hf => by
    rcases List.mem_cons.1 (show f ∈ idY :: (segHead np).idn from hf) with rfl | hf
    · exact Nat.zero_le 10
    · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hf
      exact le_refl 10

theorem att_sharp [scl : Scl] {X : Type} (g u0 : ℕ) (tb : Tables) :
    Sharp (attSpec (X := X) (E := Cb.Gl.E) g u0 tb) 30 0 22 where
  tabs := fun k hk => by
    simp only [attSpec, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inl rfl
  k16 := v_glued_byT _ (t := 16) (c := 7) (V := 27)
    (le_trans (List.length_filter_le _ _) (le_of_eq (att_nums g u0 tb).2.2.1))
    fun k hk _ => ((att_nums g u0 tb).1.2 k hk).2
  k8 := fun q hq h8 => by
    obtain ⟨k, hk, e⟩ := tab_glued _ q hq
    rw [e] at h8
    simp only [attSpec, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> exact absurd (h8 : (16 : ℕ) = 8) (by decide : ¬ (16 : ℕ) = 8)
  idn := idn_glued_le _ (c := 12) (V := 18) (le_of_eq (att_nums g u0 tb).2.1) fun f hf => by
    have hf' : f ∈ (List.range DA.lT).map (famAt1 g) ++ [famAt2 g, famAt3 g] := hf
    rw [List.mem_append, List.mem_map] at hf'
    rcases hf' with ⟨k, _, rfl⟩ | hf'
    · show 5 + DA.lX ≤ 18
      decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
      rcases hf' with rfl | rfl <;> (show 5 + DA.lX ≤ 18) <;> decide

theorem ff_sharp {X : Type} (κ : ℕ → LayerScale) (nf : NormPar) (g : ℕ) (tok : X → ℕ → ℕ) :
    Sharp (ffSeg κ nf g tok) 31 30 28 := by
  letI : Scl := SFK κ nf g
  refine ⟨fun k hk => ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, _, rfl⟩ := List.mem_map.1 hk
    show tOf s = 16 ∨ tOf s = 8
    unfold tOf
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · refine v_glued_byT _ (t := 16) (c := 24) (V := 26) ?_ fun k hk _ =>
      ((ff_nums κ nf g tok).1.2 k hk).2
    show ((allFams.map fun s =>
          (kfAll (X := X) g tbRef s, tabOf (FFSeg.lut tbRef (FFSeg.call s)) (tOf s))).filter
        fun k => decide (k.2.T = 16)).length ≤ 24
    rw [List.filter_map, List.length_map]
    exact (by decide : (allFams.filter fun s => decide (tOf s = 16)).length ≤ 24)
  · refine v_glued_byT _ (t := 8) (c := 10) (V := 26) ?_ fun k hk _ =>
      ((ff_nums κ nf g tok).1.2 k hk).2
    show ((allFams.map fun s =>
          (kfAll (X := X) g tbRef s, tabOf (FFSeg.lut tbRef (FFSeg.call s)) (tOf s))).filter
        fun k => decide (k.2.T = 8)).length ≤ 10
    rw [List.filter_map, List.length_map]
    exact (by decide : (allFams.filter fun s => decide (tOf s = 8)).length ≤ 10)
  · refine idn_glued_le _ (c := 19) (V := 23) (ff_nums κ nf g tok).2.1 fun f hf => ?_
    rcases (mem_idnFams g tok f).1 hf with ⟨k, _, rfl⟩ | rfl | ⟨_, rfl⟩
    · show 3 + 10 ≤ 23
      decide
    · show 1 + 10 ≤ 23
      decide
    · exact le_refl 23

/-! ## 3. All segments -/

theorem Sharp.of {X : Type} {S : SegSpec X Cb.Gl.F Cb.Gl.E} {a b c a' b' c' : ℕ} (h : Sharp S a b c)
    (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') : Sharp S a' b' c' :=
  ⟨h.tabs, fun q hq e => le_trans (h.k16 q hq e) h1,
    fun q hq e => le_trans (h.k8 q hq e) h2,
    fun f hf => le_trans (h.idn f hf) h3⟩

theorem segM_sharp (s : Scales) (k : ℕ) : Sharp (segM s k) 31 30 28 := by
  unfold segM segOf
  split_ifs
  · exact (headY_sharp s.nf).of (by decide) (by decide) (by decide)
  · exact ff_sharp s.kap s.nf (k / 2) tokX
  · exact (att_sharp (scl := SFK s.kap s.nf (k / 2)) (X := XI) (k / 2)
        (s.kap (4 * (k / 2))).expRows.toNat tbRef).of
      (by decide) (by decide) (by decide)

/-! ## 4. How many families of keys -/

/-- The number of families of keys of a glued segment, from a list that holds all tables of the
segment. -/
theorem gluedLen_le {X F E : Type} [Field F] [Field E] [Algebra F E] (S : SegSpec X F E)
    (D : List (Tab F)) (h : ∀ k ∈ S.keys, k.2 ∈ D) :
    S.glued.keys.length ≤ D.length := by
  classical
  show ((S.keys.map (·.2)).dedup.map _).length ≤ _
  rw [List.length_map]
  refine ((List.nodup_dedup _).subperm fun x hx => ?_).length_le
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hx)
  exact h k hk

theorem headY_keysLen (np : NormPar) : (segHeadY np).glued.keys.length ≤ 4 :=
  gluedLen_le (segHeadY np)
      [tabOf R16 16, tabOf Plain.TP.R23 16, tabOf R8 8, tabOf FC 16] fun k hk => by
    obtain ⟨f, _, rfl⟩ :=
      List.mem_map.1 (show k ∈ allFam.map (fun f => (keyFam np f, keyTab f)) from hk)
    cases f <;> first
      | exact .head _
      | exact .tail _ (.head _)
      | exact .tail _ (.tail _ (.head _))
      | exact .tail _ (.tail _ (.tail _ (.head _)))

theorem att_keysLen [scl : Scl] {X : Type} (g u0 : ℕ) (tb : Tables) :
    (attSpec (X := X) (E := Cb.Gl.E) g u0 tb).glued.keys.length ≤ 4 :=
  gluedLen_le _ [tabA u0 tb 0, tabA u0 tb 1, tabA u0 tb 2, tabA u0 tb 3] fun k hk => by
    simp only [attSpec, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .head _
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head _))
    · exact .tail _ (.tail _ (.head _))
    · exact .tail _ (.tail _ (.tail _ (.head _)))

theorem ff_keysLen {X : Type} (κ : ℕ → LayerScale) (nf : NormPar) (g : ℕ) (tok : X → ℕ → ℕ) :
    (ffSeg κ nf g tok).glued.keys.length ≤ 5 :=
  gluedLen_le _ [tabOf R16 16, tabOf R8 8, tabOf FC 16, tabOf (FS tbRef) 16, tabOf (FL tbRef) 16]
      fun k hk => by
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 hk
    cases s <;> first
      | exact .head _
      | exact .tail _ (.head _)
      | exact .tail _ (.tail _ (.head _))
      | exact .tail _ (.tail _ (.tail _ (.head _)))
      | exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

/-- A glued segment of the model (`segM s k`) has at most 5 families of keys. -/
theorem segM_keysLen (s : Scales) (k : ℕ) : (segM s k).glued.keys.length ≤ 5 := by
  unfold segM segOf
  split_ifs
  · exact le_trans (headY_keysLen s.nf) (by decide)
  · exact ff_keysLen s.kap s.nf (k / 2) tokX
  · exact le_trans
      (att_keysLen (scl := SFK s.kap s.nf (k / 2)) (X := XI) (k / 2)
        (s.kap (4 * (k / 2))).expRows.toNat tbRef) (by decide)

/-- The families of keys of a glued segment. -/
theorem segM_gluedKeys (s : Scales) (k : ℕ) :
    ∀ q ∈ (segM s k).glued.keys,
      (q.2.T = 16 ∨ q.2.T = 8) ∧ q.1.v ≤ 31 ∧ (q.2.T = 8 → q.1.v ≤ 30) := fun q hq => by
  have h := segM_sharp s k
  obtain ⟨k', hk', e⟩ := tab_glued _ q hq
  have hT : q.2.T = 16 ∨ q.2.T = 8 := by rw [e]; exact h.tabs k' hk'
  refine ⟨hT, ?_, h.k8 q hq⟩
  rcases hT with h16 | h8
  · exact h.k16 q hq h16
  · exact le_trans (h.k8 q hq h8) (by decide)

end Cm.Seg.TS
