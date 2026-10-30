-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPartNumSeg.lean: the model's numbers over p = 2^64 - 2^32 + 1, before gluing, for each of
the 25 segments `Cm.Seg.TS.segM s k` (Cm/TargetSegModel.lean): atoms in a term, variables, numbers
of families, sizes of tables, the shape.

Statements on data only, with their proofs. Cm/TargetPartNumKeys.lean
uses them for the glued segments.
A segment (`SegSpec`, Cb/Req/ReqSpec.lean) has the shape of a matrix of cells, families of
identities, and families of keys, each of these with a table (`Tab`) of 2^T entries. A family
(`Fam`) is a sum of terms on the vertices b < 2^v (v variables); a term (`Term`) is a table of
public coefficients times a product of atoms. An atom is affine in cells, an index atom, or a sum
atom: the sum, over w further variables, of a sum of terms. Gluing (`SegSpec.glued`,
Cb/Req/ReqGlue.lean) leaves one family of identities and one family of keys for each table.

What is counted (Cb/Req/ReqNumsGlue.lean):
  `Fam.DegLe f d`: no term of f, and no term under a sum atom of f, has more than d atoms.
  `SegSpec.NumsLe S d V`: that, and at most V variables, for all families of S.

Main names, for all values of their parameters:
                kind                              d   V   families of  families  tables
                                                          identities   of keys
  `ff_nums`     all of four layers but attention  4   26  at most 19   34        2^8 or 2^16 entries
  `att_nums`    attention weights                 12  27  12           7         2^16 entries
  `headY_nums`  the head with the identity on y   2   28  18           7         2^8 or 2^16 entries
  Of a table these three state T ≤ 16 and no more. That each T is 8 or 16 is the field tabs of
  `Sharp` (Cm/TargetPartNumKeys.lean: `ff_sharp`, `att_sharp` over `Cb.Gl.E`, `headY_sharp`,
  `segM_sharp`); attention's 2^16 is by the definitions' texts (`tabA`, `attSpec`,
  Cm/TargetSegAtt.lean).
  `segM_nums`: every segment has NumsLe 12 28, at most 19 families of identities, at most 34 of
    keys, tables of at most 2^16 entries (which k is of which kind: `segOf`,
    Cm/TargetSegModelOf.lean).
  `segM_shape`: the matrices of cells have the layout's own rowsLog k, cols k; rowsLog k ≤ 19,
    cols k ≤ 7,200 (the three pairs 2^19 × 5,990, 2^18 × 7,200, 2^19 × 4,816: the columns:
    `lay_figures`, Cm/SegLayoutProofs.lean; which k has which: the texts of `rowsLog`, `cols`,
    Cm/SegLayout.lean).
All are upper bounds (the numbers of families without "at most", and rowsLog, cols in `segM_shape`,
are stated as equations).

At the head the third key of a margin (`keyEx` at HD0, Cm/TargetSegHead.lean) has no factor (the
scaled table: `R23`, Cm/TargetPHead.lean); `headY_nums`: one identity on y (`idY`,
Cm/TargetSegHeadY.lean: no variable, one term without atoms).

Limits: No number here is a security level. This file says nothing on the numbers of further
variables of the sum atoms, and nothing on these numbers against the size of the field.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegNumsExp
import Cm.TargetSegModel
import Cm.SegLayoutProofs

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All Finset Cm.Seg.Ex

/-! ## 1. The head -/

section Led
variable {X E : Type} [Field E]

theorem d1_rowEx (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) : D1 (X := X) 1 (rowEx D g) :=
  D1.aff _

theorem d1_wsEx (v w : ℕ) (B : ℕ → ℕ → CForm E) (s : ℕ) : D1 (X := X) 2 (wsEx v w B s) := by
  unfold wsEx
  exact (D1.sumA _ _
      (Dg.pSum fun _ _ =>
        Dg.pSum fun _ _ => Dg.ite (fun _ => (Dg.aff0 _).mul (Dg.aff0 _)) fun _ => Dg.zero)).of
    (by decide)

theorem d1_ledEx (np : NormPar) {Ws : ℕ → Ex1 X E} (D : ℕ → ℕ → CForm E)
    (k : ℕ) (hW : ∀ s, D1 2 (Ws s)) : D1 2 (ledEx np Ws D k) := by
  have r := fun g => d1_rowEx (X := X) D g
  unfold ledEx
  split_ifs with hk
  · exact ((hW k).add (r _)).of (by decide)
  · match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact absurd (by norm_num) hk
    | 9 => exact (((r _).mul (r _)).sub (r _)).of (by decide)
    | 10 => exact ((r _).sub ((r _).mul (r _))).of (by decide)
    | 11 => exact ((r _).sub ((r _).mul (r _))).of (by decide)
    | 12 => exact (r _).of (by decide)
    | 13 => exact ((((r _).mul (r _)).add ((r _).mul (r _))).sub (r _)).of (by decide)
    | 14 => exact ((r _).mul (r _)).of (by decide)
    | 15 => exact ((r _).sub (((r _).mul (r _)).smul _)).of (by decide)
    | 16 => exact (r _).of (by decide)
    | _ + 17 => exact D1.zero.of (by decide)

end Led

theorem d1_lgV : D1 2 lgV := by
  unfold lgV
  exact (D1.sumA _ _ ((Dg.aff0 _).mul (Dg.idx0 _))).of (by decide)
theorem d1_lgW : D1 2 lgW := by
  unfold lgW
  exact (D1.sumA _ _ (((Dg.aff0 _).mul (Dg.idx0 _)).sc _)).of (by decide)
theorem d1_k1Ex : D1 1 k1Ex := by
  unfold k1Ex
  exact ((D1.aff _).add ((D1.pub _).smul _)).of (by decide)
theorem d1_k2Ex : D1 1 k2Ex := by
  unfold k2Ex
  exact ((D1.aff _).add ((D1.pub _).smul _)).of (by decide)
theorem d1_mgEx : D1 2 mgEx := (((d1_lgW.sub d1_lgV).sub (D1.pub _)).sc _).of (by decide)

theorem d1_keyEx (np : NormPar) (f : Plain.Fam) : D1 2 (keyEx np f) := by
  cases f
  · exact (((D1.aff _).mul (D1.aff _)).add (D1.aff _)).of (by decide)
  · exact (D1.aff _).of (by decide)
  · exact ((d1_mgEx.sub (d1_k1Ex.smul _)).sub d1_k2Ex).of (by decide)
  · exact d1_k1Ex.of (by decide)
  · exact (D1.aff _).of (by decide)
  · exact d1_k2Ex.of (by decide)
  · exact (D1.aff _).of (by decide)

theorem head_nums (np : NormPar) :
    (segHead np).NumsLe 2 28 ∧
    (segHead np).idn.length = 17 ∧
    (segHead np).keys.length = 7 ∧
    ∀ q ∈ (segHead np).keys, q.2.T ≤ 16 := by
  refine ⟨⟨fun f hf => ?_, fun q hq => ?_⟩, by simp [segHead],
    by simp [segHead, allFam], fun q hq => ?_⟩
  · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hf
    exact ⟨fam_degLe (d1_ledEx np _ k fun s => d1_wsEx 10 13 blIn s), by show 10 ≤ 28; decide⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hq
    exact ⟨fam_degLe (d1_keyEx np f), by cases f <;> (show _ + 10 ≤ 28) <;> decide⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hq
    show tabLog f ≤ 16
    cases f <;> decide

/-- The last segment: the head with the identity on y. -/
theorem headY_nums (np : NormPar) :
    (segHeadY np).NumsLe 2 28 ∧
    (segHeadY np).idn.length = 18 ∧
    (segHeadY np).keys.length = 7 ∧
    ∀ q ∈ (segHeadY np).keys, q.2.T ≤ 16 := by
  obtain ⟨a, b, c, d⟩ := head_nums np
  refine ⟨⟨fun f hf => ?_, a.2⟩, ?_, c, d⟩
  · rcases List.mem_cons.1 (show f ∈ idY :: (segHead np).idn from hf) with rfl | hf
    · refine ⟨⟨(Req.deg_le_iff _ _ _ 2).2 fun t ht => ?_, fun j w P e => ?_⟩, Nat.zero_le 28⟩
      · rw [List.mem_singleton.1
            (show t ∈ [(⟨fun x _ => if x.e < ppref.T then ((x.y.val : ℕ) : Cb.Gl.E) else 0,
                []⟩ : Term XI Cb.Gl.E)] from ht)]
        exact Nat.zero_le 2
      · cases e
    · exact a.1 f hf
  · show (idY :: (segHead np).idn).length = 18
    rw [List.length_cons, b]

/-! ## 2. Attention -/

section Att
variable [scl : Scl] {X E : Type} [Field E] [Algebra Cb.Gl.F E]

theorem dg_exProd {a : ℕ} {f : ℕ → Ex0 X E} : ∀ n, (∀ k < n, Dg a (f k)) → Dg (n * a) (exProd n f)
  | 0, _ => (Dg.con _).of (Nat.zero_le _)
  | n + 1, h =>
    ((dg_exProd n fun k hk => h k (Nat.lt_succ_of_lt hk)).mul (h n (Nat.lt_succ_self n))).of
      (by rw [Nat.succ_mul])

theorem d1_exAt2 (g : ℕ) : D1 (X := X) (E := E) 12 (exAt2 g) := by
  unfold exAt2
  exact ((D1.aff _).sub
      (D1.sumA _ _ (((Dg.aff0 _).mul (Dg.aff0 _)).mul (dg_exProd DA.lT fun _ _ => Dg.aff0 _)))).of
    (by decide)

theorem att_nums (g u0 : ℕ) (tb : Tables) :
    (attSpec (X := X) (E := E) g u0 tb).NumsLe 12 27 ∧
    (attSpec (X := X) (E := E) g u0 tb).idn.length = 12 ∧
    (attSpec (X := X) (E := E) g u0 tb).keys.length = 7 ∧
    ∀ q ∈ (attSpec (X := X) (E := E) g u0 tb).keys, q.2.T ≤ 16 := by
  refine ⟨⟨fun f hf => ?_, fun q hq => ?_⟩, ?_, rfl, fun q hq => ?_⟩
  · have hf' : f ∈ (List.range DA.lT).map (famAt1 g) ++ [famAt2 g, famAt3 g] := hf
    rw [List.mem_append, List.mem_map] at hf'
    rcases hf' with ⟨k, _, rfl⟩ | hf'
    · refine ⟨fam_degLe (D1.of (a := 1 + max 1 0) ?_ (by decide)), by show 5 + DA.lX ≤ 27; decide⟩
      exact (D1.aff _).mul ((D1.aff _).sub (D1.con _))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
      rcases hf' with rfl | rfl
      · exact ⟨fam_degLe (d1_exAt2 g), by show 5 + DA.lX ≤ 27; decide⟩
      · refine ⟨fam_degLe (D1.of (a := max 1 (max 1 1)) ?_ (by decide)),
          by show 5 + DA.lX ≤ 27; decide⟩
        exact (D1.aff _).sub (D1.sumA _ _ (Dg.aff0 _))
  · simp only [attSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨DegLe.of (affFam_degLe _ _) (by decide), by show 5 + DA.lM ≤ 27; decide⟩
    · exact ⟨DegLe.of (affFam_degLe _ _) (by decide), by show 5 + DA.lD ≤ 27; decide⟩
    · refine ⟨fam_degLe (D1.of (a := max 1 (max 1 (1 + 1))) ?_ (by decide)),
        by show 5 + DA.lM ≤ 27; decide⟩
      exact (D1.aff _).sub (D1.sumA _ _ ((Dg.aff0 _).mul (Dg.aff0 _)))
    · refine ⟨fam_degLe (D1.of (a := max 1 (max 1 (1 + 1))) ?_ (by decide)),
        by show 5 + DA.lD ≤ 27; decide⟩
      exact (D1.aff _).sub (D1.sumA _ _ ((Dg.aff0 _).mul (Dg.aff0 _)))
    · refine ⟨fam_degLe (D1.of (a := max (max (max (max 1 (1 + 1)) 1) (1 + 1)) 1) ?_ (by decide)),
        by show 5 + DA.lW ≤ 27; decide⟩
      exact ((((D1.sumA _ _ ((Dg.aff0 _).mul (Dg.aff0 _))).smul _).add (D1.aff _)).sub
          (((D1.aff _).mul (D1.aff _)).smul _)).sc _
        |>.add (D1.aff _)
    · exact ⟨DegLe.of (affFam_degLe _ _) (by decide), by show 5 + DA.lX ≤ 27; decide⟩
    · exact ⟨DegLe.of (affFam_degLe _ _) (by decide), by show 5 + DA.l4 ≤ 27; decide⟩
  · show ((List.range DA.lT).map (famAt1 (X := X) (E := E) g) ++ [famAt2 g, famAt3 g]).length = 12
    simp
    decide
  · simp only [attSpec, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact le_refl _

end Att

/-! ## 3. Feed-forward (`ffSeg`) -/

section FF
variable [scl : Scl] {X : Type}

theorem qspec_degLe {E : Type} [Field E] (S : QSpec X E) : S.fam.DegLe 2 := by
  refine ⟨(Req.deg_le_iff X E _ 2).2 fun t ht => ?_, fun j w P e => ?_⟩
  · have ht' : t ∈
        (⟨fun _ _ => 1, [0]⟩ : Term X E) :: ⟨fun _ _ => 1, [1]⟩ ::
          (List.range S.nQ).map fun n => (⟨fun _ _ => 1, [2 * n + 2, 2 * n + 3]⟩ : Term X E) := ht
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact Nat.le_succ 1
    · rcases List.mem_cons.1 ht' with rfl | ht'
      · exact Nat.le_succ 1
      · obtain ⟨n, _, rfl⟩ := List.mem_map.1 ht'
        exact le_refl _
  · have e' : (if j = 0 then Atom.sum S.w S.inner
          else if j = 1 then .base (.cell S.a)
          else .base (.cell (if j % 2 = 0 then S.f ((j - 2) / 2) else S.g ((j - 2) / 2)))) =
        Atom.sum w P := e
    split_ifs at e'
    cases e'
    refine (Req.deg_le_iff X E _ 2).2 fun t ht => ?_
    obtain ⟨n, _, rfl⟩ := List.mem_map.1
      (show t ∈ (List.range S.nS).map fun n => (⟨S.κ n, [2 * n, 2 * n + 1]⟩ : Term X E) from ht)
    exact le_refl _

theorem dg_cellsE {E : Type} [Field E] (vx w : ℕ) :
    ∀ fs : List (ℕ → ℕ → ℕ → ℕ → CForm E), Dg (X := X) fs.length (cellsE vx w fs)
  | [] => Dg.con _
  | _ :: l => ((Dg.aff0 _).mul (dg_cellsE vx w l)).of (by rw [List.length_cons, Nat.add_comm])

theorem d1_blk {E : Type} [Field E] (vx w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → E)
    (fs : List (ℕ → ℕ → ℕ → ℕ → CForm E)) (ia : ℕ → IdxAtom E) :
    D1 (X := X) (max 1 (fs.length + 1)) (blk vx w n c fs ia) :=
  D1.sumA _ _ (Dg.pSum fun _ _ => ((dg_cellsE vx w fs).mul (Dg.idx0 _)).sc _)

theorem d1_wpart (g : ℕ) (tb : Tables) (s : FFSeg.Fam) : D1 (X := X) 4 (wpart g tb s) := by
  cases s <;> first
    | exact D1.zero.of (by decide)
    | exact (d1_blk _ _ _ _ _ _).of (by simp)
    | exact ((d1_blk _ _ _ _ _ _).add (d1_blk _ _ _ _ _ _)).of (by simp)

theorem vx_le (s : FFSeg.Fam) : vxOf s ≤ 14 := Nat.clog_le_of_le_pow (by cases s <;> decide)

theorem kfAll_nums (g : ℕ) (tb : Tables) (s : FFSeg.Fam) :
    (kfAll (X := X) g tb s).DegLe 4 ∧ (kfAll (X := X) g tb s).v ≤ 26 := by
  have hv := vx_le s
  unfold kfAll
  split_ifs
  · exact ⟨DegLe.of (affFam_degLe _ _) (by decide), by show 2 + vxOf s + 10 ≤ 26; omega⟩
  · exact ⟨DegLe.of (qspec_degLe _) (by decide), by show 2 + vxOf s + 10 ≤ 26; omega⟩
  · exact ⟨fam_degLe (((D1.aff _).add (d1_wpart g tb s)).of (by decide)),
      by show 2 + vxOf s + 10 ≤ 26; omega⟩

theorem idnFams_nums (g : ℕ) (tok : X → ℕ → ℕ) :
    (∀ f ∈ idnFams g tok, f.DegLe 4 ∧ f.v ≤ 26) ∧ (idnFams g tok).length ≤ 19 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · rcases (mem_idnFams g tok f).1 hf with ⟨k, _, rfl⟩ | rfl | ⟨_, rfl⟩
    · exact ⟨DegLe.of (qspec_degLe _) (by decide), by show 3 + 10 ≤ 26; decide⟩
    · exact ⟨DegLe.of (affFam_degLe _ _) (by decide), by show 1 + 10 ≤ 26; decide⟩
    · refine ⟨DegLe.of (a := 1) (famL_degLe (fun t ht => ?_) fun a ha w P e => ?_) (by decide),
        by show 23 ≤ 26; decide⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> exact le_refl _
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> cases e
        refine (Req.deg_le_iff X Cb.Gl.E _ 1).2 fun t ht => ?_
        have ht' : t ∈ [(⟨κ11 tok, [0]⟩ : Term X Cb.Gl.E)] := ht
        rw [List.mem_singleton] at ht'
        subst ht'
        exact le_refl _
  · unfold idnFams
    split_ifs <;> simp

end FF

theorem ff_nums {X : Type} (κ : ℕ → LayerScale) (nf : NormPar) (g : ℕ) (tok : X → ℕ → ℕ) :
    (ffSeg κ nf g tok).NumsLe 4 26 ∧
    (ffSeg κ nf g tok).idn.length ≤ 19 ∧
    (ffSeg κ nf g tok).keys.length = 34 ∧
    ∀ q ∈ (ffSeg κ nf g tok).keys, q.2.T ≤ 16 := by
  letI : Scl := SFK κ nf g
  refine ⟨⟨(idnFams_nums g tok).1, fun q hq => ?_⟩,
    (idnFams_nums g tok).2,
    by simp [ffSeg, ffSpec, allFams],
    fun q hq => ?_⟩
  · obtain ⟨s, _, rfl⟩ := List.mem_map.1 hq
    exact kfAll_nums g tbRef s
  · obtain ⟨s, _, rfl⟩ := List.mem_map.1 hq
    show tOf s ≤ 16
    unfold tOf
    split_ifs <;> decide

/-! ## 4. All 25 segments -/

theorem NumsLe.of {X F E : Type} [Field E] {S : SegSpec X F E} {a b d V : ℕ} (h : S.NumsLe a b)
    (h1 : a ≤ d) (h2 : b ≤ V) : S.NumsLe d V :=
  ⟨fun f hf => ⟨DegLe.of (h.1 f hf).1 h1, le_trans (h.1 f hf).2 h2⟩,
    fun k hk => ⟨DegLe.of (h.2 k hk).1 h1, le_trans (h.2 k hk).2 h2⟩⟩

/-- Every segment of the model. -/
theorem segM_nums (s : Scales) (k : ℕ) :
    (segM s k).NumsLe 12 28 ∧
    (segM s k).idn.length ≤ 19 ∧
    (segM s k).keys.length ≤ 34 ∧
    ∀ q ∈ (segM s k).keys, q.2.T ≤ 16 := by
  unfold segM segOf
  split_ifs
  · obtain ⟨a, b, c, d⟩ := headY_nums s.nf
    exact ⟨NumsLe.of a (by decide) (by decide), by rw [b]; decide, by rw [c]; decide, d⟩
  · obtain ⟨a, b, c, d⟩ := ff_nums s.kap s.nf (k / 2) tokX
    exact ⟨NumsLe.of a (by decide) (by decide), b, by rw [c], d⟩
  · obtain ⟨a, b, c, d⟩ := att_nums (scl := SFK s.kap s.nf (k / 2)) (X := XI) (E := Cb.Gl.E) (k / 2)
      (s.kap (4 * (k / 2))).expRows.toNat tbRef
    exact ⟨NumsLe.of a (by decide) (by decide),
      by rw [show (attM s (k / 2)).idn.length = 12 from b]; decide,
      by rw [show (attM s (k / 2)).keys.length = 7 from c]; decide,
      d⟩

/-- The shapes of the matrices of cells. -/
theorem segM_shape (s : Scales) (k : ℕ) :
    (segM s k).rowsLog = rowsLog k ∧ (segM s k).cols = cols k ∧ rowsLog k ≤ 19 ∧ cols k ≤ 7200 := by
  obtain ⟨_, f1, f2, f3, _⟩ := lay_figures
  refine ⟨?_, ?_, by unfold rowsLog; split_ifs <;> decide,
    by unfold cols; rw [f1, f2, f3]; split_ifs <;> decide⟩
  · unfold segM segOf
    split_ifs with h1 h2
    · rw [h1]; rfl
    · show 19 = rowsLog k
      unfold rowsLog
      rw [if_neg (by omega)]
    · show 18 = rowsLog k
      unfold rowsLog
      rw [if_pos (by omega)]
  · unfold segM segOf
    split_ifs with h1 h2
    · rw [h1]; rfl
    · show colsFF = cols k
      unfold cols
      rw [if_neg h1, if_neg (by omega)]
    · show colsAtt = cols k
      unfold cols
      rw [if_neg h1, if_pos (by omega)]

end Cm.Seg.TS
