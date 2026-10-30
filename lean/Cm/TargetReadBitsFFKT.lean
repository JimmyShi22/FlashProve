-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsFFKT.lean: a value of a feed-forward segment at the vertex (layer ℓ, index x,
position i), under a guard and with a coefficient that read ℓ and the high bits of x, is separable
at a row side that depends on the group g, on vx and on its matrix alone (in `termLo`, `termHi` also
on OFF X mod 2^f), under the premises below.

Four main theorems (`term0`, `termLo`, `termHi`, `termAny`): Cm/TargetReadBitsFldFF.lean's four
rules on values, in the coordinates (ℓ, x, i) of `dec3` (Cm/SegAlg.lean). Stated and proved in one
file.

A row side W (`RowT`, Cm/TargetReadBitsFldRow.lean) is a segment seg, lists cs, rs of row and column
sources, a guard gT on t, a row map ρ and a list L of block numbers; t and u are the numbers that cs
and rs form at the vertex. A value function is separable at W up to a constant (`SepK`) if there are
column tables β, the same at all vertices, such that at each vertex b and for all matrices A its
value is a constant k b plus, where gT t holds, Σ_{j ∈ L} Σ_{y < C seg} β j u y · A seg (ρ t j) y;
and where gT t holds, the row ρ t j is below R seg wherever β j u y is not 0 (j ∈ L, y < C seg).

Main names:
  `W3 g slot Q vx f`: the row side: the low f bits of x and the position; `W3Lo`, `W3Hi` with a
    further c₀: with the guard "no carry" / "carry" of c₀ + (x mod 2^f); `WA g slot Q vx f`: the
    fall-back: the position alone.
  The form: b ↦ if G ℓ (x / 2^f) then cf ℓ (x / 2^f) · (cVal g X (a ℓ) (x − 2^f · x0) i).val A else
    0 (x0: where the array's channels begin among the family's indices, in units of 2^f; in the four
    theorems f = `fBitsX X`, slot = `slotFF X.mx`, Q = `nPartX X`, c₀ = OFF X mod 2^f).
  `term0`: 2^f ∣ OFF X, 2^f ∣ width X: SepK at W3.
  `termLo`, `termHi`: 2^f ∣ width X: the form under the further guard on x mod 2^f: SepK at W3Lo,
    W3Hi.
  `termAny`: b ↦ if G ℓ x then cf ℓ x · (cVal g X (a ℓ x) (j ℓ x) i).val A else 0: SepK at WA.
  Premises: the array X is not `.x0` in a group g > 0; f ≤ vx; for ℓ < 4 and xh < 2^(vx − f) under
    G: x0 ≤ xh, a ℓ < cnt X, 2^f · (xh − x0) + 2^f ≤ width X; every place of a valid cell that the
    segment reads lies in the shapes. In `termAny` the second falls away, and the third is: for ℓ <
    4 and x < 2^vx under G: a ℓ x < cnt X, j ℓ x < width X.

Limits: what the head of Cm/TargetReadBitsFldFF.lean lists as not said is not said here either. That
is: that the families' atoms have this form; anything on the look-up's bits (matrix b); that so many
pieces are needed.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetReadBitsFFK3
import Cm.TargetReadBitsFldFF

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TR

open Cb Blocks Finset Inst.Model Inst.Model.All Cm.Seg

abbrev W3 (g slot Q vx f : ℕ) : RowT :=
  rowF (2 * g) (cs3 vx f) (rs3 vx f) (fun _ => True) (fun t => t / 2 ^ 10)
    (fun t => t % 2 ^ 10) DF.T slot Q
abbrev W3Lo (g slot Q vx f c₀ : ℕ) : RowT :=
  rowF (2 * g) (cs3 vx f) (rs3 vx f) (fun t => True ∧ c₀ + t / 2 ^ 10 < 2 ^ f)
    (fun t => c₀ + t / 2 ^ 10) (fun t => t % 2 ^ 10) DF.T slot Q
abbrev W3Hi (g slot Q vx f c₀ : ℕ) : RowT :=
  rowF (2 * g) (cs3 vx f) (rs3 vx f) (fun t => True ∧ 2 ^ f ≤ c₀ + t / 2 ^ 10)
    (fun t => c₀ + t / 2 ^ 10 - 2 ^ f) (fun t => t % 2 ^ 10) DF.T slot Q
abbrev WA (g slot Q vx f : ℕ) : RowT :=
  rowAny (2 * g) (csA vx) (rsA vx) (fun _ => True) (fun t => t) f DF.T slot Q

variable {E : Type} [Field E]

theorem chan_eq (M x x0 : ℕ) (h : x0 ≤ x / M) : M * (x / M - x0) + x % M = x - M * x0 := by
  have h1 := Nat.div_add_mod x M
  have h2 : M * (x / M - x0) = M * (x / M) - M * x0 := Nat.mul_sub M (x / M) x0
  have h3 : M * x0 ≤ M * (x / M) := Nat.mul_le_mul_left M h
  omega

theorem term0 (R C : ℕ → ℕ) (g : ℕ) (X : FFSeg.Arr) (vx : ℕ) (G : ℕ → ℕ → Prop)
    [∀ l xh, Decidable (G l xh)] (cf : ℕ → ℕ → E) (a : ℕ → ℕ) (x0 : ℕ) (hX : ¬ (X = .x0 ∧ 0 < g))
    (hf : fBitsX X ≤ vx) (hO : 2 ^ fBitsX X ∣ FFSeg.OFF DF X) (hW : 2 ^ fBitsX X ∣ X.width DF)
    (hG : ∀ l < 4, ∀ xh < 2 ^ (vx - fBitsX X),
      G l xh → x0 ≤ xh ∧ a l < X.cnt DF ∧ 2 ^ fBitsX X * (xh - x0) + 2 ^ fBitsX X ≤ X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepK R C (2 + vx + 10) (W3 g (slotFF X.mx) (nPartX X) vx (fBitsX X)) fun b A =>
      if G (dec3 vx b).1 ((dec3 vx b).2.1 / 2 ^ fBitsX X) then
        cf (dec3 vx b).1 ((dec3 vx b).2.1 / 2 ^ fBitsX X) *
          (cVal g X (a (dec3 vx b).1) ((dec3 vx b).2.1 - 2 ^ fBitsX X * x0)
            (dec3 vx b).2.2 : CForm E).val A
      else 0 := by
  refine sepK_congr E R C _ _ _ _ (fun b hb A => ?_)
    (sepK_cVal0 R C (2 + vx + 10) g g X X (cs3 vx (fBitsX X)) (rs3 vx (fBitsX X)) (fun _ => True)
      (fun u => G (u / 2 ^ (vx - fBitsX X)) (u % 2 ^ (vx - fBitsX X)))
      (fun u => cf (u / 2 ^ (vx - fBitsX X)) (u % 2 ^ (vx - fBitsX X)))
      (fun u => a (u / 2 ^ (vx - fBitsX X))) (fun u => u % 2 ^ (vx - fBitsX X) - x0)
      (fun t => t / 2 ^ 10) (fun t => t % 2 ^ 10) (own_self g X hX) hO hW (fun b hb _ hU => ?_) hSh)
  · simp only [t3_lo vx _ b hf, t3_pos vx _ b hf, u3_l vx _ b hf hb, u3_hi vx _ b hf hb, true_and]
    by_cases hg : G (dec3 vx b).1 ((dec3 vx b).2.1 / 2 ^ fBitsX X)
    · rw [if_pos hg, if_pos hg, chan_eq _ _ _ (hG _ (dec3_l_lt vx b hb) _ (xh_lt vx _ b hf) hg).1]
    · rw [if_neg hg, if_neg hg]
  · simp only [t3_lo vx _ b hf, t3_pos vx _ b hf, u3_l vx _ b hf hb, u3_hi vx _ b hf hb] at hU ⊢
    obtain ⟨-, h2, h3⟩ := hG _ (dec3_l_lt vx b hb) _ (xh_lt vx _ b hf) hU
    exact ⟨Nat.mod_lt _ (by positivity), dec3_i_lt vx b, h2, h3⟩

theorem termLo (R C : ℕ → ℕ) (g : ℕ) (X : FFSeg.Arr) (vx : ℕ) (G : ℕ → ℕ → Prop)
    [∀ l xh, Decidable (G l xh)] (cf : ℕ → ℕ → E) (a : ℕ → ℕ) (x0 : ℕ)
    (hX : ¬ (X = .x0 ∧ 0 < g)) (hf : fBitsX X ≤ vx) (hW : 2 ^ fBitsX X ∣ X.width DF)
    (hG : ∀ l < 4, ∀ xh < 2 ^ (vx - fBitsX X),
      G l xh → x0 ≤ xh ∧ a l < X.cnt DF ∧ 2 ^ fBitsX X * (xh - x0) + 2 ^ fBitsX X ≤ X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepK R C (2 + vx + 10) (W3Lo g (slotFF X.mx) (nPartX X) vx (fBitsX X) (FFSeg.OFF DF X % 2 ^ fBitsX X)) fun b A =>
      if FFSeg.OFF DF X % 2 ^ fBitsX X + (dec3 vx b).2.1 % 2 ^ fBitsX X < 2 ^ fBitsX X ∧
          G (dec3 vx b).1 ((dec3 vx b).2.1 / 2 ^ fBitsX X) then
        cf (dec3 vx b).1 ((dec3 vx b).2.1 / 2 ^ fBitsX X) *
          (cVal g X (a (dec3 vx b).1) ((dec3 vx b).2.1 - 2 ^ fBitsX X * x0)
            (dec3 vx b).2.2 : CForm E).val A
      else 0 := by
  refine sepK_congr E R C _ _ _ _ (fun b hb A => ?_)
    (sepK_cValLo R C (2 + vx + 10) g g X X (cs3 vx (fBitsX X)) (rs3 vx (fBitsX X)) (fun _ => True)
      (fun u => G (u / 2 ^ (vx - fBitsX X)) (u % 2 ^ (vx - fBitsX X)))
      (fun u => cf (u / 2 ^ (vx - fBitsX X)) (u % 2 ^ (vx - fBitsX X)))
      (fun u => a (u / 2 ^ (vx - fBitsX X))) (fun u => u % 2 ^ (vx - fBitsX X) - x0)
      (fun t => t / 2 ^ 10) (fun t => t % 2 ^ 10) (own_self g X hX) hW (fun b hb _ hU => ?_) hSh)
  · simp only [t3_lo vx _ b hf, t3_pos vx _ b hf, u3_l vx _ b hf hb, u3_hi vx _ b hf hb, true_and]
    by_cases hg : FFSeg.OFF DF X % 2 ^ fBitsX X + (dec3 vx b).2.1 % 2 ^ fBitsX X < 2 ^ fBitsX X ∧
      G (dec3 vx b).1 ((dec3 vx b).2.1 / 2 ^ fBitsX X)
    · rw [if_pos hg, if_pos hg, chan_eq _ _ _ (hG _ (dec3_l_lt vx b hb) _ (xh_lt vx _ b hf) hg.2).1]
    · rw [if_neg hg, if_neg hg]
  · simp only [t3_lo vx _ b hf, t3_pos vx _ b hf, u3_l vx _ b hf hb, u3_hi vx _ b hf hb] at hU ⊢
    obtain ⟨-, h2, h3⟩ := hG _ (dec3_l_lt vx b hb) _ (xh_lt vx _ b hf) hU
    exact ⟨Nat.mod_lt _ (by positivity), dec3_i_lt vx b, h2, h3⟩

theorem termHi (R C : ℕ → ℕ) (g : ℕ) (X : FFSeg.Arr) (vx : ℕ) (G : ℕ → ℕ → Prop)
    [∀ l xh, Decidable (G l xh)] (cf : ℕ → ℕ → E) (a : ℕ → ℕ) (x0 : ℕ)
    (hX : ¬ (X = .x0 ∧ 0 < g)) (hf : fBitsX X ≤ vx) (hW : 2 ^ fBitsX X ∣ X.width DF)
    (hG : ∀ l < 4, ∀ xh < 2 ^ (vx - fBitsX X),
      G l xh → x0 ≤ xh ∧ a l < X.cnt DF ∧ 2 ^ fBitsX X * (xh - x0) + 2 ^ fBitsX X ≤ X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepK R C (2 + vx + 10) (W3Hi g (slotFF X.mx) (nPartX X) vx (fBitsX X) (FFSeg.OFF DF X % 2 ^ fBitsX X)) fun b A =>
      if 2 ^ fBitsX X ≤ FFSeg.OFF DF X % 2 ^ fBitsX X + (dec3 vx b).2.1 % 2 ^ fBitsX X ∧
          G (dec3 vx b).1 ((dec3 vx b).2.1 / 2 ^ fBitsX X) then
        cf (dec3 vx b).1 ((dec3 vx b).2.1 / 2 ^ fBitsX X) *
          (cVal g X (a (dec3 vx b).1) ((dec3 vx b).2.1 - 2 ^ fBitsX X * x0)
            (dec3 vx b).2.2 : CForm E).val A
      else 0 := by
  refine sepK_congr E R C _ _ _ _ (fun b hb A => ?_)
    (sepK_cValHi R C (2 + vx + 10) g g X X (cs3 vx (fBitsX X)) (rs3 vx (fBitsX X)) (fun _ => True)
      (fun u => G (u / 2 ^ (vx - fBitsX X)) (u % 2 ^ (vx - fBitsX X)))
      (fun u => cf (u / 2 ^ (vx - fBitsX X)) (u % 2 ^ (vx - fBitsX X)))
      (fun u => a (u / 2 ^ (vx - fBitsX X))) (fun u => u % 2 ^ (vx - fBitsX X) - x0)
      (fun t => t / 2 ^ 10) (fun t => t % 2 ^ 10) (own_self g X hX) hW (fun b hb _ hU => ?_) hSh)
  · simp only [t3_lo vx _ b hf, t3_pos vx _ b hf, u3_l vx _ b hf hb, u3_hi vx _ b hf hb, true_and]
    by_cases hg : 2 ^ fBitsX X ≤ FFSeg.OFF DF X % 2 ^ fBitsX X + (dec3 vx b).2.1 % 2 ^ fBitsX X ∧
      G (dec3 vx b).1 ((dec3 vx b).2.1 / 2 ^ fBitsX X)
    · rw [if_pos hg, if_pos hg, chan_eq _ _ _ (hG _ (dec3_l_lt vx b hb) _ (xh_lt vx _ b hf) hg.2).1]
    · rw [if_neg hg, if_neg hg]
  · simp only [t3_lo vx _ b hf, t3_pos vx _ b hf, u3_l vx _ b hf hb, u3_hi vx _ b hf hb] at hU ⊢
    obtain ⟨-, h2, h3⟩ := hG _ (dec3_l_lt vx b hb) _ (xh_lt vx _ b hf) hU
    exact ⟨Nat.mod_lt _ (by positivity), dec3_i_lt vx b, h2, h3⟩

theorem termAny (R C : ℕ → ℕ) (g : ℕ) (X : FFSeg.Arr) (vx : ℕ) (G : ℕ → ℕ → Prop)
    [∀ l x, Decidable (G l x)] (cf : ℕ → ℕ → E) (a j : ℕ → ℕ → ℕ) (hX : ¬ (X = .x0 ∧ 0 < g))
    (hG : ∀ l < 4, ∀ x < 2 ^ vx, G l x → a l x < X.cnt DF ∧ j l x < X.width DF)
    (hSh : ∀ p : Cb.Place, IsFF g p → p.2.1 < R p.1 ∧ p.2.2 < C p.1) :
    SepK R C (2 + vx + 10) (WA g (slotFF X.mx) (nPartX X) vx (fBitsX X)) fun b A =>
      if G (dec3 vx b).1 (dec3 vx b).2.1 then
        cf (dec3 vx b).1 (dec3 vx b).2.1 *
          (cVal g X (a (dec3 vx b).1 (dec3 vx b).2.1)
            (j (dec3 vx b).1 (dec3 vx b).2.1) (dec3 vx b).2.2 : CForm E).val A
      else 0 := by
  refine sepK_congr E R C _ _ _ _ (fun b hb A => ?_)
    (sepK_cValAny R C (2 + vx + 10) g g X X (csA vx) (rsA vx) (fun _ => True)
      (fun u => G (u / 2 ^ vx) (u % 2 ^ vx)) (fun u => cf (u / 2 ^ vx) (u % 2 ^ vx))
      (fun u => a (u / 2 ^ vx) (u % 2 ^ vx)) (fun u => j (u / 2 ^ vx) (u % 2 ^ vx)) (fun t => t)
      (own_self g X hX) (fun b hb _ hU => ?_) hSh)
  · simp only [num_csA vx b, uA_l vx b hb, uA_x vx b hb, true_and]
  · simp only [num_csA vx b, uA_l vx b hb, uA_x vx b hb] at hU ⊢
    obtain ⟨h2, h3⟩ := hG _ (dec3_l_lt vx b hb) _ (dec3_x_lt vx b) hU
    exact ⟨dec3_i_lt vx b, h2, h3⟩

end Cm.TR
