-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyLaw.lean: small lemmas for proving that a part's distribution
over its coins is its simulator's (the fields `exact` and `fresh` of `Good`, Honest/Side.lean).
Despite its name, the file contains no example and names no sub-protocol.

  1  `map_unif_by_equiv`, `map_unif_fst_equiv`, `map_unif_point`   two functions of uniform coins
     have the same distribution: where a bijection of the coins onto β, or onto β × δ, takes the one
     to a function g of β; where both are constant
  2  `Cs.ext'`, `Cs.one`, `Cs.two`, `Cs.eq0`, `Cs.eq1`, `Cs.eq2`, `Cs.eq1u`, `Cs.eq2u`,
     `Cs.eq01u`   coins of a small count as elements of the base field
  3  `shear`, `rot`   two bijections on pairs and triples of elements
  4  `spentBy_nil`, `fresh_of_nil`   where a part spends nothing of an owner, the two distributions
     of `fresh` are the same
  5  `drawsFit_one`, `drawsFit_two`, `one_of_length`, `ofF_toF_zero`   lists of one and of two
     challenges; the word 0

From the library: `Iop.MaskKit.map_unif_of_equiv` (Ior/KnowCollRulesMaskProofs.lean),
`map_fst_unif`, `map_snd_unif` (Prob/Count.lean).

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Side
import Ior.KnowCollRulesMaskProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob

/-! ## 1 The same distribution -/

section
variable {α β γ δ : Type}

/-- A bijection e of the coins onto β, and f = g after e: f has the same distribution as g. -/
theorem map_unif_by_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) (g : β → γ)
    (f : α → γ) (h : ∀ a, f a = g (e a)) : (unif α).map f = (unif β).map g := by
  have hf : f = fun a => g (e a) := funext h
  subst hf
  exact Iop.MaskKit.map_unif_of_equiv e g

/-- A bijection e of the coins onto β × δ, and f = g after the first component of e: f has the same
distribution as g. -/
theorem map_unif_fst_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] [Fintype δ]
    [Nonempty δ] (e : α ≃ β × δ) (g : β → γ) (f : α → γ) (h : ∀ a, f a = g (e a).1) :
    (unif α).map f = (unif β).map g := by
  have h1 : (unif α).map f = (unif (β × δ)).map (g ∘ Prod.fst) :=
    map_unif_by_equiv e (g ∘ Prod.fst) f h
  rw [h1, ← PMF.map_comp, map_fst_unif]

/-- Two constant functions with the same value have the same distribution. -/
theorem map_unif_point [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (x : γ) (f : α → γ)
    (f' : β → γ) (h : ∀ a, f a = x) (h' : ∀ b, f' b = x) : (unif α).map f = (unif β).map f' := by
  have hf : f = Function.const α x := funext h
  have hf' : f' = Function.const β x := funext h'
  rw [hf, hf', PMF.map_const, PMF.map_const]

end

/-! ## 2 Coins of a small count -/

/-- Two lists of coins with the same entries are equal. -/
theorem Cs.ext' {d : Due} {a b : Cs d} (hf : ∀ i, a.f i = b.f i) (he : ∀ i, a.e i = b.e i) :
    a = b := by
  cases a
  cases b
  simp only [Cs.mk.injEq]
  exact ⟨funext hf, funext he⟩

/-- One coin of the base field. -/
def Cs.one (x : Cb.Gl.F) : Cs ⟨1, 0⟩ := ⟨fun _ => x, fun i => i.elim0⟩

/-- Two coins of the base field. -/
def Cs.two (t u : Cb.Gl.F) : Cs ⟨2, 0⟩ := ⟨fun i => if i.1 = 0 then t else u, fun i => i.elim0⟩

def Cs.eq0 : Cs ⟨0, 0⟩ ≃ Unit where
  toFun _ := ()
  invFun _ := Cs.empty
  left_inv _ := Cs.ext' (fun i => i.elim0) (fun i => i.elim0)
  right_inv _ := rfl

def Cs.eq1 : Cs ⟨1, 0⟩ ≃ Cb.Gl.F where
  toFun c := c.f ⟨0, by decide⟩
  invFun x := Cs.one x
  left_inv c := Cs.ext'
    (fun i => congrArg c.f (Fin.ext (by
      have h : i.1 < 1 := i.2
      show 0 = i.1
      omega)))
    (fun i => i.elim0)
  right_inv _ := rfl

def Cs.eq2 : Cs ⟨2, 0⟩ ≃ Cb.Gl.F × Cb.Gl.F where
  toFun c := (c.f ⟨0, by decide⟩, c.f ⟨1, by decide⟩)
  invFun x := Cs.two x.1 x.2
  left_inv c := Cs.ext'
    (fun i => by
      have h : i.1 < 2 := i.2
      by_cases h0 : i.1 = 0
      · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
        subst hi
        rfl
      · have hi : i = ⟨1, by decide⟩ := Fin.ext (by
          show i.1 = 1
          omega)
        subst hi
        rfl)
    (fun i => i.elim0)
  right_inv _ := rfl

/-- A bijection: one coin, beside no block of coins, as a field element. -/
def Cs.eq1u : Cs ⟨1, 0⟩ × Unit ≃ Cb.Gl.F where
  toFun c := c.1.f ⟨0, by decide⟩
  invFun x := (Cs.one x, ())
  left_inv c := Prod.ext (Cs.eq1.left_inv c.1) rfl
  right_inv _ := rfl

/-- A bijection: two coins, beside no block of coins, as two field elements. -/
def Cs.eq2u : Cs ⟨2, 0⟩ × Unit ≃ Cb.Gl.F × Cb.Gl.F where
  toFun c := (c.1.f ⟨0, by decide⟩, c.1.f ⟨1, by decide⟩)
  invFun x := (Cs.two x.1 x.2, ())
  left_inv c := Prod.ext (Cs.eq2.left_inv c.1) rfl
  right_inv _ := rfl

/-- A bijection: no coin, beside one block of one coin, as a field element. -/
def Cs.eq01u : Cs ⟨0, 0⟩ × (Cs ⟨1, 0⟩ × Unit) ≃ Cb.Gl.F where
  toFun c := c.2.1.f ⟨0, by decide⟩
  invFun x := (Cs.empty, (Cs.one x, ()))
  left_inv c := Prod.ext (Cs.eq0.left_inv c.1) (Cs.eq1u.left_inv c.2)
  right_inv _ := rfl

/-! ## 3 Two bijections -/

/-- (t, u) to (A + t + u + u, u). -/
def shear (A : Cb.Gl.F) : Cb.Gl.F × Cb.Gl.F ≃ Cb.Gl.F × Cb.Gl.F where
  toFun x := (A + x.1 + x.2 + x.2, x.2)
  invFun y := (y.1 - y.2 - y.2 - A, y.2)
  left_inv x := by
    refine Prod.ext ?_ rfl
    show A + x.1 + x.2 + x.2 - x.2 - x.2 - A = x.1
    ring
  right_inv y := by
    refine Prod.ext ?_ rfl
    show A + (y.1 - y.2 - y.2 - A) + y.2 + y.2 = y.1
    ring

/-- (a, (y, u)) to ((y, a), u). -/
def rot {A B C : Type} : A × (B × C) ≃ (B × A) × C where
  toFun x := ((x.2.1, x.1), x.2.2)
  invFun w := (w.1.2, (w.1.1, w.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## 4 Where nothing is spent -/

/-- If the book has no entry by which the part at p spends coins of the part at o,
`ProverCoinCounts.spentBy o p` is empty. -/
theorem spentBy_nil (B : ProverCoinCounts) (o p : Addr)
    (h : ∀ e ∈ B.ahead, e.once = true → e.owner = o → e.spender ≠ p) : B.spentBy o p = [] := by
  unfold ProverCoinCounts.spentBy
  rw [List.filter_eq_nil_iff]
  intro e he hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact h e he hc.2 hc.1.1 hc.1.2

/-- **Where the list of spent blocks is empty, the two distributions of `Good.fresh` are the same.**
`S`: what the owner shows. `K`: its other coins that are passed on. -/
theorem fresh_of_nil {γ δ : Type} {d : Due} (es : List Ahead) (hes : es = []) (S : Cs d → γ)
    (K : Cs d → δ) :
    (unif (Cs d)).map (fun c => (cutAll c es, S c, K c)) =
      (unif (CsAll (es.map Ahead.named) × Cs d)).map fun a => (some a.1, S a.2, K a.2) := by
  subst hes
  have h : (unif (CsAll (([] : List Ahead).map Ahead.named) × Cs d)).map
        ((fun c : Cs d => (cutAll c [], S c, K c)) ∘ Prod.snd) =
      (unif (Cs d)).map fun c => (cutAll c [], S c, K c) := by
    rw [← PMF.map_comp, map_snd_unif]
  exact h.symm

/-! ## 5 Lists of one and of two challenges -/

theorem drawsFit_one {d : Fmt.DeclaredRound} {ds : List Fmt.Drawn} (h : drawsFit [d] ds = true) :
    ∃ R, ds = [R] ∧ drawFit d R = true := by
  match ds, h with
  | [R], h => exact ⟨R, rfl, by simpa [drawsFit] using h⟩
  | [], h => simp [drawsFit] at h
  | _ :: _ :: _, h => simp [drawsFit] at h

theorem drawsFit_two {d₀ d₁ : Fmt.DeclaredRound} {ds : List Fmt.Drawn}
    (h : drawsFit [d₀, d₁] ds = true) :
    ∃ R₀ R₁, ds = [R₀, R₁] ∧ drawFit d₀ R₀ = true ∧ drawFit d₁ R₁ = true := by
  match ds, h with
  | [R₀, R₁], h => exact ⟨R₀, R₁, rfl, by simpa [drawsFit] using h⟩
  | [], h => simp [drawsFit] at h
  | [_], h => simp [drawsFit] at h
  | _ :: _ :: _ :: _, h => simp [drawsFit] at h

theorem one_of_length {α : Type} {l : List α} (h : l.length = 1) : ∃ a, l = [a] := by
  match l, h with
  | [a], _ => exact ⟨a, rfl⟩
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

/-- The word 0, read as a field element and converted back to a word, is 0. -/
theorem ofF_toF_zero : OnBytes.Slice.ofF (OnBytes.Slice.toF 0) = 0 := by
  have h : OnBytes.Slice.ofF (0 : Cb.Gl.F) = 0 := congrArg UInt64.ofNat ZMod.val_zero
  rw [OnBytes.Slice.toF_zero]
  exact h

end ProofFile.Honest

#print axioms ProofFile.Honest.map_unif_by_equiv
#print axioms ProofFile.Honest.map_unif_fst_equiv
#print axioms ProofFile.Honest.map_unif_point
#print axioms ProofFile.Honest.Cs.ext'
#print axioms ProofFile.Honest.spentBy_nil
#print axioms ProofFile.Honest.fresh_of_nil
#print axioms ProofFile.Honest.drawsFit_one
#print axioms ProofFile.Honest.drawsFit_two
#print axioms ProofFile.Honest.one_of_length
#print axioms ProofFile.Honest.ofF_toF_zero
