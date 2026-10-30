-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/HostT.lean: a frame's letters (`Host`, Cb/Pv/Tail/InLink.lean) whose reads are given by
tables (Cb/Pv/Tail/Tables.lean).

`Host` has the reads' weights, the symbols and the reads as functions on finite index sets. The
letters with tables (`TLetters`) have the tables' weights, the symbols and the vector of reads at
plain numbers. This file says when a `Host` is of the second kind, and carries two statements over.

Main names:
  `IsT Q phi symN u3N`: the weights of Q are the tables' weights `phi` on their stretches, the
    symbols are `symN`, the reads are the entries of the vector `u3N` at the tables' places.
  `thetaQ Q phi symN u3N`: the letters with tables on Q's types.
  `eqs_thetaQ`: every tie and read at `(thetaQ ..).letters` is one at `Q.let`.
  `hk_thetaQ`: a read of Q that stands for no segment of a table has weights 0 and values 0.



Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.ClaimsT
import Cb.Pv.Tail.ClOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open TWhole

variable {K : Type} [Field K] {t : TSize} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
  (Q : Host K t.size J₁ J₂) (phi : Q.Xe → ℕ → ℕ → K) (symN : Q.M₁ → ℕ → ℕ → ℕ → K)
  (u3N : Q.U₁ → ℕ → K)

/-- The reads of Q are given by the tables of t. -/
structure IsT : Prop where
  w : ∀ e μ r i, Q.w e μ r i = wOf t (phi e) μ r i
  sym : ∀ m μ i' c, Q.sym m μ i' c = symN m μ i' c
  tab : ∀ u μ r c, Q.tab u μ r c = tabOf t (u3N u) μ r c

/-- The letters with tables, on Q's types. -/
def thetaQ : TLetters K t where
  X := Q.let.X
  M := Q.M
  E := Q.Ex
  W := Q.Wp₁
  phi := fun x => phi x.1
  sym := fun m => symN (Q.left m)
  u3 := fun m => u3N (Q.right m)
  dig := Q.dig
  ride := Q.let.ride

variable {Q phi symN u3N}

/-- Every tie and every read at the letters with tables is one at Q's letters. -/
theorem eqs_thetaQ (h : IsT Q phi symN u3N) {x : Q.let.X} {β : Dr t.size} {msg : Q.M}
    {Z : Dig K t.size}
    (g : Late.Eqs (Λ := (thetaQ Q phi symN u3N).letters) x β msg Z) :
    Late.Eqs (Λ := Q.let) x β msg Z := by
  refine ⟨fun μ u i' => ?_, fun μ u r => ?_⟩
  · have e := g.1 μ u i'
    show ∑ c, (((β μ u c).val : ℤ) : K) * Q.sym (Q.left msg) μ i' c = _
    simp only [h.sym]
    exact e
  · have e := g.2 μ u r
    show ∑ c, (((β μ u c).val : ℤ) : K) * Q.tab (Q.right msg) μ r c =
      ∑ i, Q.w x.1 μ r i * comb Z μ u i
    simp only [h.tab, h.w]
    exact e

/-- A read that stands for no segment of a table has weights 0 and values 0. -/
theorem hk_thetaQ (h : IsT Q phi symN u3N) (x : Q.let.X) (msg : Q.let.M) (μ : Fin t.size.NM)
    (r : Fin (t.size.nr μ)) (hr : keepT t μ r = false) :
    (∀ i, Q.let.w x μ r i = 0) ∧ ∀ c, Q.let.tab msg μ r c = 0 := by
  obtain ⟨g1, g2⟩ := keepT_false (thetaQ Q phi symN u3N) (x := x) (msg := msg) μ r hr
  exact ⟨fun i => (h.w x.1 μ r i).trans (g1 i), fun c => (h.tab (Q.right msg) μ r c).trans (g2 c)⟩

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.eqs_thetaQ
#print axioms Cb.Pv.Tail.hk_thetaQ
