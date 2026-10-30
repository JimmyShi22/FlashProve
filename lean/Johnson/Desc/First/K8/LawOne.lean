-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/LawOne.lean: THE SMALLNESS TEST, ITS FIRST HALF: WHAT STANDS BEHIND THE BLOCK
SPEAKS OF ONE MATRIX.

`Reads.relB` (Johnson/Desc/First/K8/LawPiece.lean) says the proved block's second joint of EVERY
typed matrix whose list lies in the record. Two typed matrices can have one list: a coefficient is
two bits, and both pairs with the first bit 0 have the value 0. Here: the proved block's second
joint reads a typed matrix by its entries' values alone; so it holds of every typed matrix with a
given list as soon as it holds of one. Whoever is to reach what stands behind the block need show it
at one typed matrix.
  `val_of_listOf`: two typed matrices with one list have the same value at every entry.
  `relOut_congr`: the relation behind the draw (Cb/Pv/Tail/Block.lean) reads the matrix by these
    values.
  `Reads.relB_of_one`, `Reads.relB_iff`: so `relB` holds if and only if, where some typed matrix has
    the record's list, the joint holds at one such matrix.
Statements and proofs. Limits: those of LawPiece.lean.

-/
import Johnson.Desc.First.K8.LawPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb.Pv.Tail OnBytes.Tie.Pv.Tail KObj VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

/-- Two typed matrices with one list have the same value at every entry. -/
theorem val_of_listOf {s : Size} {β β' : Dr s} (h : listOf β = listOf β') (μ : Fin s.NM)
    (u : Fin s.tau) (c : Fin (s.k μ)) : (β μ u c).val = (β' μ u c).val := by
  rw [← listOf_get β μ c u, ← listOf_get β' μ c u, h]

/-- The relation behind the draw reads the matrix by its entries' values. -/
theorem relOut_congr {K : Type} [CommRing K] {s : Size} (Λ : Letters K s) (x : Λ.X) {β β' : Dr s}
    (h : ∀ μ u c, (β μ u c).val = (β' μ u c).val) (msg : Λ.M) (Z : Dig K s) :
    relOut Λ x β msg Z ↔ relOut Λ x β' msg Z := by
  unfold relOut
  simp only [h]

section
variable {S Cl W : Type} {F : Frame} {seat : Seat S} {p : Par} {base e : ℕ} {d : TailCallerOn}

/-- The joint behind the proved block, at two typed matrices with one list. -/
theorem Reads.behind_congr (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str) {β β' : Dr d.c.s}
    (h : listOf β = listOf β') (w : W) :
    (KTailRngOn.dst d).relR (Q.behind a β) (Q.wit w) ↔
      (KTailRngOn.dst d).relR (Q.behind a β') (Q.wit w) := by
  have hr := relOut_congr d.c.letters (Q.rd a).1.1 (val_of_listOf h)
    (d.c.Sg.msgs (Q.wit w).1) (d.c.dig (Q.wit w).2)
  constructor
  · intro k
    exact ⟨k.1, k.2.1, hr.1 k.2.2⟩
  · intro k
    exact ⟨k.1, k.2.1, hr.2 k.2.2⟩

/-- **It is enough to show what stands behind the block at ONE typed matrix with the record's
list.** -/
theorem Reads.relB_of_one (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str) (w : W)
    (β : Dr d.c.s)
    (hβ : Q.cf a.1 = listOf β) (h : (KTailRngOn.dst d).relR (Q.behind a β) (Q.wit w)) :
    Q.relB a w := fun _ hβ' => (Q.behind_congr a (hβ.symm.trans hβ') w).1 h

theorem Reads.relB_iff (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str) (w : W) (β : Dr d.c.s)
    (hβ : Q.cf a.1 = listOf β) :
    Q.relB a w ↔ (KTailRngOn.dst d).relR (Q.behind a β) (Q.wit w) :=
  ⟨fun h => h β hβ, Q.relB_of_one a w β hβ⟩

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.val_of_listOf
#print axioms VerifiableInference.Desc.First.K8.relOut_congr
#print axioms VerifiableInference.Desc.First.K8.Reads.relB_iff
