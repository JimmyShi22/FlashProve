-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/Block.lean: the smallness test's own round as a typed reduction between two joints, and
the statement of its knowledge soundness. Definitions, and the plain facts beside it.

One round: the prover sends nothing, the verifier draws the matrix (Cb/Pv/Tail/Size.lean).

Before the round (`relIn`): there are cells: for every column of every matrix there are integers,
each below twice the shift in absolute value, whose packing is the committed symbols of that column
and whose weighted sums are its committed reads (`Alg.Fixed.Good`, Alg/Range.lean).
After the round (`relOut`): there are digits, each in its table, such that at the drawn matrix, for
every combination u, every single equation holds: one for each row of symbols of each matrix (a
tie), one for each read of each matrix.

Letters (`Letters`): the ring K; the explicit statement X, from which the weights of the reads come;
the committed messages M, from which the symbols and the reads come; the implicit instance E; a
further witness W, of which the digits are a part, and a condition `ride`, which stands unchanged on
both sides. The witness has one type on both sides and the extractor hands it back.

Main names:
  `Letters.fixed`, `relIn`, `relOut`: the two relations.
  `R`, `A`, `B`, `eps`: the reduction, its joints, the error. The extractor hands the witness back.
  `HoleAt`: knowledge soundness of the round at one size.
  `point`, `isLocal`, `onOut`, `knowAt_of`: with `HoleAt` they give `TWhole.KnowAt`.

Limits: M stands for what is committed before the matrix is drawn: the symbols, those of earlier
sub-proofs too, and the reads. The digits, and whatever else is sent after the draw, belong to W. At
letters whose M holds something that is sent after the draw, the statement stays true and says
nothing of the protocol: it would count a prover that cannot answer the draw.
That the digits are in their tables is a clause of `relOut`: it is to be had from the lookup on the
digits. The sending of the digits, the planes of that lookup's counts and the batching of the
equations are other blocks'. The cells stand under "there are": no map from the committed messages
to cells is named; that they are unique is `Alg.small_unique` (Alg/Range.lean), under conditions on
the radix and the characteristic, and is not used here. In a ring of small characteristic the
statement is true and weak. The honest relations `rel` are here the relaxed ones, so no honest side
can be proved at these joints as they stand.

Terms: lean/GLOSSARY.md.

-/
import Cb.G6.Join
import Cb.Gen.RngAlg
import Cb.Pv.Tail.Size
import Ior.Draw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open Iop

/-- What the block takes from its surroundings. -/
structure Letters (K : Type) (s : Size) where
  /-- the explicit statement, the committed messages, the implicit instance, a further witness -/
  X : Type
  M : Type
  E : ExtSpec
  W : Type
  /-- the weights of a read on the rows of cells -/
  w : X → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → K
  /-- the committed symbols: matrix, row of symbols, column -/
  sym : M → ∀ μ : Fin s.NM, Fin (Alg.symRows (s.m μ)) → Fin (s.k μ) → K
  /-- the committed reads: matrix, read, column -/
  tab : M → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → K
  /-- the digits, a part of the further witness -/
  dig : W → Dig K s
  /-- what else the joint says -/
  ride : X × E.Str → M → W → Prop

variable {K : Type} [CommRing K] {s : Size} (Λ : Letters K s)

/-- What is determined before the matrix is drawn. -/
def Letters.fixed (x : Λ.X) (msg : Λ.M) :
    Alg.Fixed K (fun μ : Fin s.NM => s.m μ) (fun μ : Fin s.NM => Alg.symRows (s.m μ))
      (fun μ : Fin s.NM => Fin (s.k μ)) (fun μ : Fin s.NM => Fin (s.nr μ)) :=
  ⟨Λ.sym msg, Λ.w x, Λ.tab msg⟩

/-- There are cells. -/
def relIn (x : Λ.X) (msg : Λ.M) : Prop := (Λ.fixed x msg).Good (s.beta : ℤ) (s.rad : ℤ)

/-- There are digits in their tables that meet every tie and every read at the drawn matrix. -/
def relOut (x : Λ.X) (β : Dr s) (msg : Λ.M) (Z : Dig K s) : Prop :=
  (∀ μ u i, Cb.Rng.InTab s.lo (Z.zl μ u i) ∧ Cb.Rng.InTab s.hi (Z.zh μ u i)) ∧
  (∀ (μ : Fin s.NM) u (i' : Fin (Alg.symRows (s.m μ))),
    ∑ c, (((β μ u c).val : ℤ) : K) * Λ.sym msg μ i' c = Alg.pack (s.rad : ℤ) (comb Z μ u) i') ∧
  (∀ μ u r,
    ∑ c, (((β μ u c).val : ℤ) : K) * Λ.tab msg μ r c = ∑ i, Λ.w x μ r i * comb Z μ u i)

/-- The round. -/
def R : IOR Λ.X Λ.E (Λ.X × Dr s) Λ.E := IOR.draw (Dr s) Prod.mk Λ.E

/-- The joint before the round. -/
def A : IOR.Rels Unit Λ.X Λ.E (Λ.M × Λ.W) where
  rel x y v := Λ.ride (x, y) v.1 v.2 ∧ relIn Λ x v.1
  relR a v := Λ.ride a v.1 v.2 ∧ relIn Λ a.1 v.1
  on _ := True
  core _ := ()

/-- The joint after the round. -/
def B : IOR.Rels Unit (Λ.X × Dr s) Λ.E (Λ.M × Λ.W) where
  rel x y v := Λ.ride (x.1, y) v.1 v.2 ∧ relOut Λ x.1 x.2 v.1 (Λ.dig v.2)
  relR b v := Λ.ride (b.1.1, b.2) v.1 v.2 ∧ relOut Λ b.1.1 b.1.2 v.1 (Λ.dig v.2)
  on _ := True
  core _ := ()

/-- The error: of all values that can be drawn, one part in 2 ^ tau. -/
def eps : Err (R Λ).shape := ((Fintype.card (Dr s) / 2 ^ s.tau, ()) : ℕ × Unit)

/-- Knowledge soundness of the round, at one size. -/
def HoleAt : Prop :=
  ∀ m, (R Λ).red.Know (A Λ).on (fun a wp => (A Λ).relR a (m, wp))
    (fun b wp => (B Λ).relR b (m, wp)) (fun _ _ wp => wp) (eps Λ)

omit [CommRing K] in
theorem point : Nonempty (R Λ).shape.IsPoint :=
  ⟨((Blocks.plainPoint Unit (Dr s) (), ()) : (IOR.drawRound (Dr s)).IsPoint × Unit)⟩

omit [CommRing K] in
theorem isLocal : (R Λ).IsLocal :=
  ⟨fun x _ _ τ τ' hρ _ _ _ => by
      have e : IOR.drawn τ = IOR.drawn τ' :=
        congrArg (fun r : Rho [IOR.drawRound (Dr s)] => (show Dr s × Unit from r).1) hρ
      show some ((x, IOR.drawn τ) : Λ.X × Dr s) = some (x, IOR.drawn τ')
      rw [e],
    fun _ _ _ _ p _ _ hE _ => hE p (Finset.mem_singleton_self p)⟩

theorem onOut : ∀ a τ b, (A Λ).on a → (R Λ).red.out a τ = some b → (B Λ).on b :=
  fun _ _ _ _ _ => trivial

/-- The four together. -/
theorem knowAt_of (h : HoleAt Λ) :
    TWhole.KnowAt (R Λ) (A Λ) (B Λ) (fun _ _ _ wp => wp) (eps Λ) :=
  ⟨point Λ, isLocal Λ, onOut Λ, h⟩

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.point
#print axioms Cb.Pv.Tail.isLocal
#print axioms Cb.Pv.Tail.onOut
#print axioms Cb.Pv.Tail.knowAt_of
