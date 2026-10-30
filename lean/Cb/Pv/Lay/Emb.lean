-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Emb.lean: the two further points of the first layers' sub-proof: from an identity at the
two drawn points to the identity at every index.

In the first layers' sub-proof two points are drawn behind the token point
(OnBytes/Params/SubRounds.lean, planLayerOwn, at firstGroup; OnBytes/Model/Layer.lean: ZE, tkh).
They test one family of identities: that each entry of the stream that comes in is the entry of
the embedding's row of that position's token. No sumcheck and no lookup belongs to this test. The
chain of the sub-proof's own rounds (Cb/Pv/Lay/Own.lean, LayOwnFirst) has a law on the bad draws
at each of the two rounds as a premise. Here the two laws are proved, for claims that are made of
the identities' gaps.

Main names:
  law_pt: a bound on the bad draws of a point. If the claim before the draw says that all vectors
    of a family vanish on the cube of g variables, and Q; and the claim behind it gives that their
    extensions vanish at the point, and Q; then at most g |E|^(g - 1) points are bad.
  embFirst: the letters of the first sub-proof's own rounds in which the claims before the two
    further points are made of a family of gaps e x m U V, U below 2^gA, V below 2^gB, and a claim
    Q that is carried along. Before the first point: all gaps are 0. Between the two: for every V
    the extension over U vanishes at the first point. The bounds are gA |E|^(gA - 1) and gB
    |E|^(gB - 1).
  emb_cA, emb_cB: the two laws. emb_cB has one premise: the claim at the head of the stages behind
    gives that the extension over both indices vanishes at the two points, and Q.
  emb_laws: the laws of LayOwnFirst at these letters, from that premise, the law at the token
    point and the laws of the stages behind.
  emb_ratio: the count g q^(g - 1) among q^g points is g among q.

Limits. The gaps are parameters: that they are the differences between the stream's entries and
the embedding's rows at the request's tokens is not stated; nor that the extension over both
indices is the difference of the two claims that the programs add (one on a table of the stream,
one on the committed weights). Nothing is said on an honest prover or on hiding.

-/
import Cb.Pv.Lay.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR TWhole Johnson.L5.Layers Cb.Pv.Att

variable {E : Type} [Field E] [Fintype E] {M : Type}

/-- A bound on the bad draws of a point, for a family of vectors. -/
theorem law_pt {X J : Type} (g : ℕ) (d : X → M → J → ℕ → E) (Q P : X → M → Prop)
    (T : X × (Fin g → E) → M → Prop)
    (hP : ∀ x m, (∀ k, ∀ Y < 2 ^ g, d x m k Y = 0) → Q x m → P x m)
    (hT : ∀ x p m, T (x, p) m → (∀ k, Blocks.ext g (d x m k) (Blocks.nat p) = 0) ∧ Q x m)
    (x : X) (m : M) (h : ¬ P x m) :
    cnt (fun p : Fin g → E => T (x, p) m) ≤ g * Fintype.card E ^ (g - 1) := by
  refine le_trans (cnt_mono fun p hp => ?_) (cnt_badPtFam g (d x m))
  by_contra hn
  obtain ⟨h1, h2⟩ := hT x p m hp
  exact h (hP x m (zero_of_pt_fam hn h1) h2)

section Emb
variable {X : Type} (gT eT : ℕ) (pT : X → M → Prop) (gA gB : ℕ)
  (e : X × (Fin gT → E) → M → ℕ → ℕ → E) (Q : X × (Fin gT → E) → M → Prop)
  (tail : LayTail E M (((X × (Fin gT → E)) × (Fin gA → E)) × (Fin gB → E)))

/-- The letters, with the claims before the two further points made of gaps. -/
def embFirst : LayOwnFirst E M X where
  gT := gT
  eT := eT
  pT := pT
  gA := gA
  eA := gA * Fintype.card E ^ (gA - 1)
  pA := fun x m => (∀ V < 2 ^ gB, ∀ U < 2 ^ gA, e x m U V = 0) ∧ Q x m
  gB := gB
  eB := gB * Fintype.card E ^ (gB - 1)
  pB := fun y m =>
    (∀ V < 2 ^ gB, Blocks.ext gA (fun U => e y.1 m U V) (Blocks.nat y.2) = 0) ∧ Q y.1 m
  tail := tail

/-- The law at the first of the two points. -/
theorem emb_cA (x : X × (Fin gT → E)) (m : M) (h : ¬ (embFirst gT eT pT gA gB e Q tail).pA x m) :
    cnt (fun p : Fin gA → E => (embFirst gT eT pT gA gB e Q tail).pB (x, p) m) ≤
      (embFirst gT eT pT gA gB e Q tail).eA :=
  law_pt gA (fun x m (V : Fin (2 ^ gB)) U => e x m U V) Q _ _
    (fun _ _ h1 h2 => ⟨fun V hV U hU => h1 ⟨V, hV⟩ U hU, h2⟩)
    (fun _ _ _ h1 => ⟨fun V => h1.1 V V.2, h1.2⟩) x m h

/-- The law at the second. -/
theorem emb_cB
    (hL : ∀ z m, tail.pL z m →
      Blocks.ext gB (fun V => Blocks.ext gA (fun U => e z.1.1 m U V) (Blocks.nat z.1.2))
        (Blocks.nat z.2) = 0 ∧ Q z.1.1 m)
    (y : (X × (Fin gT → E)) × (Fin gA → E)) (m : M)
    (h : ¬ (embFirst gT eT pT gA gB e Q tail).pB y m) :
    cnt (fun p : Fin gB → E => tail.pL (y, p) m) ≤ (embFirst gT eT pT gA gB e Q tail).eB :=
  law_pt gB
    (fun (y : (X × (Fin gT → E)) × (Fin gA → E)) m (_ : Unit) V =>
      Blocks.ext gA (fun U => e y.1 m U V) (Blocks.nat y.2))
    (fun y m => Q y.1 m) _ _ (fun _ _ h1 h2 => ⟨fun V hV => h1 () V hV, h2⟩)
    (fun y p m h1 => ⟨fun _ => (hL (y, p) m h1).1, (hL (y, p) m h1).2⟩) y m h

/-- The laws of the first sub-proof's own rounds at these letters. -/
theorem emb_laws
    (hT : ∀ x m, ¬ pT x m →
      cnt (fun p : Fin gT → E => (embFirst gT eT pT gA gB e Q tail).pA (x, p) m) ≤ eT)
    (hL : ∀ z m, tail.pL z m →
      Blocks.ext gB (fun V => Blocks.ext gA (fun U => e z.1.1 m U V) (Blocks.nat z.1.2))
        (Blocks.nat z.2) = 0 ∧ Q z.1.1 m)
    (ht : tail.Laws) : (embFirst gT eT pT gA gB e Q tail).Laws where
  cT := hT
  cA := emb_cA gT eT pT gA gB e Q tail
  cB := emb_cB gT eT pT gA gB e Q tail hL
  tail := ht

end Emb

/-- The count g q^(g - 1) among q^g points is g among q. -/
theorem emb_ratio (g q : ℕ) (h : 1 ≤ g) : g * q ^ (g - 1) * q = g * q ^ g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
  rw [Nat.succ_sub_one, Nat.mul_assoc, ← pow_succ]

end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.law_pt
#print axioms Cb.Pv.Lay.emb_cA
#print axioms Cb.Pv.Lay.emb_cB
#print axioms Cb.Pv.Lay.emb_laws
#print axioms Cb.Pv.Lay.emb_ratio
