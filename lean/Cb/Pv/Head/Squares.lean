-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Squares.lean: the sum of squares of the final norm, in the sub-proof of the output head.

The stream's value at a position and a feature is held in five limbs. For the final norm the prover
sends nine hidden values, said to be the sums W_s of limb products, s = 0 .. 8, extended over the
positions at the norm's point. One element g is drawn and batches them. Since the batch of the W_s
under the powers of g is the sum over the features of the square of the limbs' batch under the same
powers, one product layer with two equal halves checks it. The layer runs over the lPd bits of a
feature, summed without weights (the equality weights at the coordinate 1/2, with the factor
2^-lPd in the claim), and the lt bits of a position, at the norm's point. Behind the layer the plan
has the round LINE, whose element the head's check does not use.

This file gives the layer's data (sqKind) and the block of the layer with the round LINE, between
the layer's own joints. The round that sends and batches the nine values stands before it
(Cb/Pv/Head/Batch.lean).

Main definitions: SqSize, sqSizes, sqNums, SqSt, sqVec, sqKind, sqR, sqA, sqB, sqErr, HSquares.
Main theorems: sq_knowAt (for all sizes), hSquares, sq_nums, sq_in.

Letters. J: the committed entries. limb m l c: limb l of the stream at the index c = 2^lt j + a, for
feature j and position a, as a function of the entries; it is meant to be 0 for a feature from the
model's width on. slot i: the mask entry of the block's slot number i; the nine values have the
slots 0 to 8. An index is read with its top bit at coordinate 0 of a point (Alg.num).

What is not claimed. That the verifier's routine computes this block's output is not shown here.
Who claims what the two end values are, and on which committed array, is said where the sub-proof's
claims are read. Nothing is said about hiding.


-/
import Cb.Pv.Head.Layer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Iop Prob TWhole

/-- The sizes: the bits of a position and of a padded feature. -/
structure SqSize where
  /-- the bits of a position -/
  lt : ℕ
  /-- the bits of a feature, padded -/
  lPd : ℕ
  deriving DecidableEq, Repr

/-- The sizes in the two example configurations: 64 positions and width 512; 1,024 positions and
width 5,120, padded to 8,192. -/
def sqSizes : List SqSize := [⟨6, 9⟩, ⟨10, 13⟩]

/-- The errors of the layer's rounds and of LINE, as counts of draws: eps 1; lPd + lt rounds of 2;
the further variable 2 (of the elements other than 0); the end values 0; LINE 1. -/
def sqNums (s : SqSize) : List ℕ := 1 :: (List.replicate (s.lPd + s.lt) 2 ++ [2] ++ [0]) ++ [1]

/-- What is public before the layer. -/
structure SqSt (E P : Type) (s : SqSize) where
  /-- whatever else is public -/
  pub : P
  /-- the norm's point over the positions -/
  pv : Fin s.lt → E
  /-- what was sent for the nine sums -/
  sent : Fin 9 → E
  /-- the element that batches them -/
  g : E

section
variable {E : Type} [Field E] [Fintype E] {J P : Type} [Fintype J] [DecidableEq J]
variable (limb : (J → E) → ℕ → ℕ → E) (slot : ℕ → J)

/-- The limbs' batch under the powers of g, at an index. -/
def sqVec (g : E) (m : J → E) (c : ℕ) : E := ∑ l ∈ Finset.range 5, g ^ l * limb m l c

/-- The factor of sum number t in the layer's claim. -/
def sqCoef (s : SqSize) (g : E) (t : ℕ) : E := (2 : E)⁻¹ ^ s.lPd * g ^ t

/-- The layer's data. -/
def sqKind (s : SqSize) : LayerKind E (SqSt E P s) J where
  k := s.lPd + s.lt
  pt := fun st => Fin.append (fun _ : Fin s.lPd => (2 : E)⁻¹) st.pv
  half := fun st m _ b => sqVec limb st.g m (Alg.num b)
  inc := fun st j => ∑ t : Fin 9, if slot t = j then sqCoef s st.g t else 0
  mask := fun i => slot (9 + i)

/-- The layer's target: the batch of what was sent. -/
def sqTarget (s : SqSize) (st : SqSt E P s) : E := ∑ t : Fin 9, sqCoef s st.g t * st.sent t

variable (Ex : ExtSpec)

/-- The block: the layer's sumcheck, then the round LINE. -/
noncomputable def sqR (s : SqSize) :
    IOR (E × SqSt E P s) Ex ((sqKind (P := P) limb slot s).par.Out × E) Ex :=
  ((sqKind (P := P) limb slot s).R Ex).seq (IOR.draw E (fun o tau => (o, tau)) Ex)

variable {M Wp Kc : Type} (msg : M → J → E)

section
variable (s : SqSize) (A0 : IOR.Rels Kc (SqSt E P s) Ex (M × Wp))

/-- The joint before the block: the layer's claim; A0 rides along. -/
noncomputable def sqA : IOR.Rels Kc (E × SqSt E P s) Ex (M × Wp) :=
  (sqKind (P := P) limb slot s).par.baseIn A0 fun w => msg w.1

/-- The joint behind the layer: the row and the two claims on end values; A0 rides along. -/
noncomputable def sqMid : IOR.Rels Kc (sqKind (P := P) limb slot s).par.Out Ex (M × Wp) :=
  (sqKind (P := P) limb slot s).par.baseOut A0 fun w => msg w.1

/-- The joint behind the block: the same, with the element of the round LINE beside it. -/
noncomputable def sqB :
    IOR.Rels Kc ((sqKind (P := P) limb slot s).par.Out × E) Ex (M × Wp) where
  rel := fun x y w => (sqMid limb slot Ex msg s A0).rel x.1 y w
  relR := fun a w => (sqMid limb slot Ex msg s A0).relR (a.1.1, a.2) w
  on := fun a => (sqMid limb slot Ex msg s A0).on (a.1.1, a.2)
  core := (sqMid limb slot Ex msg s A0).core

/-- The errors: the layer's, then the plan's 1 for the round LINE. -/
noncomputable def sqErr : Err (sqR (P := P) limb slot Ex s).shape :=
  Err.app ((sqKind (P := P) limb slot s).err Ex)
    (IOR.Nums.draw Kc E
      (fun (o : (sqKind (P := P) limb slot s).par.Out) (tau : E) => (o, tau)) Ex 1).err

/-- The block between its joints. No element of the round LINE is bad. -/
theorem sq_knowAt :
    KnowAt (sqR (P := P) limb slot Ex s) (sqA limb slot Ex msg s A0) (sqB limb slot Ex msg s A0)
      (fun _ _ _ wp => wp) (sqErr (P := P) (Kc := Kc) limb slot Ex s) :=
  knowAt_seq ((sqKind (P := P) limb slot s).knowAt Ex M Wp Kc A0 msg)
    (knowAt_draw _ (sqMid limb slot Ex msg s A0) (sqB limb slot Ex msg s A0) 1
      (fun _ _ _ h => h) fun _ _ _ _ => by
        rw [cnt_false fun _ h => by
          obtain ⟨_, h1, h2⟩ := h
          exact h2 h1]
        exact Nat.zero_le _)

end

/-- The block's soundness property, at the sizes of the list. -/
def HSquares (A0 : ∀ s : SqSize, IOR.Rels Kc (SqSt E P s) Ex (M × Wp)) : Prop :=
  ∀ s ∈ sqSizes, ∀ m : M,
    (sqR (P := P) limb slot Ex s).red.Know (sqA limb slot Ex msg s (A0 s)).on
      (fun a wp => (sqA limb slot Ex msg s (A0 s)).relR a (m, wp))
      (fun b wp => (sqB limb slot Ex msg s (A0 s)).relR b (m, wp)) (fun _ _ wp => wp)
      (sqErr (P := P) (Kc := Kc) limb slot Ex s)

/-- The property holds. -/
theorem hSquares (A0 : ∀ s : SqSize, IOR.Rels Kc (SqSt E P s) Ex (M × Wp)) :
    HSquares limb slot Ex msg A0 :=
  fun s _ m => (sq_knowAt limb slot Ex msg s (A0 s)).know m

/-- The errors are the written list. -/
theorem sq_nums (s : SqSize) :
    errList (sqErr (P := P) (Kc := Kc) limb slot Ex s) = sqNums s :=
  (errList_app ((sqKind (P := P) limb slot s).err Ex)
    (IOR.Nums.draw Kc E
      (fun (o : (sqKind (P := P) limb slot s).par.Out) (tau : E) => (o, tau)) Ex 1).err).trans
    (by
      rw [(sqKind (P := P) limb slot s).nums Ex]
      rfl)

/-- What the layer's claim says at the target sqTarget: the sum over the corners of the squares of
the limbs' batch, under the equality weights, is the batch of the nine hidden values: what was sent
less the mask entries. -/
theorem sq_in (s : SqSize) (st : SqSt E P s) (m : J → E) :
    (sqKind (P := P) limb slot s).par.SumHolds (sqTarget s st, st) m ↔
      ∑ b : Fin (s.lPd + s.lt) → Bool,
          Alg.eqk (Fin.append (fun _ : Fin s.lPd => (2 : E)⁻¹) st.pv) b *
            (sqVec limb st.g m (Alg.num b) * sqVec limb st.g m (Alg.num b)) =
        ∑ t : Fin 9, sqCoef s st.g t * (st.sent t - m (slot t)) := by
  rw [(sqKind (P := P) limb slot s).in_iff]
  have e : ∑ j, (∑ t : Fin 9, if slot t = j then sqCoef s st.g t else 0) * m j =
      ∑ t : Fin 9, sqCoef s st.g t * m (slot t) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [ite_mul]
  show _ + ∑ j, (∑ t : Fin 9, if slot t = j then sqCoef s st.g t else 0) * m j = _ ↔ _
  rw [e]
  unfold sqTarget
  simp only [mul_sub, Finset.sum_sub_distrib]
  constructor
  · intro h
    exact eq_sub_of_add_eq h
  · intro h
    exact add_eq_of_eq_sub h

end

end Cb.Pv.Head

#print axioms Cb.Pv.Head.sq_knowAt
#print axioms Cb.Pv.Head.hSquares
#print axioms Cb.Pv.Head.sq_nums
#print axioms Cb.Pv.Head.sq_in
