-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Point.lean: the point at which vectors that should be zero are tested.

In the sub-proof of the output head the final norm is stated by 17 identities, each of which must
hold at every position. The verifier draws one point over the positions, and all that follows
speaks of the multilinear extensions of the 17 vectors at that point. In the plan of rounds this
is the round ZERO: the prover sends nothing, the verifier draws lt elements of the field, and the
round's error is lt / |E|.

This file states that round as a block between two joints, and proves its knowledge soundness.
Before the round: every vector of a family d is 0 at every place below 2 ^ lt. Behind it: the
extension of every vector is 0 at the drawn point. The family d is a function of the committed
messages and may be any such function; n is the number of its members. Whatever else is claimed
rides along in a joint Q, which both joints repeat.

Main definitions: PointSize, pointSizes, pointR, pointA, pointB, pointErr, HPoint.
Main theorems: point_knowAt (for all sizes), hPoint, point_nums.

What is not claimed. That the committed messages are fixed before the draw is the form of the
statement (for every m), not a fact on a run. That the 17 extensions are 0 at the point is what the
blocks behind this one are to give. Nothing is said about hiding.

-/
import Cb.G6.Join
import Cb.G6.Johnson.Layers.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Iop Prob TWhole Johnson.L5.Layers

/-- The sizes of the block: a place has lt bits; the family has n vectors. -/
structure PointSize where
  /-- the bits of a place -/
  lt : ℕ
  /-- the number of vectors -/
  n : ℕ
  deriving DecidableEq, Repr

/-- The sizes at which the head's sub-proof runs the block, in the two example configurations:
64 positions and 1,024 positions, 17 identities. -/
def pointSizes : List PointSize := [⟨6, 17⟩, ⟨10, 17⟩]

section
variable {E : Type} [Field E] [Fintype E] {M P Wp Kc : Type} (Ex : ExtSpec)

/-- The statement behind the round: the one before it, and the point. -/
def pointNx (s : PointSize) (x : P) (pv : Fin s.lt → E) : P × (Fin s.lt → E) := (x, pv)

/-- The block: the verifier draws a point of lt coordinates. -/
abbrev pointR (s : PointSize) : IOR P Ex (P × (Fin s.lt → E)) Ex :=
  IOR.draw (Fin s.lt → E) (pointNx (E := E) (P := P) s) Ex

variable (d : M → ℕ → ℕ → E) (Q : IOR.Rels Kc P Ex (M × Wp))

/-- The joint before the round: vector k of the family is 0 at every place. -/
def pointA (s : PointSize) : IOR.Rels Kc P Ex (M × Wp) where
  rel := fun x y w => Q.rel x y w ∧ ∀ k < s.n, ∀ X < 2 ^ s.lt, d w.1 k X = 0
  relR := fun a w => Q.relR a w ∧ ∀ k < s.n, ∀ X < 2 ^ s.lt, d w.1 k X = 0
  on := Q.on
  core := Q.core

/-- The joint behind the round: the extension of vector k is 0 at the point. -/
def pointB (s : PointSize) : IOR.Rels Kc (P × (Fin s.lt → E)) Ex (M × Wp) where
  rel := fun x y w =>
    Q.rel x.1 y w ∧ ∀ k < s.n, Blocks.ext s.lt (d w.1 k) (Blocks.nat x.2) = 0
  relR := fun a w =>
    Q.relR (a.1.1, a.2) w ∧ ∀ k < s.n, Blocks.ext s.lt (d w.1 k) (Blocks.nat a.1.2) = 0
  on := fun a => Q.on (a.1.1, a.2)
  core := Q.core

/-- The round's error, as a count of points: lt |E|^(lt - 1) of the |E|^lt points. -/
def pointErr (s : PointSize) : Err (pointR (E := E) (P := P) Ex s).shape :=
  (IOR.Nums.draw Kc (Fin s.lt → E) (pointNx (E := E) (P := P) s) Ex
    (s.lt * Fintype.card E ^ (s.lt - 1))).err

/-- The block's soundness property, at the sizes of the list. -/
def HPoint : Prop :=
  ∀ s ∈ pointSizes, ∀ m : M,
    (pointR (E := E) (P := P) Ex s).red.Know (pointA Ex d Q s).on
      (fun a wp => (pointA Ex d Q s).relR a (m, wp))
      (fun b wp => (pointB Ex d Q s).relR b (m, wp)) (fun _ _ wp => wp)
      (pointErr (E := E) (P := P) (Kc := Kc) Ex s)

/-- The block between its joints, for all sizes. There is one set of bad points for the whole
family, that of one member that is not 0, so n does not enter the error. -/
theorem point_knowAt (s : PointSize) :
    KnowAt (pointR (E := E) (P := P) Ex s) (pointA Ex d Q s) (pointB Ex d Q s)
      (fun _ _ _ wp => wp) (pointErr (E := E) (P := P) (Kc := Kc) Ex s) :=
  knowAt_draw (pointNx (E := E) (P := P) s) (pointA Ex d Q s) (pointB Ex d Q s) _
    (fun _ _ _ h => h) fun x y m _ => by
      refine le_trans (cnt_mono fun β hβ => ?_)
        (cnt_badPtFam s.lt fun k : Fin s.n => d m k)
      obtain ⟨wp, hB, hA⟩ := hβ
      by_contra hnb
      exact hA ⟨hB.1, fun k hk X hX =>
        zero_of_pt_fam hnb (fun k' => hB.2 k' k'.2) ⟨k, hk⟩ X hX⟩

/-- The property holds. -/
theorem hPoint : HPoint (E := E) Ex d Q := fun s _ m => (point_knowAt Ex d Q s).know m

/-- The list of the block's errors has the one number. -/
theorem point_nums (s : PointSize) :
    errList (pointErr (E := E) (P := P) (Kc := Kc) Ex s) =
      [s.lt * Fintype.card E ^ (s.lt - 1)] := rfl

end

end Cb.Pv.Head
