-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Norm2.lean: the chain of the final norm goes on: behind the layer of the sum of squares
come the seven row products, their batch, and the token sumcheck on the batch.

Cb/Pv/Head/Norm.lean ends in a joint that still speaks of the extensions of the seven row products.
Cb/Pv/Head/BatTok.lean has the block in which the prover sends seven hidden values for them, one
element batches them, and a token sumcheck is run on the batch. This file joins the two. The chain
then leads
  from: the 17 identities hold at every position;
  to: the 17 identities hold at the drawn point on the nine and the seven hidden values and on the
    extensions of the digits; the output claims of the layer's sumcheck hold; the hidden value of
    the token sumcheck's first scalar is the batch of the seven; its output claims hold.

Main definitions: sqSlot, sPvOf, SqOut, tvW, tvFrame, toTV, norm2R, norm2Err, norm2Sizes, HNorm2.
Main theorems: nat_pt, trueP_prodTrue, norm2_seam, norm2_knowAt, hNorm2.

Letters. msk j: the mask entry of the sub-proof's slot j. sW: the slot of the first of the nine
sums. The others as in Norm.lean.

What is not claimed. As in Norm.lean and BatTok.lean.


-/
import Cb.Pv.Head.Norm
import Cb.Pv.Head.ToksLed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Iop Prob TWhole Finset Inst.Model Tok

section
variable {E : Type} [Field E]

/-- With no further rounds the sumcheck's point is the point over the positions. -/
theorem nat_pt {Pb : Type} (lt sPv : ℕ) (st : TokSt E Pb (kindTV lt sPv)) :
    Blocks.nat st.pt = Blocks.nat st.zt := by
  funext t
  by_cases h : t < lt
  · show (if h' : t < (kindTV lt sPv).vars then st.pt ⟨t, h'⟩ else 0) =
      if h' : t < (kindTV lt sPv).lt then st.zt ⟨t, h'⟩ else 0
    rw [dif_pos (show t < (kindTV lt sPv).vars from h),
      dif_pos (show t < (kindTV lt sPv).lt from h)]
    exact dif_pos h
  · show (if h' : t < (kindTV lt sPv).vars then st.pt ⟨t, h'⟩ else 0) =
      if h' : t < (kindTV lt sPv).lt then st.zt ⟨t, h'⟩ else 0
    rw [dif_neg (show ¬ t < (kindTV lt sPv).vars from h),
      dif_neg (show ¬ t < (kindTV lt sPv).lt from h)]

end

section
variable {E : Type} [Field E] [Fintype E] {J P M Wp Kc : Type} [Fintype J] [DecidableEq J]
variable (np : NormPar) (limb : (J → E) → ℕ → ℕ → E) (dig : (J → E) → ℕ → ℕ → E)
variable (msk : ℕ → J) (sW : ℕ)

/-- The mask entries of the slots from the first of the nine sums on. -/
def sqSlot : ℕ → J := fun i => msk (sW + i)

/-- The slot of the first row product: behind the nine sums and the layer's 2 (lPd + lt) + 5
slots. -/
def sPvOf (s : SqSize) : ℕ := sW + (2 * (s.lPd + s.lt) + 14)

/-- The statement behind the round LINE. -/
abbrev SqOut (P : Type) (s : SqSize) : Type :=
  (sqKind (P := P) limb (sqSlot msk sW) s).par.Out × E

/-- The entries and tables of the sumcheck of the row products. -/
abbrev tvW (P : Type) (s : SqSize) : TokWorld E (kindTV s.lt (sPvOf sW s)) :=
  worldTV s.lt (sPvOf sW s) (SqOut limb msk sW P s) J msk dig

omit [Fintype E] in
/-- The true products of the two files are the same. -/
theorem trueP_prodTrue {Pb : Type} (s : SqSize) (sPv : ℕ) (pv : Fin s.lt → E)
    (om : Fin (kindTV s.lt sPv).np → E) (pb : Pb) (m : J → E) (j : Fin 7) :
    trueP (kindTV s.lt sPv) (worldTV s.lt sPv Pb J msk dig) ⟨pv, om, pb⟩ m j =
      prodTrue dig s m pv j := by
  rw [trueP_prods, nat_pt]
  rfl

variable (Ex : ExtSpec) (msg : M → J → E) (Q : IOR.Rels Kc P Ex (M × Wp))

/-- What stands around the block of the seven products: Q and the layer's output claims ride; of
the seven values the 17 identities are claimed, with the nine hidden values. -/
@[reducible] def tvFrame (s : SqSize) :
    BtFrame E (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s) where
  Kc := Kc
  M := M
  Wp := Wp
  Ex := Ex
  A0 :=
    ⟨fun x y w => Q.rel x.2.1.st.pub y w ∧
        (sqKind (P := P) limb (sqSlot msk sW) s).par.OutHolds x.2.1 (msg w.1),
      fun a w => Q.relR (a.1.2.1.st.pub, a.2) w ∧
        (sqKind (P := P) limb (sqSlot msk sW) s).par.OutHolds a.1.2.1 (msg w.1),
      fun a => Q.on (a.1.2.1.st.pub, a.2), Q.core⟩
  msg := msg
  phi := fun x V m =>
    NormAt np dig s x.1 (fun t => x.2.1.st.sent t - m (sqSlot msk sW t)) V m

/-- From the statement behind LINE to the statement before the seven products. -/
def toTV (s : SqSize) (x : SqOut limb msk sW P s) : (Fin s.lt → E) × SqOut limb msk sW P s :=
  (x.1.st.pv, x)

/-- The block of the seven products, from the joint in which Norm.lean ends. -/
theorem norm2_seam (s : SqSize) :
    KnowAt
      ((btR (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s) Ex).pre
        (fun x => some (toTV limb msk sW s x)) (ExtMap.id Ex))
      (sqB limb (sqSlot msk sW) Ex msg s (rideS np dig (sqSlot msk sW) Ex msg Q s))
      (tokOut (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s).behind
        (tvFrame np limb dig msk sW Ex msg Q s).tok)
      (fun _ _ _ wp => wp)
      (Err.app (Bat.batErr E ((Fin s.lt → E) × SqOut limb msk sW P s) 7 Ex)
        (tokErr (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s).behind Ex)) :=
  knowAt_preMap
    (A' := sqB limb (sqSlot msk sW) Ex msg s (rideS np dig (sqSlot msk sW) Ex msg Q s))
    (toTV limb msk sW s) (fun _ _ h => h)
    (fun x _ w _ h => by
      have h2 : NormAt np dig s x.1.st.pv
          (fun t => x.1.st.sent t - msg w.1 (sqSlot msk sW t))
          (fun j : Fin 7 => trueP (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s)
            ⟨x.1.st.pv, fun _ => 0, x⟩ (msg w.1) j) (msg w.1) := h.2
      have e : (fun j : Fin 7 => trueP (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s)
          ⟨x.1.st.pv, fun _ => 0, x⟩ (msg w.1) j) =
          fun j : Fin 7 => prodTrue dig s (msg w.1) x.1.st.pv j :=
        funext fun j => trueP_prodTrue dig msk s (sPvOf sW s) x.1.st.pv _ x (msg w.1) j
      rw [e] at h2
      exact ⟨⟨h.1.1, h2⟩, h.1.2⟩)
    (bt_knowAt (tvFrame np limb dig msk sW Ex msg Q s))

/-- The chain. -/
noncomputable def norm2R (s : SqSize) :=
  (normR (P := P) limb (sqSlot msk sW) Ex s).seq
    ((btR (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s) Ex).pre
      (fun x => some (toTV limb msk sW s x)) (ExtMap.id Ex))

/-- Its errors. -/
noncomputable def norm2Err (s : SqSize) : Err (norm2R (P := P) limb dig msk sW Ex s).shape :=
  Err.app (normErr (P := P) (Kc := Kc) limb (sqSlot msk sW) Ex s)
    (Err.app (Bat.batErr E ((Fin s.lt → E) × SqOut limb msk sW P s) 7 Ex)
      (tokErr (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s).behind Ex))

/-- The chain between its joints, for all sizes. -/
theorem norm2_knowAt (s : SqSize) (h2 : (2 : E) ≠ 0) :
    KnowAt (norm2R (P := P) limb dig msk sW Ex s)
      (pointA Ex (normD np limb dig msg s) Q ⟨s.lt, 17⟩)
      (tokOut (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s).behind
        (tvFrame np limb dig msk sW Ex msg Q s).tok)
      (fun _ _ _ wp => wp) (norm2Err (P := P) (Kc := Kc) limb dig msk sW Ex s) :=
  knowAt_seq (norm_knowAt np limb dig (sqSlot msk sW) Ex msg Q s h2)
    (norm2_seam np limb dig msk sW Ex msg Q s)

/-- The sizes in the two example configurations, each with the slot of the first of the nine
sums. -/
def norm2Sizes : List (SqSize × ℕ) := [(⟨6, 9⟩, 1531), (⟨10, 13⟩, 1995)]

/-- The chain's soundness property, at the sizes of the list. -/
def HNorm2 : Prop :=
  ∀ z ∈ norm2Sizes, ∀ m : M,
    (norm2R (P := P) limb dig msk z.2 Ex z.1).red.Know
      (pointA Ex (normD np limb dig msg z.1) Q ⟨z.1.lt, 17⟩).on
      (fun a wp => (pointA Ex (normD np limb dig msg z.1) Q ⟨z.1.lt, 17⟩).relR a (m, wp))
      (fun b wp => (tokOut (kindTV z.1.lt (sPvOf z.2 z.1)) (tvW limb dig msk z.2 P z.1).behind
        (tvFrame np limb dig msk z.2 Ex msg Q z.1).tok).relR b (m, wp))
      (fun _ _ wp => wp) (norm2Err (P := P) (Kc := Kc) limb dig msk z.2 Ex z.1)

/-- The property holds where 2 is not 0. -/
theorem hNorm2 (h2 : (2 : E) ≠ 0) : HNorm2 np limb dig msk Ex msg Q :=
  fun z _ m => (norm2_knowAt np limb dig msk z.2 Ex msg Q z.1 h2).know m

end

end Cb.Pv.Head

#print axioms Cb.Pv.Head.norm2_knowAt
#print axioms Cb.Pv.Head.hNorm2
