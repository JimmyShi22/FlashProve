-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/ReachHands.lean: "REACHED" AT AN IOP AS WRITTEN IN LEAN (RchAt, ReachAt.lean;
RchAt₂, RchAt₃, ReachThree.lean) ARE FAMILIES THAT THE TABLE's FRAME's SECOND FORM TAKES
(Johnson/Desc/Sound/ChainOfPromisesR.lean: HandsOn, EachHandsOn): each is handed on at every piece
of its row, whatever extractor is laid in.

  handsOn_at, handsOn_map   HandsOn (RchAt F) k at the piece number k of the first row, and at that
                    piece with another extractor; handsOn₂_…, handsOn₃_…: at the two other rows
  eachHandsOn_of    from "at every number" to the list's form
  eachHandsOn_row, eachHandsOn_row₂, eachHandsOn_row₃   EachHandsOn … 0 at the three rows

No soundness statement.

-/
import Johnson.Top.H0.Walk.ReachThree
import Johnson.Desc.Sound.ChainOfPromisesR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound

section
variable {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type} {F : FileDescription Xi}
  {T : ThreeAt C D all F X₁ X₂ W}

theorem handsOn_at (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (F.XiPub × F.S₁) F.Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) : HandsOn (RchAt F) k q :=
  fun _ _ _ hr h => rchAt_hand hT hq h hr

theorem handsOn_map (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (F.XiPub × F.S₁) F.Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) (E) : HandsOn (RchAt F) k (q.withMap E) :=
  fun _ _ _ hr h => rchAt_hand_map hT hq E h hr

theorem handsOn₂_at (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₂ T.ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl W}
    (hq : (T.p₂ :: T.l₂)[k]? = some q) : HandsOn (RchAt₂ F) k q :=
  fun _ _ _ hr h => rchAt₂_hand hT hq h hr

theorem handsOn₂_map (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₂ T.ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl W}
    (hq : (T.p₂ :: T.l₂)[k]? = some q) (E) : HandsOn (RchAt₂ F) k (q.withMap E) :=
  fun _ _ _ hr h => rchAt₂_hand_map hT hq E h hr

theorem handsOn₃_at (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₃ T.ft₃) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl W}
    (hq : (T.p₃ :: T.l₃)[k]? = some q) : HandsOn (RchAt₃ F) k q :=
  fun _ _ _ hr h => rchAt₃_hand hT hq h hr

theorem handsOn₃_map (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₃ T.ft₃) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl W}
    (hq : (T.p₃ :: T.l₃)[k]? = some q) (E) : HandsOn (RchAt₃ F) k (q.withMap E) :=
  fun _ _ _ hr h => rchAt₃_hand_map hT hq E h hr

end

/-- From "at every number" to the list's form. -/
theorem eachHandsOn_of {A Cl W : Type} {C : CK} {Fr : Frame} (Rch : ℕ → A × Fr.E.Str → Prop) :
    ∀ (l : List (Piece C Fr A Cl W)) (k : ℕ),
    (∀ i q, l[i]? = some q → HandsOn Rch (k + i) q) → EachHandsOn Rch k l
  | [], _, _ => trivial
  | q :: l, k, h =>
    ⟨h 0 q rfl, eachHandsOn_of Rch l (k + 1) fun i q' hq' => by
      have := h (i + 1) q' hq'
      rwa [Nat.add_assoc, Nat.add_comm 1 i]⟩

theorem eachHandsOn_row {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}
    {F : FileDescription Xi} {T : ThreeAt C D all F X₁ X₂ W} (hT : OfDesc F T) :
    EachHandsOn (RchAt F) 0 (T.p₁ :: T.l₁) :=
  eachHandsOn_of _ _ 0 fun i q hq => by
    rw [Nat.zero_add]
    exact handsOn_at hT hq

theorem eachHandsOn_row₂ {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}
    {F : FileDescription Xi} {T : ThreeAt C D all F X₁ X₂ W} (hT : OfDesc F T) :
    EachHandsOn (RchAt₂ F) 0 (T.p₂ :: T.l₂) :=
  eachHandsOn_of _ _ 0 fun i q hq => by
    rw [Nat.zero_add]
    exact handsOn₂_at hT hq

theorem eachHandsOn_row₃ {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}
    {F : FileDescription Xi} {T : ThreeAt C D all F X₁ X₂ W} (hT : OfDesc F T) :
    EachHandsOn (RchAt₃ F) 0 (T.p₃ :: T.l₃) :=
  eachHandsOn_of _ _ 0 fun i q hq => by
    rw [Nat.zero_add]
    exact handsOn₃_at hT hq

#print axioms handsOn_map
#print axioms eachHandsOn_row
#print axioms eachHandsOn_row₂
#print axioms eachHandsOn_row₃

end Johnson.Desc.First.Walk.Tied
