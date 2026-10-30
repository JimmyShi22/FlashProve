-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FieldsAtNameScope.lean: THE
FIELDS r1_4 AND r1_10 AT The21AtName's TERMS (FieldsAtName.lean), IN SCOPE: the premises of
r1_4_at_name and r1_10_at_name that are theorems in scope are paid by these theorems: RoomFor,
target = 128 and LookHeld (seat_in_scope, AtFreeCfg.lean) · the own message counts an answer
(answers_in_scope, AllAtO.lean) · two lookups (five_in_scope, KeyInScope.lean; held_full_two).

Main names:
  r1_4_in_scope, r1_10_in_scope: the two fields of The21 at The21AtName's terms.

Object: the fields r1_4 and r1_10 of LPFD.The21 at The21AtName's terms.
User: paid_in_scope (Johnson/Top/Fire/Code/KeyAtRest.lean).
Letters: X, N, P, DK, tab; the frame's heads and tails.
ALL PREMISES: the scope's four, as letters_of_handed takes them
(Johnson/Top/Fire/Code/KeyPublicAtSeat.lean): the public files are in scope · the policy read · the
chains made · the source of them · planOk · the data: the description's data of a file are
DK.at frS.P.T.a · q₁, q₂, q₃ (The21AtName's own binders) · hb₁: the first chain's bases:
The21AtName's own fourth conjunct.

Limits. Two fields of twenty-one. Nothing on soundness.

-/
import Johnson.RunOne.Law.FieldsAtName
import Johnson.RunOne.Law.AllAtO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FieldsAtNameScope
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open Lk6.AtPlan
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where pinned madeAt sourceOf)
open Johnson.G.OfPlan (Made)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁ atSix)
open Johnson.RunOne.KeyRows1 (open₁)
open Johnson.RunOne.Law.SourceIs
open Johnson.RunOne.Law.AtFreeCfg
open Johnson.RunOne.Law.AllAtO
open Johnson.RunOne.Law.KeyInScope
open Johnson.RunOne.Law.FieldsAtName
open LPFD (On₁' KeepsAt baseAt readAt decN recBack collN capRest MsgN)

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}
  (DK : WholeD) (tab : MsgN → ℕ → ℕ → OnBytes.F)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))

/-- **THE FIELD r1_4 AT The21AtName's TERMS, IN SCOPE.** -/
theorem r1_4_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (FK X N P).planOk = true) (file : String)
    (hD : (FK X N P).data file = .ok (DK.at frS.P.T.a)) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hb₁ : ∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N
            P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some p
                → ∀ j ∈ pinned (open₁ 2 n), (atSix j).1 < p.base) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
      (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
              (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 4 := by
  obtain ⟨ht, hL, hR⟩ := seat_in_scope hZ hP hm hX hp
  have hn : X.Y.k.oneTime.ranges.lookups.length = 2 := by
    rw [(five_in_scope hZ hP hm hX hp).2.1]
    exact held_full_two
  exact r1_4_at_name X N P DK tab c₁ k₁ c₂ k₂ c₃ k₃ hp file hD q₁ q₂ q₃ hR
    (answers_in_scope hZ hP hm hX hp) hn ht (hL 0 (by omega)) hb₁

/-- **THE FIELD r1_10 AT The21AtName's TERMS, IN SCOPE.** -/
theorem r1_10_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (FK X N P).planOk = true) (file : String)
    (hD : (FK X N P).data file = .ok (DK.at frS.P.T.a)) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hb₁ : ∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N
            P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some p
                → ∀ j ∈ pinned (open₁ 2 n), (atSix j).1 < p.base) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
      (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
              (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 10 := by
  obtain ⟨ht, hL, hR⟩ := seat_in_scope hZ hP hm hX hp
  have hn : X.Y.k.oneTime.ranges.lookups.length = 2 := by
    rw [(five_in_scope hZ hP hm hX hp).2.1]
    exact held_full_two
  exact r1_10_at_name X N P DK tab c₁ k₁ c₂ k₂ c₃ k₃ hp file hD q₁ q₂ q₃ hR
    (answers_in_scope hZ hP hm hX hp) hn ht (hL 1 (by omega)) hb₁

end Johnson.RunOne.Law.FieldsAtNameScope

#print axioms Johnson.RunOne.Law.FieldsAtNameScope.r1_4_in_scope
#print axioms Johnson.RunOne.Law.FieldsAtNameScope.r1_10_in_scope
