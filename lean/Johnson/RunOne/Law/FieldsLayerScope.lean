-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/FieldsLayerScope.lean: THE
FIELDS r1_5 AND r1_11 (FieldsLayer.lean) AT THE VERY TERMS AT WHICH ANOTHER FILE'S JOINING TERM
ASKS THEM (LPFD.The21AtName, Johnson/Top/Fire/Code/KeyAtName.lean), IN SCOPE: as r1_4 and r1_10
(FieldsAtName.lean, FieldsAtNameScope.lean).

Main names:
  r1_5_in_scope, r1_11_in_scope: the two fields of The21 at The21AtName's terms.
  layer_fit: a witness for the forms: The21AtName, taken apart, has the very types of the two
    conclusions.

Object: the fields r1_5 and r1_11 of LPFD.The21 at The21AtName's terms.
User: none yet.
Letters: X, N, P, DK, tab; the frame's heads and tails.
ALL PREMISES: the scope's four (the public files are in scope · the policy read · the chains made ·
the source of them) · planOk · q₁ (The21AtName's own binder) · hb₁: the first chain's bases:
The21AtName's own fourth conjunct.

Limits. IMPLICATIONS: no member of the promise at these terms, and no public files at which the
premises hold together, is exhibited. Two fields of twenty-one. Nothing on soundness.

-/
import Johnson.RunOne.Law.FieldsLayer
import Johnson.RunOne.Law.FieldsAtNameScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.FieldsLayerScope
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open Lk6.AtPlan
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where pinned madeAt sourceOf)
open Johnson.G.OfPlan (Made)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁ atSix smReadsK)
open Johnson.RunOne.KeyRows1 (open₁)
open Johnson.RunOne.Law.SourceIs
open Johnson.RunOne.Law.AtFreeCfg
open Johnson.RunOne.Law.AllAtO
open Johnson.RunOne.Law.KeyInScope
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.FieldsLayer
open LPFD (On₁' KeepsAt baseAt readAt decN recBack collN cellOnly_collN capRest MsgN)

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}
  (DK : WholeD) (tab : MsgN → ℕ → ℕ → OnBytes.F)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))

/-- **THE FIELD r1_5 AT The21AtName's TERMS, IN SCOPE.** -/
theorem r1_5_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (FK X N P).planOk = true) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hb₁ : ∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N
            P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some p
                → ∀ j ∈ pinned (open₁ 2 n), (atSix j).1 < p.base) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
      (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
              (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 5 := by
  obtain ⟨-, -, hR⟩ := seat_in_scope hZ hP hm hX hp
  have hn : X.Y.k.oneTime.ranges.lookups.length = 2 := by
    rw [(five_in_scope hZ hP hm hX hp).2.1]
    exact held_full_two
  exact r1_5 X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN c₁ k₁ c₂ k₂ c₃
      k₃
    capRest capRest capRest () () hp q₁ hR (answers_in_scope hZ hP hm hX hp) hn
    (fun n p h2 h14 hx j hj => hb₁ n p hx j (by rw [pinned_link n h2 h14]; exact hj))
    cellOnly_collN (smReadsK _ _ _ _ _ _ _) rfl

/-- **THE FIELD r1_11 AT The21AtName's TERMS, IN SCOPE.** -/
theorem r1_11_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (FK X N P).planOk = true) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hb₁ : ∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂
        c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N
            P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some p
                → ∀ j ∈ pinned (open₁ 2 n), (atSix j).1 < p.base) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
      (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
              (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 11 := by
  obtain ⟨-, -, hR⟩ := seat_in_scope hZ hP hm hX hp
  have hn : X.Y.k.oneTime.ranges.lookups.length = 2 := by
    rw [(five_in_scope hZ hP hm hX hp).2.1]
    exact held_full_two
  exact r1_11 X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN c₁ k₁ c₂ k₂
      c₃ k₃
    capRest capRest capRest () () hp q₁ hR (answers_in_scope hZ hP hm hX hp) hn
    (fun n p h2 h14 hx j hj => hb₁ n p hx j (by rw [pinned_link n h2 h14]; exact hj))
    cellOnly_collN (smReadsK _ _ _ _ _ _ _) rfl

/-- **A WITNESS FOR THE FORMS**: a member of The21 at The21AtName's terms has, as its fields r1_5
and r1_11, the very types of the two conclusions above. It proves nothing else. -/
theorem layer_fit (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (off₂ off₃ : ℕ → ℕ)
    (H : LPFD.The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ()
      (baseAt X decN recBack) atSix (readAt tab) enc rad collN off₂ off₃) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
        (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
            capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
                (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 5 ∧
      KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
        (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
            capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
                (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 11 :=
  ⟨H.r1_5, H.r1_11⟩

end Johnson.RunOne.Law.FieldsLayerScope

#print axioms Johnson.RunOne.Law.FieldsLayerScope.r1_5_in_scope
#print axioms Johnson.RunOne.Law.FieldsLayerScope.r1_11_in_scope
#print axioms Johnson.RunOne.Law.FieldsLayerScope.layer_fit
