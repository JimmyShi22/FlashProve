-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15J.lean: THE JOIN: THE FIELD r1_15 OF THE KEY FILE's TABLES AT The21AtName's TERMS (Johnson/Top/Fire/Code/KeyAtName.lean), IN SCOPE: the equations of scope that Johnson/RunOne/Law/K12Facts15LS.lean's r1_15_scope_cap takes as premises are paid here by their theorems, in one environment. Statements with proofs: calls, and one evaluation in the kernel. IT PAYS NO FIELD OF THE TABLES: Gives15 HOLDS ALL THE WEIGHT AND IS SHOWN OF NOTHING. (Where this and lean/THEOREM.md differ, the page holds.)
OBJECT. `LPFD.The21`'s field r1_15 at the letters that The21AtName fixes: the rests at the cap, the base, the seats, the reading, the collision's relation.
USER. The21AtName's filler.
LETTERS. X N P DK tab; the chains' heads and tails; rd.
ALL PREMISES. The scope's four, as another file takes them (Johnson/RunOne/Law/FieldsAtNameScope.lean): the public files are in scope · the policy read · the chains made, at any digest · the source of them. Four conjuncts of what the seat's yes hands: the place's numbers are made of the same m · the description's tests planOk and wantedOk · its data are DK's at the frame's depth. DK is the written data. q₁. AND Gives15.
WHAT IT SAYS AND DOES NOT SAY OF BITS. Each of the 23 rounds' count is at most 2⁻¹²⁸ of ITS OWN round's written verifier messages (bits of work among them), by exact numbers in the kernel; one round at a time, no sum.

  two_full, hl_in_scope: the plan has two lookups.
  r1_15_in_scope: the field. PAID INSIDE: the sized key (key_in_scope) · the setting of all sizes (set_in_scope) · the nineteen blocks' numbers of rounds (rounds_in_scope) · two lookups · the rests' errors are the cap's (by the text of capRest).
Limits. As empty as Gives15. One field of twenty-one. One size. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Facts15LS
import Johnson.RunOne.Law.K12Facts15Z
import Johnson.RunOne.Sound.KeyListsInScope
import Johnson.Top.Fire.Code.KeyAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Johnson.RunOne.Law.K12AtThe21
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open Lk6.AtPlan
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where madeAt sourceOf rangesNumbers lookupsOf)
open Johnson.G.OfPlan (Made)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁ atSix)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (key_in_scope five_in_scope)
open LPFD (On₁' KeepsAt baseAt readAt decN recBack collN capRest MsgN)

theorem two_full : (Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)).length = 2 := by
  decide +kernel

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- The plan has two lookups. -/
theorem hl_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) :
    (lookupsOf X.Y.k.oneTime).length = 2 := by
  obtain ⟨-, hr, hlin, -, -⟩ := five_in_scope hZ hP hm hX hp
  unfold lookupsOf
  rw [hr, hlin]
  exact two_full

variable (DK : WholeD) (tab : MsgN → ℕ → ℕ → OnBytes.F)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))

/-- **THE FIELD r1_15 AT The21AtName's TERMS, IN SCOPE, FROM THE ONE PREMISE THAT HOLDS THE WEIGHT.** -/
theorem r1_15_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (file : String)
    (hD : (Fk X N P).data file = .ok (DK.at frS.P.T.a)) (hDK : DK = Johnson.G.writtenKFull)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (rd : ℕ → ℕ)
    (gives : Gives15 (W := Unit) X N P DK c₁ k₁ capRest (baseAt X decN recBack) atSix (readAt tab)
      (OnH X N P DK (baseAt X decN recBack) atSix (readAt tab) collN) K12Facts15.radRng rd) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
      (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 15 :=
  r1_15_scope_cap X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tab)
    collN file rd m hX hN hp hD hDK (key_in_scope hZ hP hm) (K12Facts15.set_in_scope hZ hP hm)
    ((Johnson.RunOne.Sound.rounds_in_scope hZ hP hm hX hp hw).1.trans rfl) q₁ (hl_in_scope hZ hP hm hX hp)
    (fun _ => rfl) gives

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.two_full
#print axioms Johnson.RunOne.Law.K12AtThe21.hl_in_scope
#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_in_scope
