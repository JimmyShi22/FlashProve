-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12FwdName.lean: THE INVARIANT's HALF AT THE KEY FILE's THREE LATER PROXIMITY TESTS (rows 2.9 · 2.10 · 3.2 of the tables), IN THE GOALS' SCOPE, AT THE VERY TERMS OF The21AtName (Johnson/Top/Fire/Code/KeyAtName.lean): WITH NO PREMISE ON A LETTER. Three statements; each proof is one call.
(Words: "invariant": our files' "promise"; "sub-protocol": "block"; "accepts": "says yes"; "the IOP as written in Lean": "the description".)
OBJECT. On₂ | On₃ at B := baseAt X decN recBack · at_ := atSix · R := readAt tab · coll := collN. USER. Whoever fills the fields r2_9 · r2_10 · r3_2 at The21AtName.
WHAT FALLS against Johnson/RunOne/Law/K12FwdScope.lean: B.SmOnly: smOnlyK (Johnson/RunOne/KeyFillSmOnly.lean) · hcoll: cellOnly_collN (Johnson/Top/Fire/Code/KeyAtName.lean).
WHAT STAYS: the scope's six equations · at 3.2: the state in front is one that the last chain reaches. tab · enc · rad · off₂ · off₃ · D: free, as The21AtName binds them.
Limits. A sub-protocol that rejects everything meets every statement. That the invariant in front holds at any state is not said. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12FwdScope
import Johnson.RunOne.KeyFillSmOnly
import Johnson.Top.Fire.Code.KeyAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12FwdName
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.K12SeatsAt (tableBlocks)
open Johnson.RunOne.Law.K12FwdScope (fwd_29_scope fwd_210_scope fwd_32_scope)
open LPFD (baseAt readAt decN recBack collN cellOnly_collN MsgN)

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD) (tab : MsgN → ℕ → ℕ → OnBytes.F)
  (enc : (Nat → OnBytes.E) → Nat → OnBytes.E) (rad : Nat) (off₂ off₃ : Nat → Nat)
  {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hp : (descriptionFromSource X N P).planOk = true)
include hZ hP hm hX hL hp

/-- **Row 2.9.** -/
theorem fwd_29_name : ∀ b : Block St₂ Key.Claim, (descriptionFromSource X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 0)]? = some b →
    ∀ a c rs gs, On₂ X N P D (baseAt X decN recBack) atSix (readAt tab) enc rad collN off₂ 9 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) atSix (open₂ 9) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D (baseAt X decN recBack) atSix (readAt tab) enc rad collN off₂ 10 c :=
  fwd_29_scope X N P D _ atSix _ enc rad collN off₂ hZ hP hm hX hL hp (smOnlyK _ _ _ _ _ _ _) fun y y' r h => (cellOnly_collN y y' r h).1

/-- **Row 2.10.** -/
theorem fwd_210_name (nO : H2U.PlaceNums) (hO : P.O = some nO) : ∀ b : Block St₂ Key.Claim, (descriptionFromSource X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 1)]? = some b →
    ∀ a c rs gs, On₂ X N P D (baseAt X decN recBack) atSix (readAt tab) enc rad collN off₂ 10 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) atSix (open₂ 10) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D (baseAt X decN recBack) atSix (readAt tab) enc rad collN off₂ 11 c :=
  fwd_210_scope X N P D _ atSix _ enc rad collN off₂ hZ hP hm hX hL hp nO hO (smOnlyK _ _ _ _ _ _ _) fun y y' r h => (cellOnly_collN y y' r h).1

/-- **Row 3.2**, at a state that the last chain reaches. -/
theorem fwd_32_name (Dh : WholeD) : ∀ b : Block St₃ Key.Claim, (descriptionFromSource X N P).second.blocksInOrder[2]? = some b →
    ∀ a c rs gs, On₃ X N P D (baseAt X decN recBack) atSix (readAt tab) collN off₂ off₃ 2 a → LPFD.Hist₃ (descriptionFromSource X N P) Dh 2 a.1 →
      (held b : Block (P₃ × St₃) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) atSix (open₃ 2) (strsOf (fr₃ X N P D) a.2) (strsOf (fr₃ X N P D) c.2) → On₃ X N P D (baseAt X decN recBack) atSix (readAt tab) collN off₂ off₃ 3 c :=
  fwd_32_scope X N P D _ atSix _ collN off₂ off₃ hZ hP hm hX hL hp (fun y y' r h => (cellOnly_collN y y' r h).1) Dh

end Johnson.RunOne.Law.K12FwdName

#print axioms Johnson.RunOne.Law.K12FwdName.fwd_29_name
#print axioms Johnson.RunOne.Law.K12FwdName.fwd_210_name
#print axioms Johnson.RunOne.Law.K12FwdName.fwd_32_name
