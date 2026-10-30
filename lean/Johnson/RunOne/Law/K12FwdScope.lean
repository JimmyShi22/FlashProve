-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12FwdScope.lean: ROWS 2.9 · 2.10 · 3.2 OF THE KEY FILE's TABLES: THE PROMISE's HALVES AT THE DESCRIPTION's OWN BLOCKS, AND IN THE GOALS' SCOPE. Statements; each proof is a call.
OBJECT. The blocks at (Fk X N P).shared.blocksInOrder and .second.blocksInOrder where the three later proximity tests stand (fk_U_at | fk_O_at | fk_own_at, Johnson/RunOne/Law/K12SeatsAt.lean) · On₂ | On₃. USER. Whoever fills the fields r2_9 · r2_10 · r3_2 of The21.
WHAT FALLS against Johnson/RunOne/Law/K12FwdAt.lean: hb (retyping, baring and the stamp of the place turn no decision: rfl) · IN SCOPE: hf (a field of the test on the plan) · hft ×2 (Johnson/RunOne/Law/K12AtMaker.lean: the maker's yes) · ha1 (samples_in_scope, Johnson/RunOne/KeySamples.lean) · at 3.2, AT A STATE THAT THE LAST CHAIN REACHES: the codes' lengths at the state's codes (codes_in_scope₃, Johnson/RunOne/KeyCodesScope.lean: the carried codes are the written key's; their lengths by the kernel: lengths_full).
WHAT STAYS: the scope's own equations (the three public files read; the maker's yeses) and (descriptionFromSource X N P).planOk = true · ON THE TABLES' FILES' LETTERS: B.SmOnly (2.9 | 2.10) · hcoll.
OUTSIDE THE SCOPE no test of the description ties the sized key's codes (at which the later chains start) to the one-time chain's: fwd_32_flat keeps the codes' lengths at the state's codes as a premise.
  fwd_29_flat | fwd_210_flat | fwd_32_flat · fwd_29_scope | fwd_210_scope | fwd_32_scope.
Limits. A block that says no to all meets every statement. That a promise in front is met at any state is not said. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12FwdAt
import Johnson.RunOne.Law.K12AtMaker
import Johnson.RunOne.Law.K12SeatsAt
import Johnson.RunOne.KeySamples
import Johnson.RunOne.KeyCodesLater
import Johnson.RunOne.KeyCodesScope
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12FwdScope
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (Blk' Gs)
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.K12SeatsAt (tableBlocks fk_U_at fk_O_at fk_own_at)
open Johnson.RunOne.Law.K12FwdAt (fwd_29_at fwd_210_at fwd_32_at)
open Johnson.RunOne.Law.K12AtMaker (later_zero)
open Johnson.RunOne.Law.K12Join15 (lengths_of_fileOk)
open Johnson.RunOne.KeySendGood (samples_in_scope)

variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD) (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M)
  (enc : (Nat → OnBytes.E) → Nat → OnBytes.E) (rad : Nat) (coll : Strs → Rec → Prop) (off₂ off₃ : Nat → Nat)

theorem fwd_29_flat (hf : (descriptionFromSource X N P).fileOk = true) (hft : P.U.nums.firstTree = 0) (ha1 : (oneAt X).given.plan.samples = 1) (hSm : B.SmOnly)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r) :
    ∀ b : Block St₂ Key.Claim, (descriptionFromSource X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 0)]? = some b →
    ∀ a c rs gs, On₂ X N P D B at_ R enc rad coll off₂ 9 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₂ 9) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D B at_ R enc rad coll off₂ 10 c := by
  intro b hb
  obtain rfl := Option.some.inj ((fk_U_at X N P).symm.trans hb)
  exact fwd_29_at X N P D B at_ R enc rad coll off₂ hf hft ha1 hSm hcoll _ rfl

theorem fwd_210_flat (hf : (descriptionFromSource X N P).fileOk = true) (nO : H2U.PlaceNums) (hO : P.O = some nO) (hft : nO.nums.firstTree = 0)
    (ha1 : (oneAt X).given.plan.samples = 1) (hSm : B.SmOnly) (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r) :
    ∀ b : Block St₂ Key.Claim, (descriptionFromSource X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 1)]? = some b →
    ∀ a c rs gs, On₂ X N P D B at_ R enc rad coll off₂ 10 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₂ 10) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D B at_ R enc rad coll off₂ 11 c := by
  intro b hb
  obtain rfl := Option.some.inj ((fk_O_at X N P nO hO).symm.trans hb)
  exact fwd_210_at X N P D B at_ R enc rad coll off₂ hf nO hO hft ha1 hSm hcoll _ rfl

theorem fwd_32_flat (hf : (descriptionFromSource X N P).fileOk = true) (ha1 : (oneAt X).given.plan.samples = 1)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r) :
    ∀ b : Block St₃ Key.Claim, (descriptionFromSource X N P).second.blocksInOrder[2]? = some b →
    ∀ a c rs gs, On₃ X N P D B at_ R coll off₂ off₃ 2 a → a.1.2.st.codes.lengthsOk = true → (held b : Block (P₃ × St₃) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₃ 2) (strsOf (fr₃ X N P D) a.2) (strsOf (fr₃ X N P D) c.2) → On₃ X N P D B at_ R coll off₂ off₃ 3 c := by
  intro b hb
  obtain rfl := Option.some.inj ((fk_own_at X N P).symm.trans hb)
  exact fwd_32_at X N P D B at_ R coll off₂ off₃ hf ha1 hcoll _ rfl

/-- The written key's codes' lengths are in order: closed data, by the kernel. -/
theorem lengths_full : Lk6.AtPlan.keyFull.codes.lengthsOk = true := by decide +kernel

section
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hp : (descriptionFromSource X N P).planOk = true)
include hZ hP hm hX hL hp

/-- **Row 2.9's promise's half, in scope.** -/
theorem fwd_29_scope (hSm : B.SmOnly) (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r) :
    ∀ b : Block St₂ Key.Claim, (descriptionFromSource X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 0)]? = some b →
    ∀ a c rs gs, On₂ X N P D B at_ R enc rad coll off₂ 9 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₂ 9) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D B at_ R enc rad coll off₂ 10 c :=
  fwd_29_flat X N P D B at_ R enc rad coll off₂ (((descriptionFromSource X N P).planOk_ok).1 hp).fileOk (later_zero hL).1 (samples_in_scope hZ hP hm hX hp) hSm hcoll

/-- **Row 2.10's, in scope.** -/
theorem fwd_210_scope (nO : H2U.PlaceNums) (hO : P.O = some nO) (hSm : B.SmOnly) (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r) :
    ∀ b : Block St₂ Key.Claim, (descriptionFromSource X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 1)]? = some b →
    ∀ a c rs gs, On₂ X N P D B at_ R enc rad coll off₂ 10 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₂ 10) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D B at_ R enc rad coll off₂ 11 c :=
  fwd_210_flat X N P D B at_ R enc rad coll off₂ (((descriptionFromSource X N P).planOk_ok).1 hp).fileOk nO hO ((later_zero hL).2 nO hO) (samples_in_scope hZ hP hm hX hp) hSm hcoll

/-- **Row 3.2's, in scope, at a state that the last chain reaches.** -/
theorem fwd_32_scope (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r) (Dh : WholeD) :
    ∀ b : Block St₃ Key.Claim, (descriptionFromSource X N P).second.blocksInOrder[2]? = some b →
    ∀ a c rs gs, On₃ X N P D B at_ R coll off₂ off₃ 2 a → LPFD.Hist₃ (descriptionFromSource X N P) Dh 2 a.1 → (held b : Block (P₃ × St₃) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₃ 2) (strsOf (fr₃ X N P D) a.2) (strsOf (fr₃ X N P D) c.2) → On₃ X N P D B at_ R coll off₂ off₃ 3 c := by
  intro b hb a c rs gs hon hh
  have hf := (((descriptionFromSource X N P).planOk_ok).1 hp).fileOk
  have e : a.1.2.st.codes = Lk6.AtPlan.keyFull.codes := Johnson.RunOne.KeyCodes.codes_in_scope₃ hZ hP hm hX Dh 2 a.1 hh
  exact fwd_32_flat X N P D B at_ R coll off₂ off₃ hf (samples_in_scope hZ hP hm hX hp) hcoll b hb a c rs gs hon (by
    rw [e]
    exact lengths_full)

end

end Johnson.RunOne.Law.K12FwdScope

#print axioms Johnson.RunOne.Law.K12FwdScope.lengths_full
#print axioms Johnson.RunOne.Law.K12FwdScope.fwd_29_flat
#print axioms Johnson.RunOne.Law.K12FwdScope.fwd_210_flat
#print axioms Johnson.RunOne.Law.K12FwdScope.fwd_32_flat
#print axioms Johnson.RunOne.Law.K12FwdScope.fwd_29_scope
#print axioms Johnson.RunOne.Law.K12FwdScope.fwd_210_scope
#print axioms Johnson.RunOne.Law.K12FwdScope.fwd_32_scope
