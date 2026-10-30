-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/AllAtO.lean: It stands on Johnson/RunOne/Sound/.
ALL THAT THESE FILES SAY OF THE KEY FILE'S DESCRIPTION IN SCOPE, OF ONE
DESCRIPTION: one "there are X N P" with every conclusion behind it. seat_at_o, front_at_o
(ReadAtO.lean), units_at_o (UnitsInScope.lean) and links_at_o (LinksAtO.lean) each bind a triple of
their own, and the equation r = (FK X N P).run pins no X: so two of them cannot be joined. Here they
are joined behind one reading of the piece's yes.

Main names:
  roundsFit_two, fk_two₀, fk_two₁: the blocks 0 and 1 declare two rounds: rounds that fit are two.
  answers_in_scope: the lookups' own message counts an answer, in scope, at any digest.
  FrontGood X N P: the two steps and what the row at border 2 promises of the record.
  front_in_scope: FrontGood, in scope, at any digest.
  AllGood X N P hp D: the target, LookHeld, RoomFor, FrontGood, the units, LinksGood
    (LinksAtO.lean), ChainGood (ChainAtO.lean), and: the test on the instance says yes at every
    typed record (OkStartInScope.lean).
  all_in_scope, all_at_fixed, all_at_o: AllGood; from Key.keyDataAndDecisionAtFixedDigest's yes; at every letter o.

Object: (FK X N P) at the X N P that Key.keyDataAndDecisionAtFixedDigest's yes gives (laidFixed_is,
Johnson/Desc/Key/SlotIs.lean).
User: Johnson/RunOne/Law/FieldsAtNameScope.lean calls answers_in_scope.
Letters: Zp: three public files in scope · o: any function in the hash function's place.

Limits. Those of the files that are joined. That the slot of the verifier's text holds the term of
all_at_o is another file's equation, not imported here. One size. Nothing on soundness.

-/
import Johnson.RunOne.Law.ChainAtO
import Johnson.RunOne.Law.UnitsInScope
import Johnson.RunOne.Law.OkStartInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace Johnson.RunOne.Law.AllAtO
open OnBytes OnBytes.Params
open OnBytes.Maker (WholeD)
open OnBytes.Model (wsLayOf)
open OnBytes.Model.Verify (Public)
open OnBytes.Params (exc_bind recordLines)
open Lk6.AtPlan
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc (Block roundsFit)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim Source madeAt sourceOf keyDataAndDecisionAtFixedDigest KeyRun)
open Johnson.G.OfPlan (Made)
open Johnson.RunOne.Sound (FK fk_idx_at fk_msg_at)
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.SourceIs
open Johnson.RunOne.Law.AtFreeCfg
open Johnson.RunOne.Law.FrontSteps
open Johnson.RunOne.Law.FrontAtFK
open Johnson.RunOne.Law.ReadAtO
open Johnson.RunOne.Law.UnitsInScope
open Johnson.RunOne.Law.LinksAtO
open Johnson.RunOne.Law.ChainAtO
open Johnson.RunOne.Law.OkStartInScope

/-- Rounds that fit two declared rounds are two. -/
theorem roundsFit_two {a b : Fmt.DeclaredRound} :
    ∀ {rs : List Fmt.RoundView}, roundsFit [a, b] rs = true → ∃ r₁ r₂, rs = [r₁, r₂]
  | [r₁, r₂], _ => ⟨r₁, r₂, rfl⟩
  | [], h => by simp [roundsFit] at h
  | [_], h => by simp [roundsFit] at h
  | _ :: _ :: _ :: _, h => by simp [roundsFit] at h

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- Block 0 declares two rounds. -/
theorem fk_two₀ (b : Block FirstState Claim) (hb : (FK X N P).first.blocksInOrder[0]? = some b)
    {rs : List Fmt.RoundView} (h : roundsFit b.rounds rs = true) : ∃ r₁ r₂, rs = [r₁, r₂] := by
  obtain ⟨g, hg⟩ := fk_idx_at X N P
  obtain rfl := Option.some.inj (hg.symm.trans hb)
  exact roundsFit_two h

/-- Block 1 declares two rounds. -/
theorem fk_two₁ (b : Block FirstState Claim) (hb : (FK X N P).first.blocksInOrder[1]? = some b)
    {rs : List Fmt.RoundView} (h : roundsFit b.rounds rs = true) : ∃ r₁ r₂, rs = [r₁, r₂] := by
  obtain ⟨g, hg⟩ := fk_msg_at X N P
  obtain rfl := Option.some.inj (hg.symm.trans hb)
  exact roundsFit_two h

/-- **The two steps in front of the first link, and what the row at border 2 promises of the
record.** -/
def FrontGood : Prop :=
  (∀ (b : Block FirstState Claim) (q : (FK X N P).XiPub) (t : FirstState) (r₁ r₂ : Fmt.RoundView)
      (gs : List (List (ℕ × List UInt64))), (FK X N P).first.blocksInOrder[0]? = some b →
      b.decide ((FK X N P).start₁ q) [r₁, r₂] gs = .ok t → Half X.Y.k.oneTime t) ∧
    (∀ (b : Block FirstState Claim) (s t : FirstState) (r₁ r₂ : Fmt.RoundView)
      (gs : List (List (ℕ × List UInt64))), (FK X N P).first.blocksInOrder[1]? = some b →
      Half X.Y.k.oneTime s → b.decide s [r₁, r₂] gs = .ok t → Front X.Y.k.oneTime t) ∧
    ∀ (Ex : FirstState → Prop) (t : FirstState), Front X.Y.k.oneTime t → Ex t →
      t.base.rows.length = 0 ∧ t.base.keys.length = 0 ∧
        PromL X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime) 0 X.Y.k.oneTime.ranges.lookups.length
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape)
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) Ex 0 t

/-- **All that is said of one description and its data.** -/
def AllGood (hp : (FK X N P).planOk = true) (D : WholeD) : Prop :=
  X.set.target = 128 ∧
    (∀ l, l < X.Y.k.oneTime.ranges.lookups.length →
      LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
        (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)))) ∧
    RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape ∧
    FrontGood X N P ∧
    (∃ Y, wsLayOf wsFull true recordLines.blockLog = .ok Y ∧ X.Y.units = Plan.unitsOfLayout Y) ∧
    LinksGood X N P hp D ∧ ChainGood X N P hp D ∧
    ∀ rec : OnBytes.Flat.RecFull, (VerifiableInference.Desc.Key.descriptionFromSource X N P).okStart
      (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample rec) = true

variable {X N P}

/-- The lookups' own message counts an answer, in scope, at any digest. -/
theorem answers_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (FK X N P).planOk = true) :
    X.Y.k.oneTime.ranges.message.shape.answers ≠ 0 := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hP
  have hk := key_at_chains hP (madeAt_parts hm).2.1
  rw [(five_at hm hX hp).2.1, hk]
  exact answers_full

/-- **The front, in scope, at any digest.** -/
theorem front_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (FK X N P).planOk = true) : FrontGood X N P :=
  ⟨fun b q _ _ _ _ hb hd => fk_step₀ X N P hp b hb q hd,
    fun b _ _ _ _ _ hb hs hd => fk_step₁ X N P (answers_in_scope hZ hP hm hX hp) b hb hs hd,
    fun _ _ hf hE => fk_border₂ X N P hp (seat_in_scope hZ hP hm hX hp).2.2 hf hE⟩

/-- **ALL OF IT, OF ONE DESCRIPTION, IN SCOPE, AT ANY DIGEST.** -/
theorem all_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (FK X N P).planOk = true) {D : WholeD}
    (hD : (FK X N P).data "key file" = .ok D) : AllGood X N P hp D := by
  obtain ⟨h1, h2, h3⟩ := seat_in_scope hZ hP hm hX hp
  exact ⟨h1, h2, h3, front_in_scope hZ hP hm hX hp, units_in_scope hZ hP hm hX,
    links_in_scope hZ hP hm hX hp hD, chain_in_scope hZ hP hm hX hp hD,
    okStart_in_scope hZ hP hm hX hp⟩

/-- **From the yes of the key file's piece at the fixed digest.** -/
theorem all_at_fixed {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {D : WholeD} {r : KeyRun} (h : keyDataAndDecisionAtFixedDigest Z Zp.lay = .ok (D, r)) :
    ∃ X N P, ∃ hp : (FK X N P).planOk = true, (FK X N P).data "key file" = .ok D ∧
      r = (FK X N P).run ∧ AllGood X N P hp D := by
  obtain ⟨m, X, N, P, hm, hX, hp, hD, hr⟩ := Johnson.RunOne.Law.KeyInScope.laid_parts h
  exact ⟨X, N, P, hp, hD, hr, all_in_scope hZ hP hm hX hp hD⟩

/-- **AT EVERY LETTER o IN THE HASH FUNCTION'S PLACE.** -/
theorem all_at_o {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {o : Nat → ByteArray → ByteArray} {D : WholeD} {r : KeyRun}
    (h : ((publicOfO o Zp.pol Zp.KL (some Zp.lay)).bind fun Z => keyDataAndDecisionAtFixedDigest Z Zp.lay) =
      .ok (D, r)) :
    ∃ X N P, ∃ hp : (FK X N P).planOk = true, (FK X N P).data "key file" = .ok D ∧
      r = (FK X N P).run ∧ AllGood X N P hp D := by
  obtain ⟨Z, hP, hl⟩ := exc_bind h
  exact all_at_fixed hZ (readOf_publicOfO hP) hl

end Johnson.RunOne.Law.AllAtO

#print axioms Johnson.RunOne.Law.AllAtO.roundsFit_two
#print axioms Johnson.RunOne.Law.AllAtO.fk_two₀
#print axioms Johnson.RunOne.Law.AllAtO.fk_two₁
#print axioms Johnson.RunOne.Law.AllAtO.answers_in_scope
#print axioms Johnson.RunOne.Law.AllAtO.front_in_scope
#print axioms Johnson.RunOne.Law.AllAtO.all_in_scope
#print axioms Johnson.RunOne.Law.AllAtO.all_at_fixed
#print axioms Johnson.RunOne.Law.AllAtO.all_at_o
