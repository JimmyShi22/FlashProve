-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LinksAtO.lean: It stands on Johnson/RunOne/Sound/.
THE SEATS OF THE LOOKUPS' LINKS, IN SCOPE, FROM THE YES OF THE KEY FILE'S
PIECE, WITH EVERY PREMISE PAID THAT IS NOT A LETTER: fk_link_own (OwnRest.lean) at every lookup of
the plan, where: the tests on the plan and the data come from the piece's yes; LookHeld and
target = 128 from seat_at_fixed (AtFreeCfg.lean); the rests are written out (ownRest); the two
ledgers are the ledgers as the sendings open them (ledOf, FrontSteps.lean) and the index-mask
message's number is 0, as front_at_fixed shows of the record in front of the first link; nothing
else is kept (Ex := True); the decoder, its condition and what else rides are pulled back from
letters at (the public part of the instance, a statement), so they are blind by their make
(LettersAt.lean).

What is left, all of it named in the statement: the letters dec', cond', Oth', wd, mx; a type of
witnesses with a member; that the rows at the links' borders are the links' seven rows, lifted; that
the pulled-back decoder and condition read the oracles below the first link's first piece.

Main names:
  LinksGood X N P hp D: what is said of the links' seats at a description and its data.
  links_in_scope: at the source that the maker's record gives, at any digest, under ReadOf.
  links_at_fixed: from Key.keyDataAndDecisionAtFixedDigest's yes.
  links_at_o: from the yes of (publicOfO o pol KL (some lay)).bind fun Z => Key.keyDataAndDecisionAtFixedDigest Z lay.

Object: the blocks at the places 2 + (6 · l + j), j < 6, l below the number of lookups, of
(FK X N P).first.blocksInOrder, at the X N P whose run is the piece's decision.
User: all_at_o (AllAtO.lean).
Letters: see "What is left".

Limits. Those of fk_link_own. One size: the scope's. The bound 2⁻¹ ^ 128 counts a round's proof of
work and is a bound round by round, no sum. That the condition of the row at border 2 holds behind
block 1 is not said here (its promise and lengths: FrontAtFK.lean; the decoder's condition: nobody).
Nothing on soundness of the whole.

-/
import Johnson.RunOne.Law.ReadAtO
import Johnson.RunOne.Law.OwnRest
import Johnson.RunOne.Law.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.LinksAtO
open Iop OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open OnBytes.Model.Verify (Public)
open OnBytes.Params (exc_bind)
open _root_.Run (ckP)
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim Source keyDataAndDecisionAtFixedDigest KeyRun)
open Johnson.RunOne.Sound (FK H₁)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.OwnRest
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.AtFreeCfg
open Johnson.RunOne.Law.FrontSteps
open Johnson.RunOne.Law.ReadAtO

/-- **What is said of the links' seats at a description X N P with data D**: see the file's head. -/
def LinksGood (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)
    (hp : (FK X N P).planOk = true) (D : WholeD) : Prop :=
  ∀ (W M Wp : Type) (_ : Nonempty (M × Wp)) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE)
    (dec' : (H₁ X N P × Statement) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M)
    (cond' : (H₁ X N P × Statement) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop)
    (Oth' : H₁ X N P × Statement → M × Wp → Prop)
    (b₁ : Block (FK X N P).S₁ (FK X N P).Cl) (l₁ : List (Block (FK X N P).S₁ (FK X N P).Cl))
    (b₂ : Block (FK X N P).S₂ (FK X N P).Cl) (l₂ : List (Block (FK X N P).S₂ (FK X N P).Cl))
    (b₃ : Block (FK X N P).S₃ (FK X N P).Cl) (l₃ : List (Block (FK X N P).S₃ (FK X N P).Cl))
    (_ : (FK X N P).first.blocksInOrder = b₁ :: l₁) (_ : (FK X N P).shared.blocksInOrder = b₂ :: l₂)
    (_ : (FK X N P).second.blocksInOrder = b₃ :: l₃)
    (rest₀ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FK X N P).XiPub × (FK X N P).S₁) W ds)
    (rest₂) (rest₃) (d wEnd : W) (st0 : TK (H₁ X N P))
    (A0 : JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))
    (rs : List (JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))),
    (∀ l, l < X.Y.k.oneTime.ranges.lookups.length → ∀ j ≤ 6, keyRowAt A0 rs (2 + 6 * l + j) =
      upF fun p₀ => rows7 p₀ X.Y.k.oneTime X.set X.Y.k.oneTime.ranges.messageId
        (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime)
        (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime)) (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape))
        (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime)) (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape))
        0 wd mx (fun a => dec' (pullK a.1, a.2)) (fun a => cond' (pullK a.1, a.2))
        X.Y.k.oneTime.ranges.lookups.length
        (PromL X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime) 0 X.Y.k.oneTime.ranges.lookups.length
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape)
          (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) fun _ => True)
        l Wp (fun x w => Oth' (pullK x) w) j) →
    let T := piecesAt (ckP .two) (FK X N P) D b₁ l₁ b₂ l₂ b₃ l₃
      (ownRest X N P hp D 0 (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape)
        (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) wd mx
        (fun a => dec' (pullK a.1, a.2)) (fun a => cond' (pullK a.1, a.2))
        (fun x w => Oth' (pullK x) w) st0 rest₀) rest₂ rest₃ d wEnd
    (∀ p, (T.p₁ :: T.l₁)[2]? = some p →
      LowDec (fun a => dec' (pullK a.1, a.2)) (fun a => cond' (pullK a.1, a.2)) p.base) →
    ∀ l, l < X.Y.k.oneTime.ranges.lookups.length → ∀ j < 6,
      SeatGood ((2 : ℝ≥0∞)⁻¹ ^ 128) A0 (T.p₁ :: T.l₁) rs (2 + (6 * l + j))

/-- **THE LINKS' SEATS, IN SCOPE, AT THE SOURCE THAT THE MAKER'S RECORD GIVES AT ANY DIGEST.** -/
theorem links_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Source}
    {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}
    (hm : VerifiableInference.Desc.Key.madeAt Z Zp.lay cfg = .ok m)
    (hX : VerifiableInference.Desc.Key.sourceOf m = .ok X) (hp : (FK X N P).planOk = true)
    {D : WholeD} (hD : (FK X N P).data "key file" = .ok D) : LinksGood X N P hp D := by
  obtain ⟨ht, hL, -⟩ := seat_in_scope hZ hP hm hX hp
  intro W M Wp hw wd mx dec' cond' Oth' b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₀ rest₂ rest₃ d wEnd st0 A0
    rs hrow T hlow l hl j hj
  have key := fk_link_own X N P hp "key file" D hD b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₀ rest₂ rest₃ d
    wEnd l hl A0 rs (Nat.zero_ne_one) (kept_true _ _ _ _) (hrow l hl) (blind_pull dec' cond' Oth')
        st0 hw
    (hL l hl) hlow j hj
  rw [ht] at key
  exact key

/-- **The same from the yes of the key file's piece at the fixed digest.** -/
theorem links_at_fixed {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {D : WholeD} {r : KeyRun} (h : keyDataAndDecisionAtFixedDigest Z Zp.lay = .ok (D, r)) :
    ∃ X N P, ∃ hp : (FK X N P).planOk = true, (FK X N P).data "key file" = .ok D ∧
      r = (FK X N P).run ∧ LinksGood X N P hp D := by
  obtain ⟨m, X, N, P, hm, hX, hp, hD, hr⟩ := Johnson.RunOne.Law.KeyInScope.laid_parts h
  exact ⟨X, N, P, hp, hD, hr, links_in_scope hZ hP hm hX hp hD⟩

/-- **The same at every letter o in the hash function's place.** -/
theorem links_at_o {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {o : Nat → ByteArray → ByteArray} {D : WholeD} {r : KeyRun}
    (h : ((publicOfO o Zp.pol Zp.KL (some Zp.lay)).bind fun Z => keyDataAndDecisionAtFixedDigest Z Zp.lay) =
      .ok (D, r)) :
    ∃ X N P, ∃ hp : (FK X N P).planOk = true, (FK X N P).data "key file" = .ok D ∧
      r = (FK X N P).run ∧ LinksGood X N P hp D := by
  obtain ⟨Z, hP, hl⟩ := exc_bind h
  exact links_at_fixed hZ (readOf_publicOfO hP) hl

end Johnson.RunOne.Law.LinksAtO

#print axioms Johnson.RunOne.Law.LinksAtO.links_in_scope
#print axioms Johnson.RunOne.Law.LinksAtO.links_at_fixed
#print axioms Johnson.RunOne.Law.LinksAtO.links_at_o
