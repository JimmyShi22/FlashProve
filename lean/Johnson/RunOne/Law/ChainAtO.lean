-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/ChainAtO.lean: It stands on Johnson/RunOne/Sound/.
EVERY SEAT OF THE KEY FILE'S FIRST CHAIN, IN SCOPE, FROM ITS PARTS, WITH THE
LINKS PAID IN AND EVERY PREMISE PAID THAT IS NOT A LETTER OR ANOTHER SEAT: fk_chain₁_own
(Chain1Priced.lean) at the terms of LinksAtO.lean: the two ledgers as the sendings open them, the
index-mask message's number 0, nothing else kept, the letters pulled back, the bound 2⁻¹ ^ 128.

What is left, all of it named in the statement: what LinksGood leaves (LinksAtO.lean); the last row
is the row before it with the seal's clauses passed; the last piece's errors lie below the bound and
the last row reads below that piece's place; THE SEATS 0 AND 1 AND THE SEATS OF THE CHAIN'S BACK.

Main names:
  ChainGood X N P hp D: what is said.
  chain_in_scope: at the source that the maker's record gives, at any digest, under ReadOf.

Object: (FK X N P).first.blocksInOrder, whole.
User: all_in_scope (AllAtO.lean).
Letters: see "What is left".

Limits. A joining. Those of fk_chain₁_own and of LinksAtO.lean. Nothing on soundness of the whole.

-/
import Johnson.RunOne.Law.LinksAtO
import Johnson.RunOne.Law.Chain1Priced

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.ChainAtO
open Iop OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open OnBytes.Model.Verify (Public)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim Source)
open Johnson.RunOne.Sound (FK H₁ asks₁ fkFirst)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.OwnRest
open Johnson.RunOne.Law.Chain1Priced
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.AtFreeCfg
open Johnson.RunOne.Law.FrontSteps

/-- **What is said of the first chain's seats at a description X N P with data D**: see the file's
head. -/
def ChainGood (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)
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
    keyRowAt A0 rs (T.l₁.length + 1) =
      (keyRowAt A0 rs T.l₁.length).passed (fun t => asks₁ t.2) →
    (∀ p, (T.p₁ :: T.l₁)[T.l₁.length]? = some p → Err.Below p.err ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      ReadsBelow p.base (keyRowAt A0 rs (T.l₁.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A0 rs (T.l₁.length + 1)).rel) →
    (∀ i, i < 2 → SeatGood ((2 : ℝ≥0∞)⁻¹ ^ 128) A0 (T.p₁ :: T.l₁) rs i) →
    (∀ j, j < (fkFirst X N).back.length → SeatGood ((2 : ℝ≥0∞)⁻¹ ^ 128) A0 (T.p₁ :: T.l₁) rs
      (2 + 6 * X.Y.k.oneTime.ranges.lookups.length + j)) →
    ∀ i, i < (T.p₁ :: T.l₁).length → SeatGood ((2 : ℝ≥0∞)⁻¹ ^ 128) A0 (T.p₁ :: T.l₁) rs i

/-- **EVERY SEAT OF THE FIRST CHAIN FROM ITS PARTS, IN SCOPE, AT ANY DIGEST.** -/
theorem chain_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Source}
    {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}
    (hm : VerifiableInference.Desc.Key.madeAt Z Zp.lay cfg = .ok m)
    (hX : VerifiableInference.Desc.Key.sourceOf m = .ok X) (hp : (FK X N P).planOk = true)
    {D : WholeD} (hD : (FK X N P).data "key file" = .ok D) : ChainGood X N P hp D := by
  obtain ⟨ht, hL, -⟩ := seat_in_scope hZ hP hm hX hp
  intro W M Wp hw wd mx dec' cond' Oth' b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₀ rest₂ rest₃ d wEnd st0 A0
    rs hrow T hlow hlastRow hlast g0 gb
  have key := fk_chain₁_own X N P hp "key file" D hD b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₀ rest₂ rest₃ d
    wEnd A0 rs (Nat.zero_ne_one) (kept_true _ _ _ _) hrow (blind_pull dec' cond' Oth') st0 hw hL _
        rfl
  rw [ht] at key
  exact key hlow hlastRow hlast g0 gb

end Johnson.RunOne.Law.ChainAtO

#print axioms Johnson.RunOne.Law.ChainAtO.chain_in_scope
