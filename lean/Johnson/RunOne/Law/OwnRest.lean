-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/OwnRest.lean: It stands on Johnson/RunOne/Sound/.
RESTS OF THE FIRST CHAIN AT WHICH THE PIECE OF EACH LOOKUP'S OWN BLOCK HAS
THE TYPED LOOKUP'S ERRORS ALONG THE MAPS. fk_link_priced (LinkPriced.lean) asks that of the rests as
a premise; here rests are written out that meet it, so the premise falls.

The maker of the pieces (cutRow, Johnson/Desc/Sound/Tiles.lean) hands the rests the piece's number
and its stretch (cutRow_rest, Johnson/RunOne/Sound/CutRowAt.lean). ownRest takes any rests; at the
number 2 + 6 · l + 2 of a lookup l of the plan, and at a stretch that is made of the lookup's shape,
it lays the typed lookup's errors along the maps in the place of the given errors; everything else,
every extractor among it, stays.

Main names:
  ownErr, ownRest: the errors; the rests.
  ownErr_blind: they read neither the decoder, nor its condition, nor what else rides, nor how a
    witness's messages are read.
  ownRest_err, own_meets: the premise of fk_link_priced, at the pieces that the maker cuts.
  fk_link_own: THE SIX SEATS OF LOOKUP NUMBER l AT THESE RESTS.

Object: the six blocks at the places 2 + (6 · l + j), j < 6, of (FK X N P).first.blocksInOrder
(Johnson/RunOne/Sound/KeyAtFK.lean), which are lookupLink's (fk_link_at, KeyMapAtFK.lean).
User: fk_chain₁_own (Chain1Priced.lean).
Letters: those of fk_link_priced but rest₁; rest₀, the rests that are turned, is free.

Limits. Those of fk_link_priced, but for the premise on the rests. Whether a stretch is made of the
lookup's shape is decided classically: the rests are no program. The extractors are not touched:
nothing is said of them here.

-/
import Johnson.RunOne.Law.LinkPriced
import Johnson.RunOne.Sound.CutRowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.OwnRest
open Iop OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim Source lookupsOf)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.LinkAtLow
open Johnson.RunOne.Law.LinkPriced
open Johnson.RunOne.Sound (FK H₁ cutRow_rest)

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

local notation "one" => X.Y.k.oneTime
local notation "idM" => X.Y.k.oneTime.ranges.messageId
local notation "mM" => Wf.matrixOf X.Y.k.oneTime.lin
local notation "nL" => X.Y.k.oneTime.ranges.lookups.length

variable {W : Type} {M Wp : Type}

/-- The typed lookup's errors along the maps, where the stretch is made of the shape of lookup
number l; else the given errors. -/
def ownErr (hp : (FK X N P).planOk = true) (D : WholeD) (idxN : ℕ) (lo lk : Ledger)
    (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE)
    (dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M)
    (cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop) (Oth : TK (H₁ X N P) → M ×
        Wp → Prop) (st0 : TK (H₁ X N P))
    (l : ℕ) (hl : l < nL) (ds : List RDT) (e : Err (uLT (ckP .two) ds)) :
    Err (uLT (ckP .two) ds) :=
  open Classical in
  if hds : List.Forall₂ MadeOf ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))) then
    (mapsAt (Fr := frameAt D (allOf D) D.key₁ 0) one idM mM (Lof one)
          (handed (cntO idM mM (Lof one)) lo) (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
            (tests_at (fk_admitted X N P hp) hl).2.2)
          (d_le (tests_at (fk_admitted X N P hp) hl).2.1) st0 ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err
  else e

/-- **The rests.** At the number of the piece of a lookup's own block: the given extractor, and
`ownErr`. Everywhere else the given rests. -/
def ownRest (hp : (FK X N P).planOk = true) (D : WholeD) (idxN : ℕ) (lo lk : Ledger)
    (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE)
    (dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M)
    (cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop) (Oth : TK (H₁ X N P) → M ×
        Wp → Prop) (st0 : TK (H₁ X N P))
    (rest₀ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FK X N P).XiPub × (FK X N P).S₁) W ds) :
    (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FK X N P).XiPub × (FK X N P).S₁) W ds :=
  fun i ds =>
    if h : (i - 4) / 6 < nL ∧ i = 2 + 6 * ((i - 4) / 6) + 2 then
      ⟨(rest₀ i ds).ext,
        ownErr X N P hp D idxN lo lk wd mx dec cond Oth st0 ((i - 4) / 6) h.1 ds (rest₀ i ds).err⟩
    else rest₀ i ds

variable {idxN : ℕ} {wd : M → Means.Words GE} {mx : M → ℕ → ℕ → GE} {lo lk : Ledger}
  {Ex : FirstState → Prop}

/-- The errors read neither the decoder, nor its condition, nor what else rides, nor how a witness's
messages are read. -/
theorem ownErr_blind (hp : (FK X N P).planOk = true) (D : WholeD)
    (wd' : M → Means.Words GE) (mx' : M → ℕ → ℕ → GE)
    (dec dec' : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M)
    (cond cond' : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop)
    (Oth Oth' : TK (H₁ X N P) → M × Wp → Prop) (st0 : TK (H₁ X N P)) (l : ℕ) (hl : l < nL) (ds :
        List RDT)
    (e : Err (uLT (ckP .two) ds)) :
    ownErr X N P hp D idxN lo lk wd mx dec cond Oth st0 l hl ds e =
      ownErr X N P hp D idxN lo lk wd' mx' dec' cond' Oth' st0 l hl ds e :=
  rfl

theorem ownErr_eq (hp : (FK X N P).planOk = true) (D : WholeD)
    {dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M}
    {cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop} {Oth : TK (H₁ X N P) → M ×
        Wp → Prop}
    (st0 : TK (H₁ X N P)) (l : ℕ) (hl : l < nL) (ds : List RDT)
    (e : Err (uLT (ckP .two) ds)) (l' : ℕ) (hl' : l' < nL) (hll : l' = l)
    (hds : List.Forall₂ MadeOf ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l))))) :
    ownErr X N P hp D idxN lo lk wd mx dec cond Oth st0 l' hl' ds e =
      (mapsAt (Fr := frameAt D (allOf D) D.key₁ 0) one idM mM (Lof one)
          (handed (cntO idM mM (Lof one)) lo) (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
            (tests_at (fk_admitted X N P hp) hl).2.2)
          (d_le (tests_at (fk_admitted X N P hp) hl).2.1) st0 ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err := by
  subst hll
  unfold ownErr
  rw [dif_pos hds]

/-- At the number 2 + 6 · l + 2 and a stretch made of the lookup's shape. -/
theorem ownRest_err (hp : (FK X N P).planOk = true) (D : WholeD)
    {dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M}
    {cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop} {Oth : TK (H₁ X N P) → M ×
        Wp → Prop} (st0 : TK (H₁ X N P))
    (rest₀ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FK X N P).XiPub × (FK X N P).S₁) W ds)
    (l : ℕ) (hl : l < nL) (i : ℕ) (hi : i = 2 + 6 * l + 2) (ds : List RDT)
    (hds : List.Forall₂ MadeOf ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l))))) :
    (ownRest X N P hp D idxN lo lk wd mx dec cond Oth st0 rest₀ i ds).err =
      (mapsAt (Fr := frameAt D (allOf D) D.key₁ 0) one idM mM (Lof one)
          (handed (cntO idM mM (Lof one)) lo) (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
            (tests_at (fk_admitted X N P hp) hl).2.2)
          (d_le (tests_at (fk_admitted X N P hp) hl).2.1) st0 ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err := by
  have e : (i - 4) / 6 = l := by omega
  have hc : (i - 4) / 6 < nL ∧ i = 2 + 6 * ((i - 4) / 6) + 2 := ⟨by omega, by omega⟩
  unfold ownRest
  rw [dif_pos hc]
  exact ownErr_eq X N P hp D st0 l hl ds _ _ hc.1 e hds

/-- **The premise of fk_link_priced on the rests, at the pieces that the maker cuts.** -/
theorem own_meets (hp : (FK X N P).planOk = true) (D : WholeD)
    (b₁ : Block (FK X N P).S₁ (FK X N P).Cl) (l₁ : List (Block (FK X N P).S₁ (FK X N P).Cl))
    (b₂ : Block (FK X N P).S₂ (FK X N P).Cl) (l₂ : List (Block (FK X N P).S₂ (FK X N P).Cl))
    (b₃ : Block (FK X N P).S₃ (FK X N P).Cl) (l₃ : List (Block (FK X N P).S₃ (FK X N P).Cl))
    (rest₀ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FK X N P).XiPub × (FK X N P).S₁) W ds)
    (rest₂) (rest₃) (d wEnd : W)
    {dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M}
    {cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop} {Oth : TK (H₁ X N P) → M ×
        Wp → Prop}
    (st0 : TK (H₁ X N P)) (l : ℕ) (hl : l < nL) :
    let T := piecesAt (ckP .two) (FK X N P) D b₁ l₁ b₂ l₂ b₃ l₃
      (ownRest X N P hp D idxN lo lk wd mx dec cond Oth st0 rest₀) rest₂ rest₃ d wEnd
    ∀ p, (T.p₁ :: T.l₁)[2 + 6 * l + 2]? = some p →
      ∀ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))),
        p.err = (mapsAt (Fr := frameAt D (allOf D) D.key₁ 0) one idM mM (Lof one)
          (handed (cntO idM mM (Lof one)) lo) (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
            (tests_at (fk_admitted X N P hp) hl).2.2)
          (d_le (tests_at (fk_admitted X N P hp) hl).2.1) st0 p.ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err := by
  intro T p hq hds
  have h := (cutRow_rest (ownRest X N P hp D idxN lo lk wd mx dec cond Oth st0 rest₀) [sealRound]
    (l₁.map held) (held b₁) 0 0 D.ds₁ (2 + 6 * l + 2) p hq).1
  rw [h]
  exact ownRest_err X N P hp D st0 rest₀ l hl _ (by omega) p.ds hds

/-- **THE SIX SEATS OF THE LINK OF LOOKUP NUMBER l, AT RESTS THAT ARE WRITTEN OUT.** -/
theorem fk_link_own (hp : (FK X N P).planOk = true) (file : String) (D : WholeD)
    (hD : (FK X N P).data file = .ok D)
    (b₁ : Block (FK X N P).S₁ (FK X N P).Cl) (l₁ : List (Block (FK X N P).S₁ (FK X N P).Cl))
    (b₂ : Block (FK X N P).S₂ (FK X N P).Cl) (l₂ : List (Block (FK X N P).S₂ (FK X N P).Cl))
    (b₃ : Block (FK X N P).S₃ (FK X N P).Cl) (l₃ : List (Block (FK X N P).S₃ (FK X N P).Cl))
    (h₁ : (FK X N P).first.blocksInOrder = b₁ :: l₁) (h₂ : (FK X N P).shared.blocksInOrder = b₂ :: l₂)
    (h₃ : (FK X N P).second.blocksInOrder = b₃ :: l₃)
    (rest₀ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FK X N P).XiPub × (FK X N P).S₁) W ds)
    (rest₂) (rest₃) (d wEnd : W)
    {dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M}
    {cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop} {Oth : TK (H₁ X N P) → M ×
        Wp → Prop}
    (l : ℕ) (hl : l < nL)
    (A0 : JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))
    (rs : List (JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))) (hidx : idxN ≠ 1)
    (hE : Kept one idM mM (Lof one) Ex)
    (hr : ∀ j ≤ 6, keyRowAt A0 rs (2 + 6 * l + j) =
      upF fun p₀ => (rows7 p₀ one X.set idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
        (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL
        (PromL one idM mM (Lof one) idxN nL lo lk Ex) l Wp Oth j))
    (hB : Blind dec cond Oth) (st0 : TK (H₁ X N P)) (hw : Nonempty (M × Wp))
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))) :
    let T := piecesAt (ckP .two) (FK X N P) D b₁ l₁ b₂ l₂ b₃ l₃
      (ownRest X N P hp D idxN lo lk wd mx dec cond Oth st0 rest₀) rest₂ rest₃ d wEnd
    (∀ p, (T.p₁ :: T.l₁)[2]? = some p → LowDec dec cond p.base) →
    ∀ j < 6, SeatGood ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) A0 (T.p₁ :: T.l₁) rs (2 + (6 * l + j)) := by
  intro T hlow
  exact fk_link_priced X N P hp file D hD b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ _ rest₂ rest₃ d wEnd l hl A0
    rs hidx hE hr hB st0 hw hL hlow
    (own_meets X N P hp D b₁ l₁ b₂ l₂ b₃ l₃ rest₀ rest₂ rest₃ d wEnd st0 l hl)

end Johnson.RunOne.Law.OwnRest

#print axioms Johnson.RunOne.Law.OwnRest.ownErr_blind
#print axioms Johnson.RunOne.Law.OwnRest.ownErr_eq
#print axioms Johnson.RunOne.Law.OwnRest.ownRest_err
#print axioms Johnson.RunOne.Law.OwnRest.own_meets
#print axioms Johnson.RunOne.Law.OwnRest.fk_link_own
