-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/Chain1Priced.lean: It stands on Johnson/RunOne/Sound/.
THE FIRST CHAIN'S SEATS AT THE PIECES THAT THE MAKER CUTS, WITH
THE LOOKUPS' LINKS PAID IN AT THEIR PRICE: fk_chain₁ (Johnson/RunOne/Sound/KeyChainsAtFK.lean: every
seat of the chain from its parts) and fk_link_priced (LinkPriced.lean: the six seats of a lookup's
link, with errors below 2⁻¹ ^ target), joined.

What is said. Where the key file's own description passes its tests on the plan and its data are
made, at the pieces that the maker cuts: IF the rows at the borders 2 + 6 · l + j are the lookups'
seven rows a link; the decoder is blind and reads below the first link's first piece; the planner's
own rounds hold for each lookup (LookHeld); the index-mask message's number is not 1; what else the
promise keeps is kept by the links' blocks (Kept); there is a witness's type with a member; the last
row is the row before it with the seal's clauses passed; THE LAST PIECE'S ERRORS LIE BELOW THE BOUND
and the last row's condition and relation read below that piece's place; AND THE SEATS 0 AND 1 AND
THE SEATS OF THE CHAIN'S BACK ARE FILLED: THEN EVERY SEAT OF THE FIRST CHAIN IS FILLED, at the bound
2⁻¹ ^ target. At the rests of OwnRest.lean the last piece's errors are those of the rests that were
turned: a premise on a letter.

Main names:
  looksOf_length: the description's list of lookups is as long as the plan's.
  fk_chain₁_priced: at any rests whose piece of each lookup's own block has the typed lookup's
    errors along the maps.
  fk_chain₁_own: at the rests that OwnRest.lean writes out: that premise falls.

Object: (FK X N P).first.blocksInOrder, whole (Johnson/RunOne/Sound/KeyAtFK.lean).
User: chain_in_scope (ChainAtO.lean).
Letters: X, N, P: the description's source and the two records of places · the data D and the three
flat lists' heads and tails · the rests of chains 2 and 3, and rest₀ · the rows A0, rs · the
decoder, its condition, what else rides (dec, cond, Oth, at TK (H₁ X N P)), the words, the matrix
(wd, mx) · the two ledgers lo, lk in front of the first link · Ex, what else the promise keeps ·
idxN, the index-mask message's number · st0, any value · k, the length of the chain's back.

Limits. A joining. The letters are exhibited by nobody. Named nowhere in the theorem, and owed
beside it: that PromL 0 holds at the record that stands behind the sending of the second message
(shown step by step in FrontAtFK.lean; no law on the seats 0 and 1 spends it yet).
The target counts a round's proof of work. A bound round by round, no sum.
Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.Sound.KeyChainsAtFK
import Johnson.RunOne.Law.OwnRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.Chain1Priced
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
open Johnson.RunOne.Law.OwnRest
open Johnson.RunOne.Sound (FK H₁ fk_chain₁ fk_sealLast asks₁ fkFirst allOf_nodup)

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

local notation "one" => X.Y.k.oneTime
local notation "idM" => X.Y.k.oneTime.ranges.messageId
local notation "mM" => Wf.matrixOf X.Y.k.oneTime.lin
local notation "nL" => X.Y.k.oneTime.ranges.lookups.length

/-- The description's list of lookups is as long as the plan's. -/
theorem looksOf_length : (lookupsOf one).length = nL := by
  show (X.Y.k.oneTime.ranges.lookups.map (Wf.lookupOf idM mM)).length = _
  rw [List.length_map]

variable {W : Type} {idxN : ℕ} {M Wp : Type} {wd : M → Means.Words GE} {mx : M → ℕ → ℕ → GE}
  {lo lk : Ledger} {Ex : FirstState → Prop}

/-- **Every seat of the first chain, at the pieces that the maker cuts, with the links paid in at
their price.** -/
theorem fk_chain₁_priced (hp : (FK X N P).planOk = true) (file : String) (D : WholeD)
    (hD : (FK X N P).data file = .ok D)
    (b₁ : Block (FK X N P).S₁ (FK X N P).Cl) (l₁ : List (Block (FK X N P).S₁ (FK X N P).Cl))
    (b₂ : Block (FK X N P).S₂ (FK X N P).Cl) (l₂ : List (Block (FK X N P).S₂ (FK X N P).Cl))
    (b₃ : Block (FK X N P).S₃ (FK X N P).Cl) (l₃ : List (Block (FK X N P).S₃ (FK X N P).Cl))
    (h₁ : (FK X N P).first.blocksInOrder = b₁ :: l₁) (h₂ : (FK X N P).shared.blocksInOrder = b₂ :: l₂)
    (h₃ : (FK X N P).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d wEnd : W)
    {dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M}
    {cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop} {Oth : TK (H₁ X N P) → M ×
        Wp → Prop}
    (A0 : JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))
    (rs : List (JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))) (hidx : idxN ≠ 1)
    (hE : Kept one idM mM (Lof one) Ex)
    (hr : ∀ l, l < nL → ∀ j ≤ 6, keyRowAt A0 rs (2 + 6 * l + j) =
      upF fun p₀ => (rows7 p₀ one X.set idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
        (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL
        (PromL one idM mM (Lof one) idxN nL lo lk Ex) l Wp Oth j))
    (hB : Blind dec cond Oth) (st0 : TK (H₁ X N P)) (hw : Nonempty (M × Wp))
    (hL : ∀ l, l < nL → LookHeld X.set (faceOfLkp (Wf.lookupOf idM mM (Lof one l))))
    (k : ℕ) (hk : (fkFirst X N).back.length = k) :
    let T := piecesAt (ckP .two) (FK X N P) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    (∀ p, (T.p₁ :: T.l₁)[2]? = some p → LowDec dec cond p.base) →
    (∀ l (hl : l < nL), ∀ p, (T.p₁ :: T.l₁)[2 + 6 * l + 2]? = some p →
      ∀ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))),
        p.err = (mapsAt (Fr := frameAt D (allOf D) D.key₁ 0) one idM mM (Lof one)
          (handed (cntO idM mM (Lof one)) lo) (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
            (tests_at (fk_admitted X N P hp) hl).2.2)
          (d_le (tests_at (fk_admitted X N P hp) hl).2.1) st0 p.ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err) →
    keyRowAt A0 rs (T.l₁.length + 1) =
      (keyRowAt A0 rs T.l₁.length).passed (fun t => asks₁ t.2) →
    (∀ p, (T.p₁ :: T.l₁)[T.l₁.length]? = some p → Err.Below p.err ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) ∧
      ReadsBelow p.base (keyRowAt A0 rs (T.l₁.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A0 rs (T.l₁.length + 1)).rel) →
    (∀ i, i < 2 → SeatGood ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) A0 (T.p₁ :: T.l₁) rs i) →
    (∀ j, j < k → SeatGood ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) A0 (T.p₁ :: T.l₁) rs (2 + 6 * nL + j)) →
    ∀ i, i < (T.p₁ :: T.l₁).length →
      SeatGood ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) A0 (T.p₁ :: T.l₁) rs i := by
  intro T hlow hown hrow hlast g0 gb
  obtain ⟨hO, -, -⟩ := paidAtDesc _ W (FK X N P) file D hD (fk_sealLast X N P) (ckP .two) b₁ l₁
    b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd
  refine fk_chain₁ X N P _ A0 T.p₁ T.l₁ rs hO.b₁ k hk hrow (allOf_nodup D) hlast g0
    (fun a ha j hj => ?_) fun j hj => ?_
  · rw [looksOf_length] at ha
    exact fk_link_priced X N P hp file D hD b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd
      a ha A0 rs hidx hE (hr a ha) hB st0 hw (hL a ha) hlow (hown a ha) j hj
  · rw [looksOf_length]
    exact gb j hj

/-- **The same at rests that are written out.** -/
theorem fk_chain₁_own (hp : (FK X N P).planOk = true) (file : String) (D : WholeD)
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
    (A0 : JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))
    (rs : List (JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))) (hidx : idxN ≠ 1)
    (hE : Kept one idM mM (Lof one) Ex)
    (hr : ∀ l, l < nL → ∀ j ≤ 6, keyRowAt A0 rs (2 + 6 * l + j) =
      upF fun p₀ => (rows7 p₀ one X.set idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
        (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL
        (PromL one idM mM (Lof one) idxN nL lo lk Ex) l Wp Oth j))
    (hB : Blind dec cond Oth) (st0 : TK (H₁ X N P)) (hw : Nonempty (M × Wp))
    (hL : ∀ l, l < nL → LookHeld X.set (faceOfLkp (Wf.lookupOf idM mM (Lof one l))))
    (k : ℕ) (hk : (fkFirst X N).back.length = k) :
    let T := piecesAt (ckP .two) (FK X N P) D b₁ l₁ b₂ l₂ b₃ l₃
      (ownRest X N P hp D idxN lo lk wd mx dec cond Oth st0 rest₀) rest₂ rest₃ d wEnd
    (∀ p, (T.p₁ :: T.l₁)[2]? = some p → LowDec dec cond p.base) →
    keyRowAt A0 rs (T.l₁.length + 1) =
      (keyRowAt A0 rs T.l₁.length).passed (fun t => asks₁ t.2) →
    (∀ p, (T.p₁ :: T.l₁)[T.l₁.length]? = some p → Err.Below p.err ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) ∧
      ReadsBelow p.base (keyRowAt A0 rs (T.l₁.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A0 rs (T.l₁.length + 1)).rel) →
    (∀ i, i < 2 → SeatGood ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) A0 (T.p₁ :: T.l₁) rs i) →
    (∀ j, j < k → SeatGood ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) A0 (T.p₁ :: T.l₁) rs (2 + 6 * nL + j)) →
    ∀ i, i < (T.p₁ :: T.l₁).length →
      SeatGood ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) A0 (T.p₁ :: T.l₁) rs i := by
  intro T hlow
  exact fk_chain₁_priced X N P hp file D hD b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ _ rest₂ rest₃ d wEnd A0 rs
    hidx hE hr hB st0 hw hL k hk hlow fun l hl =>
      own_meets X N P hp D b₁ l₁ b₂ l₂ b₃ l₃ rest₀ rest₂ rest₃ d wEnd st0 l hl

end Johnson.RunOne.Law.Chain1Priced

#print axioms Johnson.RunOne.Law.Chain1Priced.looksOf_length
#print axioms Johnson.RunOne.Law.Chain1Priced.fk_chain₁_priced
#print axioms Johnson.RunOne.Law.Chain1Priced.fk_chain₁_own
