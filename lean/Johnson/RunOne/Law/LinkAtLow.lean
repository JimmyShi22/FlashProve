-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LinkAtLow.lean: It stands on Johnson/RunOne/Sound/.
THE SIX SEATS OF EACH LOOKUP'S LINK, WITH ONE PREMISE ON WHAT THE
DECODER READS: fk_link_cut (LinkAtCut.lean), where "the decoder reads below each piece's place" is
asked at the first link's first piece alone: in a tiled row the pieces' places do not fall.

Main names:
  tiled_head_le, tiled_base_le: in a tiled row the pieces' places do not fall.
  fk_link_low: THE SIX SEATS OF LOOKUP NUMBER l.

Limits. Those of LinkAtCut.lean's fk_link_cut, but for LowDec, which is asked at the place of the
piece number 2 alone.

-/
import Johnson.RunOne.Law.LinkAtCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.LinkAtLow
open Iop OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim Source layerOrder)
open Johnson.RunOne.Sound (FK H₁ fk_sealLast)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtCut

/-- In a tiled row no piece's place lies below the first piece's. -/
theorem tiled_head_le {C : CK} {F : Frame} {S Cl W : Type} : ∀ (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (j : ℕ) (r : Piece C F S Cl W), Tiled p l →
    (p :: l)[j]? = some r → p.base ≤ r.base
  | p, _, 0, r, _, hr => by
    obtain rfl : p = r := Option.some.inj hr
    exact Nat.le_refl _
  | _, [], _ + 1, _, _, hr => by cases hr
  | p, q :: l, j + 1, r, h, hr => by
    have h' : p.Owed ∧ p.Listed ∧ p.back = [] ∧ q.base = p.base + p.trees ∧ Tiled q l := h
    have e := tiled_head_le q l j r h'.2.2.2.2 hr
    have e2 := h'.2.2.2.1
    omega

/-- In a tiled row the pieces' places do not fall. -/
theorem tiled_base_le {C : CK} {F : Frame} {S Cl W : Type} : ∀ (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (i j : ℕ) (q r : Piece C F S Cl W), Tiled p l →
    (p :: l)[i]? = some q → (p :: l)[j]? = some r → i ≤ j → q.base ≤ r.base
  | p, l, 0, j, q, r, h, hq, hr, _ => by
    obtain rfl : p = q := Option.some.inj hq
    exact tiled_head_le p l j r h hr
  | _, _, _ + 1, 0, _, _, _, _, _, hij => absurd hij (Nat.not_succ_le_zero _)
  | _, [], _ + 1, _ + 1, _, _, _, hq, _, _ => by cases hq
  | p, s :: l, i + 1, j + 1, q, r, h, hq, hr, hij => by
    have h' : p.Owed ∧ p.Listed ∧ p.back = [] ∧ s.base = p.base + p.trees ∧ Tiled s l := h
    exact tiled_base_le s l i j q r h'.2.2.2.2 hq hr (Nat.le_of_succ_le_succ hij)

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

local notation "one" => X.Y.k.oneTime
local notation "idM" => X.Y.k.oneTime.ranges.messageId
local notation "mM" => Wf.matrixOf X.Y.k.oneTime.lin
local notation "nL" => X.Y.k.oneTime.ranges.lookups.length

variable {W : Type} {idxN : ℕ} {M Wp : Type} {wd : M → Means.Words GE} {mx : M → ℕ → ℕ → GE}
  {lo lk : Ledger} {Ex : FirstState → Prop}

/-- **THE SIX SEATS OF THE LINK OF LOOKUP NUMBER l, WITH ONE PREMISE ON WHAT THE DECODER READS.** -/
theorem fk_link_low (hp : (FK X N P).planOk = true) (file : String) (D : WholeD)
    (hD : (FK X N P).data file = .ok D)
    (b₁ : Block (FK X N P).S₁ (FK X N P).Cl) (l₁ : List (Block (FK X N P).S₁ (FK X N P).Cl))
    (b₂ : Block (FK X N P).S₂ (FK X N P).Cl) (l₂ : List (Block (FK X N P).S₂ (FK X N P).Cl))
    (b₃ : Block (FK X N P).S₃ (FK X N P).Cl) (l₃ : List (Block (FK X N P).S₃ (FK X N P).Cl))
    (h₁ : (FK X N P).first.blocksInOrder = b₁ :: l₁) (h₂ : (FK X N P).shared.blocksInOrder = b₂ :: l₂)
    (h₃ : (FK X N P).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d wEnd : W)
    {dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M}
    {cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop} {Oth : TK (H₁ X N P) → M ×
        Wp → Prop}
    (l : ℕ) (hl : l < nL) (εs : ℝ≥0∞)
    (A0 : JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))
    (rs : List (JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))) (hidx : idxN ≠ 1)
    (hE : Kept one idM mM (Lof one) Ex)
    (hr : ∀ j ≤ 6, keyRowAt A0 rs (2 + 6 * l + j) =
      upF fun p₀ => (rows7 p₀ one X.set idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
        (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL
        (PromL one idM mM (Lof one) idxN nL lo lk Ex) l Wp Oth j))
    (hB : Blind dec cond Oth) (st0 : TK (H₁ X N P)) (hw : Nonempty (M × Wp)) :
    let T := piecesAt (ckP .two) (FK X N P) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    (∀ p, (T.p₁ :: T.l₁)[2]? = some p → LowDec dec cond p.base) →
    (∀ j < 6, ∀ p, (T.p₁ :: T.l₁)[2 + 6 * l + j]? = some p → Err.Below p.err εs) →
    (∀ p, (T.p₁ :: T.l₁)[2 + 6 * l + 2]? = some p →
      ∀ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))),
        Err.le ((mapsAt (Fr := frameAt D (allOf D) D.key₁ 0) one idM mM (Lof one)
          (handed (cntO idM mM (Lof one)) lo) (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
            (tests_at (fk_admitted X N P hp) hl).2.2)
          (d_le (tests_at (fk_admitted X N P hp) hl).2.1) st0 p.ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err) p.err) →
    ∀ j < 6, SeatGood εs A0 (T.p₁ :: T.l₁) rs (2 + (6 * l + j)) := by
  intro T hlow hbelow herr
  obtain ⟨-, hF, -⟩ := paidAtDesc _ W (FK X N P) file D hD (fk_sealLast X N P) (ckP .two) b₁ l₁
    b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd
  have hbase : ∀ i p, (T.p₁ :: T.l₁)[i]? = some p → 2 ≤ i → LowDec dec cond p.base :=
    fun i p hq hi => by
      have hlt : i < (T.p₁ :: T.l₁).length := (List.getElem?_eq_some_iff.1 hq).1
      have h2 : (T.p₁ :: T.l₁)[2]? = some ((T.p₁ :: T.l₁)[2]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      exact lowDec_mono (tiled_base_le T.p₁ T.l₁ 2 i _ p hF.tiled₁ h2 hq hi) (hlow _ h2)
  exact fk_link_cut X N P hp file D hD b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd
    l hl εs A0 rs hidx hE hr hB st0 hw
    (fun j hj p hq => ⟨hbelow j hj p hq, hbase _ p hq (by omega)⟩) herr

end Johnson.RunOne.Law.LinkAtLow

#print axioms Johnson.RunOne.Law.LinkAtLow.tiled_head_le
#print axioms Johnson.RunOne.Law.LinkAtLow.tiled_base_le
#print axioms Johnson.RunOne.Law.LinkAtLow.fk_link_low
