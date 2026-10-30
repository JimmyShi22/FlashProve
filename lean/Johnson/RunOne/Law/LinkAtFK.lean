-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LinkAtFK.lean: It stands on Johnson/RunOne/Sound/.
THE SIX SEATS OF EACH LOOKUP'S LINK AT THE KEY FILE'S OWN DESCRIPTION: at
the first chain's own flat list (FK X N P, Johnson/RunOne/Sound/KeyAtFK.lean), seats
2 + (6 · l + j) for j < 6: link_seats_at (LinkAtPlan.lean) with the flat list, the plan's values and
the place filled in.

Main names:
  look_at: the plan's lookup number l, as the description's list of lookups has it.
  fk_link_seats: THE SIX SEATS OF LOOKUP NUMBER l.

Limits. Left as letters: the decoder dec, its condition cond and what else rides, Oth (Blind; LowDec
at each piece's place) · wd, mx · the two ledgers lo, lk in front of the first link · what else is
promised, Ex (Kept) · the index-mask message's number idxN. Left as premises: the lookup's number
lies below the number of the plan's lookups · the plan passes Wf.admitted · the own message's number
is not idxN · the pieces hold the flat list's blocks · the seven rows are the link's · no two trees
of the frame's list have one number · a value st0 of the riding part's type · the witnesses' type M
× Wp is not empty · each piece's errors lie below the bound · the piece of the kind's block puts no
round back, its stretch is MadeOf the lookup's shape, and the typed lookup's errors along the maps
lie below its errors. Named nowhere in the theorem, and owed beside it: that PromL 0 holds at the
record that stands behind the sending of the second message.

-/
import Johnson.RunOne.Law.LinkAtPlan
import Johnson.RunOne.Sound.KeyMapAtFK
import Johnson.RunOne.Sound.KeyEndsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.LinkAtFK
open Iop OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim Source lookupLink layerOrder lookupsOf)
open Johnson.RunOne.Sound (FK H₁ fk_link_at)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan

/-- The plan's lookup number l, as the description's list of lookups has it. -/
theorem look_at (one : OneTime) (l : ℕ) (hl : l < one.ranges.lookups.length) :
    (lookupsOf one)[l]? =
      some (Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin) (Lof one l)) := by
  have e : one.ranges.lookups[l]? = some (Lof one l) := by
    unfold Lof
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    rfl
  show (one.ranges.lookups.map (Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin)))[l]? = _
  rw [List.getElem?_map, e]
  rfl

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

local notation "one" => X.Y.k.oneTime
local notation "idM" => X.Y.k.oneTime.ranges.messageId
local notation "mM" => Wf.matrixOf X.Y.k.oneTime.lin
local notation "nL" => X.Y.k.oneTime.ranges.lookups.length

variable {Fr : Frame} {W : Type} {idxN : ℕ} {M Wp : Type} {wd : M → Means.Words GE}
  {mx : M → ℕ → ℕ → GE} {dec : TK (H₁ X N P) × Fr.E.Str → Option M} {cond : TK (H₁ X N P) × Fr.E.Str
      → Prop}
  {Oth : TK (H₁ X N P) → M × Wp → Prop} {lo lk : Ledger} {Ex : FirstState → Prop}

/-- **THE SIX SEATS OF THE LINK OF LOOKUP NUMBER l, AT THE KEY FILE'S OWN DESCRIPTION.** -/
theorem fk_link_seats (l : ℕ) (hl : l < nL)
    (εs : ℝ≥0∞) (A0 : JointRow (H₁ X N P × FirstState) Fr)
    (ps : List (Piece (ckP .two) Fr (H₁ X N P × FirstState) Claim W))
    (rs : List (JointRow (H₁ X N P × FirstState) Fr))
    (hW : Wf.admitted (one).codes (one).ranges mM = true) (hne : idM ≠ idxN)
    (hE : Kept one idM mM (Lof one) Ex)
    (hbs : ps.map (·.b) =
      ((FK X N P).first.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hr : ∀ j ≤ 6, keyRowAt A0 rs (2 + 6 * l + j) =
      upF fun p₀ => (rows7 p₀ one X.set idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
        (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL
        (PromL one idM mM (Lof one) idxN nL lo lk Ex) l Wp Oth j))
    (hnd : (Fr.all.map (·.no)).Nodup) (hB : Blind dec cond Oth) (st0 : TK (H₁ X N P))
    (hw : Nonempty (M × Wp))
    (hpc : ∀ j < 6, ∀ p, ps[2 + 6 * l + j]? = some p →
      Err.Below p.err εs ∧ LowDec dec cond p.base)
    (hk3 : ∀ p, ps[2 + 6 * l + 2]? = some p → p.back = [] ∧
      ∃ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))),
        Err.le ((mapsAt (Fr := Fr) one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
          (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at hW hl).2.1 (tests_at hW hl).2.2)
          (d_le (tests_at hW hl).2.1) st0 p.ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err) p.err) :
    ∀ j < 6, SeatGood εs A0 ps rs (2 + (6 * l + j)) := by
  intro j hj
  rw [← Nat.add_assoc]
  refine link_seats_at (set := X.set) εs A0 ps rs (FK X N P).first.blocksInOrder (2 + 6 * l) l hW hne hE
    hl
    hbs (fun j' hj' => ?_) hr hnd hB st0 hw hpc hk3 j hj
  have h := fk_link_at X N P l j' hj' _ (look_at one l hl)
  rw [Nat.add_assoc]
  exact h

end Johnson.RunOne.Law.LinkAtFK

#print axioms Johnson.RunOne.Law.LinkAtFK.look_at
#print axioms Johnson.RunOne.Law.LinkAtFK.fk_link_seats
