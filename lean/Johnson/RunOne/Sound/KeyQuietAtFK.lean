-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeyQuietAtFK.lean: It stands on Johnson/Desc/Key/Desc.lean.
TWO MORE SEATS A LOOKUP OF THE KEY FILE'S FIRST CHAIN: of each lookup's
link the first block ("laid") and the block behind the batching: they hand the record on as it is.

What is said. For lookup l (x := the plan's lookup number l):
  `fk_laid_pass`: at seat 2 + (6 · l + 0) sits a block that hands the record on just where no ledger
    is open (`asksLaid`). `fk_behind_pass`: at seat 2 + (6 · l + 4) sits a block that hands the
    record on, always (the link names no run behind the batching).
  `fk_laid_seat`, `fk_behind_seat`: SO THESE SEATS ARE FILLED (`seat_of_pass`,
    Johnson/Desc/Sound/KeySeatsMore.lean), between the row in front and the same row with the clause
    passed (for the second: with no clause). `fk_behind_same`: the second is also filled between a
    row and the same row (`seat_of_same`): so against every list of rows that has one row there.

Limits. What each still asks: that the row behind is that row; that it reads no tree from the
piece's place on; that the piece's errors are shares of at most εs; that no two trees of the frame's
list have one number.
Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.Sound.KeyMapAtFK
import Johnson.RunOne.Sound.KeyEndsAtFK
import Johnson.Desc.Sound.KeySeatsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Sound
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.ChainEnd
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.Key (descriptionFromSource Source FirstState Claim lookupLink lookupsOf)
open _root_.Run (ckP)
open _root_.Iop (Err)

variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)

/-- What a lookup's link asks at its first place. -/
def asksLaid (s : Key.FirstState) : Clauses :=
  [("a lookup's link: a ledger is open", s.base.fork.isNone)]

theorem fk_laid_pass (l : ℕ) (x : Key.Lookup) (hx : (Key.lookupsOf X.Y.k.oneTime)[l]? = some x) :
    ∃ e, (FK X N P).first.blocksInOrder[2 + (6 * l + 0)]? = some e ∧
      ∀ s rs gs s', e.decide s rs gs = .ok s' → (∀ c ∈ asksLaid s, c.2 = true) ∧ s' = s := by
  refine ⟨_, fk_link_at X N P l 0 (by decide) x hx, fun s rs gs s' h => ?_⟩
  have h' : ((need "a lookup's link: a ledger is open" s.base.fork.isNone).bind fun _ =>
      (pure s : Except String Key.FirstState)) = .ok s' := h
  cases hb : s.base.fork.isNone with
  | false =>
    rw [hb] at h'
    cases h'
  | true =>
    rw [hb] at h'
    refine ⟨fun c hc => ?_, (Except.ok.inj h').symm⟩
    obtain rfl : c = ("a lookup's link: a ledger is open", s.base.fork.isNone) :=
      List.mem_singleton.1 hc
    exact hb

theorem fk_behind_pass (l : ℕ) (x : Key.Lookup) (hx : (Key.lookupsOf X.Y.k.oneTime)[l]? = some x) :
    ∃ e, (FK X N P).first.blocksInOrder[2 + (6 * l + 4)]? = some e ∧
      ∀ s rs gs s', e.decide s rs gs = .ok s' →
        (∀ c ∈ (fun _ : Key.FirstState => ([] : Clauses)) s, c.2 = true) ∧ s' = s := by
  refine ⟨_, fk_link_at X N P l 4 (by decide) x hx, fun s rs gs s' h => ?_⟩
  have h' : (Except.ok s : Except String Key.FirstState) = .ok s' := h
  exact ⟨fun c hc => (by cases hc), (Except.ok.inj h').symm⟩

variable {F : Frame} {W : Type}

/-- **Seat 2 + (6 · l + 0) is filled.** -/
theorem fk_laid_seat (l : ℕ) (x : Key.Lookup) (hx : (Key.lookupsOf X.Y.k.oneTime)[l]? = some x)
    (εs : ℝ≥0∞) (A : JointRow (H₁ X N P × (FK X N P).S₁) F)
    (ps : List (Piece (ckP .two) F (H₁ X N P × (FK X N P).S₁) (FK X N P).Cl W))
    (rs : List (JointRow (H₁ X N P × (FK X N P).S₁) F))
    (hbs : ps.map (·.b) =
      ((FK X N P).first.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow : keyRowAt A rs (2 + (6 * l + 0) + 1) =
      (keyRowAt A rs (2 + (6 * l + 0))).passed fun t => asksLaid t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, ps[2 + (6 * l + 0)]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (2 + (6 * l + 0) + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (2 + (6 * l + 0) + 1)).rel) :
    SeatGood εs A ps rs (2 + (6 * l + 0)) := by
  obtain ⟨e, he, hd⟩ := fk_laid_pass X N P l x hx
  exact seat_of_pass εs A ps rs _ hbs _ e he asksLaid hd hrow hnd hp

/-- **Seat 2 + (6 · l + 4) is filled.** -/
theorem fk_behind_seat (l : ℕ) (x : Key.Lookup) (hx : (Key.lookupsOf X.Y.k.oneTime)[l]? = some x)
    (εs : ℝ≥0∞) (A : JointRow (H₁ X N P × (FK X N P).S₁) F)
    (ps : List (Piece (ckP .two) F (H₁ X N P × (FK X N P).S₁) (FK X N P).Cl W))
    (rs : List (JointRow (H₁ X N P × (FK X N P).S₁) F))
    (hbs : ps.map (·.b) =
      ((FK X N P).first.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow : keyRowAt A rs (2 + (6 * l + 4) + 1) =
      (keyRowAt A rs (2 + (6 * l + 4))).passed fun _ => [])
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, ps[2 + (6 * l + 4)]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (2 + (6 * l + 4) + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (2 + (6 * l + 4) + 1)).rel) :
    SeatGood εs A ps rs (2 + (6 * l + 4)) := by
  obtain ⟨e, he, hd⟩ := fk_behind_pass X N P l x hx
  exact seat_of_pass εs A ps rs _ hbs _ e he (fun _ => []) hd hrow hnd hp

/-- **Seat 2 + (6 · l + 4) is filled against every list of rows that has one row at its two
borders.** -/
theorem fk_behind_same (l : ℕ) (x : Key.Lookup) (hx : (Key.lookupsOf X.Y.k.oneTime)[l]? = some x)
    (εs : ℝ≥0∞) (A : JointRow (H₁ X N P × (FK X N P).S₁) F)
    (ps : List (Piece (ckP .two) F (H₁ X N P × (FK X N P).S₁) (FK X N P).Cl W))
    (rs : List (JointRow (H₁ X N P × (FK X N P).S₁) F))
    (hbs : ps.map (·.b) =
      ((FK X N P).first.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow : keyRowAt A rs (2 + (6 * l + 4) + 1) = keyRowAt A rs (2 + (6 * l + 4)))
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, ps[2 + (6 * l + 4)]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (2 + (6 * l + 4) + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (2 + (6 * l + 4) + 1)).rel) :
    SeatGood εs A ps rs (2 + (6 * l + 4)) := by
  obtain ⟨e, he, hd⟩ := fk_behind_pass X N P l x hx
  exact seat_of_same εs A ps rs _ hbs _ e he (fun s rs gs s' h => (hd s rs gs s' h).2) hrow hnd hp

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.fk_laid_pass
#print axioms Johnson.RunOne.Sound.fk_behind_pass
#print axioms Johnson.RunOne.Sound.fk_laid_seat
#print axioms Johnson.RunOne.Sound.fk_behind_same
#print axioms Johnson.RunOne.Sound.fk_behind_seat
