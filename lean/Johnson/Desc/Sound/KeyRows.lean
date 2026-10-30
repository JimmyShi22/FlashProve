-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyRows.lean: THE TABLE OF JOINTS AT THE KEY FILE AS A COMPOSITION: a list of
seats along a list of rows, seats of two sorts, and the rule at it.

The setting. Johnson/Desc/Sound/KeyJoints.lean has the form of a row (`JointRow`) and of a seat
between two rows (`Seat`); the rule (`keyCoreOfDecides`, Johnson/Desc/Sound/KeyDecides.lean) takes
a value `SL` that is indexed by the typed joints alone, so that two kinds' rows of seats meet by
two equations. And it takes one sort of seat: a block that is CARRIED from a proved typed block.

What is said.
  `SeatRow Cl W A Z`: seats in a row from the row A to the row Z, INDEXED BY THE ROWS: what stands
    behind one seat is what stands in front of the next BY TYPE: no equation is left. A seat is
    `carried`: a `Seat`: a block, its stretch, a proved typed block between the two rows' joints,
    maps; or `outright`: a piece of which goodness between the two rows' conditions and relations is
    proved outright.
  `SeatRow.pieces`, `SeatRow.on`, `SeatRow.rel`: the chain's pieces, conditions and relations,
    WRITTEN.
  `SeatRow.Laws εs`: for each carried seat `Seat.Law` and "the written counts are shares of at most
    εs"; for each seat outright: the piece is good between the two rows, and its errors are shares
    of at most εs.
  `eachGoodOfRow`, `belowOfRow`: then the premise of the rule of composition, and the errors' size.
  `KeyCoreAtRows`, `keyCoreAtRows`: three such rows of seats, for the description's three flat lists
    with neighbours laid together: with the facts on the fold; THE FIRST ROW ANY ROW whose condition
    holds of the file's first statements without a collision and whose relation there gives
    "decodes"; at each seam: the condition goes over, the relation comes back; at the end: the last
    row's relation holds where its condition does: `KeyCore` AT THE DECISION `F.run`.
  `gathers_refl`: a list is itself with nothing laid together.

Limits. A rule. No row but those of KeyJoints.lean is filled, and no seat but a chain's end.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyAtGathered
import Johnson.Desc.Sound.KeyJoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.Iop.Reduction (orOff)

variable {S : Type} {F : Frame}

/-- **Seats in a row, along rows of the table.** -/
inductive SeatRow (Cl W : Type) : JointRow S F → JointRow S F → Type 1
  | nil (A : JointRow S F) : SeatRow Cl W A A
  | carried {A B Z : JointRow S F} (s : Seat Cl A B) (l : SeatRow Cl W B Z) : SeatRow Cl W A Z
  | outright {A Z : JointRow S F} (B : JointRow S F) (p : Piece (ckP .two) F S Cl W)
      (l : SeatRow Cl W B Z) : SeatRow Cl W A Z

namespace SeatRow
variable {Cl W : Type}

def len : {A Z : JointRow S F} → SeatRow Cl W A Z → ℕ
  | _, _, .nil _ => 0
  | _, _, .carried _ l => l.len + 1
  | _, _, .outright _ _ l => l.len + 1

/-- **The chain's pieces, written.** -/
def pieces : {A Z : JointRow S F} → SeatRow Cl W A Z → List (Piece (ckP .two) F S Cl W)
  | _, _, .nil _ => []
  | _, _, .carried s l => seatPiece W s.b s.base s.ds s.back s.k s.M :: l.pieces
  | _, _, .outright _ p l => p :: l.pieces

/-- **The condition at the boundary with the number i**: the row's. -/
def on : {A Z : JointRow S F} → SeatRow Cl W A Z → ℕ → S × F.E.Str → Prop
  | A, _, .nil _, _ => A.on
  | A, _, .carried _ _, 0 => A.on
  | A, _, .outright _ _ _, 0 => A.on
  | _, _, .carried _ l, i + 1 => l.on i
  | _, _, .outright _ _ l, i + 1 => l.on i

/-- **The relation at the boundary with the number i**: the row's. -/
def rel : {A Z : JointRow S F} → SeatRow Cl W A Z → ℕ → S × F.E.Str → W → Prop
  | A, _, .nil _, _ => fun a _ => A.rel a
  | A, _, .carried _ _, 0 => fun a _ => A.rel a
  | A, _, .outright _ _ _, 0 => fun a _ => A.rel a
  | _, _, .carried _ l, i + 1 => l.rel i
  | _, _, .outright _ _ l, i + 1 => l.rel i

/-- **What is asked of each seat.** -/
def Laws (εs : ℝ≥0∞) : {A Z : JointRow S F} → SeatRow Cl W A Z → Prop
  | _, _, .nil _ => True
  | _, _, .carried s l => (s.Law ∧ Err.Below (s.M.err s.k.err) εs) ∧ l.Laws εs
  | A, _, .outright B p l =>
    ((p.bk A.on B.on (fun a _ => A.rel a) (fun a _ => B.rel a)).Good ∧ Err.Below p.err εs) ∧
      l.Laws εs

theorem on_zero {A Z : JointRow S F} (L : SeatRow Cl W A Z) : L.on 0 = A.on := by
  cases L <;> rfl
theorem rel_zero {A Z : JointRow S F} (L : SeatRow Cl W A Z) : L.rel 0 = fun a _ => A.rel a := by
  cases L <;> rfl
theorem on_len {A Z : JointRow S F} (L : SeatRow Cl W A Z) : L.on L.len = Z.on := by
  induction L with
  | nil A => rfl
  | carried s l ih => exact ih
  | outright B p l ih => exact ih
theorem rel_len {A Z : JointRow S F} (L : SeatRow Cl W A Z) :
    L.rel L.len = fun a _ => Z.rel a := by
  induction L with
  | nil A => rfl
  | carried s l ih => exact ih
  | outright B p l ih => exact ih
theorem pieces_len {A Z : JointRow S F} (L : SeatRow Cl W A Z) : L.pieces.length = L.len := by
  induction L with
  | nil A => rfl
  | carried s l ih => exact congrArg (· + 1) ih
  | outright B p l ih => exact congrArg (· + 1) ih

end SeatRow

variable {Cl W : Type}

/-- **A row of seats that meet their laws meets the premise of the rule of composition.** -/
theorem eachGoodOfRow (εs : ℝ≥0∞) : ∀ {A Z : JointRow S F} (L : SeatRow Cl W A Z), L.Laws εs →
    EachGood L.on L.rel 0 L.pieces
  | _, _, .nil _, _ => trivial
  | A, _, .carried (B := B) s l, h => by
    refine ⟨?_, eachGood_shift _ _ _ 0 (eachGoodOfRow εs l h.2)⟩
    obtain ⟨hk, hB, hM, hb, hd⟩ := h.1.1
    have g := goodOfSim (seatPiece (F := F) W s.b s.base s.ds s.back s.k s.M) s.k A.rd B.rd A.inv
      B.inv hk hB (simOfDecide W s.b s.base s.ds s.back s.k s.M A.rd B.rd A.inv B.inv hM hb hd)
    show ((seatPiece (F := F) W s.b s.base s.ds s.back s.k s.M).bk A.on (l.on 0)
      (fun a _ => A.rel a) (l.rel 0)).Good
    rw [l.on_zero, l.rel_zero]
    exact g
  | A, _, .outright B p l, h => by
    refine ⟨?_, eachGood_shift _ _ _ 0 (eachGoodOfRow εs l h.2)⟩
    show (p.bk A.on (l.on 0) (fun a _ => A.rel a) (l.rel 0)).Good
    rw [l.on_zero, l.rel_zero]
    exact h.1.1

/-- Its pieces' errors are shares of at most εs. -/
theorem belowOfRow (εs : ℝ≥0∞) : ∀ {A Z : JointRow S F} (L : SeatRow Cl W A Z), L.Laws εs →
    ∀ q ∈ L.pieces, Err.Below q.err εs
  | _, _, .nil _, _, _, hq => by cases hq
  | _, _, .carried s l, h, q, hq => by
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact h.1.2
    · exact belowOfRow εs l h.2 q hq'
  | _, _, .outright _ p l, h, q, hq => by
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact h.1.2
    · exact belowOfRow εs l h.2 q hq'

theorem gathers_refl {S' Cl' : Type} : ∀ l : List (Block S' Cl'), Gathers l l
  | [] => .nil
  | b :: l => .keep b (gathers_refl l)

/-- **`KeyCore` at a description's own decision, from three rows of seats along the table's rows.**
-/
def KeyCoreAtRows : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK : WholeD) (TFk TJk T3k : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (all : List LeftT) (X₁ X₂ W : Type) (F : FileDescription Kc.conf.Rec)
    (g₁ : List (Block F.S₁ F.Cl)) (g₂ : List (Block F.S₂ F.Cl)) (g₃ : List (Block F.S₃ F.Cl))
    (T : ThreeAt (ckP .two) (DK.at a) all F X₁ X₂ W)
    (A₁ Z₁ : JointRow (F.XiPub × F.S₁) (frameAt (DK.at a) all (DK.at a).key₁ T.ft₁))
    (A₂ Z₂ : JointRow ((F.XiPub × F.S₁) × F.S₂) (frameAt (DK.at a) all (DK.at a).key₂ T.ft₂))
    (A₃ Z₃ : JointRow ((F.XiPub × F.S₁ × F.S₂) × F.S₃)
      (frameAt (DK.at a) all (DK.at a).key₃ T.ft₃))
    (L₁ : SeatRow F.Cl W A₁ Z₁) (L₂ : SeatRow F.Cl W A₂ Z₂) (L₃ : SeatRow F.Cl W A₃ Z₃)
    (εs : ℝ≥0∞),
    Gathers F.first.blocksInOrder g₁ → Gathers F.shared.blocksInOrder g₂ → Gathers F.second.blocksInOrder g₃ →
    OfGathered F g₁ g₂ g₃ T →
    T.p₁ :: T.l₁ = L₁.pieces → T.p₂ :: T.l₂ = L₂.pieces → T.p₃ :: T.l₃ = L₃.pieces →
    (atDesc F T).Fits → L₁.Laws εs → L₂.Laws εs → L₃.Laws εs →
    (∀ rec y, ¬ Kc.conf.coll y rec.1 →
      A₁.on ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => []))) →
    (∀ rec y, A₁.rel ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => [])) →
      Kc.conf.D y rec ≠ none) →
    (∀ b, Z₁.on b → A₂.on ((b.1, F.start₂ b.1.1), b.2) ∧
      (A₂.rel ((b.1, F.start₂ b.1.1), b.2) → Z₁.rel b)) →
    (∀ b s, F.start₃ b.1.1.1 b.1.1.2 b.1.2 = .ok s → Z₂.on b →
      A₃.on (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) ∧
      (A₃.rel (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) → Z₂.rel b)) →
    (∀ b, Z₃.on b → Z₃.rel b) →
    RowFit (DK.at a) all all →
    KeyCore Kc DK tFk tJk t3k silK F.run 1 εs

theorem keyCoreAtRows : KeyCoreAtRows := by
  intro a Kc DK TFk TJk T3k tFk tJk t3k silK all X₁ X₂ W F g₁ g₂ g₃ T A₁ Z₁ A₂ Z₂ A₃ Z₃ L₁ L₂ L₃ εs
    G₁ G₂ G₃ hO e₁ e₂ e₃ hf w₁ w₂ w₃ hon hrel hs₁ hs₂ hlast hfit
  refine keyCoreAnti a Kc DK TFk TJk T3k tFk tJk t3k silK silK
    (runRow (atDesc F T).run₁ (atDesc F T).run₂ (atDesc F T).run₃) F.run 1 εs
    (fun _ _ _ _ h => h) (runGivesRowGathered F g₁ g₂ g₃ T hO G₁ G₂ G₃) ?_
  have n₁ : 1 + T.l₁.length = L₁.len := by
    have := congrArg List.length e₁
    rw [List.length_cons, L₁.pieces_len] at this
    omega
  have n₂ : 1 + T.l₂.length = L₂.len := by
    have := congrArg List.length e₂
    rw [List.length_cons, L₂.pieces_len] at this
    omega
  have n₃ : 1 + T.l₃.length = L₃.len := by
    have := congrArg List.length e₃
    rw [List.length_cons, L₃.pieces_len] at this
    omega
  let Q : PlacesAt (DK.at a) all F W := ⟨L₁.on, L₁.rel, L₂.on, L₂.rel, L₃.on, L₃.rel⟩
  have hgl : (atDesc F T).Glued Q :=
    { glue₁ := by
        intro x b w hm
        have h' : orOff (L₂.on 0) (L₂.rel 0) ((b.1, F.start₂ b.1.1), b.2) w := hm
        rw [L₂.on_zero, L₂.rel_zero] at h'
        show orOff (L₁.on (1 + T.l₁.length)) (L₁.rel (1 + T.l₁.length)) b w
        rw [n₁, L₁.on_len, L₁.rel_len]
        by_cases hz : Z₁.on b
        · obtain ⟨h1, h2⟩ := hs₁ b hz
          exact Or.inl (h2 (h'.resolve_right fun hn => hn h1))
        · exact Or.inr hz
      glue₂ := by
        intro x b w hm
        obtain ⟨s, hs, hm⟩ := hm
        obtain ⟨s₃, h1, h2⟩ := Option.map_eq_some_iff.1 hs
        have h3 : F.start₃ b.1.1.1 b.1.1.2 b.1.2 = .ok s₃ := by
          cases hh : F.start₃ b.1.1.1 b.1.1.2 b.1.2 with
          | error e =>
            have h1' : (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s₃ := h1
            rw [hh] at h1'
            cases h1'
          | ok t =>
            have h1' : (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s₃ := h1
            rw [hh] at h1'
            exact congrArg Except.ok (Option.some.inj h1')
        have h' : orOff (L₃.on 0) (L₃.rel 0) (s, b.2) w := hm
        rw [L₃.on_zero, L₃.rel_zero, ← h2] at h'
        show orOff (L₂.on (1 + T.l₂.length)) (L₂.rel (1 + T.l₂.length)) b w
        rw [n₂, L₂.on_len, L₂.rel_len]
        by_cases hz : Z₂.on b
        · obtain ⟨k1, k2⟩ := hs₂ b s₃ h3 hz
          exact Or.inl (k2 (h'.resolve_right fun hn => hn k1))
        · exact Or.inr hz
      ends := by
        intro x b _
        show orOff (L₃.on (1 + T.l₃.length)) (L₃.rel (1 + T.l₃.length)) b T.wEnd
        rw [n₃, L₃.on_len, L₃.rel_len]
        by_cases hz : Z₃.on b
        · exact Or.inl (hlast b hz)
        · exact Or.inr hz }
  exact keyCoreOfBlocks a Kc DK TFk TJk T3k tFk tJk t3k silK all _ _ _ _ _ F.Cl W (atDesc F T) Q
    yes₂ yes₂ yes₂ hf.shape₁ hf.shape₂ hf.shape₃ 1 εs hf
    (e₁ ▸ eachGoodOfRow εs L₁ w₁) (e₂ ▸ eachGoodOfRow εs L₂ w₂) (e₃ ▸ eachGoodOfRow εs L₃ w₃)
    hgl hfit
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    (fun rec y h => by
      have h' : L₁.on 0 ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => [])) →
          ∃ w, L₁.rel 0 ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => [])) w := h
      rw [L₁.on_zero, L₁.rel_zero] at h'
      by_cases hc : Kc.conf.coll y rec.1
      · exact Or.inl hc
      · exact Or.inr (hrel rec y ((h' (hon rec y hc)).elim fun _ hw => hw)))
    (belowOfPieces (ckP .two) (DK.at a) all Kc.conf.Rec _ _ _ _ _ F.Cl W TFk TJk T3k tFk tJk t3k
      (atDesc F T) Q yes₂ yes₂ yes₂ hf.shape₁ hf.shape₂ hf.shape₃ 1 εs
      (e₁ ▸ belowOfRow εs L₁ w₁)
      (by
        intro q hq
        rw [times_one]
        exact (e₂ ▸ belowOfRow εs L₂ w₂) q hq)
      (e₃ ▸ belowOfRow εs L₃ w₃))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.eachGoodOfRow
#print axioms VerifiableInference.Desc.Sound.belowOfRow
#print axioms VerifiableInference.Desc.Sound.keyCoreAtRows
