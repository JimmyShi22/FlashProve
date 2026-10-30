-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyRowsPlaces.lean: THREE ROWS OF SEATS AS THE RULE OF COMPOSITION'S OWN LETTER:
the conditions and relations at the boundaries (`Places`, Johnson/Desc/Sound/FileRule.lean), with
the premises on them as theorems.

The setting. The rule of composition across a file's three chains, and every rule that is stated
over it, takes one letter Q: six functions of a boundary's number (a condition and a relation for
each chain), at one type of witnesses. Johnson/Desc/Sound/KeyRows.lean has a chain's seats along
the rows of the table of joints, with the conditions and relations written from the rows.

What is said. `rowsPlaces L₁ L₂ L₃`: that letter, of three rows of seats. Of it, where the pieces of
T are the rows' own:
  `rowsGood₁` (₂, ₃): each block of each chain is good (`EachGood`);
  `rowsGlued`: the relations at the chains' ends fit together (`Three.Glued`), from the two seams
    and the end;
  `rowsFirstOn`, `rowsFirstRel`: the first boundary's two facts;
  `rowsBelow₁` (₂, ₃): every piece's errors are shares of at most εs.

Limits. The boundaries are those between the SEATS: where a seat holds several blocks of the
description laid as one, the boundaries inside it have no row, and T's pieces are the gathered
blocks' (`OfGathered`), not the description's own (`OfDesc`).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyRows

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

variable {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type} {F : FileDescription Xi}
  {T : ThreeAt (ckP .two) D all F X₁ X₂ W}
  {A₁ Z₁ : JointRow (F.XiPub × F.S₁) (frameAt D all D.key₁ T.ft₁)}
  {A₂ Z₂ : JointRow ((F.XiPub × F.S₁) × F.S₂) (frameAt D all D.key₂ T.ft₂)}
  {A₃ Z₃ : JointRow ((F.XiPub × F.S₁ × F.S₂) × F.S₃) (frameAt D all D.key₃ T.ft₃)}
  (L₁ : SeatRow F.Cl W A₁ Z₁) (L₂ : SeatRow F.Cl W A₂ Z₂) (L₃ : SeatRow F.Cl W A₃ Z₃)

/-- **The conditions and relations at the boundaries, of three rows of seats.** -/
def rowsPlaces : PlacesAt D all F W := ⟨L₁.on, L₁.rel, L₂.on, L₂.rel, L₃.on, L₃.rel⟩

variable {L₁ L₂ L₃}

theorem rowsGood₁ (εs : ℝ≥0∞) (e : T.p₁ :: T.l₁ = L₁.pieces) (h : L₁.Laws εs) :
    EachGood (rowsPlaces L₁ L₂ L₃).on₁ (rowsPlaces L₁ L₂ L₃).R₁ 0
      ((atDesc F T).p₁ :: (atDesc F T).l₁) :=
  e ▸ eachGoodOfRow εs L₁ h

theorem rowsGood₂ (εs : ℝ≥0∞) (e : T.p₂ :: T.l₂ = L₂.pieces) (h : L₂.Laws εs) :
    EachGood (rowsPlaces L₁ L₂ L₃).on₂ (rowsPlaces L₁ L₂ L₃).R₂ 0
      ((atDesc F T).p₂ :: (atDesc F T).l₂) :=
  e ▸ eachGoodOfRow εs L₂ h

theorem rowsGood₃ (εs : ℝ≥0∞) (e : T.p₃ :: T.l₃ = L₃.pieces) (h : L₃.Laws εs) :
    EachGood (rowsPlaces L₁ L₂ L₃).on₃ (rowsPlaces L₁ L₂ L₃).R₃ 0
      ((atDesc F T).p₃ :: (atDesc F T).l₃) :=
  e ▸ eachGoodOfRow εs L₃ h

theorem rowsBelow₁ (εs : ℝ≥0∞) (e : T.p₁ :: T.l₁ = L₁.pieces) (h : L₁.Laws εs) :
    ∀ q ∈ (atDesc F T).p₁ :: (atDesc F T).l₁, Err.Below q.err εs :=
  e ▸ belowOfRow εs L₁ h

theorem rowsBelow₂ (εs : ℝ≥0∞) (e : T.p₂ :: T.l₂ = L₂.pieces) (h : L₂.Laws εs) :
    ∀ q ∈ (atDesc F T).p₂ :: (atDesc F T).l₂, Err.Below q.err εs :=
  e ▸ belowOfRow εs L₂ h

theorem rowsBelow₃ (εs : ℝ≥0∞) (e : T.p₃ :: T.l₃ = L₃.pieces) (h : L₃.Laws εs) :
    ∀ q ∈ (atDesc F T).p₃ :: (atDesc F T).l₃, Err.Below q.err εs :=
  e ▸ belowOfRow εs L₃ h

/-- The first boundary's condition is the first row's. -/
theorem rowsFirstOn (a : (F.XiPub × F.S₁) × (frameAt D all D.key₁ T.ft₁).E.Str) :
    (rowsPlaces L₁ L₂ L₃).on₁ 0 a ↔ A₁.on a := by
  show L₁.on 0 a ↔ A₁.on a
  rw [L₁.on_zero]

/-- The first boundary's relation is the first row's. -/
theorem rowsFirstRel (a : (F.XiPub × F.S₁) × (frameAt D all D.key₁ T.ft₁).E.Str) (w : W) :
    (rowsPlaces L₁ L₂ L₃).R₁ 0 a w ↔ A₁.rel a := by
  show L₁.rel 0 a w ↔ A₁.rel a
  rw [L₁.rel_zero]

/-- **The relations at the chains' ends fit together.** -/
theorem rowsGlued (e₁ : T.p₁ :: T.l₁ = L₁.pieces) (e₂ : T.p₂ :: T.l₂ = L₂.pieces)
    (e₃ : T.p₃ :: T.l₃ = L₃.pieces)
    (hs₁ : ∀ b, Z₁.on b → A₂.on ((b.1, F.start₂ b.1.1), b.2) ∧
      (A₂.rel ((b.1, F.start₂ b.1.1), b.2) → Z₁.rel b))
    (hs₂ : ∀ b s, F.start₃ b.1.1.1 b.1.1.2 b.1.2 = .ok s → Z₂.on b →
      A₃.on (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) ∧
      (A₃.rel (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) → Z₂.rel b))
    (hlast : ∀ b, Z₃.on b → Z₃.rel b) : (atDesc F T).Glued (rowsPlaces L₁ L₂ L₃) := by
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
  exact
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

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.rowsGood₁
#print axioms VerifiableInference.Desc.Sound.rowsBelow₁
#print axioms VerifiableInference.Desc.Sound.rowsFirstOn
#print axioms VerifiableInference.Desc.Sound.rowsFirstRel
#print axioms VerifiableInference.Desc.Sound.rowsGlued
