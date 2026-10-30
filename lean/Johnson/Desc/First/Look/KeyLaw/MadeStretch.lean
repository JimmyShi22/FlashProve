-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/MadeStretch.lean: A STRETCH THAT IS THE DATA OF THE KIND'S OWN
BLOCK'S DECLARED ROUNDS (RoundIs, Along: Johnson/Desc/Sound/Stretch.lean) is made of the lookup's
shape (MadeOf, MeetsAt.lean): so it meets the typed lookup's formats.

Main names:
  declared_of_along: round by round: the entry, the kind of its name, its cut.
  made_of_block: AT THE KIND's BLOCK, for every seat and place whose tests on the plan pass.

Limits. That a piece's stretch goes along its block's declared rounds, and has their number, are
premises (stretchOfData, Johnson/Desc/Sound/Stretch.lean, says the first of the maker's pieces).

-/
import Johnson.Desc.First.Look.KeyLaw.MadeAt
import Johnson.Desc.Sound.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound (RoundIs Along)

/-- Round by round: the entry, the kind of its name, its cut. -/
theorem declared_of_along (num : Fmt.TreeSource → ℕ) : ∀ (es : List Fmt.Entry) (ds : List RDT),
    ds.length = es.length →
    Along (RoundIs num) (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) ds →
    List.Forall₂ AsDeclared ds es
  | [], [], _, _ => .nil
  | e :: es, d :: ds, hl, h => by
    obtain ⟨⟨h1, h2, h3, -⟩, h'⟩ := h
    exact .cons ⟨h1, h2, h3⟩ (declared_of_along num es ds (Nat.succ.inj hl) h')
  | [], _ :: _, hl, _ => by cases hl
  | _ :: _, [], hl, _ => by cases hl

/-- **At the kind's block.** -/
theorem made_of_block {S Cl : Type} (σ : SeatG S Cl) (before : List (ℕ × ℕ)) (bits : ℕ)
    (guests : List (First.Look.Guest S Cl)) (p : PG) (num : Fmt.TreeSource → ℕ) (ds : List RDT)
    (hs : p.face.shifted = false) (hok : (lookupKind σ before bits guests p).planOk = true)
    (hl : ds.length = (lookupKind σ before bits guests p).rounds.length)
    (h : Along (RoundIs num) (lookupKind σ before bits guests p).rounds ds) :
    List.Forall₂ MadeOf ds (shapeG p.face) := by
  have hok' : p.planOk before bits guests = true := hok
  unfold PG.planOk at hok'
  simp only [Bool.and_eq_true] at hok'
  obtain ⟨⟨⟨⟨k1, k2⟩, -⟩, -⟩, -⟩ := hok'
  obtain ⟨es, he⟩ := Option.isSome_iff_exists.1 k2
  have hr : (lookupKind σ before bits guests p).rounds =
      es.map fun e => ({ entry := e } : Fmt.DeclaredRound) := by
    show (p.entries.getD []).map _ = _
    rw [he]
    rfl
  rw [hr] at h hl
  rw [List.length_map] at hl
  exact made_along p.set p.scope p.face es hs k1 he ds (declared_of_along num es ds hl h)

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.declared_of_along
#print axioms VerifiableInference.Desc.K3.KeyLaw.made_of_block
