-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StringsStay.lean: WHAT A BLOCK LEAVES OF THE ORACLES' STRINGS. Statements (`def …
: Prop`) and their proofs. The strings behind a block are what the library's stage leaves
(`stageIOR`'s field `imp`: the stored table as it is, and `sLeft`).
  `CellStays`: the stored table passes every block unturned.
  `ColStays`: a tree that was sent in front of a block (its number is below the block's base) passes
    the block unturned: every column.
  `WordStays`: so the committed word of each of its tenants (`wordOf`, Johnson/Desc/Msg.lean) is the
    same in front of the block and behind it.
  `NearStays`: so a message that is near it in front is near it behind, and back.
What it is for: a boundary's relation that speaks of a committed word (`Near`, `Member`, `NEAR`,
`PIN`, `NoColl`, `PINW`) reads the strings through `cell` and `wordOf` alone: past a block that
sends other trees it rides unturned, as far as the strings go. (What it reads of the carried record
is the block's own matter.)
Limits. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MsgAt
import Johnson.Desc.Sound.StageCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel
open _root_.Run.PQ (CK SgX)

/-- The strings behind a block: what its stage leaves. -/
abbrev behind (C : CK) (F : Frame) (b : ℕ) (ds : List RDT) (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) :
    F.E.Str := (y.1, sLeft C (stg F b ds) y τ)

/-- The stored table passes every block unturned. -/
def CellStays : Prop :=
  ∀ (C : CK) (F : Frame) (b : ℕ) (ds : List RDT) (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) (x : ℕ),
    cellAt F (behind C F b ds y τ) x = cellAt F y x

theorem cellStays : CellStays := fun _ _ _ _ _ _ _ => rfl

/-- A tree that was sent in front of a block passes the block unturned. -/
def ColStays : Prop :=
  ∀ (C : CK) (F : Frame) (b : ℕ) (ds : List RDT) (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) (j x : ℕ),
    j < b → colAt F (behind C F b ds y τ) j x = colAt F y j x

theorem colStays : ColStays := by
  intro C F b ds y τ j x hj
  unfold colAt
  cases hp : posL F.all j x with
  | none => rfl
  | some p =>
    show sLeft C (stg F b ds) y τ p = y.2 p
    rw [sLeft_at C F ds b y τ j x p hp, sCol_eq, if_pos hj, hp]
    rfl

/-- The committed word of each tenant of such a tree is the same in front and behind. -/
def WordStays : Prop :=
  ∀ (Xi : Type) (G : FileDescription Xi) (C : CK) (F : Frame) (b : ℕ) (ds : List RDT) (y : F.E.Str)
    (τ : Iop.Tr (uLT C ds)) (j t : ℕ), j < b →
    wordOf G (strsOf F (behind C F b ds y τ)) j t = wordOf G (strsOf F y) j t

theorem wordStays : WordStays := by
  intro Xi G C F b ds y τ j t hj
  funext x
  show (G.oracleAt j).bind (fun o => o.cut t (colAt F (behind C F b ds y τ) j x)) = _
  rw [colStays C F b ds y τ j x hj]
  rfl

/-- A message is near it behind just where it is near it in front. -/
def NearStays : Prop :=
  ∀ (Xi M : Type) (G : FileDescription Xi) (enc : Oracle → ℕ → ℕ → M → (ℕ → Option Sym) → Prop)
    (e : ℕ) (C : CK) (F : Frame) (b : ℕ) (ds : List RDT) (y : F.E.Str) (τ : Iop.Tr (uLT C ds))
    (j t : ℕ) (m : M),
    j < b → (Near G enc e j t (strsOf F (behind C F b ds y τ)) m ↔ Near G enc e j t (strsOf F y) m)

theorem nearStays : NearStays := by
  intro Xi M G enc e C F b ds y τ j t m hj
  unfold Near
  rw [wordStays Xi G C F b ds y τ j t hj]

end VerifiableInference.Desc.Sound
