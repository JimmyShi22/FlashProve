-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageTrack.lean: tracking data (where the exposed entries of the implicit part come from) for
stages and chains; and the form of the claims in which a protocol made of stages ends. (Words of
this library: lean/GLOSSARY.md.)

The implicit part of a statement is the part that a block's verifier never reads
(Blocks/Block.lean). Blocks/BlockTrack.lean defines, for one block, the property that every entry
which its implicit output exposes is an entry that its input exposed or an entry of a vector sent in
the block. Here:
 * `Reads`: what an implicit part exposes: its entries, and the matrix of weights.
 * `Core.Track` (`S.Track` abbreviates `S.toCore.Track`), `Core.Track.OK`: how the vectors of a
   protocol are sent encoded, where each exposed entry comes from, and the condition; the matrix is
   copied.
 * `Core.Track.seq`, `Core.Track.id`; `CChain.Track`, `CChain.Track.core`: two protocols, none, any
   number in a row.
 * `OutClaims`: what a protocol made of stages ends in: affine forms in the exposed entries that are
   claimed to be 0, and one index claim whose pad part is such a form.
 * `Reads.start`: at the start the implicit part is the matrix, and no entry is exposed.
-/
import Blocks.Stage
import Blocks.BlockTrack

set_option autoImplicit false

namespace Blocks

open Iop Prob
open scoped ENNReal

/-- What an implicit part exposes between two stages: entries, indexed by N, and the matrix of
weights. -/
structure Reads (F E : Type) (a : Sorts) where
  N : Type
  rd : a.Y → N → E
  mat : a.Y → ℕ → ℕ → F

section Track

variable {F P E : Type} [Field F] [Field E] [Algebra F E] {a b c : Sorts}

/-- The tracking data: how a protocol sends its vectors (`d`), and where the exposed entries come
from (`src`). They belong to the protocol of a stage (`Core`), not to its analysis. -/
structure Core.Track (C : Core P E a b) (ra : Reads F E a) (rb : Reads F E b) where
  d : EncData F E C.B.shape
  src : rb.N → Src ra.N C.B.shape d

/-- The tracking data of a stage are those of its protocol. -/
abbrev Stage.Track (S : Stage P E a b) (ra : Reads F E a) (rb : Reads F E b) : Type 1 :=
  S.toCore.Track ra rb

/-- The condition: every entry that the output exposes is an entry that the input exposed, or an
entry of a vector sent in the protocol; the matrix is copied. -/
def Core.Track.OK {C : Core P E a b} {ra : Reads F E a} {rb : Reads F E b} (t : C.Track ra rb) :
    Prop :=
  C.B.Tracks t.d ra.rd rb.rd t.src ∧ ∀ y τ, rb.mat (C.B.imp y τ) = ra.mat y

/-- Two protocols in a row. -/
def Core.Track.seq {C₁ : Core P E a b} {C₂ : Core P E b c} {ra : Reads F E a} {rb : Reads F E b}
    {rc : Reads F E c} (t₁ : C₁.Track ra rb) (t₂ : C₂.Track rb rc) : (C₁.seq C₂).Track ra rc where
  d := t₁.d.app t₂.d
  src := srcSeq t₁.d t₂.d t₁.src t₂.src

theorem Core.Track.OK.seq {C₁ : Core P E a b} {C₂ : Core P E b c} {ra : Reads F E a}
    {rb : Reads F E b} {rc : Reads F E c} {t₁ : C₁.Track ra rb} {t₂ : C₂.Track rb rc}
    (h₁ : t₁.OK) (h₂ : t₂.OK) : (t₁.seq t₂).OK :=
  ⟨h₁.1.comp h₂.1, fun _ _ => (h₂.2 _ _).trans (h₁.2 _ _)⟩

/-- The protocol without rounds. -/
def Core.Track.id (ra : Reads F E a) : (Core.id (P := P) (E := E) a).Track ra ra where
  d := PUnit.unit
  src := fun n => .inl n

theorem Core.Track.ok_id (ra : Reads F E a) : (Core.Track.id (P := P) ra).OK :=
  ⟨Block.tracks_pure (F := F) (fun n => n) fun _ _ => rfl, fun _ _ => rfl⟩

/-- Any number of protocols in a row: the data. -/
inductive CChain.Track : {a b : Sorts} → CChain P E a b → Reads F E a → Reads F E b → Type 1
  | nil {a : Sorts} (ra : Reads F E a) : CChain.Track (.nil a) ra ra
  | cons {a b c : Sorts} {C : Core P E a b} {t : CChain P E b c} {ra : Reads F E a}
      {rb : Reads F E b} {rc : Reads F E c} (hC : C.Track ra rb) (ht : CChain.Track t rb rc) :
      CChain.Track (.cons C t) ra rc

/-- The chain as one protocol. -/
def CChain.Track.core :
    {a b : Sorts} → {t : CChain P E a b} → {ra : Reads F E a} → {rb : Reads F E b} →
    CChain.Track t ra rb → t.core.Track ra rb
  | _, _, _, _, _, .nil ra => Core.Track.id ra
  | _, _, _, _, _, .cons hC ht => hC.seq ht.core

end Track

/-! ## The claims at the end -/

/-- The claims in which a protocol made of stages ends: nCl affine forms in the exposed entries
(`none` is the constant term), each claimed to have the value 0; and an index claim
⟨g ⊗ eq(ψ, ·), W⟩ + ⟨c, entries⟩ = v. That the entries with a non-zero coefficient are pads is not
asked here, and no property in this file needs it. -/
structure OutClaims (N E : Type) (nCl : ℕ) where
  lin : Fin nCl → Option N → E
  g : ℕ → E
  ψ : ℕ → E
  c : N → E
  v : E

section Front

variable {F : Type} [Field F] [Fintype F] {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra F E] {P : Type} {X Ii : Type} {b : Sorts}

/-- At the start the implicit part is the matrix, and no entry is exposed. -/
def Reads.start (F E X Ii : Type) : Reads F E ⟨X, ℕ → ℕ → F, Ii⟩ where
  N := Empty
  rd := fun _ e => e.elim
  mat := fun W => W

end Front

end Blocks
