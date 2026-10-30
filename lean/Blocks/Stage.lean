-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Stage.lean: stages (a block with honest prover, errors and simulator) and chains of stages.

Blocks/Block.lean and Blocks/BlockHon.lean state soundness (`Block.Clean`), completeness
(`Hon.AccOn`) and masked form (`Hon.Masked`) of a block one by one, each with its rule of
composition. A long protocol is a sequence of some dozens of blocks. This file bundles what
belongs together, so that such a sequence is composed once (words of this library:
lean/GLOSSARY.md).

Main names:
  `Cut`: the relations between two stages: the relation for soundness, the relation for the honest
      run, and the validity of the honest prover's state.
  `Core`, `Stage`: a `Core` is the protocol only (a block and its honest prover); a `Stage` adds
      what the analysis needs: error counts, the pads with which it masks and those that it reads, a
      simulator, and bounds on the probabilities of the two parts of the withheld set
      (`Hon.withheld`, Blocks/BlockHon.lean).
  `Stage.Props`: all properties of a stage, between the relations before and after it.
  `Stage.Props.seq`, `Chain.Props.stage`: two stages, or any number, in a row have `Stage.Props` if
      each has it, between matching relations, they mask with disjoint sets of pads and none reads a
      pad with which a later one masks.

Limits: the composition rule follows the order of the messages. A part in which an earlier message
reads pads with which a later message masks is composed by another rule (`Hon.Masked.comp'`,
Blocks/BlockHon.lean) and enters a chain as one stage.
`Stage.Props` bounds the games by the stage's own fields: its list of errors ε, and the bounds pBad,
pWin on the probabilities of the two parts of the withheld set. It does not say how large these
fields are.
-/
import Blocks.BlockFront
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob
open scoped ENNReal

/-- The types between two stages: the explicit part X and the implicit part Y of a statement, and
the state I of the honest prover. -/
structure Sorts where
  X : Type
  Y : Type
  I : Type

/-- The relations between two stages. -/
structure Cut (P E : Type) (a : Sorts) where
  /-- the relation for soundness -/
  R : a.X → a.Y → Prop
  /-- the relation of the honest run: the statement belongs to the honest state under the pads, and
  it is true -/
  Hn : a.I → (P → E) → a.X → a.Y → Prop
  /-- validity of the honest state; it does not mention coins -/
  V : a.I → Prop

/-- The protocol of a stage: a block and its honest prover. This is all of a stage that enters a
scheme: what the verifier computes and what the honest prover sends. It is kept apart from the
numbers and the simulator of the stage, which serve statements and proofs (a simulator is a
distribution, a bound is a real number; neither is a program). -/
structure Core (P E : Type) (a b : Sorts) where
  B : Block a.X a.Y b.X b.Y
  H : Hon B P E a.I b.I

/-- A stage: the data. -/
structure Stage (P E : Type) (a b : Sorts) extends Core P E a b where
  /-- the errors, round by round, as counts -/
  ε : Err B.shape
  /-- the pads with which the stage masks, and the pads that its plain parts read. (The content of a
  vector may read any pad, and a pad vector holds pads: these do not count here. Whether their
  encodings hide the vectors is no statement of this structure.) -/
  U : Set P
  D : Set P
  /-- the simulator of the plain parts -/
  Sim : Rho B.shape → PMF (Plains B.shape)
  /-- bounds for the probabilities of the public bad set and of the rest of the withheld set -/
  pBad : ℝ≥0∞
  pWin : ℝ≥0∞

variable {P E : Type} [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E]

/-- All properties of a stage, between the relations before and after it. -/
structure Stage.Props {a b : Sorts} (S : Stage P E a b) (ca : Cut P E a) (cb : Cut P E b) :
    Prop where
  clean : S.B.Clean ca.R cb.R S.ε
  acc : S.H.AccOn ca.Hn cb.Hn
  masked : S.H.Masked ca.V S.U S.D S.Sim
  /-- a valid state stays valid, whatever the verifier sends -/
  keeps : ∀ s ρ, ca.V s → cb.V (S.H.next s ρ)
  prBad : prRho S.H.Bad ≤ S.pBad
  prWin : ∀ s, ca.V s → prRho (S.H.Win s) ≤ S.pWin

namespace Stage

variable {a b c : Sorts}

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- Two protocols in a row. -/
@[reducible] def _root_.Blocks.Core.seq (C₁ : Core P E a b) (C₂ : Core P E b c) : Core P E a c where
  B := C₁.B.seq C₂.B
  H := C₁.H.seq C₂.H

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- Two stages in a row. Errors are concatenated, sets of pads unite, the bounds `pBad`, `pWin` add.
-/
def seq (S₁ : Stage P E a b) (S₂ : Stage P E b c) : Stage P E a c where
  toCore := S₁.toCore.seq S₂.toCore
  ε := Err.app S₁.ε S₂.ε
  U := S₁.U ∪ S₂.U
  D := S₁.D ∪ S₂.D
  Sim := Hon.simSeq S₁.Sim S₂.Sim
  pBad := S₁.pBad + S₂.pBad
  pWin := S₁.pWin + S₂.pWin

/-- Composition of all properties, if the two stages mask with disjoint sets of pads (`hU`) and the
first reads none of the second's (`hD`). -/
theorem Props.seq {S₁ : Stage P E a b} {S₂ : Stage P E b c} {ca : Cut P E a}
    {cb : Cut P E b} {cc : Cut P E c} (h₁ : S₁.Props ca cb) (h₂ : S₂.Props cb cc)
    (hU : Disjoint S₁.U S₂.U) (hD : Disjoint S₁.D S₂.U) : (S₁.seq S₂).Props ca cc where
  clean := h₁.clean.comp h₂.clean
  acc := h₁.acc.comp h₂.acc
  masked := h₁.masked.comp h₂.masked (fun s ρ hs _ => h₁.keeps s ρ hs) hU hD
  keeps := fun s _ hs => h₂.keeps _ _ (h₁.keeps s _ hs)
  prBad := (prRho_cyl_union_le S₁.H.Bad S₂.H.Bad).trans (add_le_add h₁.prBad h₂.prBad)
  prWin := fun s hs =>
    (prRho_fibre_le (S₁.H.Win s) (fun ρ₁ => S₂.H.Win (S₁.H.next s ρ₁)) S₂.pWin
        fun ρ₁ _ => h₂.prWin _ (h₁.keeps s ρ₁ hs)).trans
      (add_le_add (h₁.prWin s hs) le_rfl)

/-- Consequence: for soundness a larger relation before and a smaller one after; for the honest run
and validity the reverse. -/
theorem Props.conseq {S : Stage P E a b} {ca ca' : Cut P E a} {cb cb' : Cut P E b}
    (h : S.Props ca cb) (hR : ∀ x y, ca.R x y → ca'.R x y) (hR' : ∀ x y, cb'.R x y → cb.R x y)
    (hH : ∀ s π x y, ca'.Hn s π x y → ca.Hn s π x y)
    (hH' : ∀ s π x y, cb.Hn s π x y → cb'.Hn s π x y) (hV : ∀ s, ca'.V s → ca.V s)
    (hV' : ∀ s, cb.V s → cb'.V s) : S.Props ca' cb' where
  clean := h.clean.conseq hR hR'
  acc := h.acc.conseq hH hH'
  masked := ⟨fun s ρ π π' hs => h.masked.reads s ρ π π' (hV s hs),
    fun s ρ σ hs => h.masked.law s ρ σ (hV s hs)⟩
  keeps := fun s ρ hs => hV' _ (h.keeps s ρ (hV s hs))
  prBad := h.prBad
  prWin := fun s hs => h.prWin s (hV s hs)

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- The protocol without rounds that changes nothing. -/
@[reducible] def _root_.Blocks.Core.id (a : Sorts) : Core P E a a where
  B := Block.pure some _root_.id
  H := Hon.pure some _root_.id _root_.id

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- The stage without rounds that changes nothing. -/
def id (a : Sorts) : Stage P E a a where
  toCore := Core.id a
  ε := ()
  U := ∅
  D := ∅
  Sim := fun _ => PMF.pure ()
  pBad := 0
  pWin := 0

theorem props_id (ca : Cut P E a) : (Stage.id (P := P) (E := E) a).Props ca ca where
  clean := Block.clean_pure_iff.2 fun x y xo hxo hR => by
    rw [Option.some.inj hxo]
    exact hR
  acc := Hon.accOn_pure fun _ _ x _ hi => ⟨x, rfl, hi⟩
  masked := Hon.masked_pure some _root_.id _root_.id _
  keeps := fun _ _ hs => hs
  prBad := by
    show prRho (∅ : Set (Rho [])) ≤ 0
    unfold prRho
    rw [pr_empty]
  prWin := fun _ _ => by
    show prRho (∅ : Set (Rho [])) ≤ 0
    unfold prRho
    rw [pr_empty]

end Stage

/-! ## Chains -/

/-- Any number of stages in a row. -/
inductive Chain (P E : Type) : Sorts → Sorts → Type 1
  | nil (a : Sorts) : Chain P E a a
  | cons {a b c : Sorts} (S : Stage P E a b) (t : Chain P E b c) : Chain P E a c

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- The chain as one stage. -/
def Chain.stage : {a b : Sorts} → Chain P E a b → Stage P E a b
  | _, _, .nil a => Stage.id a
  | _, _, .cons S t => S.seq t.stage

/-- Any number of protocols in a row. -/
inductive CChain (P E : Type) : Sorts → Sorts → Type 1
  | nil (a : Sorts) : CChain P E a a
  | cons {a b c : Sorts} (C : Core P E a b) (t : CChain P E b c) : CChain P E a c

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- The chain as one protocol. -/
def CChain.core : {a b : Sorts} → CChain P E a b → Core P E a b
  | _, _, .nil a => Core.id a
  | _, _, .cons C t => C.seq t.core

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- The protocols of a chain of stages. Its term mentions the stages, so no scheme's definition may
use it: it serves `Chain.toCore_stage` only; a scheme is to build its `CChain` from protocols. -/
def Chain.cores : {a b : Sorts} → Chain P E a b → CChain P E a b
  | _, _, .nil a => .nil a
  | _, _, .cons S t => .cons S.toCore t.cores

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- The protocol of a chain of stages is the chain of their protocols. -/
theorem Chain.toCore_stage : ∀ {a b : Sorts} (t : Chain P E a b), t.stage.toCore = t.cores.core
  | _, _, .nil _ => rfl
  | _, _, .cons S t => by
      show S.toCore.seq t.stage.toCore = S.toCore.seq t.cores.core
      rw [Chain.toCore_stage t]

/-- All stages of the chain have their properties, between matching relations. Each stage masks with
its own pads and reads no pad with which a later stage masks. -/
inductive Chain.Props : {a b : Sorts} → Chain P E a b → Cut P E a → Cut P E b → Prop
  | nil {a : Sorts} (ca : Cut P E a) : Chain.Props (.nil a) ca ca
  | cons {a b c : Sorts} {S : Stage P E a b} {t : Chain P E b c} {ca : Cut P E a} {cb : Cut P E b}
      {cc : Cut P E c} (hS : S.Props ca cb) (ht : Chain.Props t cb cc)
      (hU : Disjoint S.U t.stage.U) (hD : Disjoint S.D t.stage.U) : Chain.Props (.cons S t) ca cc

omit [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E] in
/-- The condition on the pads only: each stage masks with its own pads and reads no pad with which a
later stage masks. -/
def Chain.PadsOK : {a b : Sorts} → Chain P E a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons S t => Disjoint S.U t.stage.U ∧ Disjoint S.D t.stage.U ∧ t.PadsOK

/-- A chain of stages with `Chain.Props` is a stage with `Stage.Props`. -/
theorem Chain.Props.stage :
    ∀ {a b : Sorts} {t : Chain P E a b} {ca : Cut P E a} {cb : Cut P E b},
      Chain.Props t ca cb → t.stage.Props ca cb
  | _, _, _, _, _, .nil ca => Stage.props_id ca
  | _, _, _, _, _, .cons hS ht hU hD => hS.seq ht.stage hU hD

end Blocks
