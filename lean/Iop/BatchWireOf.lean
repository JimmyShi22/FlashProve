-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchWireOf.lean: data for the wire records (`QueryLayout`, `WireBP`) of an `L : BatchProtocol I X` whose
oracles are strings. Definitions. (Words of this library: lean/GLOSSARY.md.)

The data, none of them obtained from a statement of existence: the depth of the request tree,
numberings of the oracle positions and of the coins, and decision procedures for the abort sets
`Honest.withheld` of Test and Link and, for Batch, for `L.honestOnlineBatchProver.Bad ∪ L.honestOnlineBatchProver.Hid w x` (`BatchProtocol.Aux`). In a
round of Batch the positions of the shared component and those of a slot's component are numbered
separately, because each component has its own tree (Iop/BatchWire.lean). The placements of the
requests of a batch in the slots, the permutations of Fin N, are numbered in the order of Mathlib's
list `permsOfList`.
The wire records are not in this file (Iop/BatchWireDraw.lean).
-/
import Iop.BatchPull
import Iop.BatchWireP
import Iop.WireOf
import Mathlib.Data.Fintype.Perm

namespace Iop
open Prob

/-! ## 1. Numberings -/

/-- The permutations of Fin N, in the order of Mathlib's list of all permutations of a list. -/
instance finEnumPerm (N : ℕ) : FinEnum (Equiv.Perm (Fin N)) :=
  FinEnum.ofNodupList (permsOfList (List.finRange N))
    (fun _ => mem_permsOfList_of_mem fun x _ => List.mem_finRange x)
    (nodup_permsOfList (List.nodup_finRange N))

/-- the number of positions of the shared component m_0 of a round -/
def RAnn.card0 {r : Round} (a : RAnn r) (pt : r.IsPoint) : ℕ := letI := pt.finPos; Fintype.card {p : r.Pos // a.own p = false}
/-- the number of positions of a slot's component m_j -/
def RAnn.cardJ {r : Round} (a : RAnn r) (pt : r.IsPoint) : ℕ := letI := pt.finPos; Fintype.card {p : r.Pos // a.own p = true}

/-- For each round of a protocol with slots two numberings: of the positions of the shared
component, and of those of a slot's component. -/
def Shape.NumPosB : (s : Shape) → RoundSplits s → s.IsPoint → Type
  | [], _, _ => Unit
  | r :: s, (a, A), (pt, pts) =>
      ({p : r.Pos // a.own p = false} ≃ Fin (a.card0 pt)) ×
        ({p : r.Pos // a.own p = true} ≃ Fin (a.cardJ pt)) × Shape.NumPosB s A pts

/-- the numbering of an empty subtype -/
def numNone {α : Type} (P : α → Prop) [Fintype {a // P a}] (h : ∀ a, ¬ P a) :
    {a // P a} ≃ Fin (Fintype.card {a // P a}) :=
  haveI : IsEmpty {a // P a} := ⟨fun x => h x.1 x.2⟩
  (Equiv.equivOfIsEmpty _ (Fin 0)).trans (finCongr Fintype.card_eq_zero.symm)

/-- a numbering of a type, as a numbering of the subtype of all its elements -/
def numAll {α : Type} [Fintype α] (P : α → Prop) [Fintype {a // P a}]
    (h : ∀ a, P a) (np : α ≃ Fin (Fintype.card α)) :
    {a // P a} ≃ Fin (Fintype.card {a // P a}) :=
  ((Equiv.subtypeUnivEquiv h).trans np).trans
    (finCongr (Fintype.card_congr (Equiv.subtypeUnivEquiv h)).symm)

/-- A round in which only the slots send (`RAnn.ofSlot`): the shared component has no position, the
slot's component has all. -/
def RAnn.numOfSlot (k : Kind) (r : Round) (pt : r.IsPoint)
    (np : r.Pos ≃ Fin (@Fintype.card r.Pos pt.finPos)) :
    ({p : r.Pos // (RAnn.ofSlot k r).own p = false} ≃ Fin ((RAnn.ofSlot k r).card0 pt)) ×
      ({p : r.Pos // (RAnn.ofSlot k r).own p = true} ≃ Fin ((RAnn.ofSlot k r).cardJ pt)) :=
  letI := pt.finPos
  (numNone _ fun _ h => Bool.noConfusion h, numAll _ (fun _ => rfl) np)

/-- A round in which only the shared component is sent (`RAnn.ofShared`): the shared component has
all positions, the slot's component has none. -/
def RAnn.numOfShared (k : Kind) (r : Round) (pt : r.IsPoint)
    (np : r.Pos ≃ Fin (@Fintype.card r.Pos pt.finPos)) :
    ({p : r.Pos // (RAnn.ofShared k r).own p = false} ≃ Fin ((RAnn.ofShared k r).card0 pt)) ×
      ({p : r.Pos // (RAnn.ofShared k r).own p = true} ≃ Fin ((RAnn.ofShared k r).cardJ pt)) :=
  letI := pt.finPos
  (numAll _ (fun _ => rfl) np, numNone _ fun _ h => Bool.noConfusion h)

/-- With local rounds only, a numbering of the positions gives the two numberings of each round. -/
def Shape.NumPosB.ofLocal :
    (s : Shape) → (pts : s.IsPoint) → s.NumPos pts → s.NumPosB (RoundSplits.allLocal s) pts
  | [], _, _ => ()
  | r :: s, (pt, pts), (np, nps) =>
    ((RAnn.numOfSlot .lo r pt np).1,
      (RAnn.numOfSlot .lo r pt np).2,
      Shape.NumPosB.ofLocal s pts nps)

/-! ## 2. Blocks, depths, further data -/

/-- The first b of the K blocks, as the source string of a round. (Blocks beyond K, which do not
occur when b ≤ K, are zero.) -/
def firstBlocks (lam K b : ℕ) : (Fin K → Dig lam) → (Fin b → Dig lam) :=
  fun u i => if h : i.val < K then u ⟨i.val, h⟩ else fun _ => false



def RoundsQueryLayout.maxDepth {lam K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => max (max w.depth0 w.depthJ) (RoundsQueryLayout.maxDepth s A W)

variable {X : Type} {E : ExtSpec}


variable {I : Type}


/-- What else the compiled scheme needs as data: numberings of the oracle positions (`posT`, `posL`,
`posB`) and of the coins (`numRI`, `numT`, `numL`, `numB0`, `numB`), decision procedures (`decT`,
`decL`, `decB`: for what, the head says), and the depth of a request tree (`depthReq`). -/
structure BatchProtocol.Aux (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint)
    (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint) where
  posT   : L.offline.shape.NumPos pT
  posL   : L.link.shape.NumPos pL
  posB   : L.onlineBatch.loc.shape.NumPosB L.onlineBatch.ann pB
  numRI  : L.EncodingRandomness ≃ Fin (Fintype.card L.EncodingRandomness)
  numT   : L.honestOfflineProver.Coin ≃ Fin (Fintype.card L.honestOfflineProver.Coin)
  numL   : L.honestLinkProver.Coin ≃ Fin (Fintype.card L.honestLinkProver.Coin)
  numB0  : L.honestOnlineBatchProver.Coin0 ≃ Fin (Fintype.card L.honestOnlineBatchProver.Coin0)
  numB   : L.honestOnlineBatchProver.Coin ≃ Fin (Fintype.card L.honestOnlineBatchProver.Coin)
  decT   : ∀ w x ρ, Decidable (ρ ∈ L.honestOfflineProver.withheld w x)
  decL   : ∀ w x ρ, Decidable (ρ ∈ L.honestLinkProver.withheld w x)
  /-- do these local challenges make the slot abort? -/
  decB   : ∀ w x ρ, Decidable (ρ ∈ L.honestOnlineBatchProver.Bad ∪ L.honestOnlineBatchProver.Hid w x)
  /-- the depth of a request tree (that there are 2^depthReq slots is a hypothesis of
  `Spec.wireBDOK`) -/
  depthReq : ℕ

/-! ## 3. Opened positions -/


/-- the verifiers open no more positions than announced (`no.O` is the number for a slot's verifier
in Batch) -/
structure BatchProtocol.Opens (L : BatchProtocol I X) (no : OpenNums) : Prop where
  opT : ∀ x ρ pl, (L.offline.reads x ρ pl).card + (L.offline.extReads x ρ).card ≤ no.T
  opL : ∀ x ρ pl, (L.link.reads x ρ pl).card + (L.link.extReads x ρ).card ≤ no.L
  opB : ∀ x ρ pl, (L.onlineBatch.loc.reads x ρ pl).card + (L.onlineBatch.loc.extReads x ρ).card ≤ no.O

end Iop
