-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LinkAlong.lean: a code of the link's chain queries and a code of leaves over one
interface, carried to another interface along a map of queries with a partial way back; and what the
two encodings then read out of one oracle.

A compiled verifier can be said over two interfaces whose typed queries differ in form alone: a
first query that holds both tables' answers in its field for the instance, against one that holds
them as digests in its list of roots. An encoding into one hash function that is lawful over the
first interface is to serve over the second without a new string: a query of the second interface is
written as the query of the first from which it comes, and is not written if it comes from none.

Main definitions.
 `FbPair L1 L2`     how a link's chain query over L2 is read as one over L1, and the way back; each
                    undoes the other.
 `LeafPair L1 L2`   the same for leaf queries.
 `linkAlong`        a `SeedPage.LinkCode` over L1, carried to L2: the same label, the same strings.
 `leavesAlong`      a `PageG.Leaves` over L1, carried to L2.
Main theorems.
 `linkAlong_put`, `leavesAlong_put`: what is written at a query over L2 is what the given code
                    writes at the query over L1 as which it is read.
 `fb_read`, `fb_read_tail`, `leaf_read`, `node_read`: two pages' encodings that have one string at
                    two queries read one answer out of every oracle there: a chain query's whole
                    answer, if at all blocks; its chain value, if at the last block; a leaf's; a
                    vertex's.

Not claimed. No pair is given here. That a verifier over L2 asks only queries that are read as
queries over L1. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.SeedPage

set_option autoImplicit false

namespace TypedOracleCompiler.Run.LinkAlong
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I1 X1 I2 X2 : Type}

/-- How a link's chain query over L2 is read as one over L1, and the way back. -/
structure FbPair (L1 : BatchProtocolWithLeafBody I1 X1) (L2 : BatchProtocolWithLeafBody I2 X2) where
  /-- a query over L2 as a query over L1, if it comes from one -/
  sel : FbIn 256 L2 .link → Option (FbIn 256 L1 .link)
  /-- the way back -/
  bk : FbIn 256 L1 .link → Option (FbIn 256 L2 .link)
  /-- the way back undoes the reading -/
  bk_sel : ∀ a b, sel a = some b → bk b = some a
  /-- the reading undoes the way back -/
  sel_bk : ∀ b a, bk b = some a → sel a = some b

/-- The same for leaf queries. -/
structure LeafPair (L1 : BatchProtocolWithLeafBody I1 X1) (L2 : BatchProtocolWithLeafBody I2 X2) where
  /-- a leaf query over L2 as one over L1 -/
  sel : LeafIn L2 → Option (LeafIn L1)
  /-- the way back -/
  bk : LeafIn L1 → Option (LeafIn L2)
  /-- the way back undoes the reading -/
  bk_sel : ∀ a b, sel a = some b → bk b = some a
  /-- the reading undoes the way back -/
  sel_bk : ∀ b a, bk b = some a → sel a = some b

variable {L1 : BatchProtocolWithLeafBody I1 X1} {L2 : BatchProtocolWithLeafBody I2 X2} {K : ℕ}

/-- The reading, with a block. -/
def FbPair.selB (F : FbPair L1 L2) (x : FbIn 256 L2 .link × Fin (K + 1)) :
    Option (FbIn 256 L1 .link × Fin (K + 1)) := (F.sel x.1).map fun q => (q, x.2)

/-- The way back, with a block. -/
def FbPair.mkB (F : FbPair L1 L2) (y : FbIn 256 L1 .link × Fin (K + 1)) :
    Option (FbIn 256 L2 .link × Fin (K + 1)) := (F.bk y.1).map fun q => (q, y.2)

theorem FbPair.mkB_selB (F : FbPair L1 L2) (a : FbIn 256 L2 .link × Fin (K + 1))
    (b : FbIn 256 L1 .link × Fin (K + 1)) (h : F.selB a = some b) : F.mkB b = some a := by
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
  show (F.bk q).map _ = _
  rw [F.bk_sel _ _ hq]
  rfl

theorem FbPair.selB_mkB (F : FbPair L1 L2) (b : FbIn 256 L1 .link × Fin (K + 1))
    (a : FbIn 256 L2 .link × Fin (K + 1)) (h : F.mkB b = some a) : F.selB a = some b := by
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
  show (F.sel q).map _ = _
  rw [F.sel_bk _ _ hq]
  rfl

/-- **A code of the link's chain queries, carried along the pair.** -/
def linkAlong (F : FbPair L1 L2) (Lk : LinkCode L1 K) : LinkCode L2 K where
  pL := Lk.pL.pull F.selB F.mkB F.mkB_selB F.selB_mkB
  l := Lk.l
  hlt := Lk.hlt
  hne := Lk.hne
  his := fun x s h => by
    obtain ⟨y, -, hy⟩ := PCode.pull_put _ _ _ _ _ x s h
    exact Lk.his y s hy

/-- What it writes at a query that is read as q1: what the given code writes at q1. -/
theorem linkAlong_put (F : FbPair L1 L2) (Lk : LinkCode L1 K) (q2 : FbIn 256 L2 .link)
    (q1 : FbIn 256 L1 .link) (h : F.sel q2 = some q1) (j : Fin (K + 1)) :
    (linkAlong F Lk).pL.put (q2, j) = Lk.pL.put (q1, j) := by
  show (F.selB (q2, j)).bind _ = _
  have e : F.selB (q2, j) = some (q1, j) := by
    show (F.sel q2).map _ = _
    rw [h]
    rfl
  rw [e]
  rfl

/-- **A code of leaves, carried along the pair.** -/
def leavesAlong (G : LeafPair L1 L2) (V : Leaves L1) : Leaves L2 where
  lf := V.lf.pull G.sel G.bk G.bk_sel G.sel_bk
  hlf := fun q s h => by
    obtain ⟨y, -, hy⟩ := PCode.pull_put _ _ _ _ _ q s h
    exact V.hlf y s hy

/-- What it writes at a leaf query that is read as q1. -/
theorem leavesAlong_put (G : LeafPair L1 L2) (V : Leaves L1) (q2 : LeafIn L2) (q1 : LeafIn L1)
    (h : G.sel q2 = some q1) : (leavesAlong G V).lf.put q2 = V.lf.put q1 := by
  show (G.sel q2).bind _ = _
  rw [h]
  rfl

/-! ## One string, one answer -/

/-- Two pages' encodings that have one string at all blocks of two chain queries read one answer out
of every oracle. -/
theorem fb_read (C1 : Page L1 K) (C2 : Page L2 K) (t : Tag) (q1 : FbIn 256 L1 t)
    (q2 : FbIn 256 L2 t)
    (h : ∀ j, (implG C2).code (.fb t) q2 j = (implG C1).code (.fb t) q1 j) (g : Fam (rom 256)) :
    (readBlocks (implG C2) g (.fb t) q2 : (Fin K → Dig 256) × Dig 256) =
      readBlocks (implG C1) g (.fb t) q1 := by
  show ((fun k : Fin K => g () ((implG C2).code (.fb t) q2 k.castSucc)),
      g () ((implG C2).code (.fb t) q2 (Fin.last K))) =
    ((fun k : Fin K => g () ((implG C1).code (.fb t) q1 k.castSucc)),
      g () ((implG C1).code (.fb t) q1 (Fin.last K)))
  simp only [h]

/-- The same of the chain value alone, from the last block's string. -/
theorem fb_read_tail (C1 : Page L1 K) (C2 : Page L2 K) (t : Tag) (q1 : FbIn 256 L1 t)
    (q2 : FbIn 256 L2 t)
    (h : (implG C2).code (.fb t) q2 (Fin.last K) = (implG C1).code (.fb t) q1 (Fin.last K))
    (g : Fam (rom 256)) :
    (readBlocks (implG C2) g (.fb t) q2 : (Fin K → Dig 256) × Dig 256).2 =
      (readBlocks (implG C1) g (.fb t) q1 : (Fin K → Dig 256) × Dig 256).2 := by
  show g () ((implG C2).code (.fb t) q2 (Fin.last K)) =
    g () ((implG C1).code (.fb t) q1 (Fin.last K))
  rw [h]

/-- The same of a leaf's answer. -/
theorem leaf_read (C1 : Page L1 K) (C2 : Page L2 K) (q1 : LeafIn L1) (q2 : LeafIn L2)
    (h : (implG C2).code .leaf q2 (0 : Fin 1) = (implG C1).code .leaf q1 (0 : Fin 1))
    (g : Fam (rom 256)) :
    (readBlocks (implG C2) g .leaf q2 : Dig 256) = readBlocks (implG C1) g .leaf q1 := by
  show g () ((implG C2).code .leaf q2 (0 : Fin 1)) = g () ((implG C1).code .leaf q1 (0 : Fin 1))
  rw [h]

/-- The same of a vertex's answer. -/
theorem node_read (C1 : Page L1 K) (C2 : Page L2 K) (q : Bits × Bits)
    (h : (implG C2).code .node q (0 : Fin 1) = (implG C1).code .node q (0 : Fin 1))
    (g : Fam (rom 256)) :
    (readBlocks (implG C2) g .node q : Dig 256) = readBlocks (implG C1) g .node q := by
  show g () ((implG C2).code .node q (0 : Fin 1)) = g () ((implG C1).code .node q (0 : Fin 1))
  rw [h]

end TypedOracleCompiler.Run.LinkAlong
