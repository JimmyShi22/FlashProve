-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/WalkAt.lean: the walks of the compiled verifier's forests under fixed oracle
functions, as functions without queries.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Behind its chains the compiled verifier checks the opened leaves tree by tree (`runForests`,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean): it hashes the leaves, then hashes level by level, and
compares what is left with the roots. Under fixed oracle functions g each step is a value. This
file writes the walk as a function of g without queries. So each of the four premises `walk₁`,
`walk₂`, `walk₃`, `walkE` of `CutsAt` (OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean) is a Boolean equation,
forest by forest.

Main names:
  `evaluates_det g`: "has the value a under g" is kept by pure and bind (`Evaluates`,
    Compile/MerkleList.lean).
  `nodeAt g`, `leavesP g`: the hash of a node, and the digests of the opened leaves, under g.
  `walkP g F s`: the walk of one forest with the sibling digests s.
  `det_leavesV`, `det_runForest`: the verifier's programs have these values under g.
  `det_runForests`: the walks of a list of forests, each with the sibling digests read off its own
    paths, say yes under g exactly if `walkP g F F.reads` is true for each forest F of the list.

Limits: nothing on soundness. Nothing says how g comes from a hash on strings.

Terms: lean/GLOSSARY.md.

-/
import Rom.Cache
import Compile.OctopusRom
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestFacts

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- "has the value a under g" is kept by pure and bind -/
theorem evaluates_det {S : OSpec} (g : Fam S) :
    Evaluates (OComp S) (fun {_} c a => c.det g = a) where
  pure := fun _ => rfl
  bind := fun {_ _ c f a b} h h' => by
    show (c.bind f).det g = b
    rw [OComp.det_bind, h, h']

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the hash of a node of a tree over oracles, under g -/
def nodeAt (g : Fam (typedOracleFamily lam K L)) (u v : Dig lam) : Dig lam :=
  g OracleName.node (List.ofFn u, List.ofFn v)

/-- the digests of the opened leaves, under g -/
def leavesP (g : Fam (typedOracleFamily lam K L)) (cs : List (ℕ × Check lam L)) : List (Dig lam) :=
  cs.map fun e => g OracleName.leaf e.2.inp

/-- The walk of one forest under g, with the sibling digests s: the leaves' digests; level by level
up to the roots; each node that is left is compared with the root of its tree. -/
def walkP (g : Fam (typedOracleFamily lam K L)) (F : Forest lam L) (s : List (Dig lam)) : Bool :=
  ((Octopus.upN F.depth F.idx).zip
    (Octopus.octF (nodeAt g) F.depth F.idx (leavesP g F.cs) s)).all
      fun m => decide (m.2 = F.treeRoot m.1)

theorem det_leavesV (g : Fam (typedOracleFamily lam K L)) : ∀ cs : List (ℕ × Check lam L),
    (leavesV (K := K) cs).det g = leavesP g cs
  | [] => rfl
  | e :: es => by
    show ((askTypedOracle (L := L) (K := K) OracleName.leaf e.2.inp).bind fun d =>
      (leavesV es).bind fun r => OComp.pure (d :: r)).det g = _
    rw [OComp.det_bind, OComp.det_bind, det_leavesV g es]
    rfl

/-- Under g the verifier's walk of one forest is `walkP`. -/
theorem det_runForest (g : Fam (typedOracleFamily lam K L)) (F : Forest lam L) (s : List (Dig lam)) :
    (runForest (K := K) F s).det g = walkP g F s := by
  show ((leavesV (K := K) F.cs).bind fun v =>
    (Octopus.octC (Compile.Batch.hashTreeNode (K := K) (L := L)) F.depth F.idx v s).bind fun out =>
      OComp.pure (((Octopus.upN F.depth F.idx).zip out).all
        fun m => decide (m.2 = F.treeRoot m.1))).det g = _
  rw [OComp.det_bind, OComp.det_bind, det_leavesV,
    Evaluates.octC (evaluates_det g) (qN := Compile.Batch.hashTreeNode (K := K) (L := L))
      (hN := nodeAt g)
      (fun _ _ => rfl) F.depth F.idx _ s]
  rfl

/-- **Under g the walks of a list of forests, each with the sibling digests read off its own paths,
say yes exactly if each forest's walk does.** -/
theorem det_runForests (g : Fam (typedOracleFamily lam K L)) : ∀ Fs : List (Forest lam L),
    (runForests (K := K) Fs (readsF Fs)).det g = Fs.all fun F => walkP g F F.reads
  | [] => rfl
  | F :: Fs => by
    have e1 : (F.reads ++ readsF Fs).take F.need = F.reads := List.take_left' F.length_reads
    have e2 : (F.reads ++ readsF Fs).drop F.need = readsF Fs := List.drop_left' F.length_reads
    show ((runForest (K := K) F ((F.reads ++ readsF Fs).take F.need)).bind fun a =>
      (runForests Fs ((F.reads ++ readsF Fs).drop F.need)).bind fun b =>
        OComp.pure (a && b)).det g = _
    rw [e1, e2, OComp.det_bind, OComp.det_bind, det_runForest, det_runForests g Fs]
    rfl

/-- the premise on the walks of a list of forests, forest by forest -/
theorem walk_at (g : Fam (typedOracleFamily lam K L)) {Fs : List (Forest lam L)}
    (h : ∀ F ∈ Fs, walkP g F F.reads = true) :
    (runForests (K := K) Fs (readsF Fs)).det g = true := by
  rw [det_runForests]
  exact List.all_eq_true.2 h

end TypedOracleCompiler.Joined
