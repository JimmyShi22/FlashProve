-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SeedsT.lean: the seeds' protocol from rounds' data, fit to be an interface's Test;
its wiring and laws; the joint law of the state "bad y ρ" from a count.
Why: in the protocol a stored table has a record; its seeds are drawn on a chain of hash calls of
their own, begun at the table's name, in which the prover says nothing. The typed home: a protocol T
: InteractiveOracleProof Unit E without an instance, with the table as its external string, which it never opens: a
silent front and one written round.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
  CountOK, stB, joint_stB  for any shape with local rounds alone: the state "b ρ", 0 until all
      verifier messages are there, obeys the joint law with the errors ε if, whatever the earlier
      verifier messages, at most (the last entry of ε) values of the last verifier message make b
      true
  joint_stBad  the same for LaneStays' stBad bad at every string y and all vectors of slots:
      laneOf_ok's hypothesis to the letter: so the seeds' lane is a lane, and its step event is as
      rare as any lane's. The count is over the round's verifier messages: at a lawful wire
      (wqT_okg's hc) these are hash blocks, not seeds: it is the summand that carries the bias
      factor, not coll_count: SeedsTData.lean: countOK_of_pr
  seedsT C d E  the protocol: shape := the maker's silent front s0 C, then roundS C d; no reads, no
      external reads; it accepts all: there is no decision in it: only its chain is run
  seedsT_local, seedsT_coherent, seedsT_ne
  wqT C K chal d we, wqT_okg  its wiring: the maker's wire0S and wireS; the external wire we a
      parameter; lawful if the round's verifier messages are exactly uniform, its work is at most 64
      bits and we is lawful
  plainsT, drawnT  the one fixed string (no term of type OneProtocolProof: a chain takes its parts): no salt, no
      root, the rounds' fixed plain parts; what was drawn, as the format's record (pq.drawnSL)
  extST  the reading: ReadRun's extSOf at T's chain at πT, under the tag .test: seedOf of what was
      drawn; the default d where the chain has not run
Over any interface L and wiring W: how T's plain parts are written into L's queries at the tag .test
is the parameter embP (the identity, if L.offline is T).
At a round d with a tree the chain refuses behind its first query (no root is given): extST is the
default everywhere: use SeedsTData's dSeed e. seedsT's blinded, wqT's we | nOpen | maxDepth | decO
are read by nobody: only the chain is ever run.
What is not said. Which round d (kind seeds; no item, no tree, no opening; work 0: it must have
none); any bad (coll) or count; a page (the label 2^32; the table's name as the first call's
statement; a first call without a run value: the sibling's ok asks random bytes in a file: this
chain stands in no file); K ≥ 140 blocks; that extST's seed is the programs'.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ReadRun
import OnBytes.TypedOracleCompiler.Run.PlanQSLaws
import OnBytes.TypedOracleCompiler.Run.Exports

noncomputable section

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Compile.Batch Rom _root_.Compile Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The joint law from a count -/

/-- whatever the earlier verifier messages, at most (the last entry of ε) values of the last one
make b true -/
def CountOK : (s : Shape) → Err s → (Rho s → Bool) → Prop
  | [], _, _ => True
  | [r], (e, _), b => cnt (fun c : r.Chal => b (c, ()) = true) ≤ e
  | _ :: r' :: s, (_, ε), b => ∀ c, CountOK (r' :: s) ε fun ρ => b (c, ρ)

/-- the state "b ρ", 0 until all verifier messages are there -/
def stB {s : Shape} (b : Rho s → Bool) : PTr s → Bool
  | .full τ => b τ.rho
  | _ => false

theorem joint_stB (N : ℕ) : ∀ (s : Shape) (ε : Err s) (B : Fin N → Option (Rho s → Bool)),
    (∀ j b, B j = some b → CountOK s ε b) → JointLaw N s (RoundSplits.allLocal s) ε fun j => (B j).map stB
  | [], _, _, _ => trivial
  | [r], (e, _), B, h => fun m0 m =>
    ⟨fun j S hS _ => by
        obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hS
        exact h j b hb,
      fun _ => trivial⟩
  | r :: r' :: s, (e, ε), B, h => fun m0 m =>
    ⟨fun j S hS _ => by
        obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hS
        rw [cnt_false fun c => (by intro hc; cases hc)]
        exact Nat.zero_le _,
      fun v => by
        have ih := joint_stB N (r' :: s) ε (fun j => (B j).map fun b ρ => b (v j, ρ))
            (fun j b' hb' => by
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
          exact h j b hb (v j))
        have e : (fun j => ((B j).map fun b (ρ : Rho (r' :: s)) => b (v j, ρ)).map stB) =
            fun j => ((B j).map stB).map fun S τ =>
              S (PTr.cons ((RAnn.allLocal r).join m0 (m j)) ((RAnn.allLocal r).kind.slot v j) τ) :=
                  funext fun j => by
          cases B j with
          | none => rfl
          | some b =>
            show some (stB fun ρ => b (v j, ρ)) = some _
            refine congrArg some (funext fun τ => ?_)
            cases τ <;> rfl
        rw [e] at ih
        exact ih⟩

/-- The seeds' lane's joint law: laneOf_ok's hypothesis for LaneStays' stBad. -/
theorem joint_stBad (N : ℕ) {Str Y : Type} (s : Shape) (ε : Err s) (bad : Str → Rho s → Bool)
    (h : ∀ y, CountOK s ε (bad y)) (y : Str) (x : Fin N → Option Y) :
    JointLaw N s (RoundSplits.allLocal s) ε fun j => (x j).map (stBad bad y) := by
  have h0 := joint_stB N s ε (fun j => (x j).map fun _ => bad y) (fun j b hb => by
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact h y)
  have e : (fun j => ((x j).map fun _ => bad y).map stB) = fun j => (x j).map (stBad bad y) :=
      funext fun j => by
    cases x j with
    | none => rfl
    | some u =>
      show some (stB (bad y)) = some (stBad bad y u)
      refine congrArg some (funext fun τ => ?_)
      cases τ <;> rfl
  rw [e] at h0
  exact h0

/-! ## The protocol -/

/-- The seeds' protocol: a silent front, one written round; no reads; no decision. -/
def seedsT (C : PQ.CK) (d : PQ.RD) (E : ExtSpec) : InteractiveOracleProof Unit E where
  shape := _root_.Run.Twin.up (PQ.SOf C [d])
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

theorem seedsT_local (C : PQ.CK) (d : PQ.RD) (E : ExtSpec) : (seedsT C d E).IsLocal :=
    fun _ _ _ _ _ _ _ _ _ => rfl

theorem seedsT_coherent (C : PQ.CK) (d : PQ.RD) (E : ExtSpec) :
    (BatchInteractiveOracleProof.ofProto (seedsT C d E)).ann.Coherent :=
  BatchOne.BAnn.allLocal_coherent _

theorem seedsT_ne (C : PQ.CK) (d : PQ.RD) (E : ExtSpec) :
    (BatchInteractiveOracleProof.ofProto (seedsT C d E)).loc.shape ≠ [] := fun h => by cases h

/-- Its wiring. -/
def wqT (C : PQ.CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : PQ.RD) {E : ExtSpec}
    (we : WireE E) :
    ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto (seedsT C d E)) :=
  ⟨(PQ.wire0S C K chal, PQ.wireS C K chal d, ()), we, PQ.decOS C [d], 0, PQ.depthOf d.trees⟩

theorem wqT_okg (C : PQ.CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : PQ.RD)
    {E : ExtSpec} (we : WireE E)
    (hc : (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind))
        (hw : d.entry.work ≤ 64)
    (he : we.OK) : (wqT C K chal d we).OKG where
  sh := ⟨PQ.wire0S_okg C K chal, PQ.wireS_okg C K chal d hc hw, trivial⟩
  ext := he
  opens := fun _ _ _ => Nat.le_refl 0
  depth := ⟨⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩,
    ⟨fun _ h => (by cases h), fun e h => PQ.le_depthOf d.trees e h⟩, trivial⟩

/-- the one fixed string's plain parts -/
def plainsT (C : PQ.CK) (d : PQ.RD) (E : ExtSpec) : Plains (seedsT C d E).shape :=
  ((PQ.s0 C).up.dPlain, (PQ.roundS C d).up.dPlain, ())

/-- what was drawn, as the format's record -/
def drawnT (C : PQ.CK) (d : PQ.RD) (E : ExtSpec) (ρ : Rho (seedsT C d E).shape) :
    List _root_.Fmt.Drawn :=
  PQ.drawnSL C [d] ρ.2

/-- The reading of the seeds off a list of entries: T's chain at the one fixed string, under the
tag .test. -/
def extST {I X Sd : Type} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout 256 L} (C : PQ.CK) (d : PQ.RD) {E : ExtSpec}
    (wq : ProtocolQueryLayout 256 W.K (BatchInteractiveOracleProof.ofProto (seedsT C d E)))
    (embP : PlainPart (seedsT C d E).shape (RoundSplits.allLocal _) → PlainPart (shapeOf L .test) (annOf L .test))
    (seedOf : List _root_.Fmt.Drawn → Sd) (dflt : Sd) : Tc W → List (Dig 256) → Sd :=
  extSOf .test (BatchInteractiveOracleProof.ofProto (seedsT C d E)) wq embP none [] default [] (plainsT C d E)
    (fun ρ => seedOf (drawnT C d E ρ)) dflt

end TypedOracleCompiler.Slice
