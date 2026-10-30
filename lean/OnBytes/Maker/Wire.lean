-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Wire.lean: the wire record of a whole file: what the compiler needs beside the
protocol of OnBytes/Maker/Whole.lean in order to write down its compiled verifier. Definitions
alone; the laws are in OnBytes/Maker/WireLaws.lean.

The wire records are those with a list of trees for each component of a round
(OnBytes/TypedOracleCompiler/Iop/BatchWire.lean), and the record of a file is made of the records of its six parts
(OnBytes/TypedOracleCompiler/Joined/WireOf.lean, `Wires`). A written round's record IS that of
OnBytes/TypedOracleCompiler/Run/PlanQS.lean (`wireS`: a local round) or of OnBytes/TypedOracleCompiler/Slice/Batch3Wire.lean
(`wireSh`: a shared round), by definition, at the round's data without the stored tables.

A round that sends two roots. In OnBytes/Maker/Trees.lean the several trees of a round are one
oracle. Here each is a tree of its own with a root of its own: a round's record has the LIST of its
trees' depths (`depthJ` or `depth0` := `d.trees.map (·.a)`), and `treeT` says in which of them a
position stands. The library's own wire record (Iop/BatchWire.lean) has one tree for a component and
cannot say this.

What the file contains.
  `treeT`, `placeT`: of a position of a round with several trees: the number of its tree among the
    round's trees, and the number of its leaf.
  `wireLo`, `wiresLo`: a written round of the first or the third chain, and a list of them: a local
    round; its trees stand over the slot's component; its test of work belongs to the slot's query.
  `wireSh`, `wiresSh`: a written round of the second chain: a shared round; its trees stand over the
    shared component; its test of work belongs to the shared query.
  `wireSilent`: the front round, the joining round, the seam: no tree, no test, one verifier
    message.
  `wiresOf`: the six parts' records, over `chainsOf`.
  `weOne`: the stored table's record: one string, opened by pruned paths, in a tree of depth a.
  `nOpenW`, `maxDepthW`: the verifier opens at most so many positions, in trees of at most this
    depth.
  `wqWhole`: the wire record of the file's protocol (`wholeDesc` .. `.batch`).

chal: how K hash blocks give a verifier's message, for each entry and kind. A round's query has one
block more, from which the test bits are taken (Iop/GrindWire.lean, `chalGrind`).

What is not claimed. No law is stated here.


-/
import OnBytes.Maker.WholeLaws
import OnBytes.Maker.TreesLaws
import OnBytes.TypedOracleCompiler.Joined.WireOf
import OnBytes.TypedOracleCompiler.Tagged
import OnBytes.TypedOracleCompiler.Slice.Batch3Wire

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The number of a position's tree among the round's trees. -/
abbrev treeT : (ts : List Fmt.Shape) → PosT ts → ℕ := TypedOracleCompiler.Run.PQ.treeT

/-- The number of its leaf in that tree. -/
abbrev placeT : (ts : List Fmt.Shape) → PosT ts → ℕ := TypedOracleCompiler.Run.PQ.placeT

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- A written round that is local: one tree of the slot's component for each of the round's
shapes. -/
abbrev wireLo (d : RDT) : WireRB 256 (K + 1) (roundT C d).up (RAnn.allLocal (roundT C d).up) :=
  TypedOracleCompiler.Run.PQ.wireS C K chal d.toRD

/-- A written round that is shared: one tree of the shared component for each of the round's
shapes. -/
abbrev wireSh (d : RDT) : WireRB 256 (K + 1) (roundT C d).up (RAnn.ofShared .sh (roundT C d).up) :=
  TypedOracleCompiler.Slice.wireSh C K chal d.toRD

def wiresLo : (ds : List RDT) → RoundsQueryLayout 256 (K + 1) (uLT C ds) (RoundSplits.allLocal (uLT C ds))
  | [] => ()
  | d :: ds => (wireLo C K chal d, wiresLo ds)

def wiresSh :
    (ds : List RDT) → RoundsQueryLayout 256 (K + 1) (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds))
  | [] => ()
  | d :: ds => (wireSh C K chal d, wiresSh ds)

end

/-- A round that sends a plain part alone, under any annotation. -/
def wireSilent (K : ℕ) (T : Type) (t : T) (a : RAnn (plainRound T t)) :
    WireRB 256 K (plainRound T t) a where
  pt := ⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
    fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩
  depth0 := []
  depthJ := []
  tree := fun p => p.elim
  place := fun p => p.elim
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := fun _ => ()

/-- The stored table's record. -/
def weOne (a : ℕ) : WireE (oneExternalString (2 ^ a) SgX) :=
  { WireE.one (2 ^ a) SgX (0, []) with pr := true, depth := a }

/-- What a list of rounds opens at most: for each round its draws for each tree that it opens, and
the stored tables' parts. -/
def nOpenT (ds : List RDT) : ℕ :=
  (ds.map fun d => (d.stored.map (·.count)).sum + d.entry.poss * d.opens.length).sum

/-- The greatest depth of a tree that a list of rounds sends. -/
def maxDepthT (ds : List RDT) : ℕ :=
  ds.foldl (fun m d => max m (d.trees.foldl (fun n s => max n s.a) 0)) 0

def nOpenW (D : WholeD) : ℕ := nOpenT D.ds₁ + (nOpenT D.ds₂ + nOpenT D.ds₃)

def maxDepthW (D : WholeD) : ℕ :=
  max D.a (max (maxDepthT D.ds₁) (max (maxDepthT D.ds₂) (maxDepthT D.ds₃)))

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **The wire records of the six parts of a file.** -/
def wiresOf : Wires 256 (K + 1) (chainsOf C D tF tJ t3) where
  wF := wireSilent (K + 1) TF tF _
  W₁ := wiresLo C K chal D.ds₁
  wJ := wireSilent (K + 1) TJ tJ _
  W₂ := wiresSh C K chal D.ds₂
  w3 := wireSilent (K + 1) T3 t3 _
  W₃ := wiresLo C K chal D.ds₃

/-- **The wire record of the file's protocol.** -/
def wqWhole {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (wholeDesc C D tF tJ t3 silent run).batch :=
  (wiresOf C K chal D tF tJ t3).qb (wholeDesc C D tF tJ t3 silent run) (weOne D.a)
    (decWhole C D tF tJ t3) (nOpenW D) (maxDepthW D)

end

end OnBytes.Maker
