-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyQ.lean: a small protocol of this library's own, written out term by term, for a rehearsal.

The rehearsal is to run the compiled verifier (`Compile.Batch.verifyOneProtocol`: the verifier of the
non-interactive argument that the compiler makes of one protocol, with Merkle trees, a hash chain
for the challenges and proof of work; proof of work is tested where the protocol's `accept` tests
it: here `QT`'s does, by `InteractiveOracleProof.grind`) on bytes that were made outside Lean. This file has
definitions only. The toy proves nothing, and no security theorem of the compiler reaches the
verifier defined here: see part 4.

Sources. The toy is this library's own. It is not one of the toys of the programs (the C++
implementation that comes with this Lean code). It follows the format page (docs/format/FORMAT.md,
which comes with the programs) where it labels a leaf: the label holds the tree's number and how
many words the column has (three) and the salt has (five) (FORMAT.md, R2.1 and R7.3). The file was
written against an edition of the page that is not the one that ships; what is said here of these
two rules is the same in a second edition, also not the one that ships.

1. What the file contains. A toy protocol of three rounds with computable data.

The protocol. The statement is an element c of the extension field E (three 64-bit words). The
prover holds a row of 16 symbols of E.
    round 0: Nothing is sent and nothing is drawn. Its query to the hash chain is the format's call
      for a chain's first value.
    round 1: The prover sends the row as an oracle (one Merkle tree of depth 4, one symbol to a
      leaf) and does 8 bits of proof of work. The verifier draws three positions below 16, by the
      format's rule for positions.
    round 2: The prover sends one element s of E in the clear. Nothing is drawn.
    decision: s = c + the sum of the symbols at the drawn positions, each position counted once.

The main definitions (not all, and not in the file's order).
    `Q0`, `gW`, `QT`: the protocol without proof of work; the bits of work, round by round; `QT` is
      `Q0` with the work.
    `w0`, `w1`, `w2`, `wq0`, `wqT`: the wiring. An answer of the oracle is two blocks and the
      chain's value: block 0 holds the bits for the work test, block 1 the verifier's message.
    `Lt`: the surrounding interface. An interface is the library's record (`BatchProtocol`) of three
      protocols, called Test, Link and Batch, of which the compiler's theorems speak; here it gives
      the oracle queries their types; of its data the verifier's chain reads only the fields `early`
      (the identity) and `late` (none). Its Test has `QT`'s shape; everything else in it is trivial.
    `PD`: how things are spelled as bytes, for Run/CodingFn.lean: a message is the root, or s; the
      nonce; a leaf has the tree's number 0, the index 16 + x and the column, with no filling; the
      inner vertices start from `cfgT`, the digest of the toy's configuration.
    `V`: the verifier at these data. Its wiring uses pruned openings (the flag `prJ` is set): the
      opened leaves share one set of sibling digests, and the tree is walked once.
    `wq0F`, `wqF`, `VF`: the same with whole paths (the flag is not set).

2. What is checked when the file compiles. Types only: there is no test (#guard) here. Runs on a
file and on altered copies are in Run/ParseToy1.lean.

3. Theorems. None.

Notation:
  `576 256` in `V`, `VF`: `sMT`, `sFS`: the length, in bits, of the salt of a leaf (the typed salt:
    256 bits for the run's value, then the file's salt of five words: `leafCall`, Run/CodingFn.lean;
    `V` tests the length alone), and of the salt of a chain (Compile/Batch/Verifier.lean);
  `3`, `4` in `wq0`, `wq0F`: `nOpen`, `maxDepth` of `ProtocolQueryLayout` (Iop/BatchWire.lean);
  `7` in `label := 7`: the chain's label, which says of which protocol the chain is
    (Fmt/Rules4.lean);
  `4`, `7` in `kind`: the numbers of the kinds `.positions`, `.nothing` of a verifier's message
    (`Fmt.Kind.num`, Fmt/Plan.lean);
  `depth0`, `depthJ`: the depths of the trees over the shared and a slot's component (`WireRB`).

4. What is not claimed.
   The toy proves nothing. Its decision can be met for every claim c: s is sent after the positions
   are drawn, so any prover can compute c + the sum there. The toy's relation is "everything". It
   exercises hashing, parsing, the tree, the work test, and the joining of a message in the clear
   with opened symbols, and no more.
   No security theorem of the compiler reaches `V`. (`Compile.Batch.mem_of_accepted`,
   Compile/Batch/Sound.lean, speaks of `Compile.Batch.verifyB`, another verifier than `V`'s
   `verifyOneProtocol`, for any protocol and wiring, under its hypotheses: see the limits of
   Run/Toy1Laws.lean's head.) The compiler's statement on soundness (`Compile.Batch.BcsAt`) speaks
   of the verifiers at an interface's own Test, Link and Batch. `QT` is none of `Lt`'s three: `Lt`'s
   Test has `QT`'s shape and always accepts. Two theorems elsewhere do speak of `V` by name, and
   neither is about security: `toy1_lax` (Run/Toy1Laws.lean: what `V` or `VF` accepts within a trace
   of queries, `Compile.Batch.verifyB` accepts with other paths within the same trace) and
   `runOne_eq` (Run/ToyOne.lean: `V`'s run over a single oracle on bit strings is its run at the
   typed oracle functions read out of that oracle). The form that cures this, a protocol as the
   interface's own Batch, run by `Compile.Batch.vBS`, is made by the generic construction
   (Run/PlanQS.lean; at this toy's description, Run/PlanQSToy.lean), not here. Neither
   Run/PlanQS.lean nor Run/PlanQSToy.lean makes a statement on soundness (part 4 of each head).
   Also not claimed here: that the wiring obeys the conditions that the compiler's theorems ask of a
   wiring. That is proved elsewhere, with nothing assumed: `toy1_wire` in Run/Toy1Laws.lean, from
   Run/ToyQLaws.lean (which assumes that uniform blocks give uniform positions) and
   Run/ToyChalLaw.lean (`toy1_unif`: they do). Nor is it claimed that the protocol is sound for
   anything, or that `V` is a proof system.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingFn
import Fmt.Rules4
import Compile.Batch.Verifier
import Iop.GrindWire

set_option autoImplicit false

namespace Run.Toy1
open Iop Rom Compile Compile.Batch

/-- An element of E as three words. The type does not ask that they are below p. -/
abbrev E3 : Type := UInt64 × UInt64 × UInt64

def pF : Nat := _root_.Fmt.Fld.p .two
def addF (a b : UInt64) : UInt64 := UInt64.ofNat ((a.toNat + b.toNat) % pF)
def addE (a b : E3) : E3 := (addF a.1 b.1, addF a.2.1 b.2.1, addF a.2.2 b.2.2)

abbrev E0 : ExtSpec := ⟨Unit, Empty, Unit, fun _ p => p.elim⟩

@[reducible] def r0 : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := Unit
  Chal := Unit
  dOrc := ()
  dPlain := ()

@[reducible] def r1 : Round where
  Orc := Fin 16 → E3
  Pos := Fin 16
  Sym := fun _ => E3
  rd := fun o p => o p
  Plain := Unit
  Chal := Fin 3 → Fin 16
  dOrc := fun _ => (0, 0, 0)
  dPlain := ()

@[reducible] def r2 : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := E3
  Chal := Unit
  dOrc := ()
  dPlain := (0, 0, 0)

abbrev shp : Shape := [r0, r1, r2]

instance decO0 : DecidableEq (OPos shp) :=
  inferInstanceAs (DecidableEq (Empty ⊕ Fin 16 ⊕ Empty ⊕ Empty))

/-- The drawn positions, each once, in increasing order. -/
def listOf (c : Fin 3 → Fin 16) : List (Fin 16) :=
  (List.finRange 16).filter fun x => decide (∃ i, c i = x)

/-- The protocol without proof of work. -/
@[reducible] def Q0 : InteractiveOracleProof E3 E0 where
  shape := shp
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ => Finset.univ.image fun i : Fin 3 => (Sum.inr (Sum.inl (ρ.2.1 i)) : OPos shp)
  accept := fun c _ τ =>
    decide (τ.2.2.2.2.1.2 = (listOf τ.2.2.2.1).foldl (fun a x => addE a (τ.2.2.1.1 x)) c)

/-- The bits of work, round by round. -/
abbrev gW : GBits shp := (0, 8, 0, ())

/-- The protocol: `Q0` with the proof of work `gW`. -/
@[reducible] def QT : InteractiveOracleProof E3 E0 := Q0.grind ℕ gW

/-- A position below 16 from a word: its low four bits. -/
def posOf (w : UInt64) : Fin 16 := ⟨w.toNat % 16, Nat.mod_lt _ (by decide)⟩

def w0 : WireRB 256 1 r0 (RAnn.allLocal r0) where
  pt :=
    ⟨inferInstance, inferInstance, fun _ => (), fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩
  depth0 := 0
  depthJ := 0
  has0 := false
  hasJ := false
  place := fun p => p.elim
  posAt0 := fun _ => none
  posAtJ := fun _ => none
  chal := fun _ => ()

def w1 : WireRB 256 1 r1 (RAnn.allLocal r1) where
  pt := ⟨inferInstance, inferInstance, fun f => f, fun _ _ => rfl, fun _ => rfl, fun _ => (0, 0, 0)⟩
  depth0 := 0
  depthJ := 4
  has0 := false
  hasJ := true
  place := fun p => p.val
  posAt0 := fun _ => none
  posAtJ := fun j => if h : j < 16 then some ⟨j, h⟩ else none
  chal := fun u i => posOf (_root_.Fmt.wordAt (digToBytes (u 0)) (8 * i.val))
  prJ := true

def w2 : WireRB 256 1 r2 (RAnn.allLocal r2) where
  pt :=
    ⟨inferInstance, inferInstance, fun _ => (), fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩
  depth0 := 0
  depthJ := 0
  has0 := false
  hasJ := false
  place := fun p => p.elim
  posAt0 := fun _ => none
  posAtJ := fun _ => none
  chal := fun _ => ()

def we0 : WireE E0 := ⟨[], fun p => p.elim, fun p => p.elim, 0, fun _ => (), inferInstance, false⟩

def wq0 : ProtocolQueryLayout 256 1 (BatchInteractiveOracleProof.ofProto Q0) := ⟨(w0, w1, w2, ()), we0, decO0, 3, 4⟩

/-- The same as `wq0` without the flag for pruned sets: every opened leaf climbs a whole path of its
own. -/
def wq0F : ProtocolQueryLayout 256 1 (BatchInteractiveOracleProof.ofProto Q0) :=
  ⟨(w0, { w1 with prJ := false }, w2, ()), we0, decO0, 3, 4⟩

def Dn : GrData ℕ := ⟨fun _ => 65535, id, id⟩

/-- The wiring, with the work test. -/
def wqT : ProtocolQueryLayout 256 2 (BatchInteractiveOracleProof.ofProto QT) := wq0.grindLocal Dn gW

/-- The wiring with the work test, without the flag for pruned sets. -/
def wqF : ProtocolQueryLayout 256 2 (BatchInteractiveOracleProof.ofProto QT) := wq0F.grindLocal Dn gW

@[reducible] def pT : InteractiveOracleProof Unit (oneExternalString 0 Unit) :=
  { shape := QT.shape, blinded := fun _ => true, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
@[reducible] def pL : InteractiveOracleProof Unit (twoExternalStrings 0 Unit) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
@[reducible] def pB : InteractiveOracleProof E3 (oneExternalString 0 Unit) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }

/-- The surrounding interface: its Test has the toy's shape; beside that the verifier reads its
fields `early` and `late` alone: see `Lt` in the head. -/
@[reducible] def Lt : BatchProtocol Unit E3 where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => some ()
  offline := pT
  link := pL
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto pB
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (),
                           strat := fun _ _ _ =>
                               (((), ()),
                                 fun _ => ((fun _ => (0, 0, 0), ((), 0)), fun _ => (((), (0, 0, 0)), fun _ => ()))),
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun _ => (fun _ => (), fun _ => ()), strat := fun _ _ _ => (),
                        Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (), strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

def extB (e : E3) : ByteArray := _root_.Fmt.ext e

/-- The statement's bytes: one item. -/
def stmB (c : E3) : ByteArray := _root_.Fmt.item "toy: claim" (extB c)

/-- The toy's configuration: the digest of its one public file (R4.9). -/
def cfgT : ByteArray := _root_.Fmt.configDigest [_root_.Fmt.ascii "toy\n"]

/-- How the toy's data are spelled as bytes: see `PD` in the head. -/
def PD : PageD Lt where
  label := 7
  kind := fun i => if i = 1 then 4 else 7
  work := fun i => if i = 1 then 8 else 0
  stm := fun x => match x with
    | some c => stmB c
    | none => ByteArray.empty
  msg := fun _ rt pl => match rt, pl with
    | some r, _ => r
    | none, .inr (.inr (.inl (.inr s))) => extB s
    | none, _ => ByteArray.empty
  nonce := fun _ pl => match pl with
    | .inr (.inl (.inr p)) => p.2
    | _ => 0
  leaf := fun s => match s with
    | ⟨.inr (.inl x), e⟩ => (_root_.Fmt.leafPlace 0 3 5, 16 + x.val, extB e)
    | _ => (0, 0, ByteArray.empty)
  cfg := cfgT

/-- The compiled verifier of one slot at the toy. -/
def V (cms : List (Dig 256)) (c : E3) (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto QT)) : TypedOracleComputation 256 2 Lt Bool :=
  verifyOneProtocol (lam := 256) (K := 2) (L := Lt) 576 256 .test (BatchInteractiveOracleProof.ofProto QT) wqT
    (fun p a => some (.inr ⟨Tag.test, ⟨p, a⟩⟩)) id some (fun _ => none) 0 cms c π

/-- The same at the wiring without the flag for pruned sets. -/
def VF (cms : List (Dig 256)) (c : E3) (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto QT)) : TypedOracleComputation 256 2 Lt Bool :=
  verifyOneProtocol (lam := 256) (K := 2) (L := Lt) 576 256 .test (BatchInteractiveOracleProof.ofProto QT) wqF
    (fun p a => some (.inr ⟨Tag.test, ⟨p, a⟩⟩)) id some (fun _ => none) 0 cms c π

end Run.Toy1
