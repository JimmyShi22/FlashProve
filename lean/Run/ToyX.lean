-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyX.lean: a toy in which the compiled verifier opens under an external root: an interface whose
Test is the toy itself, run by `vTS`, the function that the scheme's verifier runs on a key's test
string.

Definitions only; nothing is proved. The toy is this library's own. (docs/format/FORMAT.md: R4.6,
R7.3, R7.4,
R7.7, as Fmt/ renders them; first written against an edition of the page that is not the one that
ships, where the root stands inside a stored table's name, R4.10.)
The toy's protocol reads no oracle of the prover's. It reads an external string at the drawn
positions (the honest side's string is the encoding of an index), and the compiled verifier checks
the opened symbols against the Merkle root cm, an argument of `VX`.

Why: in a toy of this library's own (Run/ToyQ.lean) two checks of the verifier are empty, one of
them the openings under the external roots (the other is the check in the request tree, which stays
empty here: Limits); and its protocol is none of the three protocols of its ambient interface. Here
the openings under the external root are not empty, and the protocol is the interface's own Test.

The interface `Lx`. An index is a table of four columns of three words. Its encoding is the string
of four symbols, each symbol carrying its position: `Sg` := position × column. (Lean's leaf of an
external tree holds the symbol alone, without tree or position; the format hashes a stored leaf
under the tree's number and 2^a + position: with the position inside the symbol an encoding of the
queries can write that call.) `decodeIndex` refuses a string in which a symbol does not carry its own
position or a column's last word is not 7.

The protocol `QX` := `Lx.offline`. No statement.
    round 0: nothing is sent, nothing is drawn: its chain query is the format's call for a chain's
      first value.
    round 1: the prover's message is empty; the verifier draws two positions below 4.
    reads: the external string at the drawn positions; no oracle of the prover's.
    decision: each symbol read carries its position, and its column's last word is 7.

Main names:
  `Lx`: the interface (the link has no round; the batch is trivial; neither is run here; the honest
    sides are placeholders).
  `w1X`, `weX`, `wqX`, `Wx : QueryLayout 256 Lx`: the wirings.
  `XD`: the constants of the encoding of the queries.
  `firstX`, `leafX`, `famX`: from a typed query to the format's call.
  `VX cm π`: := `vTS Wx 576 256 cm π`.

Why, the two departures of the encoding of the queries from Run/CodingFn.lean. (1) The one digest in
the first head is the root cm (so `vTS` has it): it goes into the statement's bytes in the way that
a field of `XD` says (in Run/ToyXRun.lean: inside the stored table's item, R4.6); the parameters'
digest is a constant of the encoding. (2) A leaf with an index symbol has a call: the stored leaves'
number; in the tree's place of the label the tree's number with the words of the column (3) and of
the file's salt (`Fmt.leafPlace`: in the format page since an edition later than the one against
which the toy was first written; not held against the page that ships); 2^a + the symbol's
position; bytes: the column, the fill, the file's salt.
One rule for all leaves, as in Run/CodingFn.lean: the first 256 bits of a leaf's typed salt stand
for the call's start, the rest is the file's salt. For a tree made in a run the start is the run's
value; for a stored tree it is the configuration's digest, put there by the parser. Why not a
constant of the encoding alone: the verifier has one length sMT for the salts of own and of external
leaves (`strictSB`, `strictExt`), so a protocol that opens both kinds of tree needs the same length
in both. The encoding compares the first 256 bits with its own constant `cfg`: a leaf query with
another start has no call.

Limits: the verifier tests the length of a salt alone: that the first 256 bits are the
configuration's digest is the parser's doing, and is seen by the encoding, not by V (`VX`). The
request tree is not reached (the chain does not join). No work.
This file does not say that the wiring meets the conditions on a wiring, or that `Lx` has any
property of an interface. (Run/ToyXLaws.lean [not in this library; so here read: not proved in this
library]: the conditions on the wirings, locality,
`Lx.Sound` at 9/16, and the library's statement on soundness at this instance: numerically vacuous.)
`firstX` gives a call to every round behind round 0, also beyond the plan's one round: harmless for
typed oracle functions; it is no encoding into a single oracle.

Terms: lean/GLOSSARY.md.
-/
import Run.ToyQ
import Run.ToyChal
import Fmt.Rules7

set_option autoImplicit false

namespace Run.ToyX
open Iop Rom Compile Compile.Batch
open Run.Toy1 (E3 r0)

/-- A symbol of the encoded index: its position, its column. -/
abbrev Sg : Type := Fin 4 × E3
/-- An index: a table of four columns. -/
abbrev Ix : Type := Fin 4 → E3

@[reducible] def r1X : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := Unit
  Chal := Fin 2 → Fin (2 ^ 2)
  dOrc := ()
  dPlain := ()

abbrev shpX : Shape := [r0, r1X]

instance decOX : DecidableEq (OPos shpX) := inferInstanceAs (DecidableEq (Empty ⊕ Empty ⊕ Empty))

/-- The symbol s is in order at the position x: it carries x, and its column's last word is 7. -/
def symOK (x : Fin 4) (s : Sg) : Bool := decide (s.1 = x) && decide (s.2.2.2 = 7)

/-- The protocol: its rounds, reads and decision are told in the head. -/
@[reducible] def QX : InteractiveOracleProof Unit (oneExternalString 4 Sg) where
  shape := shpX
  blinded := fun _ => false
  extReads := fun _ ρ => Finset.univ.image fun i : Fin 2 => (ρ.2.1 i : Fin 4)
  reads := fun _ _ _ => ∅
  accept := fun _ y τ => (List.finRange 2).all fun i => symOK (τ.2.2.2.1 i) (y (τ.2.2.2.1 i))

def encX (i : Ix) : Fin 4 → Sg := fun p => (p, i p)
def decX (y : Fin 4 → Sg) : Option Ix :=
  if (List.finRange 4).all (fun p => symOK p (y p)) then some fun p => (y p).2 else none

/-- The link: no round; it reads both strings whole and compares what they decode to. -/
@[reducible] def pL : InteractiveOracleProof Unit (twoExternalStrings 4 Sg) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => Finset.univ,
    reads := fun _ _ _ => ∅, accept := fun _ y _ => decide (decX y.1 = none ∨ decX y.2 = decX y.1) }
@[reducible] def pB : InteractiveOracleProof Unit (oneExternalString 4 Sg) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }

/-- The interface: its Test is the toy. -/
@[reducible] def Lx : BatchProtocol Ix Unit where
  wordLength := 4
  Symbol := Sg
  EncodingRandomness := Unit
  encodeIndex := fun i _ => encX i
  decodeIndex := decX
  offline := QX
  link := pL
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto pB
  honestOfflineProver := { Coin := Unit, ext := fun w => encX w.1,
                           strat := fun _ _ _ => (((), ()), fun _ => (((), ()), fun _ => ())),
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun w => (encX w.1, encX w.1), strat := fun _ _ _ => (),
                        Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun w => encX w.1, strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

def w1X : WireRB 256 1 r1X (RAnn.allLocal r1X) where
  pt :=
    ⟨inferInstance, inferInstance, fun _ => (), fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩
  depth0 := 0
  depthJ := 0
  has0 := false
  hasJ := false
  place := fun p => p.elim
  posAt0 := fun _ => none
  posAtJ := fun _ => none
  chal := fun u => chalPoss 2 2 u

def zS : Sg := (0, (0, 0, 0))

/-- The external tree: depth 2; one walk over a pruned set. -/
def weX : WireE (oneExternalString 4 Sg) := { WireE.one 4 Sg zS with pr := true }
/-- The same, every opening along a whole path of its own. -/
def weF : WireE (oneExternalString 4 Sg) := WireE.one 4 Sg zS

def wqX : ProtocolQueryLayout 256 1 (BatchInteractiveOracleProof.ofProto QX) := ⟨(Run.Toy1.w0, w1X, ()), weX, decOX, 2, 2⟩
def wqXF : ProtocolQueryLayout 256 1 (BatchInteractiveOracleProof.ofProto QX) := ⟨(Run.Toy1.w0, w1X, ()), weF, decOX, 2, 2⟩
def wqL : ProtocolQueryLayout 256 1 (BatchInteractiveOracleProof.ofProto pL) :=
  ⟨(), WireE.two 4 Sg zS, inferInstanceAs (DecidableEq Empty), 8, 2⟩
def wqB : ProtocolQueryLayout 256 1 (BatchInteractiveOracleProof.ofProto pB) :=
  ⟨(), WireE.one 4 Sg zS, inferInstanceAs (DecidableEq Empty), 0, 2⟩

/-- The verifier's wire of the interface. -/
def Wx : QueryLayout 256 Lx := ⟨1, wqX, wqL, wqB, 2, 0⟩
def WxF : QueryLayout 256 Lx := ⟨1, wqXF, wqL, wqB, 2, 0⟩

/-- The constants of the encoding of the queries. -/
structure XD where
  label : Nat
  /-- the parameters' digest -/
  pd    : ByteArray
  /-- the configuration's digest -/
  cfg   : ByteArray
  /-- the stored tree's number -/
  tree  : Nat
  /-- the statement's bytes, from the root -/
  stm   : ByteArray → ByteArray

/-- The chain queries. The first query: the chain value's block alone has a call. -/
def firstX (D : XD) (q : FbIn 256 Lx .test) (j : Fin 2) : Option _root_.Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [cm] none salt =>
      if j.val = 1 then
        some ⟨0, 160, 0, D.label, _root_.Fmt.zero32, firstBytes D.pd (D.stm (digToBytes cm)) salt⟩
      else none
  | i + 1, .f2 none ρ =>
      let b := blockNo 0 1 j
      some ⟨UInt8.ofNat (b % 2), 162, D.label, i + 1, bitsToBytes ρ,
        roundBytes ByteArray.empty 4 0 (b / 2) 0⟩
  | _, _ => none

/-- A leaf of the stored tree. -/
def leafX (D : XD) (q : LeafIn Lx) : Option _root_.Fmt.OQ :=
  match q.body with
  | some (.inl s) =>
      if bitsToBytes (q.salt.take 256) == D.cfg then
        some ⟨0, 174,
          _root_.Fmt.leafPlace D.tree 3 ((q.salt.length - 256) / 64),
          2 ^ 2 + s.1.val, D.cfg,
          _root_.Fmt.leafBytes [s.2.1, s.2.2.1, s.2.2.2] (bitsToBytes (q.salt.drop 256))⟩
      else none
  | _ => none

/-- The typed oracle functions that a function on the format's strings induces. -/
def famX (O : ByteArray → ByteArray) (D : XD) : Fam (spec 256 1 Lx)
  | .leaf, q => ansOf O (leafX D q)
  | .node, q => ansOf O (nodeCallC D.cfg q)
  | .fb .test, q => (fun k => ansOf O (firstX D q k.castSucc), ansOf O (firstX D q (Fin.last 1)))
  | .fb .link, _ => (fun _ _ => false, fun _ => false)
  | .fb .onl, _ => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- The function that the scheme's verifier runs on a key's test string, at the toy. -/
def VX (cm : Dig 256) (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto Lx.offline)) : TypedOracleComputation 256 1 Lx Bool :=
  vTS Wx 576 256 cm π
/-- The same at the wire without the flag for pruned sets. -/
def VXF (cm : Dig 256) (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto Lx.offline)) : TypedOracleComputation 256 1 Lx Bool :=
  vTS WxF 576 256 cm π

end Run.ToyX
