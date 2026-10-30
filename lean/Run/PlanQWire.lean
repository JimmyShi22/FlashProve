-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQWire.lean: from a chain's description in the programs' format to the wiring that the
compiled verifier takes.

Definitions that compute; nothing is proved.
The compiled verifier (`Compile.Batch.verifyOneProtocol`, Compile/Batch/Verifier.lean) is the verifier of
the non-interactive argument that the library's compiler makes of one interactive oracle protocol,
with Merkle trees and a chain of Fiat-Shamir queries. Beside the protocol it takes a wiring
(`ProtocolQueryLayout`, Iop/BatchWire.lean). A wiring has a wire for each round (`WireRB`), the wire of the
external oracles (`WireE`, Iop/Wire.lean) and two numbers, `nOpen` and `maxDepth`. The laws of a
wire are the conditions `WireRB.OK`, `WireRB.OKG`, `ProtocolQueryLayout.OK` and `ProtocolQueryLayout.OKG` of
Iop/BatchWire.lean.
The library's wires are for batch protocols, in which a round's prover message is the pair of a
shared component and a slot's own, each with a tree of its own. Here every round has the annotation
`RAnn.allLocal` (Iop/Batch.lean): a local round without a shared prover message.

A description of a chain (a proof's sequence of rounds) is a value of `Fmt.Spec` (Fmt/Rules8.lean);
its rounds' data are the list `rds S` of records `RD`.
Run/PlanQTypes.lean makes, from the rounds' data of a description, the shape, the proof-of-work bits
and the protocol (with any decision on an untyped view). Run/ToyQ.lean writes out the wires of one
toy, a small example protocol, term by term. Here they are a function of the rounds' data ds.
All rounds of ds are uniform: one definition `wireOf`, with no case split on a round's kind; whether
the round sends a root is read off `d.tree`.

Main names:
  `wireOf C K chal d`: the wire of one round: the tree of a slot has the depth of the round's tree,
    and is there exactly if the round sends a root; a position is at the leaf of its own number; the
    opened leaves are checked together, in one walk over a pruned set of paths (the format's
    openings); no shared component.
  `chal`: the sampler is a parameter. C is a choice of challenge types (`CK`, Run/PlanQTypes.lean):
    for each entry and kind a finite type of verifier messages. For each entry and kind `chal` gives
    a function from K blocks of 256 bits to the verifier's message of C. Entry and kind are
    `Fmt.Entry` and `Fmt.Kind` (Fmt/Plan.lean). Which function (the format's drawing on these
    blocks) is another file's matter. Run/PlanQRun.lean's `chalOf` is such a function.
  `wqT C K chal ds dec`: the wiring with the test: one block more. In a round that has proof-of-work
    bits it is in front and gives the test bits; in a round that has none it is the last block and
    is not read (`chalGrind`, Iop/GrindWire.lean).

Limits: no law of a wire is shown here (places below 2 ^ depth, places and positions inverse to each
other, the sampler's law, `nOpen` and `maxDepth` as bounds); for them see Run/PlanQWireLaws.lean
(`wq0_ok`, `wqT_okg`, each under the hypotheses of its statement; the sampler's law is there a
hypothesis, `ChalUnif`). `Dn.mo` (in a round with b test bits the honest prover tries the nonces for
0, .., `Dn.mo b`) is no matter of a verifier: no function here reads it; `wqT` hands `Dn` on to
`ProtocolQueryLayout.grindLocal` (Iop/GrindWire.lean), which copies that number into the field `more` of a
round's record (`GrW`, Iop/BatchWire.lean).
Terms: lean/GLOSSARY.md.
-/
import Run.PlanQTypes
import Iop.GrindWire
import Iop.Draw

set_option autoImplicit false

namespace Run.PQ
open Iop

/-- The depth of a round's tree; 0 if the round sends no root. -/
def depthOf : Option _root_.Fmt.Shape → Nat
  | none => 0
  | some s => s.a

/-- A round's oracle message is given by its symbols: the record that a wire asks for
(`Round.IsPoint`, Iop/Shape.lean). -/
def ptOf (C : CK) (d : RD) : (roundOf C d).IsPoint :=
  ⟨inferInstanceAs (Fintype (Fin (posN d.tree))), inferInstanceAs (DecidableEq (Fin (posN d.tree))),
    fun f => f, fun _ _ => rfl, fun _ => rfl, fun _ _ => 0⟩

/-- The wire of one round. What its fields say: the head, `wireOf`. -/
def wireOf (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD) :
    WireRB 256 K (roundOf C d) (RAnn.allLocal (roundOf C d)) where
  pt := ptOf C d
  depth0 := 0
  depthJ := depthOf d.tree
  has0 := false
  hasJ := d.tree.isSome
  place := fun (p : Fin (posN d.tree)) => p.val
  posAt0 := fun _ => none
  posAtJ := fun j => if h : j < posN d.tree then some (⟨j, h⟩ : Fin (posN d.tree)) else none
  chal := chal d.entry d.kind
  prJ := true

/-- A block sampler (`BS`, Iop/Draw.lean) with its own number b of blocks, read on K blocks: the
first b of them; blocks that are lacking count as zeros. -/
def cutK {Ch : Type} (s : BS 256 Ch) (K : Nat) (u : Fin K → Dig 256) : Ch :=
  s.φ fun i => if h : i.val < K then u ⟨i.val, h⟩ else fun _ => false

/-- The trivial round's wire. -/
def w0 (K : Nat) : WireRB 256 K r0 (RAnn.allLocal r0) where
  pt := ⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
    fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩
  depth0 := 0
  depthJ := 0
  has0 := false
  hasJ := false
  place := fun p => p.elim
  posAt0 := fun _ => none
  posAtJ := fun _ => none
  chal := fun _ => ()

/-- The wires of all rounds of ds. -/
def wiresL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    (ds : List RD) → RoundsQueryLayout 256 K (shapeL C ds) (RoundSplits.allLocal (shapeL C ds))
  | [] => ()
  | d :: ds => (wireOf C K chal d, wiresL C K chal ds)

def wiresOf (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD) :
    RoundsQueryLayout 256 K (shapeOf C ds) (RoundSplits.allLocal (shapeOf C ds)) :=
  (w0 K, wiresL C K chal ds)

/-- The greatest number of blocks that a round's verifier's message needs (kOf: by entry and
kind). -/
def kMax (kOf : _root_.Fmt.Entry → _root_.Fmt.Kind → Nat) (ds : List RD) : Nat :=
  ds.foldl (fun a d => max a (kOf d.entry d.kind)) 0

/-- At most so many positions are opened: the sum, over the rounds, of a round's number of drawn
positions times the number of trees that are opened at them. That this is a bound is not shown
here: the head, Limits. -/
def nOpen (ds : List RD) : Nat := (ds.map fun d => d.entry.poss * d.opens.length).sum

/-- The greatest depth of a tree. -/
def maxDepth (ds : List RD) : Nat := ds.foldl (fun a d => max a (depthOf d.tree)) 0

/-- The wire of the empty external oracle. -/
def we0 : WireE E0 :=
  ⟨[], fun p => p.elim0, fun p => p.elim0, 0, fun _ p => p.elim0,
    inferInstanceAs (DecidableEq (Fin 0)), false⟩

/-- The wiring of the protocol without proof of work. -/
def wq0 {Y : Type} (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (ds : List RD) (dec : Y → View → Bool) :
    ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (Q0 C ds dec)) :=
  ⟨wiresOf C K chal ds, we0, decO C ds, nOpen ds, maxDepth ds⟩

/-- The honest search's record (`GrData`, Iop/GrindWire.lean): a nonce is its number. -/
def Dn : GrData ℕ := ⟨fun _ => 65535, id, id⟩

/-- The wiring, with the test: that of the protocol with proof of work, `QT`. -/
def wqT {Y : Type} (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (ds : List RD) (dec : Y → View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto (QT C ds dec)) :=
  (wq0 C K chal ds dec).grindLocal Dn (gOf C ds)

end Run.PQ
