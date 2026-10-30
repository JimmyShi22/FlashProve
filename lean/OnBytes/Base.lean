-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Base.lean: the types that every module of this directory shares.

This directory holds a verifier, written in Lean, that reads the files of the C++ programs byte for
byte: the configuration files, a key file, an entry file, a request with its reply, and a proof
file. It is built on the directory Fmt/, which states the rules of the format page
(docs/format/FORMAT.md) as functions on bytes.

How a file is checked. A file holds one or more chains. A chain is a run of messages between prover
and verifier made non-interactive: each message of the verifier is drawn from a hash chain over what
the prover has sent so far. A chain is checked in two steps.
 1. The strict reader reads the chain's bytes. Fmt/ states it as `Fmt.readChainX`. The program runs
    `readChain` (OnBytes/Chain/Reader.lean), which returns the same (`readChain_eq`,
    OnBytes/Chain/ReaderLaws.lean). The reader is told the chain's description (`Fmt.SpecX`). The
    description's label, plan (a few settings, and each round's sizes: bytes sent, values drawn,
    bits of work), parameter bytes and the form of its rounds follow from the public files. Three
    parts do not: they hold values that were read from files or made earlier in the call.
     - The statement: for example the roots of stored tables, the request, and the seals of earlier
       chains. A seal is the digest that the last round of a sealed chain draws.
     - The random bytes of a shared chain: the root of the binding tree, which is computed from the
       first chain's seal and bytes of the file (`Shared.describe`, OnBytes/Params/Chains.lean).
     - The root and the start value of each tree that a chain takes over from an earlier chain
       (`ChainRead.tree`, OnBytes/Chain/Session.lean).
    The reader makes every hash call of the chain, tests the proof of work, draws the verifier's
    messages and checks every opening of a tree against its root. It returns what was read, or
    nothing if a rule is broken.
 2. A decision tests the protocol's equations on what was read. It is a pure function of public
    values and of the view (`Fmt.View`): each round's items without the roots, what the round drew,
    and the opened columns. In `Chain` it has the form `dec : Y → Fmt.View → Bool`. Y is the type
    in which the caller holds the statement. Nothing in `Chain` ties that value to the statement's
    bytes in the description.
No decision reads bytes or calls the hash. In the program only the two smallest test protocols
(OnBytes/Toy/) build a `Chain`. The chains of key, entry and proof files are read with
OnBytes/Chain/Session.lean and decided with `Proof.judge` (OnBytes/Proof/Reading.lean), which
returns the block's value or a name for the refusal.

Main definitions: `F`, `E` (with `E.mk3`, `E.c0`, `E.c1`, `E.c2`, `E.triple`, `E.ofTriple`),
`Chain`, `Chain.read`, `Chain.accepts`.
-/
import Fmt.Rules8X
import Fmt.FieldE

namespace OnBytes

/-- An element of the base field, the integers modulo p = 2^64 - 2^32 + 1: the word of its least
residue. The type admits every word. A word that is not below p counts as its residue
(OnBytes/Field/Word.lean). -/
abbrev F : Type := UInt64

/-- An element of the cubic extension field F[X] / (X^3 - 2): its three coordinates. One object
holds the three words. -/
structure E where
  /-- the coordinate at 1 -/
  c0 : UInt64
  /-- the coordinate at X -/
  c1 : UInt64
  /-- the coordinate at X^2 -/
  c2 : UInt64
  deriving DecidableEq, Repr, Inhabited

namespace E

/-- The element with the coordinates a, b, c. -/
@[inline] def mk3 (a b c : UInt64) : E := ⟨a, b, c⟩

/-- The element as Fmt/ spells it: a triple of words. -/
@[inline] def triple (x : E) : UInt64 × UInt64 × UInt64 := (x.c0, x.c1, x.c2)

/-- The element that a triple of words spells. -/
@[inline] def ofTriple (t : UInt64 × UInt64 × UInt64) : E := mk3 t.1 t.2.1 t.2.2

/-- From an element to its triple and back gives the element. -/
theorem ofTriple_triple (x : E) : ofTriple x.triple = x := rfl

/-- From a triple to its element and back gives the triple. -/
theorem triple_ofTriple (t : UInt64 × UInt64 × UInt64) : (ofTriple t).triple = t := rfl

/-- The first coordinate of `mk3 a b c` is a. -/
theorem c0_mk3 (a b c : UInt64) : (mk3 a b c).c0 = a := rfl

/-- The second coordinate of `mk3 a b c` is b. -/
theorem c1_mk3 (a b c : UInt64) : (mk3 a b c).c1 = b := rfl

/-- The third coordinate of `mk3 a b c` is c. -/
theorem c2_mk3 (a b c : UInt64) : (mk3 a b c).c2 = c := rfl

/-- An element is `mk3` of its three coordinates. -/
theorem mk3_eta (x : E) : mk3 x.c0 x.c1 x.c2 = x := rfl

/-- Two elements with the same coordinates are equal. -/
theorem ext3 {x y : E} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2) : x = y := by
  rw [← mk3_eta x, ← mk3_eta y, h0, h1, h2]

end E

/-- One chain: how to read it, and what to decide on what was read. Y is the statement's type. -/
structure Chain (Y : Type) where
  /-- the chain's description. Its statement, its random bytes where they are given, and the roots
  and start values of trees taken over from earlier chains do not follow from the public files -/
  spec : Fmt.SpecX
  /-- the protocol's tests on what was read -/
  dec  : Y → Fmt.View → Bool

/-- Reads the chain that begins at byte i of b, with the strict reader as Fmt/ states it. `seen` is
the record of tree vertices met so far in this verdict (format page, R7.14). Returns what was read
and the index of the first byte after the chain, or nothing if the strict reader refuses. The
program does not call this function. It calls `readChain` (OnBytes/Chain/Reader.lean), which returns
the same (`readChain_eq`, OnBytes/Chain/ReaderLaws.lean). -/
def Chain.read {Y : Type} (c : Chain Y) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    Option (Fmt.ChainOut × Nat) :=
  Fmt.readChainX (m := Id) Fmt.formatHash c.spec seen b i

/-- Reads the chain that begins at byte i of b and decides on it. Returns the record of vertices
and the index of the first byte after the chain if the chain is accepted, and nothing otherwise.
The program does not call this function. `acceptIn_eq` (OnBytes/Chain/SessionLaws.lean) compares
the accepting step of a session with it. -/
def Chain.accepts {Y : Type} (c : Chain Y) (y : Y) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    Option (Fmt.Seen × Nat) :=
  match c.read seen b i with
  | none => none
  | some (o, j) => if c.dec y (Fmt.viewX c.spec o) then some (o.seen, j) else none

end OnBytes
