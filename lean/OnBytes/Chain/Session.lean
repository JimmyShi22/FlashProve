-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Session.lean: several chains, in one or more files, read for one verdict.

The format page (R7.14) asks a verifier to keep one record of the tree vertices that it has met.
The record is keyed by a root's 32 bytes. It spans all chains of a file and all files that one
verdict reads. If a vertex under one root is shown with two values, the verifier refuses.
A session is the state that carries this record from one chain to the next.

How to use it. Write the reading of a verdict's files as one `InSession` value with `do`.
Call `readIn` once for each chain, in the order in which the verifier reads them.
Each call returns what was read, so that a later chain's description can take roots from it.
Run the whole with `InSession.run`, which starts from the empty record.
`readIn` takes no decision: the caller decides on the views afterwards. `acceptIn` reads and decides
in one step; only a test calls it.

Counterpart: VerifierSession in blocks/chain/session.h. That class also keeps how each chain has
fared. Here a refusal ends the whole reading (`Option`), so nothing of that kind is kept.
Not tested here; each point is the matter of whoever writes the reading:
 - that a file ends where its last chain ends (R8.9; finish() in blocks/chain/rounds.h): compare
   `ChainRead.next` with the file's size, by `InSession.require`;
 - that a verdict reads at least one chain: `InSession.run` of a reading without a chain returns
   its value, where VerifierSession::accepted() ends the process;
 - that a later chain's description takes roots, starts and seals from chains of this session
   (`ChainRead.tree`, `ChainRead.seal`), and that all chains have one configuration digest.
The format page is docs/format/FORMAT.md. A number such as R7.14 is a rule of that page.

Main definitions: `Session`, `ChainRead`, `ChainRead.light`, `InSession`, `readIn`, `acceptIn`,
`InSession.run`.
-/
import OnBytes.Chain.Reader

namespace OnBytes

/-- What one verdict carries from chain to chain. -/
structure Session where
  /-- the tree vertices met so far, under each root's 32 bytes -/
  seen : Fmt.Seen

/-- The state at the start of a verdict: no vertex has been met. -/
def Session.start : Session := ⟨[]⟩

/-- One chain as it was read. -/
structure ChainRead where
  /-- all that the strict reader returns -/
  out  : Fmt.ChainOut
  /-- the part of it that a decision sees -/
  view : Fmt.View
  /-- the place of the first byte after the chain -/
  next : Nat

/-- The roots that the prover sent on the chain, in the order of sending. -/
def ChainRead.roots (r : ChainRead) : List ByteArray :=
  r.out.rounds.toList.flatMap fun x => rootsT x.vals

/-- The chain's seal: the digest that its last round drew, or nothing if that round is not of the
kind `.sealed`. A later chain that follows this one holds the seal in an item of its statement
(Binder::follows in blocks/chain/public.h). That it does so is not tested in this file. -/
def ChainRead.seal (r : ChainRead) : Option ByteArray :=
  r.out.rounds.back?.bind fun x => x.drawn.digest

/-- How a later chain of the session names the n-th tree (from 0) that this chain has sent: by
its root and by the value from which its leaves' hashes start, which is the run's value of this
chain (format page, R4.5). Nothing if the chain has sent no such tree or has no random bytes.
The C++ counterpart, SentRoot in blocks/chain/rounds.h, also holds the sending chain's
configuration digest, and only a verifier's channel can make one. Here the later chain hashes the
tree's vertices from its own configuration digest, and any root and start of 32 bytes each can be
written into a description (`Fmt.Src.given`). -/
def ChainRead.tree (r : ChainRead) (n : Nat) : Option Fmt.Src :=
  match r.roots[n]?, r.out.run with
  | some root, some start => some (.given root start)
  | _, _ => none

/-- A round as it was read, with its large parts emptied: the message's bytes, the drawn elements,
positions and matrix entries, the list of positions, and the openings. What stays: the values read
from the message, among them the roots, the nonce, and the digest that a sealing round draws. -/
def lightRound (x : Fmt.RoundOut) : Fmt.RoundOut :=
  { x with
    msg := ByteArray.empty
    drawn := { x.drawn with elems := [], poss := [], trits := [] }
    list := []
    opens := [] }

/-- A chain as it was read, with its large parts emptied: each round as `lightRound` leaves it, the
record of vertices, and the view. The roots, the seal, the names of the trees and the place after
the chain are those of r (`light_roots`, `light_seal`, `light_tree`, `light_next`).
`r.out` and `r.view` share the drawn matrix entries and the opened columns. A caller that keeps
`r.light` in the place of r while a decision runs through `r.view` holds no second reference to
them, so a round's memory can be given back when the decision has left the round. -/
def ChainRead.light (r : ChainRead) : ChainRead :=
  ⟨{ r.out with seen := [], rounds := r.out.rounds.map lightRound }, ⟨[], []⟩, r.next⟩

/-- The light form has the same roots. -/
theorem ChainRead.light_roots (r : ChainRead) : r.light.roots = r.roots := by
  unfold ChainRead.roots ChainRead.light
  simp only [Array.toList_map, List.flatMap_map]
  rfl

/-- The light form has the same seal. -/
theorem ChainRead.light_seal (r : ChainRead) : r.light.seal = r.seal := by
  unfold ChainRead.seal ChainRead.light
  simp only [Array.back?_map]
  cases r.out.rounds.back? with
  | none => rfl
  | some x => rfl

/-- The light form names the trees alike. -/
theorem ChainRead.light_tree (r : ChainRead) (n : Nat) : r.light.tree n = r.tree n := by
  unfold ChainRead.tree
  rw [ChainRead.light_roots]
  rfl

/-- The light form ends at the same place. -/
theorem ChainRead.light_next (r : ChainRead) : r.light.next = r.next := rfl

/-- A reading within a session: it may change the record of vertices, and it may refuse. -/
abbrev InSession : Type → Type := StateT Session Option

/-- Refuses unless c is true. -/
def InSession.require (c : Bool) : InSession Unit := fun s => if c then some ((), s) else none

/-- Refuses if x is nothing; otherwise returns its value. -/
def InSession.get {α : Type} (x : Option α) : InSession α := fun s => x.map fun a => (a, s)

/-- Runs a reading from the empty record. Returns its value, or nothing if it refused. -/
def InSession.run {α : Type} (w : InSession α) : Option α := (w Session.start).map (·.1)

/-- Reads the chain with the description S that begins at byte i of b. No decision is taken. -/
def readIn (S : Fmt.SpecX) (b : ByteArray) (i : Nat) : InSession ChainRead := fun s =>
  match readChain S s.seen b i with
  | none => none
  | some (o, j) => some (⟨o, viewOf S o, j⟩, ⟨o.seen⟩)

/-- Reads the chain c that begins at byte i of b and decides on it for the statement y.
Refuses if the strict reader refuses or if the decision is no. -/
def acceptIn {Y : Type} (c : Chain Y) (y : Y) (b : ByteArray) (i : Nat) : InSession ChainRead :=
  fun s =>
    match readChain c.spec s.seen b i with
    | none => none
    | some (o, j) =>
      if c.dec y (viewOf c.spec o) then some (⟨o, viewOf c.spec o, j⟩, ⟨o.seen⟩) else none

end OnBytes
