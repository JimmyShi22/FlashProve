-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Why.lean: at which kind of check the strict reader refuses a chain.

The strict reader answers with what it read or with nothing. A person who looks at a refused file
wants to know more. This file goes through the reader's steps once more and names the first one
that fails, with one exception: it compares an opening with the record of vertices before it
compares it with the root (`tryOpening`), and the reader does so in the opposite order. It is meant
to be called after a refusal, for a printed line.
No verdict depends on it.

Main definitions: `ReaderCheck`, `ReaderCheck.name`, `whyRefused`.
Not claimed: that `whyRefused` returns nothing exactly if the reader accepts, or that the name is
that of the reader's first failing step. It follows the reader's steps, with the reader's own
functions, but no theorem says so.
-/
import OnBytes.Chain.Engine
import OnBytes.Chain.Index
import OnBytes.Hash.H
import OnBytes.Hash.Query

namespace OnBytes

open Fmt (Qry Hash Plan St Round Stored SpecX Seen Shape Src Fld)

/-- The kinds of check that the strict reader makes. -/
inductive ReaderCheck where
  /-- the description is not in order: no fault of the file -/
  | description
  /-- bytes are missing (other than bytes of listed positions), an element is not in canonical
  form, or a run's value is zero. Also named where the chain's label is not below 2 ^ 32, a fault
  of the description that `specXOk` does not test -/
  | form
  /-- the round's query is refused in a round that has work. In a description that is in order this
  is meant to happen only if the nonce does not pass the round's test of work; no theorem says so -/
  | work
  /-- the listed positions are not those that the verifier derives, or bytes of them are missing -/
  | listed
  /-- an opening does not lead to its tree's root -/
  | opening
  /-- a vertex under one root is shown with a second value -/
  | vertex
  deriving DecidableEq, Repr, Inhabited

/-- The name of a kind of check, for a printed line. -/
def ReaderCheck.name : ReaderCheck → String
  | .description => "description"
  | .form => "form"
  | .work => "work"
  | .listed => "listed-positions"
  | .opening => "opening"
  | .vertex => "one-value-at-a-vertex"

/-- All names that `ReaderCheck.name` can give. -/
def ReaderCheck.names : List String :=
  [ReaderCheck.description, .form, .work, .listed, .opening, .vertex].map ReaderCheck.name

/-- One opening at the list xs, from byte i of b on, compared with the record of vertices and then
with the root. Returns the new record and the place after the opening, or the check that fails.
If the opening fails both comparisons, `vertex` is named, as receive_opening in
blocks/tree/opening.h names it. The reader (`opensK`, `storedK`) compares with the root first and
enters nothing from an opening that does not lead to the root. -/
def tryOpening (h : Hash) (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape)
    (start root : ByteArray) (xs : List Nat) (b : ByteArray) (i : Nat) (sn : List Rooted) :
    Except ReaderCheck (List Rooted × Nat) :=
  match openingF h cfg f salt sh start xs b i with
  | none => .error .form
  | some o =>
    match Keeper.indexed.add root (Fmt.entered o.seen) sn with
    | none => .error .vertex
    | some sn' => if o.root == root then .ok (sn', o.next) else .error .opening

/-- The openings of a round's stored trees, as `Fmt.readStored` reads them. -/
def tryStored (h : Hash) (cfg statement : ByteArray) (P : Plan) (poss : List Nat)
    (b : ByteArray) : List Stored → List Rooted → Nat → Except ReaderCheck (List Rooted × Nat)
  | [], sn, i => .ok (sn, i)
  | t :: ts, sn, i =>
    match Fmt.itemRoot statement t.item with
    | none => .error .description
    | some root =>
      match tryOpening h cfg P.field t.salt t.sh cfg root
          (listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i sn with
      | .error e => .error e
      | .ok (sn', j) => tryStored h cfg statement P poss b ts sn' j

/-- The openings of the other trees of a round, as `Fmt.readOpens` reads them. -/
def tryOpens (h : Hash) (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    List (Shape × Src) → List Rooted → Nat → Except ReaderCheck (List Rooted × Nat)
  | [], sn, i => .ok (sn, i)
  | (sh, src) :: os, sn, i =>
    let rs : Option (ByteArray × ByteArray) :=
      match src with
      | .own n =>
        match roots[n]?, run with
        | some r, some s => some (r, s)
        | _, _ => none
      | .given r s => some (r, s)
    match rs with
    | none => .error .description
    | some (root, start) =>
      match tryOpening h cfg P.field P.salt sh start root
          (listOfT (poss.map (· % 2 ^ sh.a))) b i sn with
      | .error e => .error e
      | .ok (sn', j) => tryOpens h cfg P run roots poss b os sn' j

/-- One round: the first check that fails, or the state after the round if none fails. The
arguments are those of `roundK` (OnBytes/Chain/Engine.lean) with the record of
OnBytes/Chain/Index.lean, and the steps are `roundK`'s. What the round has read is not kept: no name
needs it. -/
def whyRound (qry : Qry) (h : Hash) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) (s : StK (List Rooted)) (r : Round)
    (ts : List Stored) : Except ReaderCheck (StK (List Rooted)) :=
  match Fmt.slice b s.pos r.entry.msg with
  | none => .error .form
  | some msg =>
    match Fmt.whole (readItemsT P.field r.items) msg with
    | none => .error .form
    | some vals =>
      match Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => .error .form
      | some (nonce, i1) =>
        match qry s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => .error (if r.entry.work == 0 then .description else .work)
        | some (c, vb) =>
          let drawn := drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)
          match readListT P r.entry.poss (listOfT drawn.poss) b i1 with
          | none => .error .listed
          | some (_, i2) =>
            match tryStored h cfg statement P drawn.poss b ts s.kept i2 with
            | .error e => .error e
            | .ok (sn1, i2') =>
              let roots := s.roots ++ (rootsT vals).toArray
              match tryOpens h cfg P run roots drawn.poss b r.opens sn1 i2' with
              | .error e => .error e
              | .ok (sn, i3) => .ok ⟨i3, c, roots, sn, #[]⟩

/-- Goes through the rounds with `whyRound`, each round once. k counts the rounds in which no check
failed. Returns the first check that fails, with the number of rounds before it, or nothing if none
fails. -/
def whyRounds (qry : Qry) (h : Hash) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) :
    List (Round × List Stored) → StK (List Rooted) → Nat → Option (ReaderCheck × Nat)
  | [], _, _ => none
  | r :: rs, s, k =>
    match whyRound qry h cfg statement P run b s r.1 r.2 with
    | .ok s' => whyRounds qry h cfg statement P run b rs s' (k + 1)
    | .error e => some (e, k)

/-- The check that fails in what follows the chain's random bytes x: the chain's first value
(`form`, after 0 rounds), then the rounds from byte i0 on. Returns nothing if none fails. -/
def whyRest (qry : Qry) (h : Hash) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) : Option (ReaderCheck × Nat) :=
  match Fmt.startChainW (m := Id) h S.base.label (Fmt.paramsDigestW (m := Id) h S.base.params)
      S.base.statement x with
  | none => some (.form, 0)
  | some hd =>
    whyRounds qry h S.base.cfg S.base.statement S.base.plan hd.run b
      (zipT S.base.rounds S.stored)
      ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], Keeper.indexed.ofSeen seen, #[]⟩ 0

/-- The check at which the reader `readChainK` refuses, with the number of rounds that it read
whole before: meant to be the reader's first failing check, except that `vertex` is named before
`opening` (`tryOpening`). No theorem says so. Returns nothing if no check fails. -/
def whyRefusedQ (qry : Qry) (h : Hash) (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    Option (ReaderCheck × Nat) :=
  if !specXOk S then some (.description, 0)
  else
    match S.base.rand with
    | .inFile =>
      match Fmt.slice b i 32 with
      | none => some (.form, 0)
      | some x => whyRest qry h S seen b (some x) (i + 32)
    | .given x => whyRest qry h S seen b (some x) i
    | .none => whyRest qry h S seen b none i

/-- `whyRefusedQ` at `queryH` and `formatHashFastForm`, the step and the hash of `readChain`
(OnBytes/Chain/Reader.lean). `program` (OnBytes/Shell/Checks.lean) calls it through `readerName`
(OnBytes/Proof/Reading.lean). So does `main` (OnBytes/Main.lean) in the calls key, entry and
toy-proof on the files of the test protocols (OnBytes/Shell/Toys.lean). In the calls verify,
verify -key and verify -leaf on a model's files `main` runs a second text of this file's functions
that hash, written over a monad (OnBytes/ChecksWithHashAsArgument/M/Chain/Why.lean), at the identity monad and
`formatHashFastForm`. There that text's
`whyRefused` returns what this function returns, for all arguments (`whyRefused_port`,
OnBytes/ChecksWithHashAsArgument/M/AtPort/Chain.lean): an equation between terms, which says nothing of compiled
code. -/
def whyRefused (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) : Option (ReaderCheck × Nat) :=
  whyRefusedQ queryH formatHashFastForm S seen b i

end OnBytes
