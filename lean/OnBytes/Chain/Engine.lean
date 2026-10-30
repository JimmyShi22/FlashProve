-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Engine.lean: the strict reader's text without a monad. The keeper of the record of
vertices (`Keeper`, OnBytes/Chain/Keeper.lean), the step of a chain and the hash are arguments;
`readChain` (OnBytes/Chain/Reader.lean) is this text at `Keeper.indexed`, `queryH` and `formatHashFastForm`.
Who calls it. `program` (OnBytes/Shell/Checks.lean) reads chains by `readChain`. So does `main`
(OnBytes/Main.lean) in the calls on the files of the test protocols (OnBytes/Shell/Toys.lean). In
the calls verify, verify -key and verify -leaf on a model's files `main` runs a second text of the
definitions that hash, written over a monad (OnBytes/ChecksWithHashAsArgument/M/Chain/EngineM.lean), at the identity
monad and `formatHashFastForm`; what does not hash (`rootAndStart`, `StK`, `viewF`) it takes from this file. The
call plan reads no chain.
How the two texts are tied. For every keeper K and every hash h, `readChainM K h` at the identity
monad returns what `readChainK K (stepOf h) h` returns (`readChainM_id`,
OnBytes/ChecksWithHashAsArgument/M/Chain/EngineAtId.lean). `stepOf h` is the step of a chain that h induces
(OnBytes/ChecksWithHashAsArgument/M/Chain/StepAny.lean), and `stepOf formatHashFastForm = queryH` (`step_port`,
OnBytes/ChecksWithHashAsArgument/M/AtPort/Chain.lean). These are equations between terms: they say nothing of
compiled code.

The strict reader is `Fmt.readChainX`: it reads one chain's bytes and refuses what breaks a rule of
the format (OnBytes/Base.lean).
The text is that of OnBytes/Chain/Step.lean with these changes. The walk from the opened leaves to
a root goes by loops (OnBytes/Chain/Climb.lean). Lists as long as the chain has
rounds are paired and summed by loops (OnBytes/Chain/Lists.lean). Long runs of values are read by
loops (OnBytes/Chain/Loops.lean). A round's draws and the list of its positions are made by the
functions of OnBytes/Chain/Draws.lean. The openings of a round are read by loops.
The record of vertices is kept by a `Keeper` (OnBytes/Chain/Keeper.lean), which is an argument.
The view is made without deep recursion.
OnBytes/Chain/EngineLaws.lean proves that the result is the same.
C++ counterparts: VerifierRounds in blocks/chain/rounds.h; receive_opening in
blocks/tree/opening.h.
The format page is docs/format/FORMAT.md. A number such as R7.14 is a rule of that page.

Main definitions: `openingF`, `storedK`, `opensK`, `roundK`, `foldRoundsK`, `readChainK`, `viewF`.
-/
import OnBytes.Chain.Step
import OnBytes.Chain.Loops
import OnBytes.Chain.Draws
import OnBytes.Chain.Lists
import OnBytes.Chain.Keeper

namespace OnBytes

open Fmt (Qry Hash Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld View)

/-- One opening at the list xs, from byte i of b on: read, hashed and walked up to its root
(format page, R7.8 to R7.10). `start` is the value from which the leaves' hashes start, cfg the
value from which the vertices' hashes start. Returns none if xs is empty, not increasing or not
below 2 ^ sh.a, if the salt's length is not one of the format's, if bytes are missing, or if an
element is not in canonical form. As many given digests are read as the walk takes.
The comparison with the tree's root is the caller's. Not tested: that two opened columns agree
where they hold copies of one symbol (blocks/tree/opening.h: a mask row's symbol is copied into
several leaves). Counterparts in blocks/tree/opening.h: read_opening, and check_opening without
its comparisons with the root and the record. -/
def openingF (h : Hash) (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) : Option OpenOut :=
  if Fmt.listOK sh.a xs && Fmt.saltLenOK salt then
    match rdOpeningT f salt sh xs b i with
    | none => none
    | some ((cs, given), next) =>
      Option.map (fun r => ⟨cs.map (·.1), cs.map (·.2), given, r.1, r.2.2 ++ r.2.1.2, next⟩)
        (walkT (fun _ _ l r => Fmt.vertexW (m := Id) h cfg l r) Fmt.takeGiven sh.a
          (leavesT h sh start xs cs) (given, []) [])
  else none

/-- The loop of `storedK`. acc: what was read of the trees before. -/
def storedLoop {R : Type} (K : Keeper R) (h : Hash) (cfg statement : ByteArray) (P : Plan)
    (poss : List Nat) (b : ByteArray) :
    List Stored → R → Nat → Array (Shape × List Nat × OpenOut) →
      Option (List (Shape × List Nat × OpenOut) × R × Nat)
  | [], sn, i, acc => some (acc.toList, sn, i)
  | t :: ts, sn, i, acc =>
    match openingF h cfg P.field t.salt t.sh cfg
        (listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
    | none => none
    | some o =>
      if some o.root == Fmt.itemRoot statement t.item then
        match K.add o.root (Fmt.entered o.seen) sn with
        | none => none
        | some sn' =>
          storedLoop K h cfg statement P poss b ts sn' o.next
            (acc.push (t.sh, listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a)), o))
      else none

/-- The openings of a round's stored trees, each at the list of its part of the draws (format
page, R7.19), taken modulo 2 ^ t.sh.a, the number of its leaves. A stored tree outlives every run
(a committed table). Its root is the one in its item of the statement and no other (R4.6). Its
leaves' hashes start from cfg, the configuration's digest (R7.4). An opening's vertices, without
the root, are entered in the record only after its walk has ended in that root (R7.14). Returns
shape, list and opening for each tree, the record, and the place after the last opening. -/
def storedK {R : Type} (K : Keeper R) (h : Hash) (cfg statement : ByteArray) (P : Plan)
    (poss : List Nat) (b : ByteArray) (ts : List Stored) (sn : R) (i : Nat) :
    Option (List (Shape × List Nat × OpenOut) × R × Nat) :=
  storedLoop K h cfg statement P poss b ts sn i #[]

/-- The root of a tree that is opened and the value from which its leaves' hashes start. `roots`
are the roots sent on the chain so far. `run` is the run's value of the chain (format page, R4.5):
the hash of its parameters' digest and its random bytes (`Fmt.runValueW`), none for a chain
without random bytes. A tree of the chain's own (`.own n`) has member n of `roots`, counted from
0, and starts from `run`; none if either is lacking. For a tree given from outside (`.given`)
root and start are taken as the description has them: from which chain they come is not asked
here. -/
def rootAndStart (roots : Array ByteArray) (run : Option ByteArray) :
    Src → Option (ByteArray × ByteArray)
  | .own n =>
    match roots[n]?, run with
    | some r, some s => some (r, s)
    | _, _ => none
  | .given r s => some (r, s)

/-- The loop of `opensK`. acc: what was read of the trees before. -/
def opensLoop {R : Type} (K : Keeper R) (h : Hash) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    List (Shape × Src) → R → Nat → Array (Shape × List Nat × OpenOut) →
      Option (List (Shape × List Nat × OpenOut) × R × Nat)
  | [], sn, i, acc => some (acc.toList, sn, i)
  | (sh, src) :: os, sn, i, acc =>
    match rootAndStart roots run src with
    | none => none
    | some (root, start) =>
      match openingF h cfg P.field P.salt sh start (listOfT (poss.map (· % 2 ^ sh.a))) b i with
      | none => none
      | some o =>
        if o.root == root then
          match K.add root (Fmt.entered o.seen) sn with
          | none => none
          | some sn' =>
            opensLoop K h cfg P run roots poss b os sn' o.next
              (acc.push (sh, listOfT (poss.map (· % 2 ^ sh.a)), o))
        else none

/-- The openings of a round's trees that are not stored trees: the chain's own and those given
from outside (`rootAndStart`). Each is opened at the list of the round's draws modulo 2 ^ sh.a,
the number of its leaves. An opening's vertices, without the root, are entered in the record only
after its walk has ended in the tree's root (format page, R7.14). All vertices are hashed from
cfg, the reading chain's configuration digest, also in a tree that another chain has sent. -/
def opensK {R : Type} (K : Keeper R) (h : Hash) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray)
    (os : List (Shape × Src)) (sn : R) (i : Nat) :
    Option (List (Shape × List Nat × OpenOut) × R × Nat) :=
  opensLoop K h cfg P run roots poss b os sn i #[]

/-- The reader's state between two rounds. -/
structure StK (R : Type) where
  /-- the place in the file -/
  pos   : Nat
  /-- the chain between rounds -/
  chain : Fmt.Chain
  /-- the roots sent so far -/
  roots : Array ByteArray
  /-- the record of vertices -/
  kept  : R
  /-- what was read -/
  out   : Array RoundOut

/-- The state as Fmt/ has it. -/
def StK.toSt {R : Type} (K : Keeper R) (s : StK R) : Fmt.St :=
  ⟨s.pos, s.chain, s.roots, K.toSeen s.kept, s.out⟩

/-- One round, as `roundQ` (OnBytes/Chain/Step.lean) reads it: the message, the nonce, the round's
query with the test of work, the draws, the listed positions, the openings. K keeps the record of
vertices. Returns none if the round is refused. -/
def roundK {R : Type} (K : Keeper R) (qry : Qry) (h : Hash) (cfg statement : ByteArray)
    (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : StK R) (r : Round)
    (ts : List Stored) : Option (StK R) :=
  match Fmt.slice b s.pos r.entry.msg with
  | none => none
  | some msg =>
    match Fmt.whole (readItemsT P.field r.items) msg with
    | none => none
    | some vals =>
      match Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => none
      | some (nonce, i1) =>
        match qry s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => none
        | some (c, vb) =>
          let drawn := drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)
          let l := listOfT drawn.poss
          match readListT P r.entry.poss l b i1 with
          | none => none
          | some (_, i2) =>
            let roots := s.roots ++ (rootsT vals).toArray
            match storedK K h cfg statement P drawn.poss b ts s.kept i2 with
            | none => none
            | some (colsS, sn1, i2') =>
              match opensK K h cfg P run roots drawn.poss b r.opens sn1 i2' with
              | none => none
              | some (cols, sn, i3) =>
                some ⟨i3, c, roots, sn, s.out.push ⟨msg, vals, nonce, drawn, l, colsS ++ cols⟩⟩

/-- All rounds, one after the other, each with the stored trees that it opens. Returns none as
soon as a round is refused. -/
def foldRoundsK {R : Type} (K : Keeper R) (qry : Qry) (h : Hash) (cfg statement : ByteArray)
    (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    List (Round × List Stored) → StK R → Option (StK R)
  | [], s => some s
  | r :: rs, s =>
    match roundK K qry h cfg statement P run b s r.1 r.2 with
    | none => none
    | some s' => foldRoundsK K qry h cfg statement P run b rs s'

/-- What follows the chain's random bytes x: the chain's first value is computed, then the rounds
are read from byte i0 on. Returns what was read and the place after the chain. -/
def restK {R : Type} (K : Keeper R) (qry : Qry) (h : Hash) (S : SpecX) (seen : Seen)
    (b : ByteArray) (x : Option ByteArray) (i0 : Nat) : Option (ChainOut × Nat) :=
  match Fmt.startChainW (m := Id) h S.base.label (Fmt.paramsDigestW (m := Id) h S.base.params)
      S.base.statement x with
  | none => none
  | some hd =>
    match foldRoundsK K qry h S.base.cfg S.base.statement S.base.plan hd.run b
        (zipT S.base.rounds S.stored)
        ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], K.ofSeen seen, #[]⟩ with
    | none => none
    | some s =>
      some (⟨Fmt.paramsDigestW (m := Id) h S.base.params, hd.run, hd.rho0, s.chain.rho,
        K.toSeen s.kept, s.out⟩, s.pos)

/-- Reads the chain with the description S that begins at byte i of b. `seen` is the record of
vertices met so far. Returns what was read and the place after the chain. Returns none if the
description is not in order (`specXOk`), whatever the bytes, or if the bytes break a rule of the
format. -/
def readChainK {R : Type} (K : Keeper R) (qry : Qry) (h : Hash) (S : SpecX) (seen : Seen)
    (b : ByteArray) (i : Nat) : Option (ChainOut × Nat) :=
  if !specXOk S then none
  else
    match S.base.rand with
    | .inFile =>
      match Fmt.slice b i 32 with
      | none => none
      | some x => restK K qry h S seen b (some x) (i + 32)
    | .given x => restK K qry h S seen b (some x) i
    | .none => restK K qry h S seen b none i

/-- The opened columns of one round's trees that are not stored trees: `Fmt.openedOf`, with each
opening's positions and columns paired by `zipT`. -/
def openedOfT (first : Nat) (r : RoundOut) : List (Nat × Nat × List UInt64) :=
  r.opens.flatMap fun x => (zipT x.2.1 x.2.2.cols).map fun p => (x.1.tree - first, p.1, p.2)

/-- The opened columns of one round, the stored trees' first: `Fmt.openedX`, with each opening's
positions and columns paired by `zipT`. -/
def openedXT (first : Nat) (ts : List Stored) (r : RoundOut) : List (Nat × Nat × List UInt64) :=
  ((zipT ts r.opens).flatMap fun y =>
    (zipT y.2.2.1 y.2.2.2.cols).map fun p => (Fmt.storedKey y.1.item, p.1, p.2)) ++
  openedOfT first { r with opens := r.opens.drop ts.length }

/-- The view of a chain that was read: `Fmt.viewX`, with the roots taken out of each message by a
filter and all pairing done by `zipT`. -/
def viewF (S : SpecX) (o : ChainOut) : View where
  rounds := o.rounds.toList.map fun r => ⟨r.vals.filter notRoot, r.drawn⟩
  opened := (zipT S.stored o.rounds.toList).flatMap fun y => openedXT S.base.firstTree y.1 y.2

end OnBytes
