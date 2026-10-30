-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Walk.lean: an honest prover that asks the description's own step on
what it has sent, sub-protocol by sub-protocol, and sends fixed substitutes after the first
rejection (`runC`). It is a second function beside `run` (Honest/Frame.lean), built from the same
pieces: `ready`, `Step.tell`, `Step.hear`, `readsOf`, `fillCols`, `Mid.took`. Executable definitions
only; no theorem.

Why. A test of the verifier's can read a value that was sent in the clear and that depends on one of
the run's coins (a fall: Honest/Side.lean). So at some coins the verifier rejects an honest run.
`run` plays on after such a rejection. The prover of this file does not: after a sub-protocol that
rejects, for whatever reason, it calls no part, asks no stop, reads no coin, and sends each later
round's fixed substitute. (`ready` gives every list of parts its coins before the first round, as
for `run`: a fault in that step makes the run return an error, wherever the list's place is.)
Two differences from the programs' prover. That prover runs the verifier on what it has produced
and, where the verifier rejects, withholds the whole response, fails the batch and exits. It also
flags, itself, a column weight that is 0, and gives that request no proof. What it does and what
this prover does are both computed from what the verifier would have been shown.
The lemmas of Honest/Law/Run.lean, Honest/Law/Along.lean, Honest/Law/StratRun.lean
and Honest/Law/Thread.lean are about `run`.

  1  `judge`, `subSaid`, `substituteZeroTable`, `subSending`, `subTold`, `Sending.shownAt`, `door₃`   the one
     definition of the test and of the substitutes, for whoever produces rounds: this prover, the
     strategies, and whoever produces simulated rounds
  2  `Lay`, `ChainProgress`, `ChainProgress.settle`, `ChainProgress.start`, `ChainProgress.say`, `ChainProgress.heard`, `walk`   a chain, round
     by round, with the verifier's state beside it
  3  `RunC`, `runC`, `RunC.called`, `outcomeC`, `sayC`   a file's three chains

The order of events. A sub-protocol's own challenges are heard. Then its columns are filled, from
the tables sent so far. Then `Block.step` is asked, at the verifier's state before the sub-protocol,
on the sub-protocol's own rounds as a view shows them and on these columns. If it accepts, the
columns are laid behind those that the parts are handed (`Seen.opened`). The rejecting
sub-protocol's own messages are real; the substitutes begin at the next sub-protocol. A sub-protocol
without a round is asked as soon as the one before it has been. Between the sub-protocol that draws
a challenge and a later one that rejects on it, sub-protocols are still played.
Two strands. A rejection in the first chain does not reach the shared chain, which has a state of
its own; it reaches the second chain, through that chain's start (`door₃`). So does one in the
shared chain. The columns go the same way: the shared chain is handed its own alone, the second
chain both earlier chains' and its own.
What is still read. Reads are computed from the declared rounds and the challenges. So after a
rejection a real table that was sent before it is still read at the positions that later rounds
draw, and so is the stored table; a substitute's table is read like any other.
Stops. They are as in `run`. A stop that a called part meets makes the run return an error, as in
`run`. A part after the verifier's rejection is not asked its stops. `silentAt` (Honest/Rule.lean)
reads them all the same, and has no coin among its arguments: `outcomeC` returns `none` wherever
`silentAt` returns a stop.

Limits.
  * Not asked here: the last test (`FileDescription.fin`), after which nothing is sent; the tests on the
    plan and on the instance, which read no message; and that every word of every item and column is
    below the prime. What a prover's side says is converted to words by the field's own functions,
    and the challenges are the caller's (`Draws.due`).
  * There is no stored run to fall back on: where no prover's side is defined nothing is sent, and
    the verifier's step returns what it returns; if such a place declares a table that is read, the
    run returns an error before the step is asked (`ChainProgress.settle`). So a description with places
    without a list of parts is played differently here than under `run` with a stored run.
  * `run` hands no columns (`Seen.opened = none`). A part that reads them has to return an error
    there (its duty: Honest/Frame.lean, `Seen.opened`), so at a prover with a part that reads them
    and keeps that duty `run` returns an error wherever that part's round is reached, and the lemmas
    about `run` say nothing there.
  * That this walk's verdict is that of `foldBlocks` on the views is not proved in this file;
    Honest/Law/RunC.lean proves it where `runC` returns (`runC_ends`).
  * That one step's rejection depends on the state, the sub-protocol's rounds as shown and its
    columns alone holds by the type of `Block.step`. That the state is computed by `judge` alone,
    from the description's own start, holds by inspection of this file's definitions; it is not
    proved.
  * That every tree which a sub-protocol opens has been sent by then is a matter of the plan: a
    sub-protocol that opens a later tree makes the run return an error.
  * Whoever produces simulated rounds is meant to call section 1's functions. No such definition is
    in this file; `session` (Honest/Law/Rule/Session.lean) is built on `judge`, `subSending` and
    `door₃`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Rule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)
open OnBytes.Slice (toF toE)

variable {S Cl Xi W₀ Rc Ky Tr X₀ X W Y : Type}

/-! ## 1 The test and the substitutes -/

/-- **The verifier's step at a sub-protocol, on what has been sent**: the description's own
`Block.step`; `none` means that it rejects. `rs`: the sub-protocol's own rounds as a view shows
them. `cols`: exactly the columns that these rounds read, in the order of `readsOf`. -/
def judge (firstTree : Nat) (b : Block S Cl) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    Option S :=
  (b.step firstTree s rs cols).toOption.map (·.1)

/-- The fixed substitute of a declared item: 0. A root has none; its table has one (`substituteZeroTable`). -/
def subSaid : Fmt.Item → List Said
  | .f => [.f (toF 0)]
  | .e => [.e (toE (0, 0, 0))]
  | .word => [.word 0]
  | .answer => [.answer (toE (0, 0, 0))]
  | .root => []

/-- The fixed substitute of a declared oracle message: the table of zeros. -/
def substituteZeroTable (o : Oracle) : Table := ⟨o.logLength, o.words, fun _ _ => toF 0⟩

/-- **The fixed substitute of a round**, computed from what the sub-protocol declares of the round
alone. No coin, no input and no challenge is among its arguments. -/
def subSending (d : Fmt.DeclaredRound) (os : List Oracle) : Sending :=
  ⟨d.items.flatMap subSaid, os.map substituteZeroTable⟩

/-- The substitute in the form in which a round's message is produced (`Told`), marked as made by no
prover's side. -/
def subTold (d : Fmt.DeclaredRound) (os : List Oracle) : Told :=
  ⟨(subSending d os).vals.map Said.got, (subSending d os).tables.map some, false⟩

/-- What a message shows at given positions, root by root. A root for which `asks` has no list shows
no column. -/
def Sending.shownAt (x : Sending) (asks : List (List Nat)) : Shown :=
  ⟨x.vals.map Said.got,
    x.tables.zipIdx.map fun t => ((asks[t.2]?).getD []).map fun p => (p, t.1.col p)⟩

/-- **The second chain's start**: rejected (`none`) if either earlier chain has been rejected, or if
the description's start of the second chain rejects. -/
def door₃ (F : FileDescription Xi) (x : Xi) (s₁ : Option F.S₁) (s₂ : Option F.S₂) : Option F.S₃ :=
  s₁.bind fun a => s₂.bind fun b => (F.start₃ (F.pub x) a b).toOption

/-! ## 2 One chain -/

/-- What a chain's reads are computed from: its number, from 0; the number in the label of its first
own tree; the stored tables' columns; the table behind a source, among the chain's rounds produced
so far. -/
structure Lay where
  chain : Nat
  firstTree : Nat
  stored : Nat → Nat → Option (List UInt64)
  tree : List Played → Fmt.TreeSource → Option (Place × Table)

/-- **The state of a chain between two rounds, with the verifier's state beside the prover's.** -/
structure ChainProgress (S Cl W Y : Type) where
  /-- the state of the prover's run; `none` once nothing more is played -/
  mid : Option (Mid W Y)
  /-- the verifier's state after the last sub-protocol that has been asked; `none` once one has
  rejected -/
  ver : Option S
  /-- the place of the first sub-protocol that rejected -/
  refused : Option Place
  /-- all rounds produced so far -/
  laid : List Played
  /-- what the sub-protocols asked so far have read, and the columns -/
  reads : List Read
  cols : List OpenedColumn
  /-- the sub-protocols not yet asked; the one that is being played comes first -/
  todo : List (Block S Cl)
  /-- that sub-protocol's rounds produced so far -/
  own : List Played

/-- **Every sub-protocol whose rounds have all been produced is asked**, in order, and so are the
sub-protocols without a round that follow. A sub-protocol's columns are filled from the tables sent
so far; where they are not available the run returns an error. Where the step accepts, these columns
are laid behind `mid`'s field `opened` (`Mid.took`): the next sub-protocol's parts are handed them.
The list argument holds the sub-protocols not yet asked. -/
def ChainProgress.settle (L : Lay) : List (Block S Cl) → ChainProgress S Cl W Y → Except Refusal (ChainProgress S Cl W Y)
  | [], z => .ok { z with todo := [] }
  | b :: bs, z =>
    if z.own.length < b.rounds.length then .ok { z with todo := b :: bs } else
    let q := readsOf L.chain L.firstTree L.stored (L.tree z.laid) b.rounds (z.own.map (·.drawn))
    (unfit (fillCols q [])).bind fun cols =>
      let v := z.ver.bind fun s => judge L.firstTree b s (roundsOf z.own) cols
      ChainProgress.settle L bs
        { z with
          ver := v, mid := if v.isSome then z.mid.map (·.took cols) else none
          refused := z.refused.or (if z.ver.isSome && v.isNone then some b.place else none)
          reads := z.reads ++ q, cols := z.cols ++ cols, own := [] }

/-- A chain's start. `m`, `v`: the state of the prover's run and the verifier's state. Either can be
`none`, and then the whole chain is substitutes. The sub-protocols without a round before the first
round are asked. `front`: the columns of earlier chains that this chain's parts are handed: they are
handed from the first round on; what `m` held in that field is dropped. -/
def ChainProgress.start (L : Lay) (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    (front : List OpenedColumn) : Except Refusal (ChainProgress S Cl W Y) :=
  ChainProgress.settle L bs
    ⟨if v.isSome then m.map ({ · with opened := some front }) else none,
      if m.isSome then v else none, none, [], [], [], bs, []⟩

/-- **A round's message**: `Step.tell`; after a rejection by the verifier, the round's fixed
substitute. -/
def ChainProgress.say (z : ChainProgress S Cl W Y) (s : Step W Y) : Except Refusal Told :=
  match z.mid with
  | some m => s.tell none m
  | none => .ok (subTold s.decl s.oracles)

/-- **After a round's challenge**: `Step.hear`. The round is added to the rounds produced, under its
part's address, a substitute too. Then the sub-protocols whose rounds have all been produced are
asked. -/
def ChainProgress.heard (L : Lay) (z : ChainProgress S Cl W Y) (s : Step W Y) (x : Told) (d : Fmt.Drawn) :
    Except Refusal (ChainProgress S Cl W Y) :=
  (match z.mid with
    | some m => (s.hear x d m).map some
    | none => .ok none).bind fun m' =>
  let p : Played := ⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩
  ChainProgress.settle L z.todo { z with mid := m', laid := z.laid ++ [p], own := z.own ++ [p] }

/-- A chain's rounds at given challenges. -/
def walk (L : Lay) : List (Step W Y) → List Fmt.Drawn → ChainProgress S Cl W Y →
    Except Refusal (ChainProgress S Cl W Y)
  | [], [], z => .ok z
  | s :: ss, d :: ds, z =>
    (z.say s).bind fun x => (z.heard L s x d).bind fun z' => walk L ss ds z'
  | _, _, _ => .error ⟨.unfit, "the challenges are not as many as the rounds"⟩

/-! ## 3 A file -/

/-- **What `runC` returns**: a run, as `run` returns it; the verifier's three states at the chains'
ends, `none` where it has rejected; and the place of the first sub-protocol that rejected, chain by
chain. Whether a chain was rejected is told by `ends`, not by `refused`: where the second chain's
start rejects, or an earlier chain has been rejected, the third end is `none` and no sub-protocol of
that chain is named. -/
structure RunC (F : FileDescription Xi) where
  run : Run
  ends : Option F.S₁ × Option F.S₂ × Option F.S₃
  refused : Option Place × Option Place × Option Place

/-- **An honest run that asks the description's own step.** `ready`, as in `run`; then the three
chains by `walk`, in the order of `run`, from the description's own three starts. The first and the
shared chain start with no column opened (`some []`): the shared chain is handed none of the first
chain's. The second chain starts with the first chain's columns and then the shared chain's. -/
def runC (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (c : Coins B) (ρ : Draws) : Except Refusal (RunC F) :=
  let stored := H.storedWords w₀ rc
  (ready F B H w₀ rc x c).bind fun R =>
  (ChainProgress.start ⟨0, 0, stored, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
    (some (F.start₁ (F.pub x))) []).bind fun a₁ =>
  (walk ⟨0, 0, stored, treeOwn⟩ R.first ρ.first a₁).bind fun z₁ =>
  if !sealQuiet z₁.laid then .error ⟨.unfit, "the sealing round sends or draws something"⟩ else
  (ChainProgress.start ⟨1, 0, stored, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
    (some (F.start₂ (F.pub x))) []).bind fun a₂ =>
  (walk ⟨1, 0, stored, treeOwn⟩ R.shared ρ.shared a₂).bind fun z₂ =>
  let L₃ : Lay := ⟨2, F.lastChainFirstTreeNumber, stored, treeThird z₁.laid z₂.laid⟩
  (ChainProgress.start L₃ F.second.blocksInOrder
    (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
    (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)).bind fun a₃ =>
  (walk L₃ R.second ρ.second a₃).map fun z₃ =>
    ⟨⟨(z₁.laid, z₂.laid, z₃.laid), (z₁.reads, z₂.reads, z₃.reads),
        (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩, ⟨roundsOf z₂.laid, z₂.cols⟩,
          ⟨roundsOf z₃.laid, z₃.cols⟩)⟩,
      (z₁.ver, z₂.ver, z₃.ver), (z₁.refused, z₂.refused, z₃.refused)⟩

/-- **The part at an address was called**: a prover's side produced one of its rounds. This is a
test on the run. -/
def RunC.called {F : FileDescription Xi} (r : RunC F) (a : Addr) : Bool :=
  (r.run.played.1 ++ r.run.played.2.1 ++ r.run.played.2.2).any fun p =>
    p.told && p.place == a.place && p.part == a.part

/-- **A run's outcome, as a statement may read it**: the three views, or `none`. It is `none`
wherever `silentAt` returns a stop, whether or not this run met the stop, and at every other error.
-/
def outcomeC (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (ρ : Draws) : Option Views :=
  if (silentAt F H w₀ rc x ρ).isSome then none
  else (runC F B H w₀ rc x c ρ).toOption.map (·.run.views)

/-- **The verdict as text**: the description's own decision on the views (`FileDescription.say`), or the
honest side's own error, printed. -/
def sayC (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (c : Coins B) (ρ : Draws) : String :=
  match runC F B H w₀ rc x c ρ with
  | .ok r => F.say x r.run.views.1 r.run.views.2.1 r.run.views.2.2
  | .error e => e.print

end ProofFile.Honest

#print axioms ProofFile.Honest.judge
#print axioms ProofFile.Honest.subSaid
#print axioms ProofFile.Honest.substituteZeroTable
#print axioms ProofFile.Honest.subSending
#print axioms ProofFile.Honest.subTold
#print axioms ProofFile.Honest.Sending.shownAt
#print axioms ProofFile.Honest.door₃
#print axioms ProofFile.Honest.Lay
#print axioms ProofFile.Honest.ChainProgress
#print axioms ProofFile.Honest.ChainProgress.settle
#print axioms ProofFile.Honest.ChainProgress.start
#print axioms ProofFile.Honest.ChainProgress.say
#print axioms ProofFile.Honest.ChainProgress.heard
#print axioms ProofFile.Honest.walk
#print axioms ProofFile.Honest.RunC
#print axioms ProofFile.Honest.runC
#print axioms ProofFile.Honest.RunC.called
#print axioms ProofFile.Honest.outcomeC
#print axioms ProofFile.Honest.sayC
