-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Session.lean: one function, `session`, built from the
candidate simulators that are paired with the parts of a description's sides (`Sim`,
Honest/Frame.lean). It calls them in the order of play, each on what the earlier ones have output.
After each sub-protocol of a chain's flat list it asks the description's own step on what it has
produced (`judge`, Honest/Walk.lean). After the first sub-protocol of a chain that rejects it calls
no simulator of that chain, nor of the second chain, and produces each round's fixed substitute
(`subSending`), as `runC` (Honest/Walk.lean) does. Definitions only: no theorem is stated here, and
none of these definitions is one of the library's goals.

  1  `Sims`, `Sides.sims`, `Teller`, `tellerOf`   the candidate simulators of three chains; one of
     them with its first argument, the input's public field, supplied
  2  `Stretch`, `Stretch.sub`, `Stretch.bare`, `Stretch.lay`, `asksFrom`, `cutRow`   a part's
     rounds, or the rounds of a place that has no list of parts; what is produced there
  3  `Laid`, `Laid.front`, `Laid.add`, `Laid.of`, `Stand`, `Stand.live`, `Stand.start`   what has
     been produced; of that, what a simulator is given; the same with the verifier's three states
     beside it
  4  `Before.wordsAt`, `colsOff`, `roundsOff`, `judgeOff`   a read's words, a sub-protocol's columns
     and rounds, from what has been produced; the verifier's step on them
  5  `Act`, `chainActs`, `theActs`, `Act.go`, `simActs`   the steps of a session, in order; the fold
     over them
  6  `viewsOff`, `session`   the three views of what has been produced; the whole function
  7  `Run.laid`, `addrsOf`, `Sides.owns`   what a run shows, in the same type; a test on the book

What `session` is given, by type. Fixed first: a description, a book, the simulators, and a function
from the instance to the key. Then: the instance, the challenges, and a list of stored tables'
columns. None of the type parameters of a prover's input (Honest/Frame.lean: W₀, Rc, Tr), no run's
coins (`Coins`), no `Prover` and no `Part` occurs in its type.

The order. The first chain's flat list, the shared chain's, the second chain's; at a place that has
simulators, part by part, as the book cuts the place (`ProverCoinCounts.cuts`); after each sub-protocol its
`judge`; before the second chain its start (`door₃`).

What a simulator is given of what has been produced (`Laid.front`) is cut as `Run.beforeAt`
(Honest/Side.lean) cuts a run. The positions at which it has to output columns are all reads of the
whole run of its part's trees, also those that rounds after a rejection make.

A rejection in the first chain does not reach the shared chain; either reaches the second chain, at
its start. The rejecting sub-protocol's own rounds are the simulators'.

Limits.
  * Nothing ties these functions to `runC` here.
  * Where a simulator outputs another number of rounds than its stretch has challenges, the outcome
    is `none` (`Stretch.lay`).
  * Where a column that a sub-protocol reads has not been produced, `judgeOff` gives "rejected",
    where `runC` returns an error.
  * Where the book has no cut for a place that has simulators, nothing is produced there.
  * Where fewer rounds have been produced at a place than it declares (no cut, a cut that sums to
    less, fewer lists of oracle messages than rounds), `judgeOff` is asked on the chain's last
    rounds all the same, earlier places' among them.
  * Which places have a list of parts is read from the simulators' own addresses.
  * At a place that has simulators, a part whose address none of them names gets `Stretch.bare`, not
    the outcome `none`.
  * A round's number of roots is the length of its list of oracle messages, with a list of parts or
    without.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Walk
import Johnson.Desc.ProofFile.Honest.Law.Rule.Bare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn Oracle)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 The candidate simulators -/

/-- The parts' candidate simulators of a description's three chains. -/
structure Sims (Xi Ky : Type) where
  first : List (Sim Xi)
  shared : List (Sim Ky)
  second : List (Sim Xi)

/-- The candidate simulators in a description's sides. -/
def Sides.sims {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Sims Xi Ky :=
  ⟨G.first.flatMap fun L => L.row.map (·.2), G.shared.flatMap fun L => L.row.map (·.2),
    G.second.flatMap fun L => L.row.map (·.2)⟩

/-- A part's candidate simulator with its first argument, the input's public field, supplied. -/
structure Teller where
  takes : Due
  tell : Before → List Fmt.Drawn → List (List (List Nat)) → Cs takes → Option (List Shown)

/-- The first simulator of a list that names the address, with its first argument supplied. -/
def tellerOf {Pb : Type} (l : List (Sim Pb)) (pb : Pb) (a : Addr) : Option Teller :=
  (l.find? fun S => S.addr == a).map fun S => ⟨S.takes, S.tell pb⟩

/-! ## 2 A stretch -/

/-- **A stretch of a session**: a part's rounds, or the rounds of a place that has no list of parts.
-/
structure Stretch where
  /-- the chain's number, from 0 -/
  chain : Nat
  addr : Addr
  /-- what the sub-protocol declares of each round: its declared round, its oracle messages -/
  rounds : List (Fmt.DeclaredRound × List Oracle)
  /-- its rounds' challenges -/
  ds : List Fmt.Drawn
  /-- by round and by root: the positions that are read, in any round of the whole run -/
  asks : List (List (List Nat))
  /-- `none`: no simulator names the address (so wherever the place has no list of parts) -/
  teller : Option Teller

/-- After a rejection: each round's fixed substitute, at the positions that are read. -/
def Stretch.sub (s : Stretch) : List (Shown × Fmt.Drawn) :=
  ((s.rounds.zip s.asks).map fun z => (subSending z.1.1 z.1.2).shownAt z.2).zip s.ds

/-- Where the stretch has no teller: no item; for each root an empty list of columns. -/
def Stretch.bare (s : Stretch) : List (Shown × Fmt.Drawn) :=
  (s.rounds.map fun z => (⟨[], List.replicate z.2.length []⟩ : Shown)).zip s.ds

/-- What a stretch contributes: a distribution whose outcomes are lists of shown rounds, or `none`.
The outcome is `none` where the simulator outputs `none`, or another number of rounds than the
stretch has challenges. `live`: the verifier has not rejected in this chain. `f`: what the stretch's
simulator is given of what has been produced. -/
noncomputable def Stretch.lay (s : Stretch) (live : Bool) (f : Before) :
    PMF (Option (List (Shown × Fmt.Drawn))) :=
  if live then
    match s.teller with
    | none => PMF.pure (some s.bare)
    | some t =>
      (Prob.unif (Cs t.takes)).map fun c => (t.tell f s.ds s.asks c).bind fun out =>
        if out.length == s.ds.length then some (out.zip s.ds) else none
  else PMF.pure (some s.sub)

/-- By round and by root: what is read of the trees from number `n` on. `tree`: the positions read
of a tree, by its number. The list: each round's number of roots. -/
def asksFrom (tree : Nat → List Nat) : List Nat → Nat → List (List (List Nat))
  | [], _ => []
  | r :: rs, n => ((List.range r).map fun i => tree (n + i)) :: asksFrom tree rs (n + r)

/-- A place with a list of parts, cut as the book cuts it. The arguments after the place: the part's
number, the cut, the place's rounds, how many trees the chain has sent before, the place's
challenges. -/
def cutRow (ch : Nat) (tree : Nat → List Nat) (tl : Addr → Option Teller) (a : Place) :
    Nat → List Nat → List (Fmt.DeclaredRound × List Oracle) → Nat → List Fmt.Drawn → List Stretch
  | _, [], _, _, _ => []
  | j, c :: cs, rs, n, ds =>
    (⟨ch, ⟨a, j⟩, rs.take c, ds.take c, asksFrom tree ((rs.take c).map (·.2.length)) n,
        tl ⟨a, j⟩⟩ : Stretch) ::
      cutRow ch tree tl a (j + 1) cs (rs.drop c) (n + ((rs.take c).map (·.2.length)).sum)
        (ds.drop c)

/-! ## 3 What has been produced -/

/-- What has been produced so far, chain by chain, as `Before.rounds` lists rounds. -/
structure Laid where
  first : List (Nat × Shown × Fmt.Drawn)
  shared : List (Nat × Shown × Fmt.Drawn)
  second : List (Nat × Shown × Fmt.Drawn)

/-- **What a simulator of chain number `ch` is given of it**: cut as `Run.beforeAt` cuts a run.
`st`: the stored tables' columns. Any `ch` from 2 on counts as the second chain; so in `Laid.add`,
`Laid.of` and `Stand.live`. -/
def Laid.front (L : Laid) (ch : Nat) (st : List (Nat × Nat × List UInt64)) : Before :=
  if ch == 0 then ⟨L.first, st⟩ else if ch == 1 then ⟨L.shared, st⟩
  else ⟨L.first ++ L.shared ++ L.second, st⟩

/-- The same with a stretch's rounds after the chain's. -/
def Laid.add (L : Laid) (ch : Nat) (new : List (Shown × Fmt.Drawn)) : Laid :=
  let l := new.map fun z => (ch, z.1, z.2)
  if ch == 0 then { L with first := L.first ++ l }
  else if ch == 1 then { L with shared := L.shared ++ l }
  else { L with second := L.second ++ l }

/-- One chain's rounds. -/
def Laid.of (L : Laid) (ch : Nat) : List (Nat × Shown × Fmt.Drawn) :=
  if ch == 0 then L.first else if ch == 1 then L.shared else L.second

/-- What has been produced, and the verifier's three states. `none`: rejected. -/
structure Stand (F : FileDescription Xi) where
  laid : Laid
  v₁ : Option F.S₁
  v₂ : Option F.S₂
  v₃ : Option F.S₃

/-- The verifier has not rejected in chain number `ch`. -/
def Stand.live {F : FileDescription Xi} (Z : Stand F) (ch : Nat) : Bool :=
  if ch == 0 then Z.v₁.isSome else if ch == 1 then Z.v₂.isSome else Z.v₃.isSome

/-- Nothing produced; the description's own first states; the second chain's start not yet reached.
-/
def Stand.start (F : FileDescription Xi) (x : Xi) : Stand F :=
  ⟨⟨[], [], []⟩, some (F.start₁ (F.pub x)), some (F.start₂ (F.pub x)), none⟩

/-! ## 4 The verifier's step, on what has been produced -/

/-- A read's words: of a stored table, from the supplied list `stored`; of a tree, from what has
been produced. The first match. -/
def Before.wordsAt (f : Before) (q : Read) : Option (List UInt64) :=
  match q.item, q.src with
  | some i, _ => (f.stored.find? fun c => c.1 == i && c.2.1 == q.pos).map (·.2.2)
  | none, some (ch, n) =>
    (f.treeCols ch n).bind fun cols => (cols.find? fun c => c.1 == q.pos).map (·.2)
  | none, none => none

/-- Columns, read by read; `none` if one has not been produced. -/
def colsOff (f : Before) : List Read → Option (List OpenedColumn)
  | [] => some []
  | q :: qs => (f.wordsAt q).bind fun w => (colsOff f qs).map fun l => (q.key, q.pos, w) :: l

/-- Rounds as a view shows them. -/
def roundsOff (l : List (Nat × Shown × Fmt.Drawn)) : List Fmt.RoundView :=
  l.map fun r => ⟨r.2.1.vals, r.2.2⟩

/-- **The verifier's step at a sub-protocol, on what has been produced**: the sub-protocol's own
rounds are its chain's last ones; its columns are looked up at its own rounds' reads, which
`readsOf` computes with no table supplied. -/
def judgeOff {S Cl : Type} (ch ft : Nat) (st : List (Nat × Nat × List UInt64)) (b : Block S Cl)
    (own : List Fmt.Drawn) (L : Laid) (s : S) : Option S :=
  (colsOff (L.front 2 st)
      (readsOf ch ft (fun _ _ => none) (fun _ => none) b.rounds own)).bind fun cols =>
    judge ft b s (roundsOff ((L.of ch).drop ((L.of ch).length - b.rounds.length))) cols

/-! ## 5 The fold -/

/-- The steps of a session, in order. -/
inductive Act (F : FileDescription Xi) where
  /-- a stretch's rounds are produced -/
  | lay (s : Stretch)
  /-- the verifier's step at a sub-protocol of the first chain; `own`: the sub-protocol's challenges
  -/
  | judge₁ (b : Block F.S₁ F.Cl) (own : List Fmt.Drawn)
  /-- the same in the shared chain -/
  | judge₂ (b : Block F.S₂ F.Cl) (own : List Fmt.Drawn)
  /-- the second chain's start -/
  | door
  /-- the verifier's step at a sub-protocol of the second chain -/
  | judge₃ (b : Block F.S₃ F.Cl) (own : List Fmt.Drawn)

/-- A chain's steps. `has`: which places have a list of parts. `J`: the chain's `judge`. The
arguments after the list: how many trees the chain has sent before, and the challenges from there
on. -/
def chainActs {S Cl : Type} (F : FileDescription Xi) (Bk : ProverCoinCounts) (ch : Nat) (tree : Nat → List Nat)
    (tl : Addr → Option Teller) (has : Place → Bool) (J : Block S Cl → List Fmt.Drawn → Act F) :
    List (Block S Cl) → Nat → List Fmt.Drawn → List (Act F)
  | [], _, _ => []
  | b :: bs, n, ds =>
    let rs := b.rounds.zip b.oracles
    let own := ds.take b.rounds.length
    (if has b.place then cutRow ch tree tl b.place 0 ((Bk.cuts.lookup b.place).getD []) rs n own
      else [(⟨ch, ⟨b.place, 0⟩, rs, own, asksFrom tree (rs.map (·.2.length)) n, none⟩ :
        Stretch)]).map Act.lay ++
      J b own :: chainActs F Bk ch tree tl has J bs (n + (rs.map (·.2.length)).sum)
        (ds.drop b.rounds.length)

/-- **A session's steps.** -/
def theActs (F : FileDescription Xi) (Bk : ProverCoinCounts) (T : Sims Xi Ky) (key : Xi → Ky) (x : Xi) (ρ : Draws) :
    List (Act F) :=
  chainActs F Bk 0 (treeAsks F ρ 0) (tellerOf T.first x)
      (fun a => T.first.any (·.addr.place == a)) Act.judge₁ F.first.blocksInOrder 0 ρ.first ++
    chainActs F Bk 1 (treeAsks F ρ 1) (tellerOf T.shared (key x))
      (fun a => T.shared.any (·.addr.place == a)) Act.judge₂ F.shared.blocksInOrder 0 ρ.shared ++
    Act.door :: chainActs F Bk 2 (treeAsks F ρ 2) (tellerOf T.second x)
      (fun a => T.second.any (·.addr.place == a)) Act.judge₃ F.second.blocksInOrder 0 ρ.second

/-- One step. -/
noncomputable def Act.go {F : FileDescription Xi} (x : Xi) (st : List (Nat × Nat × List UInt64)) :
    Act F → Stand F → PMF (Option (Stand F))
  | .lay s, Z => (s.lay (Z.live s.chain) (Z.laid.front s.chain st)).map fun o =>
      o.map fun new => { Z with laid := Z.laid.add s.chain new }
  | .judge₁ b own, Z => PMF.pure (some { Z with v₁ := Z.v₁.bind (judgeOff 0 0 st b own Z.laid) })
  | .judge₂ b own, Z => PMF.pure (some { Z with v₂ := Z.v₂.bind (judgeOff 1 0 st b own Z.laid) })
  | .door, Z => PMF.pure (some { Z with v₃ := door₃ F x Z.v₁ Z.v₂ })
  | .judge₃ b own, Z =>
    PMF.pure (some { Z with v₃ := Z.v₃.bind (judgeOff 2 F.lastChainFirstTreeNumber st b own Z.laid) })

/-- **The fold**: step by step; `none` ends it. -/
noncomputable def simActs {F : FileDescription Xi} (x : Xi) (st : List (Nat × Nat × List UInt64)) :
    List (Act F) → Stand F → PMF (Option (Stand F))
  | [], Z => PMF.pure (some Z)
  | a :: as, Z => (a.go x st Z).bind fun o =>
      match o with
      | none => PMF.pure none
      | some Z' => simActs x st as Z'

/-! ## 6 The three views -/

/-- **The three views of what has been produced**: the first without its sealing round, as in
`runC`. -/
def viewsOff (F : FileDescription Xi) (ρ : Draws) (st : List (Nat × Nat × List UInt64)) (L : Laid) :
    Option Views :=
  (colsOff (L.front 2 st) (bareReads F ρ).1).bind fun c₁ =>
  (colsOff (L.front 2 st) (bareReads F ρ).2.1).bind fun c₂ =>
  (colsOff (L.front 2 st) (bareReads F ρ).2.2).map fun c₃ =>
    (⟨(roundsOff L.first).dropLast, c₁⟩, ⟨roundsOff L.shared, c₂⟩, ⟨roundsOff L.second, c₃⟩)

/-- **The whole function**: the fold over the session's steps, and the three views of what it has
produced. It is a definition. No theorem is stated of it here, and it is none of the library's
goals. Its outcome is `none` also where `viewsOff` finds that a column that is read has not been
produced. -/
noncomputable def session (F : FileDescription Xi) (Bk : ProverCoinCounts) (T : Sims Xi Ky) (key : Xi → Ky) (x : Xi)
    (ρ : Draws) (st : List (Nat × Nat × List UInt64)) : PMF (Option Views) :=
  (simActs x st (theActs F Bk T key x ρ) (Stand.start F x)).map fun o =>
    o.bind fun Z => viewsOff F ρ st Z.laid

/-! ## 7 A run in the same type; a test on the book -/

/-- What a run shows, chain by chain, as `Before.rounds` lists rounds (`shownIn`, Honest/Side.lean).
-/
def Run.laid (r : Run) : Laid :=
  let qs := r.reads.1 ++ r.reads.2.1 ++ r.reads.2.2
  ⟨(shownIn 0 r.played.1 qs).map fun y => (0, y.2, y.1.drawn),
    (shownIn 1 r.played.2.1 qs).map fun y => (1, y.2, y.1.drawn),
    (shownIn 2 r.played.2.2 qs).map fun y => (2, y.2, y.1.drawn)⟩

/-- The addresses of the parts of a list of `Lettered` (each a list of parts at one place). -/
def addrsOf {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (l : List (Lettered Bk S Cl V W Y Pb)) : List Addr :=
  l.flatMap fun L => (List.range L.row.length).map fun j => ⟨L.place, j⟩

/-- **Every entry's owner is a part of some side**: an executable test. -/
def Sides.owns {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Bool :=
  Bk.ahead.all fun e => (addrsOf G.first ++ addrsOf G.shared ++ addrsOf G.second).contains e.owner

end ProofFile.Honest
