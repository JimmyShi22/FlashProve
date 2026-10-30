-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean: an invariant along a chain, `Thr T b`, for the free
parameters A and B of `Good` (Honest/Side.lean). A border is the point before a sub-protocol of the
chain's flat list, or after the last; borders are numbered from 0. `Thr T b` is a condition at
border b that ties the verifier's state to the state of the honest prover's run, the run's coins and
the available tables. It is meant to be used with A at a place := the condition at the border before
the place's sub-protocol, and B := the condition at the next border. So what holds after one
sub-protocol is what is asked before the next: it is one term. A `Thread` is the structure of the
invariant's parameters for one chain. Definitions, executable where that is possible; no theorem is
stated.

Where the invariant leads. A proof file has three chains, run in this order: the first (number 0),
the shared (1) and the second (2); each has a `Thread` of its own. `thr_next` (PaysLaw.lean) carries
`Thr` from one border to the next, under the hypotheses of Pays.lean on the sub-protocol between
them. At every sub-protocol of a chain these hypotheses give the two conditions `PlaysOn` and
`SaysYes` of the lemma for a whole chain (Ties.lean; from `ThrS`: PaysS.lean;
Honest/Law/ThreadC.lean). `file_accepts` (Honest/Thread/FileYes.lean) and, from `ThrS`,
`file_acceptsD` (Honest/Thread/FileD.lean) put the three chains
together. If the hypotheses hold at every sub-protocol, the invariants hold at the first and the
shared chain's starts (`Enters₁`, `Enters₂`, Honest/Thread/File.lean), and the conditions at the
second chain's start and at the file's last test hold, then wherever `ready` and `runC`
(Honest/Walk.lean: the prover's sides played against the description's own steps) return, with no
stop and no fall on the way, the description's own `FileDescription.run` accepts the views of that run.
Both also take executable tests on the description, the instance and the parameters (`F.planOk`,
`F.okStart`, `Sits`). That is one of the nine tests of the verdict of the file's interactive oracle
reduction (`FileDescription.out_eq`, Johnson/Desc/BlockSlot.lean), not a verifier's acceptance; how often a
stop or a fall occurs is not treated in this folder. This folder proves the hypotheses for no
description; for the proof file's description they are proved kind by kind, as far as they are
proved, in the folders of the kinds' own sub-protocols.

Words. Request, chain, place, kind, view, part, coins, book and stop are introduced in the head of
Honest/Frame.lean. A tree is an oracle message: a committed table. An item is an entry of a table of
joints: a named proposition on the verifier's state and the witness, open from the sub-protocol that
opens it to the one that closes it. (The word has two other uses: the statement's item of the stored
table is that table's index in the statement, and a round's items in the clear are the values that
it sends openly.) A fall is introduced in the head of Honest/Thread/Pays.lean. A tree's source
(`Fmt.TreeSource`) says whether the chain sent the tree itself (`own`) or an earlier chain did
(`taken`: the tree is taken over).

  1  `FwdRow`, `FwdRow.of`, `fwdStep`, `fwdOpen`, `fwdFit`   a row of a table of joints
     (Johnson/Desc/First/Borders.lean and its two counterparts), read forward; the sets of open
     items
  2  `declsTo`, `roundsTo`, `treesTo`, `borderNo`   a border's rounds and numbers, from the
     description's own flat list
  3  `Table.same`, `srcAt`, `Env.strs`   two tables show the same; the available tables as the
     library's plain strings
  4  `Thread`   the parameters of one chain's invariant
  5  `Thread.Hand`, `Thread.Fit`, `Thread.Form`, `Thread.Items`, `Thread.Made`, `Thr`   the clauses;
     the invariant
  6  `Thread.fits`   executable tests on the parameters
  7  `Thread.Code`, `Thread.body`, `Thread.fails`   an executable form of the invariant, clause by
     clause, each under its name, for the tests of this folder

The clauses.
(H) Available (`Thread.Hand`): the stored table's columns are the input's; and every tree that has
    been sent, or is taken over, is the table that a function of coins, input and challenges gives.
    This clause is never closed: a tree may be read after the sub-protocol that closes its items.
    That such a table is a code's encoding of a message of the witness is a matter of that function,
    not of this condition.
(F) Fit (`Thread.Fit`): the challenges heard are such as the rounds before the chain, and the
    chain's own rounds before the border, can draw.
(P) The form (`Thread.Form`): the public book-keeping of the verifier's state at the border: a Bool,
    and beside it what a table's public items say that is no Bool.
(I) The items (`Thread.Items`): every item that is open at the border holds of the witness, which is
    a function of the run's coins, the prover's input and the challenges heard: there is no
    existential quantifier. It is asked at every continuation of the challenges heard (whether or
    not the rounds can draw it). So an item that holds at a border holds at every later one as far
    as the witness goes, and whoever proves an item has to know which components it reads.
(X) Made (`Thread.Made`): the verifier's state is what the earlier sub-protocols made of the run's
    own rounds and columns, each by its own step's acceptance (`foldBlocks`,
    Johnson/Desc/Block.lean); what was heard is what the rounds shown drew; which challenges the
    stops may read; how many trees have been sent; above that number no tree is available (the text
    of `Env.Tight`, Honest/Law/Along.lean, which this file does not import). Of what the parts pass
    on (`State.own`) nothing is said.
(R) The riders (`rides`): a parameter for what a file's last test reads and no item says. A rider is
    a fact on the verifier's state that one sub-protocol establishes and a later one uses.
(V) The input is one of which something is to be stated (`valid`): a parameter. It is meant to bear
    no clause on the stored tables' pads and encoding randomness, on a seed or on a key: what the
    verifier tests of a key it tests on its own state. An implication from `valid` to a fact on the
    key, the seeds or the stored table has to be proved from the committer's construction, at every
    value of these and every seed. It is never obtained by adding the fact to `valid`. What cannot
    be proved in this way is not added to `valid` either. How often it fails, over the stored
    tables' pads and encoding randomness and the seed, has to be stated as a number beside whatever
    is proved. This is the author's own rule of use: it is no theorem.
    It rests on this remark: every
    valid private input is to be met at every index, every value of the stored tables' pads and
    encoding randomness and every seed. That it reaches the key and the stored table is the author's
    own reading (both are computed from these three: Honest/Committer.lean: `enc`, `ood`).

A row read forward. A table's row says which items its sub-protocol closes (ins), opens (outs) and
reads (ctx). Read forward: ins and ctx hold before it; outs and ctx have to be proved after it (an
item is read at the border's own state, and a sub-protocol may change what its ctx reads); ins
are open no more.

Limits.
  * Definitions alone: no theorem here says that the invariant holds along a chain of the protocol.
  * It speaks of a run as far as every earlier sub-protocol has accepted.
  * Every field of `Thread` is a parameter. At `valid := fun _ => False` the invariant is false
    everywhere, and whatever takes it as a hypothesis holds vacuously. At `means` true everywhere
    (I) says nothing.
  * Nothing here compares `table` with what a prover's side sends, `wit` with `table`, or `row` with
    a table of joints.
  * `Thread.body` is not the invariant: it is asked at one continuation, at the listed positions of
    the stored table, at the own trees below a listed number, and at executable parameters which
    nothing here compares with the invariant's own.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.Msg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs foldBlocks)

variable {S Cl V W X Pb : Type}

/-! ## 1 A row read forward -/

/-- **A sub-protocol's row of a table of joints, read forward.** -/
structure FwdRow (ι : Type) where
  /-- the items that hold before it -/
  asks : List ι := []
  /-- the items that have to be proved after it -/
  owes : List ι := []
  /-- the items that are open before it and open no more after it -/
  shuts : List ι := []

/-- From a table's row: what it closes, what it opens, what it reads and leaves. -/
def FwdRow.of {ι : Type} (ins outs ctx : List ι) : FwdRow ι := ⟨ins ++ ctx, outs ++ ctx, ins⟩

/-- The set of open items after a sub-protocol, as the tables' own `stepOpen`: an item occurs once.
-/
def fwdStep {ι : Type} [DecidableEq ι] (O : List ι) (r : FwdRow ι) : List ι :=
  let rest := O.filter fun i => !r.shuts.contains i
  rest ++ r.owes.filter fun i => !rest.contains i

/-- The set of open items at border number `b`. -/
def fwdOpen {ι : Type} [DecidableEq ι] (start : List ι) (row : Nat → FwdRow ι) : Nat → List ι
  | 0 => start
  | b + 1 => fwdStep (fwdOpen start row b) (row b)

/-- A test on the rows: whatever one of the first `n` rows asks or shuts is open before it. -/
def fwdFit {ι : Type} [DecidableEq ι] (start : List ι) (row : Nat → FwdRow ι) (n : Nat) : Bool :=
  (List.range n).all fun b => ((row b).asks ++ (row b).shuts).all (fwdOpen start row b).contains

/-! ## 2 A border's rounds and numbers -/

/-- The rounds of the first `b` sub-protocols of a list, concatenated. -/
def declsTo (bs : List (Block S Cl)) (b : Nat) : List Fmt.DeclaredRound :=
  (bs.take b).flatMap (·.rounds)

/-- How many these are. -/
def roundsTo (bs : List (Block S Cl)) (b : Nat) : Nat := (declsTo bs b).length

/-- How many oracle messages the first `b` sub-protocols declare. -/
def treesTo (bs : List (Block S Cl)) (b : Nat) : Nat :=
  ((bs.take b).flatMap fun x => x.oracles.flatMap id).length

/-- The number of the border before the sub-protocol at a place; the list's length if there is none.
-/
def borderNo (bs : List (Block S Cl)) (p : Place) : Nat := bs.findIdx fun x => x.place == p

/-! ## 3 Tables and strings -/

/-- Two tables show the same: the two numbers, and the column at every position below the length. A
Bool and no equation: a table's symbols are a function on all numbers. -/
def Table.same (t u : Table) : Bool :=
  t.logLength == u.logLength && t.words == u.words &&
    (List.range (2 ^ t.logLength)).all fun x => t.col x == u.col x

/-- The source, as a round of chain number `chain` (from 0) declares it, of the tree that has the
number `j` through the whole file. `n₁`, `n₂`: how many trees the first and the shared chain send.
In the first and the shared chain no other chain's tree has a source. Every other number of a chain
is read as the second chain's. -/
def srcAt (chain n₁ n₂ j : Nat) : Option Fmt.TreeSource :=
  if chain == 0 then (if j < n₁ then some (.own j) else none)
  else if chain == 1 then (if n₁ ≤ j ∧ j < n₁ + n₂ then some (.own (j - n₁)) else none)
  else if j < n₁ then some (.taken 0 j)
  else if j < n₁ + n₂ then some (.taken 1 (j - n₁))
  else some (.own (j - n₁ - n₂))

/-- **The available tables as the library's plain strings** (`Strs`, Johnson/Desc/Msg.lean), which
number trees through the whole file. `item`: the statement's item of the stored table. `src`: a
tree's source. Empty where no table is available, and beyond a table's length. -/
def Env.strs (item : Nat) (src : Nat → Option Fmt.TreeSource) (E : Env) : Strs :=
  ⟨fun x => (E.stored item x).map fun c => (x, c),
    fun j x =>
      match (src j).bind E.tree with
      | some u => if x < 2 ^ u.2.logLength then u.2.col x else []
      | none => []⟩

/-! ## 4 The parameters -/

/-- **The parameters of one chain's invariant.** -/
structure Thread (Bk : ProverCoinCounts) (S Cl V W X Pb : Type) where
  /-- the chain's face, its number from 0, and the number in the label of its first own tree, as in
  `readsOf` -/
  φ : Face V W Pb
  chain : Nat
  ft : Nat
  /-- the description's own flat list -/
  bs : List (Block S Cl)
  /-- the prover's sides of this chain -/
  hs : List (Placed V W X)
  /-- the rounds that have been heard and shown before the chain; how many of their challenges, the
  first ones, the stops may read; the sources of the trees that are taken over -/
  ahead : List Fmt.DeclaredRound
  near : Nat
  taken : List Fmt.TreeSource
  /-- (H): after how many challenges a tree's table changes no more; the place of the tree's sender
  and its table; the stored table's columns -/
  fixed : Fmt.TreeSource → Nat
  table : Fmt.TreeSource → Coins Bk → W → List Fmt.Drawn → Place × Table
  stored : W → Nat → Nat → Option (List UInt64)
  /-- (V) -/
  valid : W → Prop
  /-- the table of joints: its items; what is open at the chain's start; its rows, read forward -/
  ι : Type
  dec : DecidableEq ι
  start : List ι
  row : Nat → FwdRow ι
  /-- what the chain was given, from a run's coins, the input and the challenges before the chain.
  (In the first and the shared chain it is meant to be computed from the input's public field
  (`Face.pub`) alone; the second chain's items read the two earlier chains' last states too.) -/
  P : Type
  handed : Coins Bk → W → List Fmt.Drawn → P
  /-- the type of witnesses of which the table's items speak -/
  Wt : Type
  /-- (P) -/
  form : Nat → P × S → Bool
  formP : Nat → P × S → Prop
  /-- (I): what an item says. Of the input it is meant to read the index alone -/
  means : W → ι → P × S → Strs → Wt → Prop
  /-- the witness, from a run's coins, the input and challenges -/
  wit : Coins Bk → W → List Fmt.Drawn → Wt
  strs : Env → Strs
  /-- (X): the chain's first state, from a run's coins, the input and the challenges before the
  chain -/
  begun : Coins Bk → W → List Fmt.Drawn → S → Prop
  /-- (R) -/
  rides : Nat → W → S → Prop
  /-- what the sub-protocol after a border leaves unchanged in the verifier's state -/
  keeps : Nat → S → S → Prop

attribute [instance] Thread.dec

variable {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-! ## 5 The clauses, and the invariant -/

/-- How many rounds have been heard and shown before the chain. -/
def Thread.front : Nat := T.ahead.length

/-- The sources of all trees that are available at border number `b`. -/
def Thread.hand (b : Nat) : List Fmt.TreeSource :=
  T.taken ++ (List.range (treesTo T.bs b)).map Fmt.TreeSource.own

/-- A tree's sender and table, at the state of the run. -/
def Thread.tableAt (σ : Fmt.TreeSource) (k : Coins Bk) (m : Mid W X) : Place × Table :=
  T.table σ k m.st.input (m.st.heard.take (T.fixed σ))

/-- The tree behind a source is available, from that sender, and shows what that table shows. -/
def Thread.handAt (σ : Fmt.TreeSource) (k : Coins Bk) (m : Mid W X) (E : Env) : Bool :=
  (E.tree σ).any fun u => u.1 == (T.tableAt σ k m).1 && u.2.same (T.tableAt σ k m).2

/-- (H), the part on trees, at a list of sources. -/
def Thread.Trees (L : List Fmt.TreeSource) (k : Coins Bk) (m : Mid W X) (E : Env) : Prop :=
  ∀ σ ∈ L, T.handAt σ k m E = true

/-- (H) -/
def Thread.Hand (b : Nat) (k : Coins Bk) (m : Mid W X) (E : Env) : Prop :=
  (∀ i x, E.stored i x = T.stored m.st.input i x) ∧ T.Trees (T.hand b) k m E

/-- (F) -/
def Thread.Fit (b : Nat) (m : Mid W X) : Prop :=
  drawsFit (T.ahead ++ declsTo T.bs b) m.st.heard = true

/-- The items that are open at a border. -/
def Thread.opened (b : Nat) : List T.ι := fwdOpen T.start T.row b

/-- What an item speaks of: what the chain was given, and the verifier's state. -/
def Thread.seat (k : Coins Bk) (m : Mid W X) (s : S) : T.P × S :=
  (T.handed k m.st.input (m.st.heard.take T.front), s)

/-- (P) -/
def Thread.Form (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) : Prop :=
  T.form b (T.seat k m s) = true ∧ T.formP b (T.seat k m s)

/-- (I) at one continuation `ds` of the challenges heard. -/
def Thread.ItemsAt (O : List T.ι) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env)
    (ds : List Fmt.Drawn) : Prop :=
  ∀ i ∈ O,
    T.means m.st.input i (T.seat k m s) (T.strs E) (T.wit k m.st.input (m.st.heard ++ ds))

/-- (I) -/
def Thread.Items (O : List T.ι) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env) : Prop :=
  ∀ ds, T.ItemsAt O k s m E ds

/-- Of the challenges heard, those that the stops may read: the first `near` of those before the
chain, and the chain's own. -/
def Thread.locOf (h : List Fmt.Drawn) : List Fmt.Drawn := h.take T.near ++ h.drop T.front

/-- The columns that the sub-protocols before a border read, from the available tables. -/
def Thread.colsTo (b : Nat) (m : Mid W X) (E : Env) : Except String (List OpenedColumn) :=
  fillCols (readsOf T.chain T.ft E.stored E.tree (declsTo T.bs b) (m.st.heard.drop T.front)) []

/-- (X). It has two existential quantifiers: a first state that `begun` allows, and the result of
`fillCols`, which is a function's value. `begun` is a relation: a `Thread` need not allow one first
state only; lemmas that need that ask for it (`reach_of_made`, Honest/Thread/MadeLaw.lean;
`thr_state_unique`, Honest/Thread/ThrUnique.lean). -/
def Thread.Made (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env) : Prop :=
  m.seen.map (·.drawn) = m.st.heard ∧ m.loc = T.locOf m.st.heard ∧ E.sent = treesTo T.bs b ∧
    (∀ n, E.sent ≤ n → E.tree (.own n) = none) ∧
    ∃ s₀ cols, T.begun k m.st.input (m.st.heard.take T.front) s₀ ∧ T.colsTo b m E = .ok cols ∧
      foldBlocks T.ft (T.bs.take b) s₀ (m.seen.drop T.front) cols = .ok (s, [], [])

/-- **The invariant at border number `b`**: a condition on a whole run's coins, the verifier's
state, the state of the prover's run, and the available tables: the type of `Good`'s parameters A
and B. It is a definition, meant as a hypothesis. Nothing is claimed of it, and it is none of the
library's goals. -/
def Thr (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env) : Prop :=
  T.Hand b k m E ∧ T.Fit b m ∧ T.Form b k s m ∧ T.Items (T.opened b) k s m E ∧
    T.Made b k s m E ∧ T.rides b m.st.input s ∧ T.valid m.st.input

/-! ## 6 Tests on the parameters -/

/-- **Executable tests on the parameters.** `n`: how many sub-protocols' rows are looked at.
Whatever a row asks or shuts is open before it; each sub-protocol declares a list of oracle messages
for each of its rounds, one message for each root; no tree that is taken over has an own tree's
source; a tree that is available at a border is fixed by the challenges heard there; the stops read
no more challenges before the chain than there are. -/
def Thread.fits (n : Nat) : Bool :=
  fwdFit T.start T.row n &&
    (T.bs.all fun x => x.rounds.length == x.oracles.length &&
      x.rounds.map (·.entry.roots) == x.oracles.map (·.length)) &&
    (T.taken.all fun σ => match σ with
      | .own _ => false
      | .taken _ _ => true) &&
    ((List.range (n + 1)).all fun b =>
      (T.hand b).all fun σ => decide (T.fixed σ ≤ T.front + roundsTo T.bs b)) &&
    decide (T.near ≤ T.front)

/-! ## 7 An executable form -/

/-- Executable parameters beside a `Thread`'s, for the tests of this folder. Nothing compares them
with the `Thread`'s own: whoever supplies both is to take them from one definition. -/
structure Thread.Code where
  meansB : W → T.ι → T.P × S → Strs → T.Wt → Bool
  formPB : Nat → T.P × S → Bool
  /-- the chain's first state -/
  first : Coins Bk → W → List Fmt.Drawn → S
  sameS : S → S → Bool
  ridesB : Nat → W → S → Bool
  validB : W → Bool
  /-- the stored table's items and positions that are looked at -/
  looks : List (Nat × Nat)
  /-- up to which number of an own tree "no tree is available above those sent" is looked at -/
  upTo : Nat

/-- **An executable form of the invariant, clause by clause, each under its name**, at one
continuation `ds`. -/
def Thread.body (C : T.Code) (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env)
    (ds : List Fmt.Drawn) : List (String × Bool) :=
  [("(H) the stored table", C.looks.all fun q =>
      E.stored q.1 q.2 == T.stored m.st.input q.1 q.2),
    ("(H) a tree", (T.hand b).all fun σ => T.handAt σ k m E),
    ("(F) the challenges", drawsFit (T.ahead ++ declsTo T.bs b) m.st.heard),
    ("(P) the form", T.form b (T.seat k m s) && C.formPB b (T.seat k m s)),
    ("(I) an open item", (T.opened b).all fun i =>
      C.meansB m.st.input i (T.seat k m s) (T.strs E) (T.wit k m.st.input (m.st.heard ++ ds))),
    ("(X) the counts", m.seen.map (·.drawn) == m.st.heard && m.loc == T.locOf m.st.heard &&
      E.sent == treesTo T.bs b),
    ("(X) no tree above those sent", (List.range C.upTo).all fun n =>
      decide (n < E.sent) || (E.tree (.own n)).isNone),
    ("(X) the verifier's state",
      match T.colsTo b m E with
      | .ok cols =>
        (match foldBlocks T.ft (T.bs.take b) (C.first k m.st.input (m.st.heard.take T.front))
            (m.seen.drop T.front) cols with
        | .ok z => C.sameS z.1 s && z.2.1.isEmpty && z.2.2.isEmpty
        | .error _ => false)
      | .error _ => false),
    ("(R) the riders", C.ridesB b m.st.input s),
    ("(V) the input", C.validB m.st.input)]

/-- The names of the clauses that fail. -/
def Thread.fails (C : T.Code) (b : Nat) (k : Coins Bk) (s : S) (m : Mid W X) (E : Env)
    (ds : List Fmt.Drawn) : List String :=
  ((T.body C b k s m E ds).filter (!·.2)).map (·.1)

end ProofFile.Honest
