-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/BookPlan.lean: WHO MAY SHARE A TREE, WHERE AND WHEN A TREE MAY BE OPENED, AND WHICH
MESSAGES HOLD SAMPLE ANSWERS: tests on the plan alone; and where, among the groups of columns that a
block is handed, a tree's opening stands. Functions with code, over the three chains' declared
rounds (Decl/Declared.lean) and what the plan tells of each oracle message that is sent
(Johnson/Desc/Oracle.lean). No view, no carried record, no hash function.

Why. The messages of one prover's message are laid in trees; messages that share a tree are its
tenants; a leaf is the column of all tenants, and it is opened whole. So an opening shows something
of every tenant. The verifier program asks some public conditions at each opening, in its run
(OnBytes/Iop/Ground.lean: `Blk.countOpening`, `Blk.openTreesInto`, `Blk.readOpened`). None of them
reads a proof's bytes. Here they are asked once, of the plan. Where ALL tenants of a tree say
"sampled" the tree is free of two of them (oneGroup, once). That freedom is worth something only if
the sample's answer is fixed before the positions are drawn at which the tree is opened. So three
clauses more hold that word against the rounds' entries and ask the order (sentOraclesMatchEntries, answered,
inTime). A block is handed the columns of a round's openings group by group, in the order in which
the round declares them, and a group's key need not name its tree: so the order itself is asked
(inOrder). And the groups that a tenant is said to join are held against how often its tree is
opened (groupsFit, which stands beside the clauses).

The data. A declared round says which trees it opens, each with its depth, its width and whose tree
it is; its entry says, among other numbers, how many roots and how many sample answers its message
holds and how many of the elements that it draws must not be 0 (roots, answers, drawNZ), and its
name gives its kind. A round's message stands in front of its draw (its bytes enter the hash query
of which the verifier's message is drawn: Fmt/Plan.lean's head), and its trees are opened at the
positions drawn in it (`Fmt.DeclaredRound.opens`; the format page's R8.7). A declared round does not say
who shares a leaf. That is the second argument: for each chain, for each root that the chain itself
sends, in the order of sending, an `Oracle`: the log-length, the words of a symbol, and the tenants,
each a `SymbolComponent`: the words of its main and mask symbols in a column, the degree of its main rows,
whether it is sampled, and the groups to which it belongs. CHAINS ARE NUMBERED FROM 0 HERE, as in a
declared round's "taken (chain, sent)".

The clauses (`clauses`), each with a name. sum: at every root there is a tenant, and the tenants'
words add up to the words of a symbol. rows: a tenant's main rows have the degree 1 or 3, its main
words are a multiple of that degree and its mask words a multiple of 3. told: every tree that is
opened is a root that is told. range: no tree is longer than the range of the round that opens it.
alike: the sampled tenants of an opened tree belong to the same groups. oneGroup: beside a tenant
without a sample, to one group at most. once: a tree that holds a tenant without a sample is opened
once at most, in all three chains together. answered: "sampled" is said in two places, by a tenant's
flag and by the rounds' entries, and the two are held against each other, by one product a round. In
each chain the number of sample answers in the message behind a round is the number of tenants that
say "sampled" beneath the roots which that round sends, times that round's drawNZ, and no message
holds other answers; a round that sends such a tenant is of the kind "seeds" and its drawNZ is not
0; behind the chain's last round no answer is owed; and no tenant beneath a root that no round sends
says "sampled". sentOraclesMatchEntries: there are three lists of roots, and each holds as many roots as its chain's
entries send. inTime: a chain's own tree is opened in a round that is not in front of the round
which sends it, and, where one of its tenants says "sampled", behind that round (that the message of
the round behind holds the answers is answered's clause, not this one's); trees are taken over on
the last chain alone, from an earlier chain, which sends them. inOrder: the trees that one round
opens are declared in strictly rising order of their places (the chain that sent the tree, then its
number in that chain's order of sending): so no round opens a tree twice. `allClausesHold`: all eleven hold.
alike, oneGroup and once count as held at an opened tree that is not told: everyOpenedTreeIsListed is false then.
inTime takes a root that is sent and not told for one without a sample: everyOpenedTreeIsListed and sentOraclesMatchEntries are false
then.

Beside the clauses: `groupsFit`: a tenant that says "sampled" belongs to one group at least, and to
no more groups than its tree has openings in all three chains together; a tenant without a sample
belongs to none. IT IS NOT A CLAUSE OF `allClausesHold`: several makers of tenants tell every tenant with no
group, and `allClausesHold` would refuse their honest plans. It is written here so that each maker can hold its
own table against it.

Why the next message, and why the seeds. By the format page a message behind a round that samples
seeds begins with all answers, and answers stand nowhere else (R8.3; `Fmt.Round.ok`,
Fmt/Rules8.lean). A seed is a point and a factor that must not be 0, so at a round of the kind
"seeds" the entry's number of drawn elements that must not be 0 is the number of seeds. How many
elements such a round draws in all (drawE) is the format's own rule (`Fmt.Entry.fits`,
Fmt/Rules6Round.lean) and is not asked here. The verifier program draws as many seeds as the largest
number of answers that a shape in the prover's open message states, and takes each sampled message's
answers, as many as its shape states (OnBytes/Iop/Send.lean, `Send.verify`). The planner gives every
sampled message the setting's number (OnBytes/Params/Planner.lean, `planSend`).

A tenant's place (`TenantAt`): the chain that sent its tree, the root's number in that chain's order
of sending, the tenant's number in the leaf's order. `groupOfTree`: which of a block's groups of
columns is the opening of a tree behind one of the block's rounds: the groups stand round by round,
in each round the stored parts first, then the trees, as the round declares them.

Limits.
- The verifier program asks alike and oneGroup at the moment of each opening, of the groups joined
  so far. Here they are asked once, of the groups that the plan tells.
- That a root's log-length and words are the shape at every opening of its tree is not asked here.
- That the tenants told are those that the blocks lay, and that a block cuts a column by these
  words, is not asked here. That a `TenantAt` is the place of the message that a block means is its
  maker's word.
- The program's condition that the messages asked for are all the tenants of their trees has no
  counterpart: a declared round opens a tree, not messages. sum is what is left of it.
- groupsFit does not ask as many groups as openings: at both stored proof files' plans, as a
  harness read them off the verifier program's book, one tree of the shared chain is opened a second
  time by the last chain, and its tenant is told with the shared chain's one group.
- inOrder's order is by place. That it is the order in which a verifier's book lists the trees is
  not asked: no book is among the data.
- An entry says how many answers a message holds, not for which oracle message. So answered counts.
  One flag turned, either way, changes a count. Two flags beneath the roots of one round, turned
  against each other, change none: answered does not refuse them, and there are plans at which no
  clause of `allClausesHold` does. groupsFit would, since the tenant that now says no still belongs to a group;
  where the two tenants' groups are exchanged with their flags, not even that. A tenant of no words
  can bear the flag. That the message behind a sending answers THAT sending's samples, tenant by
  tenant, as the flags say, is the part of the block that takes the answers.
- Refused here, though they look honest: a plan in which a sampled message has fewer answers than
  there are seeds, which the program lets pass; the roots in one round and the seeds in the next; a
  round of seeds that marks a further element as other than 0.
- inTime asks "not in front of", not "in an earlier round": a tree may be opened at the positions
  drawn in the very round whose message holds its root, or its answers. That is in time only because
  a round's whole message stands in front of that round's draw (The data, above).
- inTime asks the order of rounds in one chain, and of chains by their numbers. That the last
  chain's draws hang on the earlier chains' messages is the compiler's matter.
- inTime, inOrder and groupsFit read whose tree an opening says it is ("own n", "taken (chain,
  sent)"). The columns that a block is handed are keyed by another number, the shape's tree number.
  No clause here reads it: that the two agree is asked above this file (`FileDescription.labelsOk`,
  Johnson/Desc/Block.lean). So the order is tested here only together with that test.
- No clause reads how many positions the opening round draws: a tree that is "opened" in a round
  which draws none is opened at nothing and passes.
- alike compares the lists of groups as they are written: [1, 2] and [2, 1] are not alike.
- `roundOfRoot` has the shape of `sendRound` in Johnson/Desc/Block.lean, which lies above this file.
- Stored tables have no tenants and are not looked at.
- No statement is proved here. Nothing on soundness. Not claimed: anything on hiding.

Terms: lean/GLOSSARY.md.

-/
import Decl.Declared
import Johnson.Desc.Oracle

set_option autoImplicit false

namespace VerifiableInference.Desc.BookPlan

/-- The three chains' declared rounds. -/
abbrev DeclaredRoundsByChain : Type := List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound

/-- For each chain, from 0, the roots that it sends itself, in the order of sending. -/
abbrev SentOraclesByChain : Type := List (List Oracle)

/-- One opening: the chain that sent the tree, the tree's number among those that this chain sent,
the shape that the opening round states, and the logarithm of that round's range. -/
structure Opening where
  chain : Nat
  sent : Nat
  shape : Fmt.Shape
  range : Nat

/-- All openings of trees, in the three chains' order. -/
def openings (D : DeclaredRoundsByChain) : List Opening :=
  [D.1, D.2.1, D.2.2].zipIdx.flatMap fun c => c.1.flatMap fun d => d.opens.map fun o =>
    match o.2 with
    | .own n => ⟨c.2, n, o.1, d.entry.logN⟩
    | .taken chain sent => ⟨chain, sent, o.1, d.entry.logN⟩

def rootOf (T : SentOraclesByChain) (o : Opening) : Option Oracle :=
  (T[o.chain]?).bind (·[o.sent]?)

/-- A condition on an opened tree's tenants: held where the tree is not told. -/
def onSymbolComponents (T : SentOraclesByChain) (o : Opening) (f : List SymbolComponent → Bool) : Bool :=
  ((rootOf T o).map fun r => f r.tenants).getD true

def sum (T : SentOraclesByChain) : Bool :=
  T.all fun c => c.all fun r =>
    !r.tenants.isEmpty && r.tenants.foldl (fun n t => n + t.main + t.mask) 0 == r.words

def rows (T : SentOraclesByChain) : Bool :=
  T.all fun c => c.all fun r => r.tenants.all fun t =>
    (t.degree == 1 || t.degree == 3) && t.main % t.degree == 0 && t.mask % 3 == 0

def everyOpenedTreeIsListed (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : Bool :=
  (openings D).all fun o => (rootOf T o).isSome

def range (D : DeclaredRoundsByChain) : Bool :=
  (openings D).all fun o => decide (o.shape.a ≤ o.range)

def alike (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : Bool :=
  (openings D).all fun o => onSymbolComponents T o fun l =>
    match (l.filter (·.sampled)).map (·.groups) with
    | [] => true
    | a :: r => r.all (· == a)

def oneGroup (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : Bool :=
  (openings D).all fun o => onSymbolComponents T o fun l =>
    l.all (·.sampled) || (l.filter (·.sampled)).all fun t => decide (t.groups.length ≤ 1)

def once (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : Bool :=
  (openings D).all fun o => onSymbolComponents T o fun l =>
    l.all (·.sampled) ||
      decide (((openings D).filter fun p => p.chain == o.chain && p.sent == o.sent).length ≤ 1)

/-- How many tenants beneath these roots say "sampled". -/
def saySampled (os : List Oracle) : Nat := (os.flatMap (·.tenants)).countP (·.sampled)

/-- answered, of one chain: its rounds from some round on; the roots that these rounds send, and
whatever is told behind them; due: the answers that the first of these rounds' messages owes. -/
def answeredIn : List Fmt.DeclaredRound → List Oracle → Nat → Bool
  | [], os, due => due == 0 && saySampled os == 0
  | d :: l, os, due =>
    let k := saySampled (os.take d.entry.roots)
    d.entry.answers == due &&
      (k == 0 || (d.entry.drawNZ != 0 && Fmt.kindOf d.entry.name == some .seeds)) &&
      answeredIn l (os.drop d.entry.roots) (k * d.entry.drawNZ)

def answered (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : Bool :=
  [D.1, D.2.1, D.2.2].zipIdx.all fun c => answeredIn c.1 ((T[c.2]?).getD []) 0

/-- Three lists of roots, each as long as its chain's entries send. -/
def sentOraclesMatchEntries (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : Bool :=
  T.length == 3 && [D.1, D.2.1, D.2.2].zipIdx.all fun c =>
    ((T[c.2]?).getD []).length == c.1.foldl (fun n d => n + d.entry.roots) 0

/-- The number of the round that sends root number n of a chain, both from 0. -/
def roundOfRoot : List Fmt.DeclaredRound → Nat → Option Nat
  | [], _ => none
  | d :: l, n =>
    if n < d.entry.roots then some 0 else (roundOfRoot l (n - d.entry.roots)).map (· + 1)

/-- Whether a tenant of the root (chain, root) says "sampled"; no, where the root is not told. -/
def holdsSampled (T : SentOraclesByChain) (chain root : Nat) : Bool :=
  ((T[chain]?).bind (·[root]?)).any fun r => r.tenants.any (·.sampled)

/-- No tree is opened in front of its sending, none with a sampled tenant in its sending round;
trees are taken over on the last chain alone, from an earlier chain that sends them. -/
def inTime (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : Bool :=
  [D.1, D.2.1, D.2.2].zipIdx.all fun c => c.1.zipIdx.all fun d => d.1.opens.all fun o =>
    match o.2 with
    | .own n => (roundOfRoot c.1 n).any fun i =>
        decide (i + (if holdsSampled T c.2 n then 1 else 0) ≤ d.2)
    | .taken chain sent => c.2 == 2 && decide (chain < 2) &&
        (roundOfRoot (([D.1, D.2.1, D.2.2][chain]?).getD []) sent).isSome

/-- The place of a tree that a round on the chain own opens: the chain that sent it, and its number
in that chain's order of sending. -/
def treePlace (own : Nat) : Fmt.TreeSource → Nat × Nat
  | .own n => (own, n)
  | .taken chain sent => (chain, sent)

/-- The first place stands before the second: an earlier chain, or an earlier root of one chain. -/
def earlierPlace (a b : Nat × Nat) : Bool :=
  decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 < b.2))

/-- Each place stands before the next. -/
def risingPlaces : List (Nat × Nat) → Bool
  | a :: b :: l => earlierPlace a b && risingPlaces (b :: l)
  | _ => true

/-- inOrder, of one chain. -/
def inOrderIn (own : Nat) (ds : List Fmt.DeclaredRound) : Bool :=
  ds.all fun d => risingPlaces (d.opens.map fun o => treePlace own o.2)

/-- In every round the opened trees' places rise strictly. -/
def inOrder (D : DeclaredRoundsByChain) : Bool := inOrderIn 0 D.1 && inOrderIn 1 D.2.1 && inOrderIn 2 D.2.2

/-- A sampled tenant belongs to one group at least and to no more than its tree has openings; a
tenant without a sample to none. NOT A CLAUSE OF `allClausesHold`. -/
def groupsFit (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : Bool :=
  T.zipIdx.all fun c => c.1.zipIdx.all fun r =>
    let n := ((openings D).filter fun o => o.chain == c.2 && o.sent == r.2).length
    r.1.tenants.all fun t =>
      if t.sampled then !t.groups.isEmpty && decide (t.groups.length ≤ n) else t.groups.isEmpty

/-- The eleven clauses by name. `groupsFit` is not among them (the head says why). -/
def clauses (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : List (String × Bool) :=
  [("sum", sum T), ("rows", rows T), ("told", everyOpenedTreeIsListed D T), ("range", range D), ("alike", alike D T),
   ("oneGroup", oneGroup D T), ("once", once D T), ("answered", answered D T),
   ("allTold", sentOraclesMatchEntries D T), ("inTime", inTime D T), ("inOrder", inOrder D)]

/-- **The tests on the plan for the trees' tenants and openings**: all eleven hold. -/
def allClausesHold (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : Bool := (clauses D T).all (·.2)

/-! ## Where a tenant lies, and where its tree's opening stands among a block's groups -/

/-- A tenant's place. -/
structure TenantAt where
  /-- the chain that sent its tree, from 0 -/
  chain : Nat
  /-- the root's number in that chain's order of sending, from 0 -/
  root : Nat
  /-- its number in the leaf's order, from 0 -/
  tenant : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The oracle message at a tenant's place. Nothing unless the root is told and has that tenant. -/
def oracleOfTenant (T : SentOraclesByChain) (x : TenantAt) : Option Oracle :=
  ((T[x.chain]?).bind (·[x.root]?)).bind fun o =>
    if x.tenant < o.tenants.length then some o else none

/-- Whether a declared opening, on the chain own (from 0), is of the tree (chain, root). -/
def opensTree (own chain root : Nat) : Fmt.TreeSource → Bool
  | .own n => own == chain && n == root
  | .taken c sent => c == chain && sent == root

/-- **The number, from 0, of the group that is the opening of the tree (chain, root) behind round
number round of the rounds ds**, which stand on the chain own. Nothing if there is no such round, or
it does not open that tree. -/
def groupOfTree (own : Nat) (ds : List Fmt.DeclaredRound) (round chain root : Nat) : Option Nat :=
  (ds[round]?).bind fun d =>
    let i := d.opens.findIdx fun o => opensTree own chain root o.2
    if i < d.opens.length then
      some ((ds.take round).foldl (fun n r => n + r.stored.length + r.opens.length) 0 +
        d.stored.length + i)
    else none

end VerifiableInference.Desc.BookPlan
