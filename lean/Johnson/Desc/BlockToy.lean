-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/BlockToy.lean: controls of Johnson/Desc/Block.lean, evaluated at a toy (`#guard`).

The toy. The instance: a number, WHICH IS WHAT IS ASKED: its public part is empty, so no block sees
it. The carried record: a running total, a link's own part (the list of what was heard in the link,
or nothing between links), and a count of claims made. Seven kinds of block. `hear n`: n rounds,
each of which draws one position; it lays the positions into the link's part and CLAIMS them IN TWO
NAMED RUNS, the first one and the rest, each marking the record in its own way and each asking the
number of claims gathered before it; and it has ONE RUN BEHIND THE BATCHING, which adds 1000 to the
total and refuses at a total of 0. `batch claims`: one round that draws one position σ; IT IS HANDED
THE LINK's CLAIMS AS ONE FUNCTION and adds σ times their sum to the total. `look`: a round that
sends one root, of a tree of depth 3 and width 1, and a round that draws one position AND OPENS THAT
TREE; it adds the opened column's first word to the total. `ask`: one round that sends one element
of the extension field and draws nothing; it asks that the total is odd, and that it is shown no
sealed digest. The last test compares the total with the instance. `table`: it opens a part of a
stored table. `send`, `peek`: the second chain sends a tree of its own, and opens it together with
the tree that is taken over from the shared chain. The file: the first chain: a front that asks
nothing, a link (hear 2 · batch), then the seal; the shared chain: such a front · look · table; the
second chain: such a front, a link (hear 1 · batch · send · peek · ask), an end that asks nothing.

The tests. The declared rounds and the table of places come out of the one text. The readings under
the target document's names; `Block.reads`. A yes. The verifier's no, named with its chain, its
block and the test that refused. The claims reach the batching; a claim that refuses. The order of
the runs is the link's datum: another order; a run left out, doubled, unknown; two runs of one name
in one block; claims in a place where nobody gathers them. The runs behind the batching: run by the
frame, in the link's order; one that refuses; one left out, doubled, unknown. The three chains'
states: the shared chain starts blind to the first chain's end; the second chain's start takes both
ends, and refuses where the first chain's link was not cleared. THE READS, HELD BY THE FOLD: a
column at another position; under another key; of another width; none; one too many. A part of a
stored table: another item's key, another position, width, word. A tree taken over and the third
chain's own tree: both under the key 0, told apart by their order; another key; one lacking. THE
ROUNDS, HELD BY THE FOLD: a round that drew a position more than its entry says; a message with an
item more; with another item; a round that shows a root, which no view does. No kind is shown a
sealed digest. A word not below the prime: in an item, in a column, in a drawn element. The tests on
the plan: a block's own; `oracles` that do not fit the roots; `oracles` that part from the shape at
the opening. a tree that is sent and opened nowhere; a stored part of another depth than the
table's; the file's own test; a tree's label against its source; the plan's entries against the
blocks'. The test on the instance. The last test. The seal: the first view is handed without it. Two
blocks as one. A block lifted to a wider record; onto a part that is there only at times. A block
whose own record is born and dies inside it. Further breakings of the frame.
And: the tests behind the adding, in
front of the runs behind the batching; the test behind each run of claims; a chain's first and last
block; the table of places and what is owed in `before`, both beside the tests on the plan; the
widths and a stored part's label; a tree declared twice. `offSeal`.

Limits: a toy. No block of the protocol.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.BlockToy

/-- The carried record. -/
structure St where
  total : Nat
  own : Option (List Nat)
  claimed : Nat := 0

/-- The elements that a stretch's rounds drew: their first words. -/
def drawn (rs : List Fmt.RoundView) : List Nat := rs.flatMap (·.drawn.elems.map (·.1.toNat))

/-- The tree that the shared chain sends: depth 3, width 1, number 0. -/
def tree : Fmt.Shape := { a := 3, W := 1, tree := 0 }

/-- An oracle message with one tenant, which fills its symbol. sampled: it has a sample: a tree all
of whose tenants have one may be opened more than once. -/
def orc (x : Nat × Nat) (sampled : Bool := false) : Oracle :=
  ⟨x.1, x.2, [⟨x.2, 0, 1, sampled, []⟩]⟩

/-- The entry of a round that draws one element and sends nothing. -/
def drawD : Fmt.Entry := { name := "CS", drawE := 1 }
/-- The entry of a round that draws one position below 8 and sends nothing. -/
def drawT : Fmt.Entry := { name := "CS", poss := 1, logN := 3 }

/-- The kind "hear". refuses: its claims refuse. -/
def hear (chain link : Nat) (refuses : Bool := false) : Kind Nat St Nat := fun n =>
  { name := s!"hear {n}"
    place := ⟨chain, some link, 1, .K4⟩
    planOk := true
    rounds := List.replicate n { entry := drawD }
    oracles := List.replicate n []
    before := []
    decide := fun s rs _ =>
      named "hear.link-open" (s.own.map fun o => { s with own := some (o ++ drawn rs) })
    claims := [
      ("first", fun k s => do
        need "first.is-first" (k == 0)
        pure ((s.own.getD []).take 1, { s with claimed := s.claimed + 1 })),
      ("rest", fun k s => do
        need "rest.willing" !refuses
        need "rest.behind-first" (k == 1)
        pure ((s.own.getD []).drop 1, { s with claimed := 10 * s.claimed }))]
    after := [("mark", fun s => do
      need "mark.total-not-0" (s.total != 0)
      pure { s with total := s.total + 1000 })] }

/-- The kind "batch": it is handed the link's claims as one function. -/
def batch (chain link : Nat) : Kind (St → Except String (List Nat × St)) St Nat := fun claims =>
  { name := "batch"
    place := ⟨chain, some link, 2, .K9⟩
    planOk := true
    rounds := [{ entry := drawD }]
    oracles := [[]]
    before := []
    decide := fun s rs _ => do
      let x ← claims s
      match drawn rs with
      | [σ] => pure { x.2 with total := x.2.total + σ * x.1.foldl (· + ·) 0 }
      | _ => .error "batch.one-draw"
    claims := [], after := [] }

/-- The entry of a round that sends one root with a sampled tenant: it draws the sample's one seed.
-/
def sendS : Fmt.Entry := { name := "SEND seed", msg := 32, roots := 1, drawE := 1, drawNZ := 1 }
/-- The entry of the round behind it: its message is the one answer; it draws one position below 16,
a range wider than the tree's 8. -/
def openA : Fmt.Entry := { name := "CS", msg := 24, answers := 1, poss := 1, logN := 4 }

/-- The kind "look". says: what `oracles` says of its tree. ok: its own test on the plan. -/
def look (says : List (Nat × Nat) := [(3, 1)]) (ok : Bool := true) : Kind Unit St Nat := fun _ =>
  { name := "look"
    place := ⟨2, none, 0, .K2⟩
    planOk := ok
    rounds := [{ entry := sendS }, { entry := openA, opens := [(tree, .own 0)] }]
    oracles := [says.map (orc · true), []]
    before := []
    decide := fun s _ cols =>
      match cols with
      | [[(_, w :: _)]] => .ok { s with total := s.total + w.toNat }
      | _ => .error "look.one-column"
    claims := [], after := [] }

/-- The kind "table": one round that draws one position and opens A PART OF A STORED TABLE there
(depth 3, width 2, under the statement's item 0); it wants just that column, at position 3, with the
words 7, 7. -/
def table : Block St Nat :=
  { name := "table", place := ⟨2, none, 1, .K14⟩, planOk := true
    rounds := [{
      entry := drawT
      stored := [{ sh := { a := 3, W := 2, stored := true, tree := 0 }, salt := 0, item := 0
                   lo := 0, count := 1 }] }]
    oracles := [[]]
    before := []
    decide := fun s _ gs => (need "table.words" (gs == [[(3, [7, 7])]])).map fun _ => s
    claims := [], after := [] }

/-- The second chain's own tree: depth 2, width 1; its number is 1: behind the first chain's trees
(none) and the one that is taken over. -/
def tree₃ : Fmt.Shape := { a := 2, W := 1, tree := 1 }

/-- The kind "send": one round that sends the root of `tree₃`. -/
def send₃ : Block St Nat :=
  { name := "send", place := ⟨3, some 0, 4, .K1⟩, planOk := true
    rounds := [{ entry := { name := "CS", msg := 32, roots := 1 } }], oracles := [[orc (2, 1)]]
    before := []
    decide := fun s _ _ => .ok s
    claims := [], after := [] }

/-- The kind "peek": one round that draws one position and opens THE TREE TAKEN OVER FROM THE SHARED
CHAIN and the chain's own tree there: TWO GROUPS; both columns show under the key 0. -/
def peek : Block St Nat :=
  { name := "peek", place := ⟨3, some 0, 5, .K12⟩, planOk := true
    rounds := [{ entry := { name := "CS", poss := 1, logN := 3 }
                 opens := [(tree, .taken 1 0), (tree₃, .own 0)] }]
    oracles := [[]]
    before := [(3, 0)]
    decide := fun s _ gs =>
      (need "peek.two-groups" (gs == [[(6, [4])], [(2, [6])]])).map fun _ => s
    claims := [], after := [] }

/-- `peek` with other openings. -/
def peekAt (opens : List (Fmt.Shape × Fmt.TreeSource)) : Block St Nat :=
  { peek with rounds := [{ entry := { name := "CS", poss := 1, logN := 3 }, opens := opens }] }

/-- The kind "ask". -/
def ask : Kind Unit St Nat := fun _ =>
  { name := "ask"
    place := ⟨3, some 0, 6, .K10⟩
    planOk := true
    rounds := [{ entry := { name := "CS", msg := 24 } }]
    oracles := [[]]
    before := []
    decide := fun s rs _ => do
      need "ask.odd" (s.total % 2 == 1)
      need "ask.no-digest" (rs.all (·.drawn.digest.isNone))
      pure s
    claims := [], after := [] }

/-- A link. keeps: it does not clear its part. -/
def link (name : String) (chain n : Nat) (close : List (Block St Nat)) (keeps refuses : Bool)
    (order : List (Nat × String) := [(0, "first"), (0, "rest")])
    (orderAfter : List (Nat × String) := [(0, "mark")])
    (tests : St → Except String Unit := fun _ => .ok ())
    (each : Nat × String → List Nat → St → Except String Unit := fun _ _ _ => .ok ()) :
    Link St Nat :=
  { name := name, chain := chain, number := 0
    lay := fun s => (need "no link is open" s.own.isNone).map fun _ => { s with own := some [] }
    hear := [hear chain 0 refuses n]
    order := order
    each := each
    orderAfter := orderAfter
    batch := batch chain 0
    tests := tests
    close := close
    clear := fun s => .ok (if keeps then s else { s with own := none }) }

/-- The seal's block: one round that sends and draws nothing. -/
def sealB : Block St Nat :=
  { name := "seal", place := ⟨1, none, 0, .frame⟩, planOk := true
    rounds := [{ entry := { name := "SEAL" } }]
    oracles := [[]], before := [], decide := fun s _ _ => .ok s, claims := [], after := [] }

/-- A chain's front here: a block that asks nothing. -/
def frontQ (chain : Nat) : Block St Nat := roundlessBlock s!"front {chain}" chain none 8 .ok
/-- The second chain's end here: a block without a round that asks nothing. -/
def endQ : Block St Nat := roundlessBlock "end 3" 3 none 9 .ok

/-- The entry of a round that sends one root and draws nothing. -/
def sendR : Fmt.Entry := { name := "CS", msg := 32, roots := 1 }

/-- The made plan's own declared rounds, as a planner would write them. -/
def thePlans : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound :=
  ([{ entry := drawD }, { entry := drawD }, { entry := drawD }, { entry := { name := "SEAL" } }],
    [{ entry := sendS }, { entry := openA, opens := [(tree, .own 0)] },
      { entry := drawT
        stored := [{ sh := { a := 3, W := 2, stored := true, tree := 0 }, salt := 0, item := 0
                     lo := 0, count := 1 }] }],
    [{ entry := drawD }, { entry := drawD }, { entry := sendR },
      { entry := drawT, opens := [(tree, .taken 1 0), (tree₃, .own 0)] },
      { entry := { name := "CS", msg := 24 } }])

/-- The table of places, as a driver would write it off the plan: place, number of rounds. -/
def theWanted : List (Place × Nat) :=
  [(⟨1, none, 8, .frame⟩, 0), (⟨1, some 0, 0, .frame⟩, 0), (⟨1, some 0, 1, .K4⟩, 2),
    (⟨1, some 0, 2, .K9⟩, 1), (⟨1, some 0, 3, .frame⟩, 0), (⟨1, some 0, 4, .frame⟩, 0),
    (⟨1, none, 0, .frame⟩, 1),
    (⟨2, none, 8, .frame⟩, 0), (⟨2, none, 0, .K2⟩, 2), (⟨2, none, 1, .K14⟩, 1),
    (⟨3, none, 8, .frame⟩, 0), (⟨3, some 0, 0, .frame⟩, 0), (⟨3, some 0, 1, .K4⟩, 1),
    (⟨3, some 0, 2, .K9⟩, 1), (⟨3, some 0, 3, .frame⟩, 0), (⟨3, some 0, 4, .K1⟩, 1),
    (⟨3, some 0, 5, .K12⟩, 1), (⟨3, some 0, 6, .K10⟩, 1), (⟨3, some 0, 7, .frame⟩, 0),
    (⟨3, none, 9, .frame⟩, 0)]

/-- The file's description. The shared chain starts blind to the first chain's end; the second
chain's start takes both ends' totals, and refuses if the first chain's link was not cleared. -/
def F (keeps refuses : Bool := false) (says : List (Nat × Nat) := [(3, 1)]) (ok : Bool := true)
    (fin : Nat → St → St → St → Bool := fun x _ _ s =>
      s.total == x && s.own.isNone && s.claimed == 110)
    (plans : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound := thePlans)
    (shared : Option (List (Block St Nat)) := none)
    (order : List (Nat × String) := [(0, "first"), (0, "rest")]) (depth : Nat := 3)
    (fileOk : Bool := true) (second : List (Block St Nat) := [send₃, peek, ask ()])
    (orderAfter : List (Nat × String) := [(0, "mark")])
    (tests : St → Except String Unit := fun _ => .ok ()) (wanted : List (Place × Nat) := theWanted)
    (owed : List (Place × List (Nat × Nat)) := [(⟨3, some 0, 5, .K12⟩, [(3, 0)])])
    (each : Nat × String → List Nat → St → Except String Unit := fun _ _ _ => .ok ()) :
    FileDescription Nat where
  S₁ := St
  S₂ := St
  S₃ := St
  Cl := Nat
  plans := plans
  tableDepth := depth
  wanted := wanted
  owed := owed
  fileOk := fileOk
  okStart := fun x => x != 0
  XiPub := Unit
  pub := fun _ => ()
  start₁ := fun _ => ⟨0, none, 0⟩
  start₂ := fun _ => ⟨0, none, 0⟩
  start₃ := fun _ s₁ s₂ =>
    (need "the first chain's link is cleared" s₁.own.isNone).map fun _ =>
      ⟨s₁.total + s₂.total, none, s₁.claimed⟩
  first := ⟨frontQ 1, [], [link "A" 1 2 [] keeps refuses order orderAfter tests each], [],
    sealB⟩
  shared := ⟨frontQ 2, shared.getD [look says ok ()], [], [], table⟩
  second := ⟨frontQ 3, [], [link "B" 3 1 second false false], [], endQ⟩
  fin := fin

/-- "ok", or the name under which a refusal came. -/
def why {α : Type} : Except String α → String
  | .ok _ => "ok"
  | .error e => e

/-- A round that drew the position p. -/
def rvP (p : Nat) : Fmt.RoundView := ⟨[], ⟨[], [p], [], none⟩⟩
/-- A round that drew the element x. -/
def rvD (x : UInt64) : Fmt.RoundView := ⟨[], ⟨[(x, 0, 0)], [], [], none⟩⟩
/-- A round that sent a root, as a view shows it: A VIEW's ROUND HOLDS NO ROOT. -/
def rvRoot : Fmt.RoundView := ⟨[], ⟨[], [], [], none⟩⟩
/-- A round that sent a root and drew one seed. -/
def rvRootS : Fmt.RoundView := ⟨[], ⟨[(5, 0, 0)], [], [], none⟩⟩
/-- A round whose message is one answer, and which drew the position p. -/
def rvPA (p : Nat) : Fmt.RoundView := ⟨[.answer (9, 0, 0)], ⟨[], [p], [], none⟩⟩
def rvE (x : UInt64 := 1) : Fmt.RoundView := ⟨[.e (x, 0, 0)], ⟨[], [], [], none⟩⟩

/-- Link A hears 1 and 10 and draws 2: the total is 22; behind the batching 1022. No sealing round.
-/
def v₁ : Fmt.View := ⟨[rvD 1, rvD 10, rvD 2], []⟩
/-- The shared chain sends a root, draws 12, which is 4 in the tree's range, and opens cols. -/
def v₂ (cols : List OpenedColumn := [(0, 4, [100])]) (st : List OpenedColumn := [(65536, 3, [7, 7])]) : Fmt.View :=
  ⟨[rvRootS, rvPA 12, rvP 3], cols ++ st⟩
/-- Link B starts at 1022 + 100, hears 5 and draws 3: 1137; behind the batching 2137. -/
def v₃ (cols : List OpenedColumn := [(0, 6, [4]), (0, 2, [6])]) (last : Fmt.RoundView := rvE) : Fmt.View :=
  ⟨[rvD 5, rvD 3, rvRoot, rvP 6, last], cols⟩

/-! one text, several readings -/
#guard F.roundsDeclaredByBlocks.1.map (·.entry.name) == ["CS", "CS", "CS", "SEAL"]
#guard F.roundsDeclaredByBlocks.2.1.map (fun r => (r.opens.length, r.stored.length)) == [(0, 0), (1, 0), (0, 1)]
#guard F.places.map (fun p => (p.1, p.2.1.chain, p.2.1.kind, p.2.2)) ==
  [("front 1", 1, .frame, 0), ("A: laid", 1, .frame, 0), ("hear 2", 1, .K4, 2),
    ("batch", 1, .K9, 1), ("A: behind the batching", 1, .frame, 0), ("A: cleared", 1, .frame, 0),
    ("seal", 1, .frame, 1), ("front 2", 2, .frame, 0), ("look", 2, .K2, 2), ("table", 2, .K14, 1),
    ("front 3", 3, .frame, 0), ("B: laid", 3, .frame, 0), ("hear 1", 3, .K4, 1),
    ("batch", 3, .K9, 1), ("B: behind the batching", 3, .frame, 0), ("send", 3, .K1, 1),
    ("peek", 3, .K12, 1), ("ask", 3, .K10, 1), ("B: cleared", 3, .frame, 0),
    ("end 3", 3, .frame, 0)]
#guard (look [(3, 1)] true ()).logLength 0 0 == some 3
#guard (look [(3, 1)] true ()).logLength 1 0 == none
#guard (look [(3, 1)] true ()).challengeBlocks 1 == some 1
#guard (look [(3, 1)] true ()).reads 0 [⟨[], [], [], none⟩, ⟨[], [12], [], none⟩] == [[(0, 4, 1)]]
#guard (look [(3, 1)] true ()).openings == 1
#guard table.reads 0 [⟨[], [11], [], none⟩] == [[(65536, 3, 2)]]
#guard F.lastChainFirstTreeNumber == 1
#guard peek.reads F.lastChainFirstTreeNumber [⟨[], [6], [], none⟩] == [[(0, 6, 1)], [(0, 2, 1)]]
#guard openedOwn F.roundsDeclaredByBlocks 1 == [(0, 3, 1), (0, 3, 1)]
#guard openedOwn F.roundsDeclaredByBlocks 2 == [(0, 2, 1)]
#guard F.planOk

/-! a yes; the verifier's no; the claims; the link's part -/
#guard F.say 2137 v₁ v₂ v₃ == "yes"
#guard F.run 2137 v₁ v₂ v₃
#guard F.say 2138 v₁ v₂ v₃ == "no: the ends fail the last test"
#guard !F.run 2138 v₁ v₂ v₃
#guard F.say 2137 ⟨[rvD 1, rvD 11, rvD 2], []⟩ v₂ v₃ == "no: the ends fail the last test"
#guard F.say 2137 v₁ (v₂ [(0, 4, [101])]) v₃ == "no: the second chain: refused at ask: ask.odd"
#guard (F (refuses := true)).say 2137 v₁ v₂ v₃ ==
  "no: the first chain: refused at batch: rest: rest.willing"
#guard (F (keeps := true)).say 2137 v₁ v₂ v₃ ==
  "no: the second chain's start: the first chain's link is cleared"

/-! the order of the claims' runs is the link's datum: another order marks the record otherwise; a
run left out, doubled, or unknown is refused on the plan alone -/
#guard (F (order := [(0, "rest"), (0, "first")])).say 2137 v₁ v₂ v₃ ==
  "no: the first chain: refused at batch: rest: rest.behind-first"
#guard (F (order := [(0, "first")])).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: A: laid"
#guard (F (order := [(0, "first"), (0, "rest"), (0, "rest")])).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: A: laid"
#guard (F (order := [(0, "first"), (0, "rest"), (1, "rest")])).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: A: laid"

/-! the runs behind the batching: the frame runs them, in the link's order (each adds 1000 here, and
refuses at a total of 0); a run left out or unknown is refused on the plan alone -/
#guard (F (orderAfter := [])).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: A: laid"
#guard (F (orderAfter := [(0, "mark"), (0, "mark")])).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: A: laid"
#guard (F (orderAfter := [(0, "mark"), (1, "mark")])).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: A: laid"
#guard F.say 2137 ⟨[rvD 0, rvD 0, rvD 2], []⟩ v₂ v₃ ==
  "no: the first chain: refused at A: behind the batching: mark: mark.total-not-0"

/-! two runs of one name in one block, as `andThen` can make them: refused on the plan alone,
whatever the order; claims where nobody gathers them -/
#guard !orderOk [Block.andThen "twice" (hear 1 0 false 1) (hear 1 0 false 1)]
  [(0, "first"), (0, "rest")]
#guard !orderOk [Block.andThen "twice" (hear 1 0 false 1) (hear 1 0 false 1)]
  [(0, "first"), (0, "rest"), (0, "first"), (0, "rest")]
#guard orderOk [hear 1 0 false 1, hear 1 0 false 1]
  [(0, "first"), (1, "first"), (0, "rest"), (1, "rest")]
#guard ((Chain.blocksInOrder ⟨frontQ 1, [hear 1 0 false 1], [], [], sealB⟩ : List (Block St Nat)).map
  (·.planOk)) == [true, false, true]
#guard ((Chain.blocksInOrder ⟨frontQ 1, [], [], [hear 1 0 false 1], sealB⟩ : List (Block St Nat)).map
  (·.planOk)) == [true, false, true]
#guard ((Chain.blocksInOrder ⟨hear 1 0 false 1, [], [], [], sealB⟩ : List (Block St Nat)).map
  (·.planOk)) == [false, true]
#guard ((Chain.blocksInOrder ⟨frontQ 1, [], [], [], hear 1 0 false 1⟩ : List (Block St Nat)).map
  (·.planOk)) == [true, false]
#guard ((Link.blocksInOrder (link "A" 1 1 [hear 1 0 false 1] false false)).head?.map (·.planOk)) ==
  some false
#guard ((Link.blocksInOrder (link "A" 1 1 [] false false)).head?.map (·.planOk)) == some true

/-! the reads, held by the fold -/
#guard F.say 2137 v₁ (v₂ [(0, 5, [100])]) v₃ == "no: the shared chain: refused at look: the columns"
#guard F.say 2137 v₁ (v₂ [(1, 4, [100])]) v₃ == "no: the shared chain: refused at look: the columns"
#guard F.say 2137 v₁ (v₂ [(0, 4, [100, 0])]) v₃ ==
  "no: the shared chain: refused at look: the columns"
#guard F.say 2137 v₁ (v₂ []) v₃ == "no: the shared chain: refused at look: the columns"
#guard F.say 2137 v₁ (v₂ [(0, 4, [100]), (0, 4, [100])]) v₃ ==
  "no: the shared chain: refused at table: the columns"
#guard F.say 2137 v₁ (v₂ [(0, 4, [100])] [(65536, 3, [7, 7]), (65536, 3, [7, 7])]) v₃ ==
  "no: the shared chain: left over: 0 rounds, 1 columns"

/-! a part of a stored table; a tree taken over; the third chain's keys -/
#guard F.say 2137 v₁ (v₂ [(0, 4, [100])] [(65537, 3, [7, 7])]) v₃ ==
  "no: the shared chain: refused at table: the columns"
#guard F.say 2137 v₁ (v₂ [(0, 4, [100])] [(65536, 2, [7, 7])]) v₃ ==
  "no: the shared chain: refused at table: the columns"
#guard F.say 2137 v₁ (v₂ [(0, 4, [100])] [(65536, 3, [7])]) v₃ ==
  "no: the shared chain: refused at table: the columns"
#guard F.say 2137 v₁ (v₂ [(0, 4, [100])] [(65536, 3, [7, 8])]) v₃ ==
  "no: the shared chain: refused at table: table.words"
#guard F.say 2137 v₁ v₂ (v₃ [(0, 2, [6]), (0, 6, [4])]) ==
  "no: the second chain: refused at peek: the columns"
#guard F.say 2137 v₁ v₂ (v₃ [(0, 6, [4]), (1, 2, [6])]) ==
  "no: the second chain: refused at peek: the columns"
#guard F.say 2137 v₁ v₂ (v₃ [(0, 6, [4])]) == "no: the second chain: refused at peek: the columns"

/-! the rounds, held by the fold -/
#guard F.say 2137 ⟨[rvD 1, ⟨[], ⟨[(10, 0, 0), (0, 0, 0)], [], [], none⟩⟩, rvD 2], []⟩ v₂ v₃ ==
  "no: the first chain: refused at hear 2: the rounds"
#guard F.say 2137 v₁ v₂ (v₃ (last := ⟨[.e (1, 0, 0), .e (1, 0, 0)], ⟨[], [], [], none⟩⟩)) ==
  "no: the second chain: refused at ask: the rounds"
#guard F.say 2137 v₁ v₂ (v₃ (last := ⟨[.answer (1, 0, 0)], ⟨[], [], [], none⟩⟩)) ==
  "no: the second chain: refused at ask: the rounds"

#guard F.say 2137 v₁ ⟨[⟨[.root ByteArray.empty], ⟨[], [], [], none⟩⟩, rvP 12, rvP 3],
  [(0, 4, [100]), (65536, 3, [7, 7])]⟩ v₃ == "no: the shared chain: refused at look: the rounds"

/-! no kind is shown a sealed digest: `ask` would refuse if it saw one -/
#guard F.say 2137 v₁ v₂ (v₃ (last := ⟨[.e (1, 0, 0)], ⟨[], [], [], some ByteArray.empty⟩⟩)) == "yes"

/-! a word not below the prime -/
#guard F.say 2137 v₁ v₂ (v₃ (last := rvE (1 + fieldPrimeWord))) ==
  "no: a word of the third view is not below the prime"
#guard F.say 2137 v₁ (v₂ [(0, 4, [100 + fieldPrimeWord])]) v₃ ==
  "no: a word of the second view is not below the prime"

#guard F.say 2137 ⟨[rvD 1, rvD 10, rvD fieldPrimeWord], []⟩ v₂ v₃ ==
  "no: a word of the first view is not below the prime"

/-! the tests on the plan; the test on the instance; the last test; the seal -/
#guard (F (ok := false)).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: look"
#guard (F (says := [])).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: look"
#guard (F (says := [(4, 1)])).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard (F (says := [(3, 2)])).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard (F (depth := 4)).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard (F (fileOk := false)).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: the file's"
-- the number in a tree's label against its source: an own tree's; a taken tree's; a source that no
-- chain may name
#guard (F (second := [send₃, peekAt [(tree, .taken 1 0), ({ tree₃ with tree := 2 }, .own 0)],
  ask ()])).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard (F (second := [send₃, peekAt [({ tree with tree := 1 }, .taken 1 0), (tree₃, .own 0)],
  ask ()])).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard !(F (second := [send₃, peekAt [(tree, .taken 1 0), (tree₃, .own 0),
  ({ tree₃ with tree := 0 }, .taken 2 0)], ask ()])).labelsOk
#guard F.say 0 v₁ v₂ v₃ == "no: the test on the instance"
#guard !F.run 0 v₁ v₂ v₃
#guard (F (plans := (thePlans.1.dropLast, thePlans.2))).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's"
#guard (F (plans := (thePlans.1, thePlans.2.1,
  thePlans.2.2.set 0 { entry := { name := "CS", poss := 2 } }))).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's"
-- a second tree of the shared chain, which nothing opens
#guard (F (shared := some [look [(3, 1)] true (), { send₃ with place := ⟨2, none, 5, .K1⟩ }])
  (plans := (thePlans.1, thePlans.2.1.take 2 ++ [{ entry := sendR }] ++ thePlans.2.1.drop 2,
    thePlans.2.2))).say 2137
  v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard (F (fin := fun _ _ _ _ => false)).say 2137 v₁ v₂ v₃ == "no: the ends fail the last test"
#guard F.say 2137 (withEmptySealRound v₁) v₂ v₃ == "no: the first chain: left over: 1 rounds, 0 columns"

/-! two blocks as one: the rounds and the groups are cut between them -/
#guard (F (shared := some [Block.andThen "look, in two"
  { look [(3, 1)] true () with
    rounds := [{ entry := sendS }], oracles := [[orc (3, 1) true]]
    decide := fun s _ gs => (need "no group" gs.isEmpty).map fun _ => s }
  { look [(3, 1)] true () with
    rounds := [{ entry := openA, opens := [(tree, .own 0)] }]
    oracles := [[]] }])).say 2137 v₁ v₂ v₃ == "yes"

/-- A block that draws one position, opens the tree there, and wants JUST ONE group. -/
def open1 (e : Fmt.Entry := { name := "CS", poss := 1, logN := 4 }) : Block St Nat :=
  { look [(3, 1)] true () with
    place := ⟨2, none, 2, .K2⟩
    rounds := [{ entry := e, opens := [(tree, .own 0)] }]
    oracles := [[]] }

#guard (F (plans := (thePlans.1, thePlans.2.1.take 2 ++
  [{ entry := { name := "CS", poss := 1, logN := 4 }, opens := [(tree, .own 0)] }] ++
  thePlans.2.1.drop 2, thePlans.2.2))
  (shared := some [{ look [(3, 1)] true () with
      rounds := [{ entry := sendS }]
      oracles := [[orc (3, 1) true]]
      decide := fun s _ _ => .ok s },
    Block.andThen "two looks" (open1 openA) open1])).say 2137 v₁
  ⟨[rvRootS, rvPA 12, rvP 5, rvP 3], [(0, 4, [60]), (0, 5, [40]), (65536, 3, [7, 7])]⟩ v₃ == "yes"

/-! a block lifted to a wider record: it turns its own part alone -/
/-- A block at `St`, lifted to `St × Nat`. -/
def up (b : Block St Nat) : Block (St × Nat) Nat := b.lift (·.1) fun t s => (s, t.2)

#guard ((up (ask ())).decide (⟨1, none, 0⟩, 9) [rvE] []).toOption.map
  (fun t => (t.1.total, t.2)) == some (1, 9)
#guard why ((up (ask ())).decide (⟨2, none, 0⟩, 9) [rvE] []) == "ask.odd"
#guard ((up (hear 1 0 false 1)).decide (⟨0, some [], 0⟩, 9) [rvD 4] []).toOption.map
  (fun t => (t.1.own, t.2)) == some (some [4], 9)
#guard (((up (hear 1 0 false 1)).claims.lookup "first").bind fun run =>
  (run 0 (⟨0, some [4, 5], 0⟩, 9)).toOption.map fun y => (y.1, y.2.1.claimed, y.2.2)) ==
  some ([4], 1, 9)

/-! a block lifted onto a part that is there only at times: where it is not, all three refuse -/
/-- A block at `St`, lifted to `Option St × Nat`. -/
def upPart (b : Block St Nat) : Block (Option St × Nat) Nat :=
  b.liftPart (·.1) fun t s => (some s, t.2)

#guard ((upPart (hear 1 0 false 1)).decide (some ⟨0, some [], 0⟩, 9) [rvD 4] []).toOption.map
  (fun t => (t.1.bind (·.own), t.2)) == some (some [4], 9)
#guard why ((upPart (hear 1 0 false 1)).decide (none, 9) [rvD 4] []) == "the part is not there"
#guard (((upPart (hear 1 0 false 1)).claims.lookup "first").map fun run => why (run 0 (none, 9))) ==
  some "the part is not there"
#guard (((upPart (hear 1 0 false 1)).after.lookup "mark").map fun run => why (run (none, 9))) ==
  some "the part is not there"
#guard (((upPart (hear 1 0 false 1)).after.lookup "mark").bind fun run =>
  (run (some ⟨5, none, 0⟩, 9)).toOption.map fun t => (t.1.map (·.total), t.2)) ==
  some (some 1005, 9)

/-! further breakings of the frame -/
-- a drawn position, a matrix entry, too many, below the prime
#guard F.say 2137 ⟨[rvD 1, ⟨[], ⟨[(10, 0, 0)], [1], [], none⟩⟩, rvD 2], []⟩ v₂ v₃ ==
  "no: the first chain: refused at hear 2: the rounds"
#guard F.say 2137 ⟨[rvD 1, ⟨[], ⟨[(10, 0, 0)], [], [1], none⟩⟩, rvD 2], []⟩ v₂ v₃ ==
  "no: the first chain: refused at hear 2: the rounds"
-- a block whose `decide` takes whatever comes, at a view without its column
#guard why (({ open1 with decide := fun s _ _ => .ok s } : Block St Nat).step 0 ⟨0, none, 0⟩
  [rvP 4] []) == "the columns"
#guard why (({ open1 with decide := fun s _ _ => .ok s } : Block St Nat).step 0 ⟨0, none, 0⟩
  [rvP 4] [(0, 4, [9])]) == "ok"

/-- A block over n rounds that draw nothing; it asks that it is shown just n rounds. -/
def wants (n : Nat) (ok : Bool := true) : Block St Nat :=
  { name := s!"wants {n}", place := ⟨1, none, 0, .K1⟩, planOk := ok
    rounds := List.replicate n { entry := { name := "ZERO" } }, oracles := List.replicate n []
    before := []
    decide := fun s rs _ => (need "wants.rounds" (rs.length == n)).map fun _ => s
    claims := [], after := [] }

/-- Three rounds that show and draw nothing. -/
def three : List Fmt.RoundView := [rvRoot, rvRoot, rvRoot]

-- `andThen` hands each block its own rounds, and keeps both tests on the plan
#guard why ((Block.andThen "x" (wants 1) (wants 2)).decide ⟨0, none, 0⟩ three []) == "ok"
#guard why ((Block.andThen "x" (wants 2) (wants 1)).decide ⟨0, none, 0⟩ three []) == "ok"
#guard why ((Block.andThen "x" (wants 1) (wants 1)).decide ⟨0, none, 0⟩ three []) ==
  "wants.rounds"
#guard !(Block.andThen "x" (wants 1) (wants 1 false)).planOk
#guard !(Block.andThen "x" (wants 1 false) (wants 1)).planOk
-- the frame's blocks' numbers in their link
#guard (F.places.filter fun p => p.2.1.chain == 3).map (fun p => p.2.1.piece) ==
  [8, 0, 1, 2, 3, 4, 5, 6, 7, 9]
-- the first and the shared chain's rounds against the plan's
#guard (F (plans := (thePlans.1.set 0 { entry := { name := "CS", poss := 2 } },
  thePlans.2))).say 2137
  v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard (F (plans := (thePlans.1, thePlans.2.1.set 1 { entry := { name := "CS", poss := 2 } },
  thePlans.2.2))).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: the file's"
-- every sort of item, and each of an element's three words
#guard viewWordsBelowPrime ⟨[⟨[.f 1, .answer (1, 1, 1), .e (1, 1, 1), .word fieldPrimeWord], ⟨[], [], [], none⟩⟩], []⟩
#guard !viewWordsBelowPrime ⟨[⟨[.f fieldPrimeWord], ⟨[], [], [], none⟩⟩], []⟩
#guard !viewWordsBelowPrime ⟨[⟨[.answer (fieldPrimeWord, 0, 0)], ⟨[], [], [], none⟩⟩], []⟩
#guard !viewWordsBelowPrime ⟨[⟨[.answer (0, fieldPrimeWord, 0)], ⟨[], [], [], none⟩⟩], []⟩
#guard !viewWordsBelowPrime ⟨[⟨[.answer (0, 0, fieldPrimeWord)], ⟨[], [], [], none⟩⟩], []⟩
#guard !viewWordsBelowPrime ⟨[⟨[.e (0, fieldPrimeWord, 0)], ⟨[], [], [], none⟩⟩], []⟩
#guard !viewWordsBelowPrime ⟨[⟨[.e (0, 0, fieldPrimeWord)], ⟨[], [], [], none⟩⟩], []⟩
#guard !viewWordsBelowPrime ⟨[⟨[], ⟨[(0, fieldPrimeWord, 0)], [], [], none⟩⟩], []⟩
#guard !viewWordsBelowPrime ⟨[⟨[], ⟨[(0, 0, fieldPrimeWord)], [], [], none⟩⟩], []⟩
-- the batching's own block may have neither claims nor runs behind the batching
#guard ((Link.blocksInOrder { link "A" 1 1 [] false false with
           batch := fun c => { batch 1 0 c with claims := [("own", fun _ s => .ok ([], s))] } }).head?.map
  (·.planOk)) == some false
#guard ((Link.blocksInOrder { link "A" 1 1 [] false false with
           batch := fun c => { batch 1 0 c with after := [("own", fun s => .ok s)] } }).head?.map
  (·.planOk)) == some false
-- a lift keeps the test on the plan, the rounds and the oracles
#guard !(up (look [(3, 1)] false ())).planOk
#guard (up (look [(3, 1)] true ())).rounds.length == 2
#guard (up (look [(3, 1)] true ())).oracles == [[orc (3, 1) true], []]
#guard !(upPart (look [(3, 1)] false ())).planOk
#guard (upPart (look [(3, 1)] true ())).rounds.length == 2
-- `oracles` one list too long
#guard !({ look [(3, 1)] true () with
  oracles := [[orc (3, 1) true], [], []] } : Block St Nat).shaped
-- the tenants' words against the symbol's; a root without a tenant
#guard !({ look [(3, 1)] true () with
  oracles := [[⟨3, 1, [⟨1, 1, 1, false, []⟩]⟩], []] } : Block St Nat).shaped
#guard !({ look [(3, 1)] true () with oracles := [[⟨3, 1, []⟩], []] } : Block St Nat).shaped
#guard ({ look [(3, 1)] true () with
  oracles := [[⟨3, 1, [⟨0, 1, 3, true, [2]⟩, ⟨0, 0, 1, false, []⟩]⟩], []] } : Block St Nat).shaped
#guard !({ look [(3, 1)] true () with
  oracles := [[⟨3, 1, [⟨1, 0, 2, false, []⟩]⟩], []] } : Block St Nat).shaped
-- two blocks at one place; a block that says another chain than the one in whose list it stands
#guard (F (second := [send₃, { peek with place := send₃.place }, ask ()])).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's"
#guard (F (second := [send₃, { peek with place := ⟨2, some 0, 5, .K12⟩ }, ask ()])).say 2137
  v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard F.placesOk
#guard (look [(3, 1)] true ()).shaped
-- two draws that fall on one position of the tree's range: one column
#guard groupsOf 0 [{ entry := { name := "CS", poss := 2 }, opens := [(tree, .own 0)] }]
  [⟨[], [12, 4], [], none⟩] == [[(0, 4, 1)]]
#guard groupsOf 0 [{ entry := { name := "CS", poss := 2 }, opens := [(tree, .own 0)] }]
  [⟨[], [5, 4], [], none⟩] == [[(0, 4, 1), (0, 5, 1)]]

/-! breakings that the same reader found to fail no guard of the form behind that one -/
/-- A block without a round that has runs behind the batching, and no claims. -/
def marks (runs : List (String × (St → Except String St))) : Block St Nat :=
  { roundlessBlock "marks" 1 (some 0) 9 .ok with after := runs }

-- a block with runs behind the batching alone, where nobody gathers them
#guard ((Link.blocksInOrder (link "A" 1 1 [marks [("m", .ok)]] false false)).head?.map (·.planOk)) ==
  some false
#guard ((Chain.blocksInOrder ⟨frontQ 1, [marks [("m", .ok)]], [], [], sealB⟩ : List (Block St Nat)).map
  (·.planOk)) == [true, false, true]
#guard ((Chain.blocksInOrder ⟨frontQ 1, [marks []], [], [], sealB⟩ : List (Block St Nat)).map
  (·.planOk)) == [true, true, true]
-- two such runs of one name
#guard !orderAfterOk [marks [("m", .ok), ("m", .ok)]] [(0, "m")]
#guard orderAfterOk [marks [("m", .ok), ("n", .ok)]] [(0, "n"), (0, "m")]
-- their order is the link's
#guard ((afterIn [marks [("inc", fun s => .ok { s with total := s.total + 1 }),
  ("dbl", fun s => .ok { s with total := 2 * s.total })]] [(0, "inc"), (0, "dbl")]
  ⟨5, none, 0⟩).toOption.map (·.total)) == some 12
#guard ((afterIn [marks [("inc", fun s => .ok { s with total := s.total + 1 }),
  ("dbl", fun s => .ok { s with total := 2 * s.total })]] [(0, "dbl"), (0, "inc")]
  ⟨5, none, 0⟩).toOption.map (·.total)) == some 11
-- `andThen`, `lift` and `liftPart` carry claims and runs on
#guard (Block.andThen "x" (hear 1 0 false 1) (marks [("m", .ok)])).after.map (·.1) == ["mark", "m"]
#guard (up (hear 1 0 false 1)).after.map (·.1) == ["mark"]
#guard (up (hear 1 0 false 1)).claims.map (·.1) == ["first", "rest"]
#guard (upPart (hear 1 0 false 1)).after.map (·.1) == ["mark"]
#guard (upPart (hear 1 0 false 1)).claims.map (·.1) == ["first", "rest"]
-- a block's own test on the plan, in the second chain
#guard (F (second := [send₃, { peek with planOk := false }, ask ()])).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: peek"
-- the second chain alone takes trees over
#guard !(F (shared := some [look [(3, 1)] true (), peekAt [(tree, .taken 0 0)]])).labelsOk
#guard F.labelsOk

/-! a block whose own record is born and dies inside it -/
/-- `wants 1` at a record of its own, a number, made of the total and laid back into it. -/
def within (b : Block Nat Nat) : Block St Nat :=
  b.inside (fun s => (need "enter.total-not-0" (s.total != 0)).map fun _ => s.total)
    fun s t => (need "leave.below-100" (decide (t < 100))).map fun _ => { s with total := t }

/-- A block at a number: it doubles it. -/
def twice (claims : List (String × (Nat → Nat → Except String (List Nat × Nat))) := []) :
    Block Nat Nat :=
  { name := "twice", place := ⟨1, none, 7, .K12⟩, planOk := true, rounds := [], oracles := []
    before := [], decide := fun t _ _ => .ok (2 * t), claims := claims, after := [] }

#guard ((within (twice)).decide ⟨5, none, 3⟩ [] []).toOption.map (fun s => (s.total, s.claimed)) ==
  some (10, 3)
#guard why ((within (twice)).decide ⟨0, none, 3⟩ [] []) == "enter.total-not-0"
#guard why ((within (twice)).decide ⟨50, none, 3⟩ [] []) == "leave.below-100"
#guard (within (twice)).planOk
#guard !(within (twice [("c", fun _ t => .ok ([], t))])).planOk

/-! fixed before the draw: asked on the plan alone -/
#guard F.beforeOk
-- the two places exchanged: the tree is then sent behind the draw that leans on it, and behind its
-- own opening: the book refuses that too, and its clause is the one that is named
#guard (F (second := [peek, send₃, ask ()]) (plans := (thePlans.1, thePlans.2.1,
  thePlans.2.2.take 2 ++ [thePlans.2.2[3]!, thePlans.2.2[2]!, thePlans.2.2[4]!]))).say 2137
  v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's: the book's inTime"
#guard !(F (second := [peek, send₃, ask ()])).beforeOk
-- a message that is never sent; of a chain that is not earlier; of an earlier chain that sends none
#guard !(F (second := [send₃, { peek with before := [(3, 1)] }, ask ()])).beforeOk
#guard !(F (shared := some [{ look [(3, 1)] true () with before := [(3, 0)] }])).beforeOk
#guard !(F (shared := some [{ look [(3, 1)] true () with before := [(1, 0)] }])).beforeOk
-- a message sent in the round of the draw itself stands in front of it
#guard sendRound [{ entry := drawD },
  { entry := { name := "CS", msg := 64, roots := 2 } }] 1 == some 1
#guard sendRound [{ entry := { name := "CS", msg := 64, roots := 2 } }] 2 == none
/-- A block that sends a root and draws in one and the same round, and names its own message. -/
def selfB : Block St Nat :=
  { send₃ with
    rounds := [{ entry := { name := "CS", msg := 32, roots := 1, poss := 1 } }]
    before := [(3, 0)] }

#guard beforeAt ([], [], selfB.rounds) ([], [], oraclesOf [selfB]) 2 0 [selfB]
-- a message of an earlier chain stands in front of every draw of a later chain, also the shared one
#guard beforeAt (send₃.rounds, (look [(3, 1)] true ()).rounds, [])
  (oraclesOf [send₃], oraclesOf [look [(3, 1)] true ()], []) 1 0
  [{ look [(3, 1)] true () with before := [(1, 0)] }]
#guard !beforeAt (send₃.rounds, (look [(3, 1)] true ()).rounds, [])
  (oraclesOf [send₃], oraclesOf [look [(3, 1)] true ()], []) 0 0 [{ send₃ with before := [(2, 0)] }]
#guard !beforeAt ([], [], send₃.rounds) ([], [], oraclesOf [send₃]) 2 0
  [{ send₃ with before := [(0, 0)] }]

/-- A round that sends a root; one whose message has a sample answer; one that draws a position. -/
def rSend : Fmt.DeclaredRound := { entry := { name := "CS", msg := 32, roots := 1 } }
def rAnswer : Fmt.DeclaredRound := { entry := { name := "CS", msg := 24, answers := 1 } }
def rDraw : Fmt.DeclaredRound := { entry := drawD }
/-- An oracle message whose one tenant is sampled. -/
def sampledO : Oracle := ⟨2, 1, [⟨1, 0, 1, true, []⟩]⟩
/-- A block over the given rounds that names the chain's first message. -/
def leans (rs : List Fmt.DeclaredRound) : Block St Nat :=
  { send₃ with rounds := rs, oracles := rs.map fun _ => [], before := [(1, 0)] }

-- a sampled message: its sample is answered in front of the draw; not at all; behind the draw
#guard beforeAt ([rSend, rAnswer, rDraw], [], []) ([sampledO], [], []) 0 0
  [leans [rSend, rAnswer, rDraw]]
#guard !beforeAt ([rSend, rDraw], [], []) ([sampledO], [], []) 0 0 [leans [rSend, rDraw]]
#guard !beforeAt ([rSend, rDraw, rAnswer], [], []) ([sampledO], [], []) 0 0
  [leans [rSend, rDraw, rAnswer]]
#guard beforeAt ([rSend, rDraw], [], []) ([orc (2, 1)], [], []) 0 0 [leans [rSend, rDraw]]
-- `andThen`, `lift`, `liftPart` and `inside` carry the list on
#guard (Block.andThen "x" selfB peek).before == [(3, 0), (3, 0)]
#guard (up peek).before == [(3, 0)]
#guard (upPart peek).before == [(3, 0)]
#guard (within { twice with before := [(1, 4)] }).before == [(1, 4)]

/-! a chain without a block; a description along a map of instances -/
#guard why (chainAt "x" 0 ([] : List (Block St Nat)) ⟨0, none, 0⟩ ⟨[], []⟩) == "x: it has no block"
#guard (F.pull fun p : Nat × Nat => p.1).say (2137, 0) v₁ v₂ v₃ == "yes"
#guard (F.pull fun p : Nat × Nat => p.1).say (2138, 0) v₁ v₂ v₃ ==
  "no: the ends fail the last test"
#guard (F.pull fun p : Nat × Nat => p.1).say (0, 2137) v₁ v₂ v₃ == "no: the test on the instance"

/-! who may share a tree, and where a tree may be opened: `BookPlan`'s clauses, through the plan -/
#guard F.treeSharingOk
/-- The file with other words on the shared chain's tree. -/
def FO (o : Oracle) : FileDescription Nat :=
  F (shared := some [{ look [(3, 1)] true () with oracles := [[o], []] }])

#guard (FO (orc (3, 1) true)).say 2137 v₁ v₂ v₃ == "yes"
-- a tree with a tenant without a sample, opened in two chains
#guard (FO (orc (3, 1))).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's: the book's once"
-- mask words that are no multiple of 3
#guard (FO ⟨3, 1, [⟨0, 1, 1, true, []⟩]⟩).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's: the book's rows"
-- two sampled tenants of other groups
#guard (FO ⟨3, 1, [⟨1, 0, 1, true, [0]⟩, ⟨0, 0, 1, true, [1]⟩]⟩).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's: the book's alike"
-- beside a tenant without a sample, a sampled one of two groups
#guard (FO ⟨3, 1, [⟨1, 0, 1, true, [0, 1]⟩, ⟨0, 0, 1, false, []⟩]⟩).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's: the book's oneGroup"
-- a tree that is longer than the range of the round that opens it
#guard (F (plans := (thePlans.1,
  thePlans.2.1.set 1 { entry := { openA with logN := 2 }, opens := [(tree, .own 0)] },
  thePlans.2.2)) (shared := some [{ look [(3, 1)] true () with
    rounds := [{ entry := sendS },
      { entry := { openA with logN := 2 }, opens := [(tree, .own 0)] }] }])).say 2137
  v₁ v₂ v₃ == "no: the tests on the plan: the file's: the book's range"
-- a sampled message of an earlier chain, named in `before`: its sample is answered there: a yes,
-- through the whole test on the plan
#guard (F (second := [send₃, { peek with before := [(2, 0), (3, 0)] }, ask ()])).say 2137
  v₁ v₂ v₃ == "yes"
#guard (F (second := [send₃, { peek with before := [(2, 0), (3, 0)] }, ask ()])).beforeOk
-- a message that the earlier chain never sends
#guard (F (second := [send₃, { peek with before := [(2, 1), (3, 0)] }, ask ()])).say 2137
  v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard !(F (second := [send₃, { peek with before := [(2, 1), (3, 0)] }, ask ()])).beforeOk

/-! a drawn position is below the range that the round's entry states -/
-- 12 is below 16, the entry's range, and is 4 in the tree's range of 8: taken (the yes above);
-- 12 + 16 is 4 in the tree's range too, and its column is the same: refused by the fold
#guard F.say 2137 v₁ ⟨[rvRootS, rvPA 28, rvP 3], [(0, 4, [100]), (65536, 3, [7, 7])]⟩ v₃ ==
  "no: the shared chain: refused at look: the rounds"
-- a position more than the entry says, both in the range
#guard F.say 2137 v₁ ⟨[rvRootS, ⟨[.answer (9, 0, 0)], ⟨[], [12, 3], [], none⟩⟩, rvP 3],
  [(0, 4, [100]), (65536, 3, [7, 7])]⟩ v₃ == "no: the shared chain: refused at look: the rounds"
#guard roundsFit [{ entry := openA }] [rvPA 15]
#guard !roundsFit [{ entry := openA }] [rvPA 16]

/-! a tenant that says "sampled" has its answer in the very next message, and no other message has
answers: `BookPlan`'s clause, through the plan -/
-- the tree's tenant says that it has no sample, and the next message holds an answer
#guard (BookPlan.clauses (FO (orc (3, 1))).roundsDeclaredByBlocks (FO (orc (3, 1))).roots).filterMap
  (fun c => if c.2 then none else some c.1) == ["once", "answered"]
-- the round behind the sending holds no answer
#guard (F (plans := (thePlans.1,
  thePlans.2.1.set 1 { entry := { openA with msg := 0, answers := 0 }, opens := [(tree, .own 0)] },
  thePlans.2.2)) (shared := some [{ look [(3, 1)] true () with
    rounds := [{ entry := sendS },
      { entry := { openA with msg := 0, answers := 0 }, opens := [(tree, .own 0)] }] }])).say 2137
  v₁ v₂ v₃ == "no: the tests on the plan: the file's: the book's answered"

/-! a matrix entry that a round drew is -1, 0 or 1 -/
#guard roundsFit [{ entry := { name := "CS", trits := 3 } }] [⟨[], ⟨[], [], [-1, 0, 1], none⟩⟩]
#guard !roundsFit [{ entry := { name := "CS", trits := 1 } }] [⟨[], ⟨[], [], [2], none⟩⟩]
#guard !roundsFit [{ entry := { name := "CS", trits := 1 } }] [⟨[], ⟨[], [], [-2], none⟩⟩]

/-! a drawn element that the entry marks as never 0 is not 0: which these are is the format's word
-/
-- the one seed's factor is 0
#guard F.say 2137 v₁ ⟨[⟨[], ⟨[(0, 0, 0)], [], [], none⟩⟩, rvPA 12, rvP 3],
  [(0, 4, [100]), (65536, 3, [7, 7])]⟩ v₃ == "no: the shared chain: refused at look: the rounds"
-- a plain element may be 0 (link A hears 0 and 0: the rounds fit; the no comes at the run "mark")
#guard roundsFit [{ entry := drawD }] [rvD 0]
-- a round of seeds, two seeds of one coordinate each: coordinate, factor, coordinate, factor
/-- Such an entry. -/
def seeds2 : Fmt.Entry := { name := "SEND seed", drawE := 4, drawNZ := 2 }
/-- A round that drew these four elements' first words. -/
def rv4 (a b c d : UInt64) : Fmt.RoundView :=
  ⟨[], ⟨[(a, 0, 0), (b, 0, 0), (c, 0, 0), (d, 0, 0)], [], [], none⟩⟩
#guard roundsFit [{ entry := seeds2 }] [rv4 0 1 0 1]
#guard !roundsFit [{ entry := seeds2 }] [rv4 1 0 1 1]
#guard !roundsFit [{ entry := seeds2 }] [rv4 1 1 1 0]
-- another kind, the same numbers: the last two
#guard roundsFit [{ entry := { seeds2 with name := "CS" } }] [rv4 0 0 1 1]
#guard !roundsFit [{ entry := { seeds2 with name := "CS" } }] [rv4 0 1 0 1]
-- an element is 0 only if all its three words are
#guard roundsFit [{ entry := sendS }] [⟨[], ⟨[(0, 0, 1)], [], [], none⟩⟩]
-- a name that the format does not know
#guard !roundsFit [{ entry := { name := "NO SUCH ROUND" } }] [⟨[], ⟨[], [], [], none⟩⟩]

/-! what a round reads, held against what its entry draws -/
/-- A part of the stored table under the statement's item `item`: from the draw number lo on, count
draws. -/
def part (lo count : Nat) (stored : Bool := true) (item : Nat := 0) : Fmt.Stored :=
  { sh := { a := 3, W := 2, stored := stored, tree := 0 }, salt := 0, item := item, lo := lo
    count := count }
/-- An entry that draws n positions below 8. -/
def drawsN (n : Nat) : Fmt.Entry := { drawT with poss := n }

#guard readsFit { entry := drawD }
#guard readsFit { entry := drawT, opens := [(tree, .own 0)] }
#guard readsFit { entry := drawsN 2, stored := [part 0 1, part 1 1 true 1] }
-- two parts of one table; the two tables exchanged
#guard !readsFit { entry := drawsN 2, stored := [part 0 1, part 1 1] }
#guard !readsFit { entry := drawsN 2, stored := [part 0 1 true 1, part 1 1] }
-- all positions drawn, nothing read
#guard !readsFit { entry := drawT }
-- an opening, or a stored part, at a round that draws no position
#guard !readsFit { entry := drawD, opens := [(tree, .own 0)] }
#guard !readsFit { entry := drawD, stored := [part 0 0] }
-- one query in the place of two; a part beyond the draws; parts that overlap; a gap; an empty part
#guard !readsFit { entry := drawsN 2, stored := [part 0 1] }
#guard !readsFit { entry := drawT, stored := [part 1 1] }
#guard !readsFit { entry := drawsN 2, stored := [part 0 1, part 0 1 true 1] }
#guard !readsFit { entry := drawsN 3, stored := [part 0 1, part 2 1 true 1] }
#guard !readsFit { entry := drawT, stored := [part 0 1, part 1 0 true 1] }
-- a stored part beside a tree; a stored part that says it is a tree
#guard !readsFit { entry := drawT, stored := [part 0 1], opens := [(tree, .own 0)] }
#guard !readsFit { entry := drawT, stored := [part 0 1 false] }
-- a stored part that is deeper than the round's range; a tree that says it is stored
#guard !readsFit { entry := { drawT with logN := 2 }, stored := [part 0 1] }
#guard !readsFit { entry := drawT, opens := [({ tree with stored := true }, .own 0)] }
-- through the plan: ONE READ DROPPED: the table's round draws two positions, as the plan says, and
-- reads at one: readsOk says no (that every other test on the plan says yes: held by no guard)
/-- The file whose table's round draws two positions and reads the parts ps. -/
def FR (ps : List Fmt.Stored) : FileDescription Nat :=
  { F (plans := (thePlans.1, thePlans.2.1.set 2 { entry := drawsN 2, stored := ps },
      thePlans.2.2)) with
    shared := ⟨frontQ 2, [look [(3, 1)] true ()], [], [],
      { table with rounds := [{ entry := drawsN 2, stored := ps }] }⟩ }
#guard (FR [part 0 1, part 1 1 true 1]).planOk
#guard !(FR [part 0 1]).readsOk
#guard (FR [part 0 1]).say 2137 v₁ v₂ v₃ == "no: the tests on the plan: the file's"
#guard F.readsOk

/-! which trees a round opens is held against the plan's own declared rounds -/
-- ONE TREE OF SEVERAL DROPPED, at a round that draws and still reads; another round opens that tree
-- too: every other test on the plan says yes
#guard (F (second := [send₃, peekAt [(tree₃, .own 0)], ask ()])).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's"
#guard (F (second := [send₃, peekAt [(tree₃, .own 0)], ask ()])
  (plans := (thePlans.1, thePlans.2.1,
    thePlans.2.2.set 3 { entry := drawT, opens := [(tree₃, .own 0)] }))).planOk
-- the two trees in the other order: they part from the plan's declared rounds, and the book's own
-- clause on the order of a round's openings refuses too: its name is the one that is said
#guard (F (second := [send₃, peekAt [(tree₃, .own 0), (tree, .taken 1 0)], ask ()])).say 2137
  v₁ v₂ v₃ == "no: the tests on the plan: the file's: the book's inOrder"

-- a label that parts from its source, IN THE PLAN's DECLARED ROUNDS TOO: `labelsOk` alone refuses
/-- The taken tree under the number 5. -/
def ops5 : List (Fmt.Shape × Fmt.TreeSource) :=
  [({ tree with tree := 5 }, .taken 1 0), (tree₃, .own 0)]
#guard (F (second := [send₃, peekAt ops5, ask ()]) (plans := (thePlans.1, thePlans.2.1,
  thePlans.2.2.set 3 { entry := drawT, opens := ops5 }))).say 2137 v₁ v₂ v₃ ==
  "no: the tests on the plan: the file's"

/-! the first chain's last block has a round -/
#guard F.sealLast
/-- The file with a block without a round behind the seal's block. -/
def FS : FileDescription Nat :=
  { F with first := { F.first with
      back := [sealB], last := roundlessBlock "behind the seal" 1 none 1 .ok } }
#guard !FS.sealLast
#guard FS.planOkCore
#guard FS.say 2137 v₁ v₂ v₃ == "no: the tests on the plan: the file's"

/-! THE LINK's TESTS, A CHAIN's FIRST AND LAST BLOCK, THE TABLE OF PLACES -/

/-! the tests behind the adding: the frame runs them, in front of the runs behind the batching -/
-- they see the total as the batching left it (22), not as the run "mark" leaves it (1022)
#guard (F (tests := fun s => need "t.22" (s.total == 22))).say 2137 v₁ v₂ v₃ == "yes"
#guard (F (tests := fun s => need "t.1022" (s.total == 1022))).say 2137 v₁ v₂ v₃ ==
  "no: the first chain: refused at A: behind the batching: the tests behind the adding: t.1022"

/-! the test behind each run of claims: it is handed the run's name, ITS OWN list, the record behind
it (link A hears 1 and 10: the run "first" claims [1], the run "rest" [10]) -/
#guard (F (each := fun o cl s => need "each" ((o, cl, s.claimed) == ((0, "first"), [1], 1) ||
  (o, cl, s.claimed) == ((0, "rest"), [10], 10)))).say 2137 v₁ v₂ v₃ == "yes"
#guard (F (each := fun o cl _ => need "each.short" (o.2 != "rest" || cl.length == 2))).say 2137
  v₁ v₂ v₃ == "no: the first chain: refused at batch: rest: behind the run: each.short"
#guard (F (each := fun o _ _ => need "each.first" (o.2 != "first"))).say 2137
  v₁ v₂ v₃ == "no: the first chain: refused at batch: first: behind the run: each.first"
-- `claimsIn` is the same with no such test
#guard ((claimsIn [hear 1 0 false 2] [(0, "first"), (0, "rest")] ⟨0, some [1, 10], 0⟩).toOption.map
  (·.1)) == some [1, 10]

/-! a chain's first and last block stand in its flat list, at its two ends -/
#guard (F.first.blocksInOrder.map (·.name)).head? == some "front 1"
#guard (F.first.blocksInOrder.map (·.name)).getLast? == some "seal"
#guard ({ F with first := { F.first with first := { frontQ 1 with planOk := false } } }).say 2137
  v₁ v₂ v₃ == "no: the tests on the plan: front 1"
#guard ({ F with second := { F.second with last := { endQ with planOk := false } } }).say 2137
  v₁ v₂ v₃ == "no: the tests on the plan: end 3"
#guard ({ F with second := { F.second with last := { endQ with
    decide := fun _ _ _ => .error "end.no" } } }).say 2137
  v₁ v₂ v₃ == "no: the second chain: refused at end 3: end.no"

/-! a block, and a chain without links, at another type of claims -/
#guard ((look [(3, 1)] true ()).retype : Block St Unit).planOk
#guard !((look [(3, 1)] false ()).retype : Block St Unit).planOk
#guard !((hear 1 0 false 1).retype : Block St Unit).planOk
#guard ((peek.retype : Block St Unit).name, (peek.retype : Block St Unit).place,
  (peek.retype : Block St Unit).rounds, (peek.retype : Block St Unit).before) ==
  (peek.name, peek.place, peek.rounds, peek.before)
#guard ((look [(3, 1)] true ()).retype : Block St Unit).oracles == (look [(3, 1)] true ()).oracles
#guard ((marks [("m", .ok)]).retype : Block St Unit).after.map (·.1) == ["m"]
#guard why ((table.retype : Block St Unit).decide ⟨0, none, 0⟩ [] [[(3, [7, 7])]]) == "ok"
#guard why ((table.retype : Block St Unit).decide ⟨0, none, 0⟩ [] [[(3, [7, 8])]]) == "table.words"
#guard ((F.shared.retype : Chain St Unit).blocksInOrder.map fun b => (b.name, b.planOk)) ==
  [("front 2", true), ("look", true), ("table", true)]
#guard (({ F.shared with back := [endQ] }.retype : Chain St Unit).blocksInOrder.map (·.name)) ==
  ["front 2", "look", "end 3", "table"]
#guard ((F.first.retype : Chain St Unit).blocksInOrder.map fun b => (b.name, b.planOk)) ==
  [("front 1", false), ("seal", true)]

/-! the table of places, beside the tests on the plan -/
#guard F.wantedOk
#guard F.sentFit
-- a block without a round more than the table has; and, against a table that has it, one struck
/-- The file with one more block without a round behind the second chain's link. -/
def FQ (wanted : List (Place × Nat) := theWanted) : FileDescription Nat :=
  { F (wanted := wanted) with
    second := { F.second with back := [roundlessBlock "more" 3 none 5 .ok] } }
/-- The table that has that block's row. -/
def wantedQ : List (Place × Nat) := theWanted.dropLast ++ [(⟨3, none, 5, .frame⟩, 0)] ++
  theWanted.drop (theWanted.length - 1)
#guard FQ.planOk
#guard !FQ.wantedOk
#guard (FQ wantedQ).wantedOk
#guard (F (wanted := wantedQ)).planOk
#guard !(F (wanted := wantedQ)).wantedOk
-- a table with a row more at its end; with its last row less
#guard !(F (wanted := theWanted ++ [(⟨3, none, 5, .frame⟩, 0)])).wantedOk
#guard !(F (wanted := theWanted.dropLast)).wantedOk
-- A ROUND MOVED BETWEEN NEIGHBOURING BLOCKS: the blocks' rounds in a row are still the plan's
/-- The file in which "hear" declares one round less and "batch" one more. -/
def FM : FileDescription Nat :=
  { F with first := { F.first with links := [{ link "A" 1 1 [] false false with
      batch := fun c => { batch 1 0 c with
        rounds := [{ entry := drawD }, { entry := drawD }], oracles := [[], []] } }] } }
#guard FM.roundsDeclaredByBlocks == F.roundsDeclaredByBlocks
#guard FM.planOk
#guard !FM.wantedOk
-- two blocks that change places
#guard (F (second := [{ send₃ with place := peek.place }, { peek with place := send₃.place },
  ask ()]) (owed := [])).planOk
#guard !(F (second := [{ send₃ with place := peek.place }, { peek with place := send₃.place },
  ask ()])).wantedOk
-- another kind at a place
#guard !(F (second := [send₃, peek, { ask () with place := ⟨3, some 0, 6, .K11⟩ }])).wantedOk

-- `pull` keeps both tables
#guard (F.pull fun x : Nat => x).wanted == F.wanted
#guard (F.pull fun x : Nat => x).owed == F.owed

/-! which messages a block must name in `before`, beside the tests on the plan -/
#guard F.owedOk
#guard (F (owed := [])).owedOk
-- an empty `before`: the tests on the plan do not see it
#guard (F (second := [send₃, { peek with before := [] }, ask ()])).planOk
#guard !(F (second := [send₃, { peek with before := [] }, ask ()])).owedOk
-- `before` names another message than the one that is owed
#guard (F (second := [send₃, { peek with before := [(2, 0)] }, ask ()])).planOk
#guard !(F (second := [send₃, { peek with before := [(2, 0)] }, ask ()])).owedOk
-- a row of two messages, of which the block names one; both
#guard !(F (owed := [(⟨3, some 0, 5, .K12⟩, [(3, 0), (2, 0)])])).owedOk
#guard (F (second := [send₃, { peek with before := [(2, 0), (3, 0)] }, ask ()])
  (owed := [(⟨3, some 0, 5, .K12⟩, [(3, 0), (2, 0)])])).owedOk
-- A QUIET BLOCK AT THE OWED PLACE that names the message, and the block that draws at another
-- place, naming nothing: the tests on the plan say yes; the table of places refuses too
/-- The second chain's link's closing blocks with `peek` at the place 11, and at its own place a
quiet block that names the owed message. -/
def quietAtOwed : List (Block St Nat) :=
  [send₃, { roundlessBlock "quiet" 3 (some 0) 5 .ok with place := peek.place, before := [(3, 0)] },
    { peek with place := ⟨3, some 0, 11, .K12⟩, before := [] }, ask ()]
#guard (F (second := quietAtOwed)).planOk
#guard !(F (second := quietAtOwed)).owedOk
#guard !(F (second := quietAtOwed)).wantedOk
-- a row that names an earlier chain's message: met wherever that message is sent: IDLE
#guard (F (second := [send₃, { peek with before := [(2, 0), (3, 0)] }, ask ()])
  (owed := [(⟨3, some 0, 5, .K12⟩, [(2, 0)])])).owedOk
-- more than is owed does no harm; a row at a place where no block stands is refused
#guard (F (second := [send₃, { peek with before := [(2, 0), (3, 0)] }, ask ()])).owedOk
#guard !(F (owed := [(⟨3, some 0, 9, .K12⟩, [])])).owedOk
-- the message that is owed is sent behind the draw: `owedOk` says yes, `beforeOk` refuses
#guard (F (second := [peek, send₃, ask ()])).owedOk
#guard !(F (second := [peek, send₃, ask ()])).beforeOk

/-! the widths, and a stored part's label -/
#guard !readsFit { entry := drawT
                   stored := [{ part 0 1 with sh := { (part 0 1).sh with W := 0 } }] }
#guard !readsFit { entry := drawT
                   stored := [{ part 0 1 with sh := { (part 0 1).sh with W := 2 ^ 24 } }] }
#guard readsFit { entry := drawT
                  stored := [{ part 0 1 with sh := { (part 0 1).sh with W := 2 ^ 24 - 1 } }] }
#guard !readsFit { entry := drawT
                   stored := [{ part 0 1 with sh := { (part 0 1).sh with tree := 1 } }] }
#guard !readsFit { entry := drawT, opens := [({ tree with W := 0 }, .own 0)] }
#guard !readsFit { entry := drawT, opens := [({ tree with W := 2 ^ 24 }, .own 0)] }
#guard readsFit { entry := drawT, opens := [({ tree with W := 2 ^ 24 - 1 }, .own 0)] }
-- a tree declared twice in one round, in the plan's declared rounds too
/-- The file whose round "peek" declares its own tree twice. -/
def FT : FileDescription Nat :=
  F (second := [send₃, peekAt [(tree, .taken 1 0), (tree₃, .own 0), (tree₃, .own 0)], ask ()])
    (plans := (thePlans.1, thePlans.2.1, thePlans.2.2.set 3
      { entry := drawT, opens := [(tree, .taken 1 0), (tree₃, .own 0), (tree₃, .own 0)] }))
#guard FT.roundsDeclaredByBlocks == FT.plans
#guard !FT.planOk
#guard (BookPlan.clauses FT.roundsDeclaredByBlocks FT.roots).any fun c => c.1 == "inOrder" && !c.2

/-! offSeal -/
#guard ((offSeal (withEmptySealRound v₁)).map fun v => v.rounds.length) == some 3
#guard ((offSeal ⟨[rvP 1, ⟨[], ⟨[], [], [], some ByteArray.empty⟩⟩], [(1, 2, [3])]⟩).map
  fun v => (v.rounds.map (·.drawn.poss), v.opened)) == some ([[1]], [(1, 2, [3])])
#guard (offSeal ⟨[], []⟩).isNone
#guard (offSeal v₁).isNone
#guard (offSeal ⟨[rvE], []⟩).isNone
#guard (offSeal ⟨[⟨[], ⟨[(1, 0, 0)], [], [], none⟩⟩], []⟩).isNone
#guard (offSeal ⟨[⟨[], ⟨[], [], [1], none⟩⟩], []⟩).isNone

end VerifiableInference.Desc.BlockToy
