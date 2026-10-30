# Words of the files on the kind "lookup" (K3)

Terms: [TERMS.md](../../../../../TERMS.md); words: [GLOSSARY.md](../../../../../GLOSSARY.md).

The comments of the Lean files under Johnson/Desc/ProofFile/Honest/K3/ use some words of their own.
This page gives each in plain terms, with the declaration that defines it. Paths are from lean/; a
path that begins with Honest/ is short for Johnson/Desc/ProofFile/Honest/. These comments also name
files that are not part of this library; where the mark "[not in this library]" stands, it says so.
Nothing in the library imports them. "There" means the file that was named last. Lean does not check
this page.

One page of the library goes before this one where it has a word in the same sense:
lean/GLOSSARY.md, below GLOSSARY.md for short. An entry below then points to it and does not say it
again. GLOSSARY.md has many of these words too, with senses by directory; in this folder's comments
the sense given here holds.

Not claimed: anything on soundness, completeness or any other property of a protocol.

- **acceptance alone (of a step)**: `IM.Yes ft b s s'` (Johnson/IMR/HandsDef.lean): there are rounds
  and columns on which the step of the sub-protocol b, at the first tree ft, accepts from the state
  s and returns the state s'. Nothing more is assumed of these rounds and columns.
- **address**: the place of a lookup, as an entry of `K3Lot.addresses`
  (Johnson/Desc/ProofFile/Lot/K3.lean), the list of all lookups' places: link by link, the lookup on
  the calls, then the lookup on the digits. `IM.k3Place l d` (Johnson/IMR/K3Seat.lean) writes the
  address of link l's lookup out; d is true for the digits.
- **agree at the run**: `AgreeAt R B` (Honest/K3/Law/Statements.lean): at the course R, the summands
  of R and the summands B yield the same lists, as read in the library's field, at the course's
  input, at the points that each stage's job is handed, and at the run's own challenges and mask
  entries. Nothing is asked at another point.
- **arm**: `Here` (Johnson/Desc/First/State.lean) says where the first chain stands. It has six
  cases; the three in which a link is open, `lay`, `att` and `head`, are the arms. The readers of
  the open link's part have one case for each of these and answer nothing at the others.
- **ask**: `Ask` (Honest/K3/Stages.lean): the small structure at which every lookup's row is seated:
  a function from the challenges heard in front to keys and bits (`Hidden`). `askOf`
  (Honest/K3/Wit.lean) makes it of the sources and the chain's input.
- **base**: `At.base` (Honest/K3/Stages.lean): the number of rounds of the first chain that stand in
  front of a lookup's place.
- **bits**: see count.
- **block**: see sub-protocol.
- **book, coins**: `ProverCoinCounts` and `Coins` (Honest/Frame.lean). The book is public data
  beside a description: for each chain, the parts that have coins of their own, each with its count.
  The coins of one run are a value of the type that the book fixes; a part's moves read the coins
  that the part is handed.
- **border**: a border lies in front of each sub-protocol of the first chain's flat list, and one
  behind the last (the head of Johnson/Desc/First/Borders.lean). `borderOf l d`
  (Johnson/Desc/Sound/MgAt/K3Open.lean) is the number of the border in front of link l's lookup;
  `k3K l d` (Johnson/Desc/First/Look/K3Base.lean) is the number of that lookup in the full size's
  list of places.
- **borrowed**: see owner.
- **call, the lookup on the calls**: `OnBytes.Model.Call` (OnBytes/Model/Frame.lean): one call of
  the lookup argument says that every key of a vector of keys is a row value of a public table. The
  lookup on the calls of a link is the one lookup that treats that link's calls together: a site
  (`Site`, Honest/K3/Lot.lean) with `digits = false`, at the seat `seatCalls`
  (Johnson/Desc/First/Look/K3Seat.lean).
- **caller**: `Caller` (Honest/K3/Lot.lean): whose link a lookup stands in: layers, attention or
  head.
- **cells, weights**: `Cells` and `Weights` (Honest/ForKinds.lean): the witness and the index as all
  kinds read them: a cell by segment, matrix name, row and column; an entry of the matrix of all
  committed weights' digits by row and column.
- **chain, first chain**: `Chain` (Johnson/Desc/Block.lean): a maker of a flat list of
  sub-protocols. A proof file has three chains (GLOSSARY.md, "chain"). The first chain is the one
  whose places have `chain := 1`; the state that it carries is `VerifiableInference.Desc.First.S`
  (Johnson/Desc/First/State.lean).
- **challenges**: GLOSSARY.md, "verifier message, challenge". In Lean: `Fmt.Drawn`
  (Fmt/Rules6Round.lean) is what a round draws. The challenges heard are the list of these values
  for the rounds so far, in order.
- **claim**: a form that is claimed to be 0 (the docstring of `Aff`, OnBytes/Model/Hide.lean). While
  the messages are read no equation is tested: each algebraic check of a sub-proof becomes a claim.
- **coins**: see book.
- **column**: `OpenedColumn` (Johnson/Desc/Step.lean): an opened column, as a view holds it: the
  tree's key, the leaf, the words. A lookup's rounds are declared by their entries alone, and such
  rounds read no column (`readsOf_plain`, Honest/K3/Law/Top.lean).
- **count, bits, planes**: the count of a row of a lookup's table is the row's multiplicity
  (`Call.kappa`, OnBytes/Model/Frame.lean: "a multiplicity has 2^kappa bits"): the exponent with
  which the row's factor enters the table side of the lookup's equation (the section "DECIDES" of
  Johnson/Desc/First/Look/K3Lookup.lean). The prover gives it in bits. Plane j is the family of the
  bits number j of all rows (`Hidden.bit`, Honest/K3/Stages.lean). A count has 2 ^ mu places for
  bits, of which the first `planes` are real (`Face.mu`, `Face.planes`,
  Johnson/Desc/First/Look/K3LookupGeneral.lean). "planes" is also the name of a run of claims: see
  run.
- **course**: `Course` (Honest/K3/Law/Statements.lean): one run of a lookup's stages. Its fields:
  the lookup's public data at its place, the summands, the ledger's next slot in front of the
  lookup, the coins stage by stage, the state in front, what is shown in front, and the challenges
  of the lookup's own rounds.
- **covered positions**: `Head.Covered` (OnBytes/Model/HeadLayout.lean): the covered positions of a
  request: the request's tokens; for each position whether it is covered, which token is checked
  there, and whether it has a cost; and the number of positions with a cost. `S.coveredAt`
  (Johnson/Desc/First/State.lean) makes it of the request's words and a reply, under four tests.
- **cut**: two senses. The book's cut: for each place at which a half may stand, how many rounds
  each part of its row has (`ProverCoinCounts`, Honest/Frame.lean). The cut of a member's acceptance
  into structure and values: Honest/Thread/Shape.lean.
- **decision**: `Block.decide` (Johnson/Desc/Block.lean): from the state, the sub-protocol's own
  rounds as a view shows them and the columns that it is owed, to the next state or a refusal under
  a name.
- **description**: `FileDescription` (Johnson/Desc/Block.lean): a proof file's description: three
  chains, each with a state of its own. "The description returns" is `IM.Open`
  (Johnson/IMR/SeatOpen.lean), which names each part of the returned value.
- **digits, the lookup on the digits**: the lookup on the digits of a link's smallness test: a site
  with `digits = true`, at the seat `seatDigits` (Johnson/Desc/First/Look/K3Seat.lean). Its keys are
  digits of combinations under a sampled matrix; `Site.rng` (Honest/K3/Lot.lean) is the number,
  among the chain's rounds, of the round that samples that matrix.
- **elder row**: in this folder's comments: `lookRow` (Honest/K3/Row.lean), the row of parts that
  pass nothing on, and its seated form `proverSideOfLookupInChainAtOneOwner`, which leaves what the
  chain's parts hand on as it is; said beside the kept row; the word marks no state of the library.
- **entry (of a plan)**: `Fmt.Entry` (Fmt/Plan.lean): a round's name and eleven numbers, among them
  the bits of proof of work, the bytes of the prover's message, how many elements of the extension
  field are sampled and how many of these must not be 0, and how many positions and matrix entries
  are sampled. The hearing's own entries of a lookup's rounds are `entriesV`
  (Johnson/Desc/First/Look/Via/Rounds.lean). An entry of a list, of a virtual row or of the
  vocabulary is meant in the plain sense.
- **event**: `Event` (Honest/K3/Good/MarkEvents.lean): the element at a spot is 0, or it is 1.
  `eventsOf f` lists all events of a lookup; `events f` (Honest/K3/GoodDraws.lean) is their number.
- **face**: `VerifiableInference.Desc.K3.Face` (Johnson/Desc/First/Look/K3LookupGeneral.lean): a
  lookup's public numbers, orders and one public function. `LFace` (Honest/K3/Stages.lean)
  abbreviates it, since Honest/Frame.lean has a `Face` of its own.
- **filling**: a value that is given to a letter or to a structure of letters. For example
  `LookJobs` (Honest/K3/Stages.lean) has two fillings: `specJobs` (Honest/K3/JobsSpec.lean) and
  `fastJobs` (Honest/K3/JobsFast.lean).
- **fit**: `Fit R` (Honest/K3/Law/Statements.lean): the course R stands at its place and its
  challenges can be sampled: the tests on the face pass; as many challenges were heard in front as
  the base says; the challenges pass the frame's test `drawsFit` at the rounds that the hearing
  hears. "Fits" at a site is something else: `k3Fits` (Honest/K3/SeatFits.lean), a list of tests
  with code on public data.
- **flat list**: `Chain.blocksInOrder` (Johnson/Desc/Block.lean): the list of a chain's
  sub-protocols in order: first, front, the links, back, last.
- **fold**: two senses. To fold a table: a function on m bits is kept as its table of 2 ^ m entries;
  at a challenge r one bit is bound: entry i of the result is a + r (b - a), where a is the i-th
  entry with that bit 0 and b its partner; the result has half as many entries (`bindAt`,
  Honest/K3/JobsFast.lean). `fastJobs` (there) computes the summands so. A fold of steps is a run
  over a list, step by step, such as `play` (Honest/Frame.lean).
- **fork**: `OnBytes.Model.Fork` (OnBytes/Model/Hide.lean): the type of a ledger. By that
  structure's docstring, in identifiers a fork is a sub-proof. `fork?`
  (Johnson/Desc/First/State.lean) reads the open sub-proof's ledger off the first chain's state.
- **form**: `OnBytes.Model.Aff` (OnBytes/Model/Hide.lean): an affine form: entries of virtual rows
  with coefficients, slots with coefficients, and a constant.
- **frame**: Honest/Frame.lean: a frame for the honest prover of a proof file's protocol: types
  (parts, halves, coins, steps; Frame.lean's own docstrings say "prover's side" for half and "list"
  for row), the run of a list of steps at given challenges (`play`), and a test with code.
  `KindName.frame` (Johnson/Desc/Block.lean) is something else: it marks a sub-protocol of no kind,
  a row of the fold's own text.
- **full size**: GLOSSARY.md, "small examples, full size, small test configuration". In this folder
  "at the full size alone" is said on two grounds. Of a statement under `P5J.AtMgA`: the layout file
  is that of the stored full-size example (`VerifierAndGoals.storedPublicFiles`, Ladder/Stored.lean;
  `VerifierAndGoals.InScope`, Ladder.lean), and there are 25 links: twelve times layers and
  attention, then the head (`linksFull`, Johnson/Desc/Sound/AtDriver.lean). Of a statement that does
  not assume it: it has a hypothesis that fixes the full size's numbers, such as `PlanLabels`
  (Honest/K3/WitPlan.lean: twelve groups, 25 lists of matrices) or `NamesFit`
  (Johnson/HonestTrace/FromCells.lean).
- **good samples**: the Boolean tests `goodRun`, `goodK3` and `goodK3Out` (Honest/K3/GoodDraws.lean)
  on the lookup's own samples. `goodRun f r` is for the slots of one run's window, `goodK3 f` for
  all of the lookup's slots: no element at a spot has a forbidden value. `goodK3Out f` is for the
  owners of other slots to call: no element at one of its own spots (`spotsOut`) is 0 or 1; and the
  factor of the planes' value in the leaves' claim, alpha - 1 - the table's row at the leaves'
  point, has its words below the prime and is not 0.
- **group**: `Site.group` (Honest/K3/Lot.lean): the caller's number among its like, from 0: which
  group of layers, or the attention of which group.
- **guests**: see run.
- **half**: `Placed` (Honest/Frame.lean): the prover's half of a sub-protocol at its place: a row of
  parts whose rounds, in the row's order, are the sub-protocol's.
  `proverSideOfLookupInChainAtOneOwner` (Honest/K3/Row.lean) is a lookup's half.
- **head**: three senses. The head of a file is the comment at its top (GLOSSARY.md, "head, `Head`,
  from the head, under the head"). The head of the model is its last segment (there too); the head's
  link is the last link, number 24 at the full size (`Caller.head`, Honest/K3/Lot.lean). The
  docstring of `P5J.AtMgA` calls that structure "the one head"; these comments call it the library's
  hypothesis `P5J.AtMgA`.
- **heard structure**: `OnBytes.Model.Forest.Heard` (OnBytes/Model/Look.lean): what the verifier
  holds after the messages of a lookup. `HeardV` (Johnson/Desc/First/Look/Via/Rounds.lean) is what
  `hearV` returns; `toHeard` (Johnson/Desc/First/Look/K3LookupGeneral.lean) leads from what was
  heard to the first structure.
- **hearing**: `hearV f F rs` (Johnson/Desc/First/Look/Via/Rounds.lean): the lookup's messages at a
  place, read off the rounds rs from the ledger F: what was heard and the ledger behind, or nothing.
  `hearVia p F rs` (Johnson/Desc/First/Look/Via/Via.lean) is the same at a place's public parameters
  p, led back to the heard structure.
- **hidden value**: `Fork` (OnBytes/Model/Hide.lean). "Hidden is the name of a value's part in the
  protocol: nothing here claims that a value stays hidden, or that a false claim is caught."
- **honest side**: `Side` (Honest/Side.lean): a kind's honest side at a place: the description's
  member there, one row of parts, each paired with a term of type `Sim`, and the place's fall.
- **instance**: two senses. The public instance of a request: GLOSSARY.md, "instance"; a half is
  handed it as `Local.x` (Honest/Frame.lean). An instance of hypotheses: values of a statement's
  variables at which all its hypotheses hold together.
- **item, public item**: `Item` and `Pub` (Johnson/Desc/First/Borders.lean). An item is a named
  claim on the witness. A public item is a named condition on the public part and the state alone:
  no oracle, no witness. At each border some items and some public items are open: see table. The
  public item `leftOn l` says what the lookup on the calls of link l has left, in the form that
  holds at every later state: what was heard is the end values of a hearing of some rounds from some
  ledger, and the ledger in hand is later than the one behind that hearing.
- **job, summand**: `StageJob` and `LookJobs` (Honest/K3/Stages.lean): what the prover's side of one
  stage's masked sumcheck computes: the summand's round polynomials and end values, at the run's
  points. `LookJobs` holds one job for each stage.
- **join**: the stage `Stage.join` (Honest/K3/Stages.lean): nothing is sent; mu elements are
  sampled. Also the name of a run of claims: see run.
- **keeps**: the field `keeps` of `Thread` (Honest/Thread/Thr.lean): what the sub-protocol behind a
  border leaves of the verifier's state as it was: a relation between the states in front of and
  behind it. `kpBy` (Honest/Thread/KeepsBy.lean) gives it by the place's kind. The lookups' clause
  is `k3KeepsAt` (Honest/K3/Law/Thread/K3KeepsAt.lean).
- **kept row, a row that passes its tables on**: `lookRowKeep` (Honest/K3/RowKeep.lean) and its
  seated form `proverSideOfLookupInChainKeepingTablesAtOneOwner`: a part for each stage, as in the
  elder row; its parts pass on a state of the row's own, `RowOwn` (Honest/K3/KeptTypes.lean): the
  lookup's store, or none, and the stage's kept state, or none. `rowOwn₀` is none and none: the
  row's last part lays it, where the letters have a job at that stage; that it is read in front of
  the row is a premise of the laws that give one result of the two rows (Honest/K3/Law/Keep/).
  Seated, the row reads its state in what the chain's parts pass on by a letter get and lays it
  there by a letter set.
- **key point**: `Pts.keyPt i m` (Honest/K3/Stages.lean): the point in front of the level with m
  variables of part i's key tree: m coordinates, the highest bit first. Where m is the part's number
  of levels, it is the tree's last point, which `keyPtsOf` (Honest/K3/Heard.lean) cuts into the
  heard structure's fields zx, zy and zk.
- **key, key side, key tree**: the keys of all calls of a lookup, each moved by its call's number
  times the shift, are the leaves of one product tree, the key side; a leaf is alpha - key (the
  section "DECIDES" of Johnson/Desc/First/Look/K3Lookup.lean). `Hidden.key` (Honest/K3/Stages.lean)
  is the prover's key at a place of a part.
- **keys and bits are honest**: `LookIn.Meets L h lm` (Honest/K3/WitLaw.lean): a condition on a
  lookup's keys and bits L (`LookIn`, Honest/K3/Wit.lean) at a shape h whose planes' matrix has 2 ^
  lm rows. It is an existence: there are key vectors of the calls and a reading nu of the verifier's
  places such that: nu reads 0 at the place that reads 0; the key vector of L is the joint vector of
  these key vectors; a bit of L is what nu reads at the bit's place, so it is 0 at a row of the
  joint table that belongs to no call; and at every shift and every point of comparison the
  library's relation `MidP` (Cb/Pv/Lookup/Alg/PadAlg.lean) holds of the joint vector, the joint
  table, the public padding and nu at the bits' places.
- **kind**: `KindName` and `Kind` (Johnson/Desc/Block.lean): a kind takes a place's public
  parameters to the sub-protocol there. K3 is the kind "lookup".
- **kit**: GLOSSARY.md, "kit", in the sense that it gives for the folder Run/: `Run.PQ.CK`
  (Run/PlanQTypes.lean): the kit of verifier's messages: for each entry and kind of a round a
  finite, nonempty type of challenges, and the map to what the round draws.
- **lawful**: `Lawful R planes keys` (Honest/K3/Law/Statements.lean): what is asked of the summands
  at one course R; the letters planes and keys say what the planes of the counts' bits and a part's
  keys come to at a point. Its five fields: sums: at each stage with end values the summand sums
  from what the claimed form should be worth to the verifier's end term on the shown end values;
  leaves: the leaves' summand sums to 1 plus the public factor of a bit times the planes' value at
  the sumcheck's own point; bits: the true end value of the bits' sumcheck is the planes' value at
  its point; count: the counts add up; keyEnds: the line between the true end values of a part's
  last key level is alpha less the keys' value at the key tree's last point.
- **leaves**: the stage `Stage.leaves` (Honest/K3/Stages.lean): the masked sumcheck on the leaves of
  the table side's trees. It has no end value.
- **ledger**: a value of `OnBytes.Model.Fork` (OnBytes/Model/Hide.lean): the state of the check of
  one sub-proof: its arrays, what was shown under its slots, and the weighted sum of its claims.
- **letter, letters**: GLOSSARY.md, "letter, letters". Structures of letters that these comments
  name: `Thread` (Honest/Thread/Thr.lean), `Letters` (Honest/Thread/First.lean), `Shape`
  (Honest/Thread/Shape.lean).
- **level**: one level of a product tree, with its masked sumcheck: `Stage.key i m` on the key side,
  `Stage.tab l` on the table side (Honest/K3/Stages.lean).
- **library's field**: see read.
- **link, segment**: GLOSSARY.md, "link", sense (3), and "sub-proof": a group of layers, the
  attention of such a group, or the output head. In Lean: `Link` (Johnson/Desc/Block.lean).
  `Site.link` (Honest/K3/Lot.lean) is the link's number in the first chain, from 0, which is the
  segment's number.
- **lookup**: the sub-protocol of the kind K3 at one place: it treats several calls together (the
  section "DECIDES" of Johnson/Desc/First/Look/K3Lookup.lean). Each link has two: the lookup on the
  calls and the lookup on the digits.
- **lot**: `ProofFile.Lot` (Johnson/Desc/ProofFile/LotCore.lean): a named table of sub-protocols
  from one module. The lookups' lot is `K3Lot.lot` (Johnson/Desc/ProofFile/Lot/K3.lean). A lot's
  honest side is `HLot` (Honest/Frame.lean): the halves at the lot's places; the lookups' is
  `theLot` (Honest/K3/LotFilled.lean).
- **mark**: five senses. Of a state: the field `failed` of the first chain's state. `S.mark`
  (Johnson/Desc/First/State.lean) sets it to a name; the first mark stays. A state bears no mark if
  `failed = none`. Of the frame, in the files under Honest/K3/Good/: a value of `Mark`
  (Honest/Law/Marks.lean): a place; a test on the challenges in front of the member at that place
  and on the member's own; and a stated share, which is a written number and no bound. The mark
  speaks where its test answers something, and is silent elsewhere. Of a slot, in
  Honest/K3/Parts/NamesMarks.lean: an entry of the verifier's list `K3.fromKeys`
  (Johnson/Desc/First/Look/K3Key.lean), one Boolean value for each of the lookup's slots, in the
  order of sending; by that definition's docstring it says whether the slot's mask entry lies in the
  second message. `Is b lo M j` and `markAt` (NamesMarks.lean) read it. Of a slot, in the files
  under Honest/K3/Shape/: an entry of the list got of the ledger's shape (`LedSh`,
  Johnson/Desc/First/Shape/Parts.lean): whether the slot is filled. Of an entry of a link's list of
  matrices (`TMat`, OnBytes/Model/Frame.lean) that is borrowed (kind = 1): its field aId. By the
  code of `markFitsB` (Honest/K3/WitFits.lean) and of `ownerOf` (Honest/K3/WitOwner.lean),
  aId / 256 - 1 is the owner's group of layers, and aId % 256 is the entry's number in that group's
  list.
- **mask, mask row**: the docstring of `Fork` (OnBytes/Model/Hide.lean): entry j of the mask row
  belongs to slot j. `MasksAre` (Honest/K3/Law/Statements.lean) says that the mask entries under a
  lookup's slots are the coins that its stages take.
- **member**: an entry of a chain's flat list: a sub-protocol as the description has it at its
  place. The lookups have 50 members of the first chain at the full size.
- **multiplicity**: see count.
- **named sets of public files**: `VerifierAndGoals.NamedFiles` (Ladder.lean): the stored full-size
  example's three public files, `VerifierAndGoals.storedPublicFiles`, or the same with another
  policy, `VerifierAndGoals.zGap` (Ladder/Stored.lean).
- **objects**: see run.
- **open part (of a heard structure)**: the eleven fields that `OpenSame`
  (Honest/K3/HeardWhole.lean) compares: shape, theta, alpha, leavesA, zx, zy, e, zb0, zb1, tT, zk.
  `lookHeardAt` (there) computes them from the shape and the challenges alone.
- **owner, borrowed matrix**: a link's list of matrices may hold a matrix to which an earlier link
  has committed: a borrowed matrix; that earlier link is its owner. The sources of keys and bits
  read such a matrix under its owner's segment and name (`ownerOf`, Honest/K3/WitOwner.lean;
  `borrowedAt`, Honest/K3/LotOwners.lean).
- **`P5J.AtMgA`, the library's hypothesis**: the structure `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean),
  which extends `P5J.AtMg` (Johnson/P5J/AtMg.lean). The fields of the second say of three public
  files: they are in the goals' scope (scope); their reading returns (reads); the verifier's own
  value is laid, which fixes the public part, the places and the first chain that the statement
  speaks of (laid); the named tests on the plan pass (plan); two ways to the public data give one
  value (pubOne). The first adds four fields: headAt, cols13, opts, k3.
- **padding**: `Face.padding` (Johnson/Desc/First/Look/K3LookupGeneral.lean): runs of places of the
  key vector that hold a public key and are not counted.
- **part, stretch**: `Part` (Honest/Frame.lean): the prover's side of a stretch of a sub-protocol's
  rounds, that is, of some rounds in a row: one move for each. A lookup's row has one part for each
  stage. `Face.parts` is something else: the parts of a lookup's keys.
- **piece**: see place.
- **pin**: two senses. An item: `Item.pin seg moment` (Johnson/Desc/First/Borders.lean): the item
  that says: the witness's messages of the sampled tenants that the segment sends at this moment are
  what their committed words decode to with their samples. Of a column of the planes' matrix, in
  Honest/K3/Law/ReadersSayCount.lean: the form that the caller's second reader yields for the
  column. `PinsSay` (there) says that it is worth the column's cells, the cell of plane j counted 2
  ^ j. `countFold` (Honest/K3/Law/SeatedWorth.lean) is the fold over the pins.
- **place, piece**: `VerifiableInference.Desc.Place` (Johnson/Desc/Block.lean): where a sub-protocol
  stands: the chain (1, 2 or 3), the link if any, the piece (its number inside the link) and the
  kind. `VerifiableInference.Desc.First.Look.Place` (Johnson/Desc/First/Look/LookAt.lean) is another
  structure: what the verifier program's routine is handed at a lookup.
- **plan, test on the plan**: the plan is what the planner returns from the three public files
  (GLOSSARY.md, "planner"); `Fmt.Entry` (Fmt/Plan.lean) is one round's entry of it. A sub-protocol's
  test on the plan is its field `planOk` (Johnson/Desc/Block.lean): it reads no round and no state.
- **planes**: see count; for the run of that name see run.
- **play**: `play` (Honest/Frame.lean): a run of a chain's rounds at given challenges, round by
  round. `Played` (there) is a round as it was played.
- **points**: `Pts` (Honest/K3/Stages.lean): what a lookup's stages read of the challenges in front,
  in the verifier's own forms: theta, alpha, and the points of the key side, of the table side and
  of the bits. `ptsOf` (Honest/K3/Heard.lean) computes them from the challenges heard.
- **program's elements**: see read.
- **promise**: three senses. The table's promise at a border: `onAt`
  (Johnson/Desc/First/Borders.lean). It says that the stored table decodes, and that either the
  state bears a mark or all of these hold: the book-keeping on the state, among it the open rows'
  lists and the groups' members; the statement is in order; the samples are held; the tree of every
  tenant whose pin is open shows all its leaves, and no two members of its list answer the sample
  alike; every public item that is open there holds (`pubHeld`); and what each open public item says
  beside its Boolean test holds (`Meaning.pubP`). It reads the oracles' strings too. The lookup's
  promise in front and behind: the two Boolean tests `k3OnIn` and `k3OnOut`
  (Johnson/Desc/First/Look/K3Borders.lean) on a place's public parameters and the state. In front:
  nothing is heard yet at the lookup's seat; no row waits; a ledger is open whose next slot is the
  lookup's first, which has its sizes, and in which the lookup's slots are there and free. Behind:
  what was heard has the parameters' shape and its points have their sizes; the shape's array of
  calls has the shape's number of calls; the ledger's next slot lies behind the lookup's slots; the
  ledger has its sizes; the own slots of the leaves' sumcheck lie within the lookup's slots and are
  free. The library's promise in front of a masked sumcheck: `LedgerReady C k F`
  (Johnson/Desc/Part/MaskedSumReady.lean): the ledger's arrays have their size; every slot that the
  start form C names is there and filled; there is room for the sumcheck's own slots and those of
  its end values; and these slots are free.
- **public parameters (of a lookup)**: `VerifiableInference.Desc.First.Look.P`
  (Johnson/Desc/First/Look/LookKind.lean): numbers and public tables alone. `Site.p`
  (Honest/K3/Lot.lean) holds them at a site.
- **public part**: `ProofFile.Pub` (Johnson/Desc/ProofFile/Pub.lean): all that the description takes
  from the three public files; in statements mostly Z or Zp. Its field p.X is the verifier program's
  own public structure, `OnBytes.Model.Verify.Public` (OnBytes/Model/VerifyPublic.lean), which the
  files under Johnson/HonestTrace/ call the public part X.
- **reached by the wrapped sub-protocols' steps**: `IM.RB` (Johnson/IMR/GrownRch.lean): the state is
  reached from the start state `ProofFile.startS` (Johnson/Desc/ProofFile/Pub.lean) by steps of the
  flat list's members, each wrapped by `below` (Johnson/Desc/Sound/ChainRule.lean): the sub-protocol
  that first tests its own rounds and the opened leaves that it is handed, and then decides as the
  member does. By its docstring `below` is a device of the proof: it is no text of the description
  and runs nowhere.
- **read, the program's elements, the library's field, words below the prime**: an element of the
  program is `OnBytes.E` (OnBytes/Base.lean): three machine words. The library's field is `Cb.Gl.E`
  (Cb/Gl/GlField.lean). `readE` (OnBytes/Slice/ProgField.lean) reads the first in the second. An
  element has its words below the prime if `okE` (OnBytes/Field/Ext.lean) accepts it; two such
  elements with one reading are equal (`readE_inj`, OnBytes/Slice/ProgField.lean).
- **reader, readers**: several senses, told apart by the word beside it. A reader of the state: a
  function that reads one thing off the first chain's state, such as `fork?`, `tl?` and `lookHeard?`
  (Johnson/Desc/First/State.lean). The caller's readers: `VerifiableInference.Desc.K3.Readers`
  (Johnson/Desc/First/Look/K3Runs.lean): what the calling kind hands in for the run "planes". The
  trace's reader, of cells, and the index's reader, of weights: `Sources.cells` and
  `Sources.weights` (Honest/K3/Wit.lean). A half's reader of the input: the argument wit of
  `proverSideOfLookupInChainAtOneOwner` (Honest/K3/Row.lean).
- **relation after the challenge**: `Data.Mid` (Johnson/HonestTrace/LookDefs.lean): every bit is 0
  or 1; weighted by 2 ^ j the bits add up to 2 ^ v less the number of padding keys; the product of
  alpha - key over the keys is the padding's factor times the product of the G_j ^ (2 ^ j).
- **rider**: two senses. A clause of a thread's rider: `RiderCl` (Honest/Thread/Riders.lean): a
  sentence on the border's number, the input and the verifier's state, from one border to another;
  `ridersOf` is the conjunction of a list of clauses. The caller's riders at a lookup: arrays of the
  calling kind; `K3OutRider` (Johnson/Top/H/K3RowOutRider.lean) says that the multilinear extension
  of each is 0 at its own places of the lookup's key point.
- **round**: GLOSSARY.md, "round, target". In Lean: `Fmt.RoundView` (Fmt/View.lean) is one round as
  a decision sees it: the values sent and what was drawn.
- **row**: four senses, told apart by the word beside it. A row of parts: the list of a half's parts
  (`Placed.parts`, Honest/Frame.lean; a lookup's is `lookRow`, Honest/K3/Row.lean). A row of a
  lookup's table: a value that a key may take. A sub-protocol's rows of the table of borders:
  `rowOf` for items, `pubRowOf` for public items (Johnson/Desc/First/Borders.lean). The mask row:
  see mask.
- **run (of claims): objects, guests, planes, join**: an entry of `Block.claims`
  (Johnson/Desc/Block.lean): a name, and a function from the number of claims gathered so far and
  the state to claims and the state behind, or a refusal. By the heads of
  Johnson/Desc/First/Look/K3Lookup.lean and K3Stated.lean: "objects" are the linear claims that the
  sumchecks left; "guests" are other kinds' identities that are tested at coordinates of the key
  side's point; "planes" are the claims on the planes of the counts' bits, listed at the calls of an
  attention link and of the head's link; "join" is the calling kind's to state.
- **sample**: two senses. Of a tenant: GLOSSARY.md, "sample, sample map"; see samples held and pin.
  In the files under Honest/K3/Good/ and in Honest/K3/GoodDraws.lean: what a round draws
  (`Fmt.Drawn`, Fmt/Rules6Round.lean): see challenges. The lookup's own samples are those of its own
  rounds. They are such as the rounds can sample if `canDraw` (Honest/K3/GoodDrawsLaw.lean) accepts
  them: the frame's own test `drawsFit` (Honest/Frame.lean) at the lookup's rounds. Among its
  clauses: the counts fit; every word of an element is below the prime; a sample that the entry
  marks as never 0 is not 0.
- **samples held**: `samplesHeld` (Johnson/Desc/First/Borders.lean): a Boolean test: the state still
  holds the sample of every tenant whose pin is open. A tenant is given by a tree's number through
  the file and the message's number in the tree (`Numbers`, there). A sampled tenant's committed
  word is decoded with its sample: see pin.
- **seat**: `VerifiableInference.Desc.K3.Seat` (Johnson/Desc/First/Look/K3Lookup.lean): where the
  state keeps what the kind reads and writes: six functions, among them the reader of the ledger,
  the writer behind the hearing and the reader of what was heard. The two seats are `seatCalls` and
  `seatDigits` (Johnson/Desc/First/Look/K3Seat.lean). "Seated at" says at which seat, site or place
  a thing is taken.
- **seated filling**: `tiedOwnSources` (Honest/K3/WitOwner.lean): the sources that `theLot`
  (Honest/K3/LotFilled.lean) lays into the lookups' rows; they read a borrowed matrix under its
  owner's segment and name. `thePlanSources` (Honest/K3/WitDigits.lean) is another filling, which
  reads every matrix at the link itself.
- **segment**: see link.
- **settled**: `Ask.Settled base w` (Honest/K3/WitLaw.lean): behind the first base challenges the
  ask w no longer moves, so all parts of a row, each of which is handed the challenges in front of
  itself, see one structure. Shown, conditionally, in `askOf_settled` (there): on the digits the
  round that samples the matrix must stand in front of base; on the calls nothing is asked.
- **shape**: three senses. A lookup's shape: `OnBytes.Model.Forest.Shape`
  (OnBytes/Model/Forest.lean): the numbers of a group of calls. The shape of a state: its image
  under a projection for flags, counts, marks and lengths (`Shape`, Honest/Thread/Shape.lean: a
  parameter: its type does not say what it keeps; that it holds no field element: `Shape.Typed`, a
  hypothesis); for the first chain `chainSh` (Johnson/Desc/First/Shape/Chain.lean). The shape of a
  ledger, in the files under Honest/K3/Shape/: `LedSh` (Johnson/Desc/First/Shape/Parts.lean); see
  mark.
- **share**: two senses. The field share of a `Mark` (Honest/Law/Marks.lean): a written number. Of a
  round's challenges, the share of them that show what a condition says: `shareAt`
  (Honest/K3/Good/MarkShare.lean): their number over the number of all challenges of the round.
- **shift, alpha**: one drawn field element by which the keys and tables of several calls are joined
  into one lookup. In this folder: `Pts.theta` (Honest/K3/Stages.lean), which is 0 where there is no
  shift; each key is moved by its call's number times it. `Pts.alpha` (there) is the drawn element
  at which the lookup's equation is tested (the section "DECIDES" of
  Johnson/Desc/First/Look/K3Lookup.lean).
- **site**: `Site` (Honest/K3/Lot.lean): a lookup's public data at its place. Its fields: link, the
  link's number; digits, whether it is the lookup on the digits; caller, whose link it is; group,
  that caller's number among its like; p, the public parameters; shape; at_, the place with its face
  and base; rng, at the digits the number of the round that samples the smallness test's matrix.
  `lookSites Z` lists all sites of a public part Z, in the order of the addresses.
- **slot**: the docstring of `Fork` (OnBytes/Model/Hide.lean): every scalar that a sub-proof sends
  has a number, its slot, counted from 0 in the order of sending. `Fork.next` is the slot of the
  next scalar.
- **small example**: GLOSSARY.md, "small examples, full size, small test configuration": the
  library's stored sets of files (prover/examples/target_small_f2 and variants), configurations of
  the real protocol. A small synthetic example (a lookup, a face, a chain, a book) is something
  else: data that a test or an instance of this folder makes up; see synthetic. The files of this
  folder whose names bear "Toy" hold small synthetic examples; where one of them takes its numbers
  from the small example, they are written numbers.
- **smallness test**: OnBytes/Model/Tail.lean: the test with which each of the three kinds of
  sub-proof ends. Its state is `HTailF2` (there), which these comments call the smallness test's
  structure; `tl?` (Johnson/Desc/First/State.lean) reads it off the first chain's state, and its
  field heard holds what the lookup on the digits has heard.
- **sort**: two senses. Of a link: `ModelPart` (Johnson/Desc/First/Driver/Chain.lean): the three
  sorts of part of the model that a segment can treat: layers, attention, head; `Caller`
  (Honest/K3/Lot.lean) has the same three. Of a lookup: whether it is on the calls or on the digits
  (`Site.digits`, Lot.lean); `Who` (Honest/K3/Wit.lean) has the four sorts of lookup: on the calls
  of layers, of attention or of the head, or on the digits.
- **sources**: `Sources` (Honest/K3/Wit.lean): what the lookups' rows are made of: the trace's
  reader, the index's reader, and for each sort of lookup a function to its keys and bits
  (`LookIn`).
- **specification**: Johnson/HonestTrace/LookDefs.lean says, over any field, what each of a lookup's
  masked sumchecks sums (the structure `Job`). `specJobs` (Honest/K3/JobsSpec.lean) is the filling
  of a row's jobs that reads every value off a field of a `Job`; `fastJobs`
  (Honest/K3/JobsFast.lean) is the filling that folds tables.
- **spot**: `Spot` (Honest/K3/GoodDraws.lean): a sampled element of the lookup that matters, by its
  stage, its round's number in the stage and its number among the elements that the round samples;
  with it, whether 0 alone is forbidden there, or 0 and 1.
- **stage**: `Stage` (Honest/K3/Stages.lean): a part of a lookup's row, by name: shift, alpha, tie,
  split, join, key, keyLine, tab, tabLine, leaves, zero, bits. `stages f` lists the stages of a
  lookup with face f in the order of the rounds.
- **state**: in these comments, the state that the first chain carries:
  `VerifiableInference.Desc.First.S` (Johnson/Desc/First/State.lean). "In front" and "behind" are
  said of the states before and after a step.
- **step**: `Block.step` (Johnson/Desc/Block.lean): the sub-protocol as a step: it tests that the
  rounds and the columns are those that it declares, then calls the decision; it returns the next
  state and the number of columns taken, or a refusal under a name.
- **step without a round**: `roundlessBlock` (Johnson/Desc/Block.lean): a sub-protocol that declares
  no round and only changes the state or refuses. `quietAt X i d`
  (Johnson/Desc/First/Look/K3Whole.lean) is what stands behind link i's lookup without a round, if
  anything: `quietLook` behind the lookup on the calls of a layers' link; `quietDigits` behind the
  lookup on the digits of a layers' or an attention link; `quietHead` behind the lookup on the
  digits of the head's link. The "step without rounds" of GLOSSARY.md is a notion of other
  directories.
- **stretch**: see part.
- **sub-protocol**: `Block` (Johnson/Desc/Block.lean), which the library's docstrings call a block:
  at one place, its test on the plan, its declared rounds, its decision and its named runs of
  claims.
- **sumcheck, masked sumcheck**: Johnson/Desc/Part/MaskedSum4.lean: the verifier's part of the
  masked sumcheck of a sub-proof, which the kinds call inside their own texts.
- **summand**: see job.
- **synthetic**: said of public data or inputs that a test makes up: GLOSSARY.md, "made-up data".
- **table**: three senses, told apart by the word beside it. A lookup's table: the public table
  whose rows the keys are looked up in (GLOSSARY.md, "lookup table"). The table side: the product
  trees over that table's rows, one for each plane. The table of borders, or "the table" alone in
  the files under Honest/K3/Law/Total/: Johnson/Desc/First/Borders.lean: for each sub-protocol of
  the first chain, which items it closes, opens and reads (`rowOf`), and which public items it asks,
  makes and drops (`pubRowOf`); the open sets at all borders are computed from these rows
  (`openSets`, `pubSets`).
- **test by evaluation**: a `#guard` line: GLOSSARY.md, "build-time test". Lean's evaluator computes
  the value; the kernel does not check it.
- **tests, the five and the six**: `IM.XK` (Johnson/IMR/HandsDef.lean): four Boolean tests on the
  state and the plan's numbers at a border (`IM.BK`), and one more that is a parameter. The five
  tests take the public items' test for it; the six take `P1K2.EQ` (Johnson/P1K2R/TieTwo.lean),
  which is "in order" and the public items' test.
- **thread**: the honest run of one chain, seen border by border. `Thr b k s m E`
  (Honest/Thread/Thr.lean) is the relation at border number b between a whole run's coins k, the
  verifier's state s, where the prover's run stands m, and the tables at hand E. By its docstring it
  is a definition, a hypothesis's form: nothing is claimed of it, and it is none of the library's
  goals. `Thread` (there) is the structure of letters in which it is stated.
- **tie**: the step that ties the two sides of the lookup's identity, the products over the keys and
  over the table. In this folder: the stages `Stage.tie s` (Honest/K3/Stages.lean), each a masked
  sumcheck without a variable.
- **trace's bundles**: four hypotheses on a trace T at a public part X. `NamesFit`
  (Johnson/HonestTrace/FromCells.lean): `PartsFit` of X, and T is 0 at every number that has no
  label. `LookPub` (Johnson/HonestTrace/FullPlanes.lean): what the laws of the three kinds of
  sub-proof ask of X: among it, the verifier's own layout functions return X's layouts, and there
  are twelve groups. `PlanesLaid` (Johnson/HonestTrace/FullPlanes.lean): in each of the 25 lists of
  T the planes' matrix holds the planes of the list's own reading. `MeetsAll`
  (Johnson/HonestTrace/Full.lean): what is known of the honest trace, as statements on a trace T.
  The library has a theorem for each, at its own honest trace, for public files in the goals' scope
  and under further hypotheses (for `MeetsAll`: a request that is served, and planes with the values
  0 and 1): `namesFit_in_scope` (Johnson/Goal/HonestTrace/FromCellsInScope.lean), `lookPub_in_scope`
  and `planesLaid_in_scope` (Johnson/Goal/HonestTrace/FullPlanesInScope.lean), `meetsAll_in_scope`
  (Johnson/Goal/HonestTrace/FullInScope.lean).
- **tree**: three senses. A product tree of a lookup: the key tree and the trees of the table side:
  see key and table. A hash tree of the proof file: "the first tree ft" in `Block.step`
  (Johnson/Desc/Block.lean) is the number of trees that stand in front of the chain. In identifiers
  that follow the verifier program, a tree is an array (the docstring of `Fork`,
  OnBytes/Model/Hide.lean).
- **view**: `Fmt.View` (Fmt/View.lean): the rounds as a decision sees them, and the opened columns.
- **weights**: see cells.
- **window**: three senses. A window of the ledger's slots along a hearing: `Win lo a hi F`
  (Honest/K3/Shape/Window.lean): a condition on a ledger F: its arrays have their size; its count of
  slots stands at a; the slots up to hi are there; from a to hi all are free; from lo to a all are
  filled. A sumcheck's window: its own slots, from its first slot on, as many as the first component
  of its walk has entries (`InWin`, Johnson/Road/K4/Slots/RunsSpare.lean). A run's window: the
  lookup's slots that a run of claims names, counted from the lookup's first slot (`windowOf`,
  Honest/K3/GoodDraws.lean).
- **witness**: `Wit` (Johnson/Desc/Msg.lean): the type of witnesses of the table of borders: among
  its fields, what the stored table commits to, the token that was heard, and the messages by
  number. The prover's half is handed the request's trace as its witness (`Local.trace`,
  Honest/Frame.lean).
- **words below the prime**: see read.
- **world, worth**: `OnBytes.Model.World` (OnBytes/Model/HideLaws.lean): a value for every slot and
  for every entry of a virtual row. What a form or a claim is worth in a world is its value there
  (`Aff.value`; `FormWorth`, Honest/K3/Law/Statements.lean, is the name of a statement on such
  values, not proved there). `Item.worth` (Johnson/Desc/First/Borders.lean) is an item: the
  committed messages, at the points that a lookup has heard, are worth what lies under its slots.
- **worth**: see world.
