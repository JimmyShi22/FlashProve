-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ScriptLots.lean: the proximity test (the kind K12) in the frame
for the honest side: THE TEXTS OF THE KIND's LOTS FOR A LAYING OF THE THREADS' SCRIPT (`TreeLot`,
`MsgLot`, `PadLot`, Honest/Thread/ScriptLots.lean): of all a run's coins, the input and the
challenges, in the types that the laying by lots asks. FOURTEEN DEFINITIONS (in a noncomputable
section: ten of them stand over the library's prover's terms), AND THREE SMALL LAWS: TWO ON COUNTS,
ONE ON WHICH LOT STANDS AT THE MEMBER's NUMBER. NOTHING IS LAID HERE; no statement is made of what
these texts hold.

WHAT THESE LOTS ARE NOT. They are texts for the threads' Script (`Script.ofLots`). No statement here
names them together with a measure over coins: `exact` and `fresh` at this kind are stated over
another lot, the parts with their simulators (`simulatorLot`, Honest/K12/Sim2/SlotValueL.lean).
«part 1» is the test's second part, «part 0» its first.
WHAT A LAW OVER COINS AT THIS KIND HAS TO MIND. (a) In the frame's `exact` (`Good.exact`,
Honest/Side.lean) every carried value stands under «for all», and the measure runs over the part's
own coins and those that it spends. Part 1 spends none and CARRIES the three coins that part 0
spends (`runs_L_at_laid`, AtFullSide/K12/RunsAtLaidL.lean: by the book, in scope, at the full size).
An exact whose measure ran over every coin handed would count these three as part 1's own. (b) Every
text here, the TreeLot's and the second tenant's too, decides whether it answers through
`handedRest` and ok, which read the carried stretches: 185 runs at part 0 and 186 at part 1, of
which that theorem writes out the last one and the last two. (c) «No coin stands at two entries» can
hold of part 1's own cut at the free entries and the pad alone. At the packed coefficients where h >
0 it is false by the format (one coefficient in several rows; place 0 a sum): which entry holds
which coefficient, or which sum of them, hangs on s.h, s.g and the place alone (no theorem here). It
is not so of the carried runs: the frame lets any part carry a block behind its spender. (d) Each of
part 1's five switches folds the tails of the stage that it leaves into its next mask message: a use
of carried coins, as data.
`runs_L_at_laid` is not imported here and occurs in no statement here.

  `handedRest`   what the frame's `lendPart` hands the test's second part off a run's coins; nothing
                 where it refuses
  `frontAt`, `testDrawsAt`   what precedes the test, and the test's own challenges by number, cut
                 off one list of challenges
  `seedRound`   the own round in which the switch out of stage τ sends its tree
  `testTbl`, `testTreeLot`   the test's tree number τ: the one table of the part's OWN message at
                 that round (`msgAt`, Parts.lean): no second text of what is sent. Total
  `psAt`   the prover's state at stage j: A SECOND TEXT of `stagesAll`'s recursion
                 (Johnson/Desc/K12/Honest/Stages.lean)
  `stageMsg`, `testMsgTxt`, `testMsgLots`   a stage's state read as a witness's message, inside the
                 fences alone; message (τ, tenant), entry by entry, into Option; two lots a switch
  `testPadTxt`, `testPadLots`   the first tenant's pad: at the library's `padB`'s place (one place
                 where the shape has a mask row)
  `testTl`, `testTn`   the tree lot by the member's number, `rest` a letter; the members' numbers
                 for which a tree lot is supplied
  `testMsgLots_length`, `testPadLots_length`, `testTl_at`   counts; the lot at the member's number

WHOSE CONVENTIONS. Those of the shared sending's lots (Honest/K1/ScriptAt.lean, ScriptLots.lean,
LotsLaid.lean, of other authors): a message's number is the witness's own at (tree, tenant); a pad's
text answers at `padB`'s places alone; a tree's text is total, their `wordlessTable` where the coins
are not there.

WHERE THIS KIND IS NOT THE SHARED SENDING. (i) Every text reads MORE of the run than the part's own
cut: the stretches that the part carries, which stand at other senders' addresses. (ii) fx adds the
sending round's own number: the messages read the test's own fold points. (iii) Beyond a message's
fences the texts answer NOTHING (theirs answers 0 there): beyond the counts this kind's mask table
and tails hold other entries' coins (Coins.lean's own limits). (iv) One letter more, ok: the lot
refuses where it says no. It is meant for a job whose first stage's rows go on in silence where a
sender's text refuses (AtProof/JobL.lean, `rowsL`): there ok is meant to be «that text returns». (v)
Their one reader asks that the book's count at the part's address COVERS the part's; ours is the
frame's `lendPart`, which asks JUST that count and that every carried run is lent: so all our texts,
the pad's too, answer nothing as soon as one carried run is not lent.

Limits.
- FOR A JOB WHOSE FIRST FRESH TABLE CAME EARLIER (`J.fresh` is some) ALONE. Where `J.fresh` is none
  the first fold's fresh table is a tree of the test's own as well: in the chain's count it comes
  ahead of the switches' trees, and it goes out with "BAT" and the first fold, not with the part
  whose coins these texts read. Each tree's number here then falls short by one, t₀ names that
  table's tree and not the first switch's, and that tree is in no lot of this file. The definitions
  are general in J and do not test it.
- THE LAST SWITCH. The library's column there (`lastCol`) encodes one main row and one mask row of
  the first tenant, number 0; `stageMsg` takes no account of last in these two arms and answers for
  every b under 2 ^ k, or 2 ^ h. The two fit where the last stage has k = h = 0, as the written
  record's has; with a larger k the text would hand out rows that enter no symbol: said here without
  a theorem.
- NO LOT IS LAID. Nothing here holds these texts against any Script, any table that a part sends, or
  any other lot (against `Script.ofLots`: LotsLaid.lean; lots against one another:
  ShareAtHead.lean).
- THE LETTERS, CARRIED ALOUD: ch (the chain's number; meant: 0), own₀, n₀ (how many challenges stand
  in front of the test), t₀ (the number in the chain of the first switch's tree: the test's first
  tree where its first fresh table came earlier), arr (the witness's number at a tree and a tenant),
  ok, codes, sh (a message's shape), b, rest. NOTHING HERE TIES A LETTER TO WHAT IT IS MEANT TO BE
  (t₀ and n₀ at the full size: `treesTo_354`, `roundsTo_354`, OffAt354.lean).
- `psAt` is tied to `testAll`'s columns by nothing here: that is ScriptLotsTie.lean's `col_is_psAt`,
  under h ≤ k at the stages. It finds a stage's first round by `roundOf`, which counts k a stage;
  `stagesAll` counts h + g at the library's `sgOf`, whose g is k - h: one number where h ≤ k.
- THE REFUSAL MOVES A DEFAULT, IT DOES NOT DO AWAY WITH IT: where a text answers nothing the laying
  lays 0, at the pad too: of that case `Script.ofLots`' own docstring speaks.
- That «answers or not» hangs on public data alone is shown nowhere here. What LotsAnswer.lean has
  of it, in the review's words, cut by program: for the pads «whether a PAD's text answers is
  public: paid, whole»; «For the messages hpub frees the answer of coins and challenges, not of the
  input.» SO FOR THE MESSAGES IT IS STILL OWED, as a theorem, before any of these lots is laid; and
  that file's hypotheses hl, hpub and hw are shown of nothing.
- A pad's lot is handed no challenge: `testPadTxt` cannot refuse where ok does.
- WHAT AN ENTRY HOLDS. First tenant: a main entry, and a mask entry below `carriedIn`, is a fold of
  the left stage's rows, tails and fresh table: a function of other senders' coins, of the data, of
  challenges and, from the second switch on, of the part's own earlier coins; from `carriedIn` on a
  mask entry is one coin of the own cut. Second tenant, but at the last switch: the library's
  packing of the next fold's coefficients (`packedN`): where the next stage's h > 0 one coefficient
  stands at more than one entry, and place 0 holds a sum of coefficients; it is 0 at every entry
  where the mask code's message is too short. Second tenant at the last switch: the masking word:
  one main row and one mask row, each place one coin of the own cut. None of this is a theorem here.
- The fences are written off the stages' numbers; that they are the declared tenants' is owed (had:
  counts of rows at the written plan alone: `tenRowsW`, ShareAtHead.lean). k stands for the
  library's h + g: one number where h ≤ k.
- Where `freeRoom` is 0 the subtraction in `testPadTxt` stops at 0 and names a coin that is no free
  entry's: the library's `CsFit`, field mask, bars it; it is shown at no stages here.
- Silent defaults beneath, each in its own file's limits: `msgAt` (the empty column; word 0),
  `testDrawsAt` (the empty draw beyond the list), `frontAt` (at a list shorter than n₀: a shorter
  front, unmarked), `stretchOf` | `stretches` (0 beyond the count), `getD … default` (a stage of
  zeros), own₀ and no round shown in the Front's stead.
- The second tenant's pads: ScriptLotsPads.lean.
- `frontAt` SHOWS NO ROUND AND HANDS NO COLUMN (`Seen.bare []`). The review's word on that, cut by
  program: «But neither «none» nor «some []» is what runC hands at 354 (your own live_field), and a
  lot's text has no slot for it. So one named premise on the job is owed beside every tie of a text
  to a run: rec₀ · rows₀ · trees₀ read nothing of the Front's Seen.» No such premise is stated in
  this file or its eleven neighbours on these lots: none of them ties a text to a run.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots
import Johnson.Desc.SeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc (padB)
open Johnson.Prover.Link (PS)
open ProofFile.Honest.FirstThread (TreeLot MsgLot PadLot)

variable {Bk : ProverCoinCounts} {W X : Type}

/-- What the frame hands the test's second part off a run's coins; nothing where it refuses. ch: the
chain's number (meant: 0). `V := Empty` is written for want of a letter: a part's coins' type does
not hang on V; a law that ties these texts to a chain's own parts must cross it. -/
def handedRest (ch : ℕ) (J : TestJob W X) (k : Coins Bk) :
    Option (restPart (V := Empty) J).Coins :=
  (lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨J.p.place, 1⟩ (restPart (V := Empty) J)).toOption

/-- What precedes the test, of one list of challenges. n₀: how many stand in front of the test.
own₀: a letter. No round is shown and no column is handed. -/
def frontAt (own₀ : X) (n₀ : ℕ) (h : List Fmt.Drawn) : Front X := ⟨h.take n₀, own₀, Seen.bare []⟩

/-- The test's own challenges by number. BEYOND THE LIST: THE EMPTY DRAW: a law on it speaks below
the list's length. -/
def testDrawsAt (n₀ : ℕ) (h : List Fmt.Drawn) (r : ℕ) : Fmt.Drawn :=
  h.getD (n₀ + r) ⟨[], [], [], none⟩

/-- The own round in which the switch out of stage τ sends its tree ("SEND seed"). -/
def seedRound (stages : List Fmt.M1.Stage) (τ : ℕ) : ℕ :=
  roundOf stages τ + 1 + (stages.getD τ default).k

/-- **The test's tree number τ** (counted from the first switch's: right for a job whose first fresh
table came earlier alone): the one table of the part's own message at that round. TOTAL: the
table of no word where the frame does not lend, where ok says no, and where that message holds no
table. -/
def testTbl (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    ℕ → Coins Bk → W → List Fmt.Drawn → VerifiableInference.Desc.Place × Table :=
  fun τ k w h =>
    match handedRest ch J k with
    | some c =>
      if ok w (h.take n₀) (restCoins J c).mem then
        (J.p.place, ((msgAt J w (frontAt own₀ n₀ h) (restCoins J c) (testDrawsAt n₀ h)
          (seedRound J.p.nums.stages τ)).tables.head?).getD K1.wordlessTable)
      else (J.p.place, K1.wordlessTable)
    | none => (J.p.place, K1.wordlessTable)

/-- The test's lot of trees. off τ: the sending round's own number. -/
def testTreeLot (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) : TreeLot Bk W :=
  ⟨testTbl ch J own₀ n₀ ok, seedRound J.p.nums.stages⟩

/-- **The state at stage j.** A SECOND TEXT OF `stagesAll`'s RECURSION
(Johnson/Desc/K12/Honest/Stages.lean): its tie to `testAll`'s columns: `col_is_psAt`,
ScriptLotsTie.lean. -/
def psAt (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) : ℕ → PS
  | 0 => J.first w fr C
  | j + 1 =>
    aNext (coinsOf J.p.nums.stages C.hide C.rest) (j + 2 == J.p.nums.stages.length) j
      (J.p.nums.stages.getD j default) (J.p.nums.stages.getD (j + 1) default)
      (roundOf J.p.nums.stages j) (psAt J w fr C D j) D

/-- A stage's state read as a witness's message. t: the tenant. last: the stage is the last. INSIDE
THE FENCES ALONE: nothing beyond. -/
def stageMsg (s : Fmt.M1.Stage) (last : Bool) (Q : PS) (t : ℕ) (mask : Bool) (b q : ℕ) :
    Option GE :=
  match t, mask with
  | 0, false => if b < 2 ^ s.k ∧ q < s.C.l then some (Q.tabM (b + 2 ^ s.k * q)) else none
  | 0, true => if b < 2 ^ s.h ∧ q < s.Z.l then some (Q.tabZ (b + 2 ^ s.h * q)) else none
  | 1, true =>
    if (if last then b = 0 else b < 2 ^ s.h) ∧ q < s.Z.l then some (Q.fM b q) else none
  | 1, false => if last = true ∧ b = 0 ∧ q < s.C.l then some (Q.sM q) else none
  | _, _ => none

/-- **Message (τ, t), entry by entry**: at every entry inside the fences, or at none. -/
def testMsgTxt (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) (τ t : ℕ) :
    Coins Bk → W → List Fmt.Drawn → Bool → ℕ → ℕ → Option GE :=
  fun k w h mask b q =>
    (handedRest ch J k).bind fun c =>
      if ok w (h.take n₀) (restCoins J c).mem then
        stageMsg (J.p.nums.stages.getD (τ + 1) default) (τ + 2 == J.p.nums.stages.length)
          (psAt J w (frontAt own₀ n₀ h) (restCoins J c) (testDrawsAt n₀ h) (τ + 1)) t mask b q
      else none

/-- **The test's lots of messages**: two a switch. arr: the witness's number at (tree, tenant). t₀:
the first switch's tree's number in the chain: the test's first tree's where its first fresh table
came earlier. -/
def testMsgLots (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ t₀ : ℕ) (arr : ℕ → ℕ → ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) : List (MsgLot Bk W) :=
  (List.range (J.p.nums.stages.length - 1)).flatMap fun τ =>
    [0, 1].map fun t =>
      ⟨arr (t₀ + τ) t, n₀ + seedRound J.p.nums.stages τ, testMsgTxt ch J own₀ n₀ ok τ t⟩

/-- **The pad of the first tenant**: at the library's `padB`'s place (one place where sh τ has a
mask row; without one `padB` accepts every place of the last main row from its bound on, and this
text answers the same coin at each): the last free coin of switch τ, off the part's own cut as the
frame hands it (the messages' reader: both answer or neither, but for ok). sh τ: the message's
shape, a letter here. -/
def testPadTxt (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes) (sh : ℕ → OnBytes.OracleShape)
    (τ : ℕ) : Coins Bk → Bool → ℕ → ℕ → Option GE :=
  fun k mask b q =>
    if padB codes (sh τ) mask b q then
      (handedRest ch J k).map fun c =>
        (stretchOf c.1).e ((marksAt J.p.nums.stages τ).free +
          (freeRoom (J.p.nums.stages.getD τ default) (J.p.nums.stages.getD (τ + 1) default) - 1))
    else none

/-- **The test's lots of pads**: one a switch, at the first tenant. -/
def testPadLots (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes)
    (sh : ℕ → OnBytes.OracleShape) (t₀ : ℕ) : List (PadLot Bk W) :=
  (List.range (J.p.nums.stages.length - 1)).map fun τ =>
    ⟨t₀ + τ, 0, fun k _ => testPadTxt ch J codes sh τ k⟩

/-- The lot of trees by the member's number. b: the test's number in the chain. rest: a letter. -/
def testTl (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) (b : ℕ)
    (rest : ℕ → TreeLot Bk W) : ℕ → TreeLot Bk W :=
  fun m => if m = b then testTreeLot ch J own₀ n₀ ok else rest m

/-- The members' numbers for which a lot of trees is supplied. -/
def testTn (b : ℕ) : List ℕ := [b]

/-- Two lots a switch. -/
theorem testMsgLots_length (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ t₀ : ℕ) (arr : ℕ → ℕ → ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    (testMsgLots (Bk := Bk) ch J own₀ n₀ t₀ arr ok).length =
      2 * (J.p.nums.stages.length - 1) := by
  unfold testMsgLots
  rw [List.length_flatMap]
  simp [Nat.mul_comm]

/-- One lot a switch. -/
theorem testPadLots_length (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes)
    (sh : ℕ → OnBytes.OracleShape) (t₀ : ℕ) :
    (testPadLots (Bk := Bk) ch J codes sh t₀).length = J.p.nums.stages.length - 1 := by
  unfold testPadLots
  rw [List.length_map, List.length_range]

/-- At the member's number the lot is the test's; elsewhere the letter's. -/
theorem testTl_at (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) (b : ℕ)
    (rest : ℕ → TreeLot Bk W) :
    testTl ch J own₀ n₀ ok b rest b = testTreeLot ch J own₀ n₀ ok ∧
      ∀ m, m ≠ b → testTl ch J own₀ n₀ ok b rest m = rest m :=
  ⟨if_pos rfl, fun _ hm => if_neg hm⟩

end ProofFile.Honest.K12

end

#print axioms ProofFile.Honest.K12.handedRest
#print axioms ProofFile.Honest.K12.frontAt
#print axioms ProofFile.Honest.K12.testDrawsAt
#print axioms ProofFile.Honest.K12.seedRound
#print axioms ProofFile.Honest.K12.testTbl
#print axioms ProofFile.Honest.K12.testTreeLot
#print axioms ProofFile.Honest.K12.psAt
#print axioms ProofFile.Honest.K12.stageMsg
#print axioms ProofFile.Honest.K12.testMsgTxt
#print axioms ProofFile.Honest.K12.testMsgLots
#print axioms ProofFile.Honest.K12.testPadTxt
#print axioms ProofFile.Honest.K12.testPadLots
#print axioms ProofFile.Honest.K12.testTl
#print axioms ProofFile.Honest.K12.testTn
#print axioms ProofFile.Honest.K12.testMsgLots_length
#print axioms ProofFile.Honest.K12.testPadLots_length
#print axioms ProofFile.Honest.K12.testTl_at
