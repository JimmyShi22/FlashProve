-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CoinsTieBook.lean: the coins that a proximity test's term reads
are the sender's, from the book's two carried entries. This is proved of the second part's reader
only (`restCoins`, Parts.lean in this folder), for its fields `hide`, `tails` and `mem 0`, each
within the bounds in `CoinsTie`; its field `rest` has the second part's own coins, and on what the
first part's moves read nothing is stated. `CoinsTie` (SameAtOne.lean in this folder), at the job
made of a sending (`jobOne`, JobOne.lean) and at the coins that the frame lends the test's two
parts, where the book hands the second part two runs of the sender's coins: message 0's, from the
purse's start, and the riding table's, from that message's first mask coin on. The frame cuts each
run out of the owner's purse (`lend_stretch`, AgreeBook.lean), and the sender's own coins are that
purse cut at its start. General in the test's place p, in what is taken of the sending, Q, in the
job's state on entry `rec₀`, in the prover's input w, in the book and in the run's coins, which are
not looked into. One definition, a structure of propositions, and four theorems with their proofs.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. Coins (`Cs d`, the frame) are
elements of the base field and of the extension field, as many as the count d states (`Due`: fields
`f` and `e`). A cut (`Cs.cut`) is the n coins from number a on, in each field; it is `none` if they
are not all there. `stretchOf` (Coins.lean in this folder), `cf` and `ce`
(Johnson/Desc/ProofFile/Honest/K1/Coins.lean, below K1/Coins.lean) read coins by number, with 0
beyond the count. A part (`Part`, the frame) is the prover's side of some rounds in a row; its
address (`Addr`) is a place (`Place`: where a sub-protocol is in a description) and the part's
number there, from 0. look gives the coins at an address, and a part's purse is `(look a).2` at its
address a; the word does not mean the frame's type `Purse`, a table of such coins. A book Bk
(`ProverCoinCounts`, the frame) is public data. An entry of it (`Ahead`) is a block of its owner's coins, from
`start` on and `count` long, that one other part, its spender, is given too, marked as spent or as
carried; a run is such a block. `carryE Bk a` (Johnson/Desc/ProofFile/Honest/Law/Rule/Cell.lean)
lists the entries marked as carried whose spender is the part at the address a, in the book's order.
Q (`OneSent`, JobOne.lean) is what is taken of a sending of the kind K1: its public data `P`, what
rides `ride`, the caller's data `data` and the sender's address `addr`. The sender is the part at
`Q.addr`, and by its count is meant `dueR Q.P Q.ride`, the whole sending's count. Message number k
has the count `dueMsg` at its shape (`shapeAt Q.P k`, Johnson/Prover/Send/Core.lean), and its coins
begin at `startR Q.P Q.ride k` (all three K1/Coins.lean). The riding table is the first fold's fresh
table, by `jobOne` message 1 of the sender; `Q.ride 1` gives its two numbers (`K1.Ride`: k rounds, 2
^ h rows), or none. Message 1's first mask coin is the first of the coins of which `rowsR`
(K1/Coins.lean) makes that message's mask rows: among the coins of the extension field, number
`(startR Q.P Q.ride 1).e` plus, where the main rows are over that field (`mainDeg == 3`), the count
of the main rows' coins (`Steps.main` of `K1.stepsOf`). The job (`TestJob`, Test.lean in this
folder: what a caller supplies for its test) is `jobOne p Q rec₀`. p (`P12`,
Johnson/Desc/K12/Frame.lean) has the test's place `p.place`, and `stA p` (PlanB.lean in this folder)
is its first stage (`Fmt.M1.Stage`: among its fields the numbers k and h and the mask code `Z`); h
and g of `sgOf` (Johnson/Desc/K12/Law/ChainOf.lean) at a stage are h and k - h. The two parts are
`firstPart` and `restPart` of the job (Parts.lean in this folder), at the part numbers 0 and 1 of
the place; the Lean text writes 1 as 0 + 1. The row of the two parts is the list of them, and c
(`RowCoins`, the frame) is what `lendRow` (the frame) returns for it. The term is `testAll`
(Test.lean); the coins that it reads are a `TestCoins` C (Test.lean; fields `hide`, `tails`, `mem`,
`rest`), and `restCoins` (Parts.lean) makes one of what the second part is given. By the plan are
meant the public numbers that `BookTies` reads next to the book: the place, the stage and, of Q,
`P`, `ride` and `addr`.

  `coinsTie_of_book`: the row of the two parts is lent its coins · the sender's own coins are its
    purse cut at the start · `BookTies` ⟹ `CoinsTie`. The conclusion is
    `CoinsTie Q w (stA p) c₁ (restCoins (jobOne p Q rec₀) c.2.1)`, where c₁ is the cut in the second
    hypothesis and c.2.1 is what the second part is given. With C for that `restCoins`, the four
    fields of `CoinsTie` say: `memF`, `memE`: in each field, at i below message 0's count, coin
    number i of c₁ is coin number i of `C.mem 0`. `hide`: at i below 2 (h + g) + 1, the coin of c₁
    that is i after message 1's first mask coin is `C.hide i`. `tails`: at r below message 1's
    number of mask rows and q below `r` of its mask code, `maskTl r q` of `rowsR` at c₁ and message
    1 is `C.tails r q`
  `BookTies Bk pl a Q e₀ e₁`: on the book and the plan: the second part's carried entries number 0
    and 1 name the sender as their owner; the first starts at the purse's start, the second at
    message 1's first mask coin · both runs lie within the sender's count · the riding table's
    number of rounds is the stage's k; message 1's mask code has the stage's tail; it has 2 ^ h mask
    rows. A definition, a structure of propositions; pl is the test's place and a its first stage.
    Field by field. `at0`, `at1`: e₀ and e₁ are entries number 0 and 1 of `carryE Bk ⟨pl, 0 + 1⟩`.
    `own0`, `own1`: the `owner` of each is `Q.addr`. `start0`: `e₀.start` is `⟨0, 0⟩`. `start1`:
    `e₁.start.e` is the number of message 1's first mask coin; `e₁.start.f` is not read. `in0f`,
    `in0e`: message 0's count is at most the sender's, in each field. `in1`: `e₁.start.e` plus
    `dueFresh a` (Coins.lean: 2 k + 1 + 2 ^ h * `Z.r`) is at most the sender's count of coins of the
    extension field. `ride`: `Q.ride 1` is `some ⟨a.k, a.h⟩`. `k`: k = h + g at the stage, which
    says that h is at most k. `tail`: `r` of message 1's mask code (number `maskCode` of
    `Q.P.codes.mask`; a default code where there is none) is `a.Z.r`. `rows`: message 1 has
    `2 ^ a.h` mask rows
  `own_f`, `own_e`: a part's own coins, by number, are the purse's. Where y is the cut of c at
    `⟨0, 0⟩` and the count t: `cf y i` is `(stretchOf c).f i` at i below `t.f`, and `ce y i` is
    `(stretchOf c).e i` at i below `t.e`
  `cut_f`: the same as `cut_e` (AgreeBook.lean) for the base field's coins: a cut's coin number i is
    the owner's coin number start + i, at i below the cut's count, both sides read by `stretchOf`

By what. `lendRow_cons_ok` (Johnson/Desc/ProofFile/Honest/Law/Rule/RowModel.lean) and `lendPart_ok`
(Johnson/Desc/ProofFile/Honest/Law/Rule/PartCell.lean) take `lendRow` apart: what the second part is
given under `carries` is what `lend` (the frame) returns at `carryE` of its address. `lend_stretch`
at the entries number 0 and 1 gives each entry's cut, by `own0` and `own1` out of `(look Q.addr).2`,
and its count, which is the one that the part states there: message 0's count and
`⟨0, dueFresh (stA p)⟩`. So `BookTies` has no clause on the entries' counts. `cut_f` and `cut_e`
number the coins of these two cuts, and `own_f` and `own_e` those of c₁. The field `tails` also
unfolds `tailsIn` (Parts.lean), `rowsR` and `K1.stepsOf`, and calls `rowIdx_lt` (RowsCongr.lean in
this folder). `cut_f` unfolds `Cs.cut`; `own_f` calls `cut_f`, and `own_e` calls `cut_e`.

Hypotheses of `coinsTie_of_book`. h: `lendRow Bk rows look p.place` at the list of the two parts,
from part number 0 on, returns c. hown: the cut of `(look Q.addr).2` at `⟨0, 0⟩` and the count
`dueR Q.P Q.ride` is c₁. B: `BookTies Bk p.place (stA p) Q e₀ e₁`.

Limits.
- `BookTies` is a hypothesis: a public clause; it is shown at no book here. As a test with code
  (`bookTiesB`), and that test at the key file's book at the written sizes: BookTiesAtKey.lean in
  this folder.
- "Public" is said of `BookTies` by its text: it reads the book, the place, the stage, the two
  entries and, of Q, the fields `P`, `ride` and `addr`; it reads neither `Q.data` nor the input nor
  a coin.
- h and hown are hypotheses too. hown has the form in which `lendPart` (the frame) cuts a part's own
  coins, but no part at `Q.addr` occurs in this file: that the frame gives the sender c₁, and that
  the part at that address takes the count `dueR Q.P Q.ride`, is not stated.
- The conclusion is at the second part's `restCoins` only. Nothing is stated on what the first part
  is given.
- `CoinsTie` has no equation on the field `rest`, on `mem` at a number other than 0, or beyond the
  bounds in its four fields.
- look and rows, a table of the parts' own counts, are free parameters: the run's coins enter by
  look only. `rec₀` is a free parameter too; nothing here shows that its values are the verifier's
  state.
- Nothing on how a coin is sampled.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.SameAtOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open Johnson.Prover.Send (Rows shapeAt)
open ProofFile.Honest.K1 (rowsR dueR dueMsg startR cf ce)
open H2K.Pub (sgOf)

variable {V W X : Type}

theorem cut_f {d : Due} (c : Cs d) (a n : Due) (x : Cs n) (h : c.cut a n = some x) (i : ℕ)
    (hi : i < n.f) : (stretchOf x).f i = (stretchOf c).f (a.f + i) := by
  unfold Cs.cut at h
  split at h
  · rename_i hb
    cases h
    have h2 : a.f + i < d.f := by
      have := hb.1
      omega
    simp only [stretchOf, dif_pos hi, dif_pos h2]
  · cases h

/-- A part's own coins, by number, are the purse's. c: the purse. y: its cut at `⟨0, 0⟩` and the
count t. Stated for the coins of the base field, at i below `t.f`; `own_e` is the same for the coins
of the extension field. -/
theorem own_f {d t : Due} (c : Cs d) (y : Cs t) (h : c.cut ⟨0, 0⟩ t = some y) (i : ℕ)
    (hi : i < t.f) : cf y i = (stretchOf c).f i := by
  have k := cut_f c ⟨0, 0⟩ t y h i hi
  rw [Nat.zero_add] at k
  rw [← k]
  simp only [cf, stretchOf]

theorem own_e {d t : Due} (c : Cs d) (y : Cs t) (h : c.cut ⟨0, 0⟩ t = some y) (i : ℕ)
    (hi : i < t.e) : ce y i = (stretchOf c).e i := by
  have k := cut_e c ⟨0, 0⟩ t y h i hi
  rw [Nat.zero_add] at k
  rw [← k]
  simp only [ce, stretchOf]

/-- On the book and the plan: the hypothesis B of `coinsTie_of_book`. pl: the test's place. a: its
first stage. Q: what is taken of the sending. e₀, e₁: entries number 0 and 1 of those that the book
marks as carried and whose spender is the second part. -/
structure BookTies (Bk : ProverCoinCounts) (pl : VerifiableInference.Desc.Place) (a : Fmt.M1.Stage)
    (Q : OneSent W) (e₀ e₁ : Ahead) : Prop where
  at0 : (carryE Bk ⟨pl, 0 + 1⟩)[0]? = some e₀
  at1 : (carryE Bk ⟨pl, 0 + 1⟩)[1]? = some e₁
  own0 : e₀.owner = Q.addr
  own1 : e₁.owner = Q.addr
  start0 : e₀.start = ⟨0, 0⟩
  start1 : e₁.start.e = (startR Q.P Q.ride 1).e +
    (if (shapeAt Q.P 1).mainDeg == 3 then
      (K1.stepsOf Q.P.codes (shapeAt Q.P 1) (Q.ride 1)).main else 0)
  in0f : (dueMsg Q.P.codes (shapeAt Q.P 0) (Q.ride 0)).f ≤ (dueR Q.P Q.ride).f
  in0e : (dueMsg Q.P.codes (shapeAt Q.P 0) (Q.ride 0)).e ≤ (dueR Q.P Q.ride).e
  in1 : e₁.start.e + dueFresh a ≤ (dueR Q.P Q.ride).e
  ride : Q.ride 1 = some ⟨a.k, a.h⟩
  k : a.k = (sgOf a).h + (sgOf a).g
  tail : (Q.P.codes.mask.getD (shapeAt Q.P 1).maskCode default).r = a.Z.r
  rows : (shapeAt Q.P 1).maskRows = 2 ^ a.h

/-- **The four equations of `CoinsTie`, from the book.** h: `lendRow` returns c for the row of the
two parts. hown: c₁ is the cut of `(look Q.addr).2` at `⟨0, 0⟩` and the sender's count. B:
`BookTies` at the test's place and first stage. -/
theorem coinsTie_of_book (p : P12) (Q : OneSent W) (rec₀ : W → Front X → T12) (w : W) (Bk : ProverCoinCounts)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart (jobOne p Q rec₀) : Part V W X), restPart (jobOne p Q rec₀)])
    (h : lendRow Bk rows look p.place
      [(firstPart (jobOne p Q rec₀) : Part V W X), restPart (jobOne p Q rec₀)] 0 = .ok c)
    (c₁ : Cs (dueR Q.P Q.ride)) (hown : (look Q.addr).2.cut ⟨0, 0⟩ (dueR Q.P Q.ride) = some c₁)
    (e₀ e₁ : Ahead) (B : BookTies Bk p.place (stA p) Q e₀ e₁) :
    CoinsTie Q w (stA p) c₁ (restCoins (jobOne p Q rec₀) c.2.1) := by
  obtain ⟨-, l2'⟩ := lendRow_cons_ok h
  obtain ⟨l2, -⟩ := lendRow_cons_ok l2'
  obtain ⟨-, -, c2⟩ := lendPart_ok l2
  obtain ⟨q0, x0, k0, z0⟩ := lend_stretch look _ _ _ c2 0 e₀ B.at0
  obtain ⟨q1, x1, k1, z1⟩ := lend_stretch look _ _ _ c2 1 e₁ B.at1
  have n0 : e₀.count = dueMsg Q.P.codes (shapeAt Q.P 0) (Q.ride 0) := (Option.some.inj q0).symm
  have n1 : e₁.count = ⟨0, dueFresh (stA p)⟩ := (Option.some.inj q1).symm
  have m0 : (restCoins (jobOne p Q rec₀) c.2.1).mem 0 = stretchOf x0 := z0
  have m1 : ∀ i, (restCoins (jobOne p Q rec₀) c.2.1).hide i = (stretchOf x1).e i := fun i => by
    show (stretches _ c.2.1.2.2 1).e i = _
    rw [z1]
  rw [B.own0] at k0
  rw [B.own1] at k1
  have hfresh : ∀ i, i < dueFresh (stA p) → ce c₁ (e₁.start.e + i) = (stretchOf x1).e i := by
    intro i hi
    rw [own_e _ c₁ hown _ (by have := B.in1; omega), cut_e _ _ _ x1 k1 i (by rw [n1]; exact hi)]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun r q hr hq => ?_⟩
  · rw [m0, own_f _ c₁ hown i (lt_of_lt_of_le hi B.in0f),
      cut_f _ _ _ x0 k0 i (by rw [n0]; exact hi), B.start0, Nat.zero_add]
  · rw [m0, own_e _ c₁ hown i (lt_of_lt_of_le hi B.in0e),
      cut_e _ _ _ x0 k0 i (by rw [n0]; exact hi), B.start0, Nat.zero_add]
  · rw [m1, ← B.start1]
    refine hfresh i ?_
    rw [← B.k] at hi
    unfold dueFresh
    omega
  · have hq' : q < (stA p).Z.r := by
      rw [← B.tail]
      exact hq
    have hr' : r < 2 ^ (stA p).h := by
      rw [← B.rows]
      exact hr
    show _ = tailsIn (stA p) (stretches _ c.2.1.2.2 1).e r q
    rw [z1]
    unfold tailsIn
    have hb := rowIdx_lt hr' hq'
    rw [← hfresh _ (by unfold dueFresh; omega)]
    simp only [rowsR]
    rw [if_pos ⟨hr, hq⟩, B.start1, B.tail]
    have hm : (K1.stepsOf Q.P.codes (shapeAt Q.P 1) (Q.ride 1)).mask = 2 * (stA p).k + 1 := by
      unfold K1.stepsOf
      rw [B.ride]
      rfl
    rw [hm]
    congr 1
    omega

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.cut_f
#print axioms ProofFile.Honest.K12.own_f
#print axioms ProofFile.Honest.K12.own_e
#print axioms ProofFile.Honest.K12.coinsTie_of_book
#print axioms ProofFile.Honest.K12.BookTies
