-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/JobOne.lean: `jobOne` defines a proximity test's job (`TestJob`,
Test.lean in this folder: what a caller supplies for its test) from a sending of the kind K1. The
group under test has one member, message number 0 of the sending; the first fold's fresh table is
message number 1 of the same sender; the job's one tree is the sending's tree number 0. Of the three
functions that a caller supplies in a `TestJob`, `rows₀` and `trees₀` are built from the sending's
own definitions. The member's rows are `rowsR` (Johnson/Desc/ProofFile/Honest/K1/Coins.lean) at the
stretch of coins that the test's parts carry; the tree's column is the sending's own `col`
(Johnson/Prover/Send/Core.lean): no second text of it. The third function, `rec₀`, the state on
entry to the test, is a free parameter. At this job the first three of the four clauses of
`DataFront` (ShapeAll.lean in this folder) hold by construction, under the public clauses `OneFits`.
`DataFront` is the hypothesis on the prover's data of the theorem on acceptance there,
`accepts_every_list`. General in the test's place p, in what is taken of the sending, Q, and in
`rec₀`. Definitions, none marked `noncomputable`, and theorems with their proofs. The file is built
on K1/Coins.lean, which it imports: `K1.Ride`, `K1.rowsR`, `K1.dueMsg` and `K1.dueR` are defined
there. That file has definitions only, no theorem.

In the list: p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the test's place. `stA p`
(PlanB.lean in this folder) is its first stage (`Fmt.M1.Stage`), with the numbers k and h; `kk` of a
stage is h + (k - h) (Johnson/Desc/K12/Law/FirstOk.lean). w is the prover's input, fr what precedes
the test (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean), C the coins that `testAll` reads
(`TestCoins`, Test.lean). A stretch (`Stretch`, Coins.lean in this folder) is a run of coins, read
by number. `Rows` (Core.lean) is what a sending's caller supplies for one oracle message: its main
rows, its mask rows and their tails. `PS` (Johnson/Prover/Link/BodyState.lean) is what a prover
holds at a stage. Pst is the first stage's state, `(jobOne p Q rec₀).first w fr C` (Test.lean):
`rows₀` with the fresh table put in. T is the job's list of trees, `trees₀ w fr C.mem Pst`. Dp
(`Plain`, FirstOk.lean) are the plain data of the group under test: among them a book of trees
`book` (`TreeBook`, OnBytes/Iop/Ground.lean), the layout `L` (`GroupLayout`, Ground.lean), the
members `mems`, the fresh table `fresh`, and the places `ts` of their trees. A tree's place is its
index in `book.trees`. A seat (`Seat1`, FirstOk.lean) is an oracle message as a part of a tree; each
member and the fresh table is a seat. Ly (`TreeLay`, Ground.lean) says how the oracle messages of
one sending are placed in trees.

  `jobOne p Q rec₀`: a definition: the job. Its `p` and `rec₀` are the arguments. `members` has one
    entry: the sender's address `Q.addr`, the message's number 0, and that message's count of coins
    (`K1.dueMsg`, K1/Coins.lean). `fresh` is `some (Q.addr, 1)`. `rows₀` is `layOne` at the first
    stage, at the first rows that `layoutAt (rec₀ w fr)` states for member 0 (`oM`, `oZ`,
    FirstOk.lean), at the shape of message 0 (`shapeAt`, Core.lean) and at the rows
    `Q.mem w (mem 0)`. `trees₀` is one tree: its depth is `logN` of the sending's tree number 0
    (`K1.Par.trees`, Johnson/Desc/K1/Send.lean; 0 where the sending has no tree), and its column at
    x is `col Q.P (Q.rows w (mem 0) Pst) 0 x`
  `state_one`, `trees_one`, `cols_one`: under `OneFits p Q (rec₀ w fr) Dp s u Ly`, at every C, with
    c for `colsFrom T Dp.ts` (Johnson/Desc/K12/Honest/FirstAsks.lean) and R for
    `plainOne Q w (C.mem 0) Pst`. `state_one`: `StateAt (stA p) Dp Pst R`
    (Johnson/Desc/K12/Honest/FirstState.lean): the state holds the member's rows at the layout's
    blocks, and 0 elsewhere. `trees_one`: T is `groupTrees Dp.ts (logAt Dp.book) c`
    (Johnson/Desc/K12/Honest/GroupState.lean): the job's trees are the group's. `cols_one`:
    `ColsAt (stA p) Dp c R` (Johnson/Desc/K12/Honest/FirstRows.lean): the columns hold the rows'
    symbols. These are the fields `state`, `trees` and `cols` of `DataFront` at this job, c and R
  `rows_one`: the first stage's rows read of the members' stretches the one member's alone. In Lean:
    `rows₀ w fr mem` is `rows₀ w fr mem'` where mem and mem' agree at every number below the length
    of the job's `members`
  `OneFits p Q t₀ Dp s u Ly`: a definition, a structure of propositions: the public clauses, each
    under its name. t₀ is a state (`T12`, Johnson/Desc/K12/Join.lean), s the member's seat, u the
    tree's place. `plan`: `Q.P` passes `K1.planOkOwn` (Johnson/Desc/K1/Own.lean). `lay`: `layTrees`
    (Ground.lean) at the sending's codes and messages returns Ly. `two`: the sending has more than
    one message (1 < `Q.P.sent.size`; not: exactly two). `mems`, `ts`: the plain data have the one
    member s and the one tree u. `seat`, `fresh`: the two seats s and `Dp.fresh` are the sending's
    messages 0 and 1 (`SeatIs`, Johnson/Desc/K12/Honest/SentMember.lean, at the first stage).
    `tree0`, `tree1`: Ly states the tree 0 for both messages (read by `getD`, which gives 0 also
    where Ly has no entry). `some0`: Ly has the shape of at least one tree. `at0`, `at1`: the tree
    of each of the two seats is at the place u. `rowsF`: the fresh table's seat has 2 ^ h mask rows.
    `layout`: the layout `Dp.L` is the state's, `layoutAt t₀`. `inM`, `inZ`: the two blocks lie
    within the tables: `oM Dp.L 0` plus the seat's number of main rows is at most 2 ^ `kk (stA p)`,
    and `oZ Dp.L 0` plus its number of mask rows at most 2 ^ h. `depth`, `width`: the book's depth
    and width at u (`logAt`, `widthAt`, FirstOk.lean) are `logN` of the sending's tree number 0, and
    the main width plus the mask width of shape number 0 of Ly. What the clauses do not ask: Limits
  `OneSent W`: a definition, a structure: what is taken of the sending. `P`: its public data
    (`K1.Par`, Send.lean). `ride`: what rides: for a message's number, the two numbers of a fold's
    fresh table (`K1.Ride`, K1/Coins.lean), or none. `data`: the caller's data as a function of the
    input only, in the form that `rowsR` takes. `addr`: the sender's address (`Addr`, in the frame,
    Johnson/Desc/ProofFile/Honest/Frame.lean)
  `csOfStretch d S`: a definition: the coins of a count d (`Cs d`; d: `Due`; both in the frame),
    read off a stretch S: coin number i of each field is the value of S at i
  `OneSent.mem Q w S`: a definition: the member's rows: `rowsR` at `Q.P`, `Q.ride`, `Q.data w` and
    message number 0. Its coins are `csOfStretch` of S at the whole sending's count (`K1.dueR`)
  `OneSent.rows Q w S Pst k`: a definition: the rows of the sending's message number k. At k = 0:
    the member's. At every other k, not at 1 only: the fresh table as the first stage's state holds
    it: `mask` is `Pst.fM`, `maskTl` is `Pst.fT`, and the four fields of main rows are 0. The
    definition does not read how many messages the sending has
  `layOne a bM bZ sh V`: a definition: the stage's two tables and tails (`tabM`, `tabZ`, `tM`, `tZ`
    of `PS`): the rows V at the two blocks, 0 elsewhere. Row b of `tabM`, where bM ≤ b < bM +
    `sh.mainRows`, is main row b - bM of V; row b of `tabZ`, where bZ ≤ b < bZ + `sh.maskRows`, is
    mask row b - bZ of V; `tM` and `tZ` hold these rows' tails. An index n of `tabM` is read as row
    n % 2 ^ `kk a` and entry n / 2 ^ `kk a`; an index of `tabZ` the same with `a.h`. The fields
    `fM`, `fT`, `sM` and `sT` are 0
  `layoutAt t`: a definition: the layout (`layoutOf`, Johnson/Desc/Means/Layout.lean) of the group
    under test, number `t.g` of `t.st.groups`; an empty one where there is no such group
  `plainOne Q w S Pst`: a definition: the prover's rows as plain functions (`PlainRows`,
    FirstRows.lean): at every member's number the rows and tails of `Q.mem w S`; the fresh table's
    rows and tails are `Pst.fM` and `Pst.fT`
  `get_one`, `colsFrom_one`: under `OneFits`: every entry of `Dp.mems` is s, and its number is 0;
    the column `colsFrom T Dp.ts u x` is `col Q.P (Q.rows w (C.mem 0) Pst) 0 x`

By what. `state_one` unfolds `layOne` and computes the row and the entry of an index, with `get_one`
and the clauses `seat.shape`, `layout`, `inM` and `inZ`; the two clauses of `StateAt` on the fresh
table hold by `rfl`. `trees_one` is `groupTrees_colsFrom` (FirstAsks.lean) with the clauses `ts` and
`depth`. `cols_one` rewrites by `colsFrom_one`. The columns' width is `length_col`, with `lay_some`
(both Johnson/Prover/Send/Enc.lean) and the clauses `plan`, `lay`, `some0` and `width`. The member's
clause is `sent_memAt` and the fresh table's `sent_freshAt` (both SentMember.lean). `rows_one`
rewrites `mem 0` by its hypothesis.

Limits.
- One member, one tree: the form of the key file's test on the ranges; a group of several members is
  not covered.
- `OneFits` is a hypothesis; no value that meets it is given in this file. As a test with code:
  OneFitsB.lean (`oneFitsB`: all clauses but `layout`). At the key file's test on the ranges:
  FrontPlainAtKey.lean, FrontAtKey.lean (not imported here). In FrontPlainAtKey.lean
  `plain_at_KR` gives `oneFitsB` and the clause `layout` at one written place, at every sending with
  the written codes and messages and every state t whose `thinSh t` is one written shape; that a
  state on entry has that shape is a hypothesis there. The three theorems at `jobOne` at that place
  are put together in FrontAtKey.lean only (`front_data_KR`).
- "Public" is said of the clauses of `OneFits` by their text: of Q they read the field `P` only. By
  type the theorems take them at `rec₀ w fr` for t₀, so the clause `layout` reads the prover's input
  w and the front fr, through `rec₀`. Dp, s, u and Ly are free parameters.
- `OneSent.rows` gives the fresh table's rows at every message number from 1 on, and the clause
  `two` asks 1 < `Q.P.sent.size`, not that the size is 2; `oneFitsB` asks the same. `col` goes
  through all messages of the sending that lie in tree number 0, and no clause of `OneFits` asks
  that messages 0 and 1 are the only ones there. At a sending with a further message with mask rows
  in that tree, the job's column is made of `Pst.fM` and `Pst.fT` at two messages: the same
  coefficients and the same tails twice. No hypothesis of `state_one`, `trees_one` or `cols_one`
  names this case; whether `OneFits` can be met there is not shown. `Q.P.sent.size = 2` is a
  hypothesis elsewhere: h2 of `same_one` (SameAtOne.lean).
- `OneFits` and `oneFitsB` never read `Q.ride`. `Q.ride 0` enters the count in `members` and,
  through `rowsR`, the member's mask rows and their tails; no clause asks anything of it. The job's
  fresh table is `packedN` (Johnson/Prover/Link/BodyPack.lean) at the first stage's numbers
  (`TestJob.first`, Test.lean), whatever `Q.ride 1` is. `rowsR` at message number 1, with which
  `same_one` compares it, builds the mask rows by `Q.ride 1`: from `K1.Ride.count` coins, packed at
  its two numbers, or, where it is none, from one coin an entry. That `Q.ride 1` holds the first
  stage's k and h is a hypothesis elsewhere: `BookTies.ride` (CoinsTieBook.lean), and hR of
  `same_one`, which writes the first number as h + (k - h).
- `OneFits` asks neither that the fresh table's seat has no main row (`Dp.fresh.sh.mainRows = 0`)
  nor the room for the packing (h + 2 (k - h) + 1 ≤ `(stA p).Z.l`). Under `OneFits` only: where
  message 1 has main rows, the job's column holds them with entries and tails 0, where `rowsR` has
  coins as tails; without the room `Pst.fM` is 0 everywhere. Both are asked elsewhere: the clause
  "f:main" of `gpL` (FirstOk.lean; in `FrontAsks.plain`, ShapeAll.lean), the clause "room" of
  `planL` (PlanB.lean), hm and hl of `same_one`.
- So a statement on hiding that rests on `jobOne` needs, next to the clauses of `OneFits`, at least
  four further hypotheses: `Q.P.sent.size = 2`; that `Q.ride 1` holds the first stage's two numbers;
  no main row at the fresh table; the room for the packing. None of the four is a clause of
  `OneFits`.
- `rec₀` is a free parameter. Its values have the type of the verifier's state inside a test
  (`T12`); nothing here shows that they are the verifier's state.
- The last clause of `DataFront` (`allSay`), that the group's open rows say true things of the
  member's words, is not shown and not used: it is a statement on the rows' content, and it does not
  follow from how the job is built. So `DataFront` is shown at no value here.
- That the stretch which the test's parts carry holds the coins with which the sender made its
  message: CoinsTieBook.lean. It is not shown in this file.
- `Q.mem` takes its coins at the whole sending's count, while `members` states message 0's count.
  That `rowsR` at one message depends on that message's coins only is not shown in this file:
  `rowsR_congr` (RowsCongr.lean). `csOfStretch` reads the stretch from its number 0 on: this fits
  message number 0 only, whose coins begin at ⟨0, 0⟩ (`K1.startR`, K1/Coins.lean). For another
  message the stretch would have to be placed at `K1.startR` of that message's number.
- `rows_one` is on `rows₀`. No such theorem is stated on `trees₀`.
- In `trees_one` the right side is built from the left: c is made of the job's own trees.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.ShapeAll
import Johnson.Desc.ProofFile.Honest.K1.Coins
import Johnson.Desc.K12.Honest.SentMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open Johnson.Prover.Send (Rows col shapeAt length_col lay_some)
open H2K.Pub (sgOf)

variable {W X : Type}

/-- What is taken of the sending: its public data, what rides, the caller's data as a function of
the input only, the sender's address. -/
structure OneSent (W : Type) where
  P : K1.Par
  ride : ℕ → Option K1.Ride
  data : W → ℕ → ℕ → ℕ → Option (GF ⊕ GE)
  addr : Addr

/-- The coins of a count d, read off a stretch S: coin i of each field is the value of S at i. -/
def csOfStretch (d : Due) (S : Stretch) : Cs d := ⟨fun i => S.f i.val, fun i => S.e i.val⟩

/-- The member's rows. S: the stretch of the member's coins. In Lean: `K1.rowsR` at message number
0, at `csOfStretch` of S at the whole sending's count (`K1.dueR`). -/
def OneSent.mem (Q : OneSent W) (w : W) (S : Stretch) : Rows :=
  K1.rowsR Q.P Q.ride (Q.data w) (csOfStretch _ S) 0

/-- The rows of the sending's message number k: the member's at 0; at every other number, not at 1
only, the fresh table's. How many messages the sending has is not read here; `OneFits.two` asks more
than one, not exactly two. Pst: the first stage's state, which holds the fresh table. -/
def OneSent.rows (Q : OneSent W) (w : W) (S : Stretch) (Pst : PS) (k : ℕ) : Rows :=
  if k = 0 then Q.mem w S
  else { mainE := fun _ _ => 0, mainF := fun _ _ => 0, mainTlE := fun _ _ => 0
         mainTlF := fun _ _ => 0, mask := Pst.fM, maskTl := Pst.fT }

/-- The stage's two tables and tails: the member's rows at two blocks, 0 elsewhere. bM, bZ: the
first row of the block of main rows and of the block of mask rows. sh: the member's shape. V: its
rows. -/
def layOne (a : Fmt.M1.Stage) (bM bZ : ℕ) (sh : OracleShape) (V : Rows) : PS where
  tabM := fun n => if bM ≤ n % 2 ^ kk a ∧ n % 2 ^ kk a < bM + sh.mainRows then
    V.main (sh.mainDeg == 3) (n % 2 ^ kk a - bM) (n / 2 ^ kk a) else 0
  tabZ := fun n => if bZ ≤ n % 2 ^ a.h ∧ n % 2 ^ a.h < bZ + sh.maskRows then
    V.mask (n % 2 ^ a.h - bZ) (n / 2 ^ a.h) else 0
  tM := fun b q => if bM ≤ b ∧ b < bM + sh.mainRows then V.mainTl (sh.mainDeg == 3) (b - bM) q
    else 0
  tZ := fun b q => if bZ ≤ b ∧ b < bZ + sh.maskRows then V.maskTl (b - bZ) q else 0
  fM := fun _ _ => 0
  fT := fun _ _ => 0
  sM := fun _ => 0
  sT := fun _ => 0

/-- The layout of the group under test; an empty one where there is no such group. -/
def layoutAt (t : T12) : GroupLayout := ((t.st.groups[t.g]?).map (layoutOf t.st)).getD {}

/-- The job. rec₀: the state on entry to the test, of the type of the verifier's state inside a
test; a free parameter, not shown to be the verifier's. -/
def jobOne (p : P12) (Q : OneSent W) (rec₀ : W → Front X → T12) : TestJob W X where
  p := p
  members := [(Q.addr, 0, K1.dueMsg Q.P.codes (shapeAt Q.P 0) (Q.ride 0))]
  fresh := some (Q.addr, 1)
  rec₀ := rec₀
  rows₀ := fun w fr mem => layOne (stA p) (oM (layoutAt (rec₀ w fr)) 0)
    (oZ (layoutAt (rec₀ w fr)) 0) (shapeAt Q.P 0) (Q.mem w (mem 0))
  trees₀ := fun w _ mem Pst => [((Q.P.trees.getD 0 {}).logN, col Q.P (Q.rows w (mem 0) Pst) 0)]

/-- The prover's rows as plain functions. Every member's number gets the one member's rows. -/
def plainOne (Q : OneSent W) (w : W) (S : Stretch) (Pst : PS) : PlainRows where
  M := fun _ => (Q.mem w S).main ((shapeAt Q.P 0).mainDeg == 3)
  T := fun _ => (Q.mem w S).mainTl ((shapeAt Q.P 0).mainDeg == 3)
  Z := fun _ => (Q.mem w S).mask
  ZT := fun _ => (Q.mem w S).maskTl
  F := Pst.fM
  FT := Pst.fT

/-- **The first stage's rows read the one member's stretch alone.** h: mem and mem' agree at every
number below the length of the job's `members`. -/
theorem rows_one (p : P12) (Q : OneSent W) (rec₀ : W → Front X → T12) (w : W) (fr : Front X)
    (mem mem' : ℕ → Stretch) (h : ∀ t, t < (jobOne p Q rec₀).members.length → mem t = mem' t) :
    (jobOne p Q rec₀).rows₀ w fr mem = (jobOne p Q rec₀).rows₀ w fr mem' := by
  show layOne _ _ _ _ (Q.mem w (mem 0)) = layOne _ _ _ _ (Q.mem w (mem' 0))
  rw [h 0 (Nat.zero_lt_one)]

/-- The public clauses. t₀: a state; in the theorems below it is `rec₀ w fr`, the state on entry to
the test. s: the member's seat. u: the tree's place in the book of trees. Ly: how the sending's
messages are placed in trees. Not among the clauses: that the sending has exactly two messages
(`two` asks more than one); that `Q.ride 1` holds the first stage's two numbers (`Q.ride` is never
read); that the fresh table's seat has no main row; the room for the packing in a mask row's
message. A statement on hiding that rests on `jobOne` needs at least these four as further
hypotheses. -/
structure OneFits (p : P12) (Q : OneSent W) (t₀ : T12) (Dp : Plain) (s : Seat1) (u : ℕ)
    (Ly : TreeLay) : Prop where
  plan : K1.planOkOwn Q.P = true
  lay : layTrees Q.P.codes Q.P.sent = some Ly
  two : 1 < Q.P.sent.size
  mems : Dp.mems = [s]
  ts : Dp.ts = [u]
  seat : SeatIs (stA p) Q.P Ly 0 s
  fresh : SeatIs (stA p) Q.P Ly 1 Dp.fresh
  tree0 : Ly.tree.getD 0 0 = 0
  tree1 : Ly.tree.getD 1 0 = 0
  some0 : 0 < Ly.shapes.size
  at0 : s.t = u
  at1 : Dp.fresh.t = u
  rowsF : Dp.fresh.sh.maskRows = 2 ^ (stA p).h
  layout : Dp.L = layoutAt t₀
  inM : oM Dp.L 0 + s.sh.mainRows ≤ 2 ^ kk (stA p)
  inZ : oZ Dp.L 0 + s.sh.maskRows ≤ 2 ^ (stA p).h
  depth : logAt Dp.book u = (Q.P.trees.getD 0 {}).logN
  width : widthAt Dp.book u = (Ly.shapes.getD 0 {}).mainWidth + (Ly.shapes.getD 0 {}).maskWidth

section Laws
variable (p : P12) (Q : OneSent W) (rec₀ : W → Front X → T12) (w : W) (fr : Front X)
  (C : TestCoins) {Dp : Plain} {s : Seat1} {u : ℕ} {Ly : TreeLay}
  (H : OneFits p Q (rec₀ w fr) Dp s u Ly)
include H

theorem get_one (j : Fin Dp.mems.length) : Dp.mems.get j = s ∧ j.val = 0 := by
  refine ⟨List.mem_singleton.1 (H.mems ▸ List.get_mem Dp.mems j), ?_⟩
  have hl : Dp.mems.length = 1 := by
    rw [H.mems]
    rfl
  exact Nat.lt_one_iff.1 (lt_of_lt_of_eq j.isLt hl)

/-- **The state holds the member's rows at the layout's blocks, and 0 elsewhere.** -/
theorem state_one : StateAt (stA p) Dp ((jobOne p Q rec₀).first w fr C)
    (plainOne Q w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) := by
  have hsh := H.seat.shape
  have hL := H.layout
  have pM : 0 < 2 ^ kk (stA p) := Nat.two_pow_pos _
  have pZ : 0 < 2 ^ (stA p).h := Nat.two_pow_pos _
  have inM := H.inM
  have inZ := H.inZ
  rw [hsh] at inM inZ
  rw [hL] at inM inZ
  refine ⟨fun j i e hi _ => ?_, fun j i q hi _ => ?_, fun j i e hi _ => ?_, fun j i q hi _ => ?_,
    fun b hb hn => ?_, fun b hb hn => ?_, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · obtain ⟨g, j0⟩ := get_one p Q rec₀ w fr H j
    rw [g, hsh] at hi
    rw [j0, hL]
    have e1 : (oM (layoutAt (rec₀ w fr)) 0 + i + 2 ^ kk (stA p) * e) % 2 ^ kk (stA p) =
        oM (layoutAt (rec₀ w fr)) 0 + i := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    have e2 : (oM (layoutAt (rec₀ w fr)) 0 + i + 2 ^ kk (stA p) * e) / 2 ^ kk (stA p) = e := by
      rw [Nat.add_mul_div_left _ _ pM, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    show (if _ ∧ _ then _ else 0) = _
    rw [e1, e2, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    rfl
  · obtain ⟨g, j0⟩ := get_one p Q rec₀ w fr H j
    rw [g, hsh] at hi
    rw [j0, hL]
    show (if _ ∧ _ then _ else 0) = _
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    rfl
  · obtain ⟨g, j0⟩ := get_one p Q rec₀ w fr H j
    rw [g, hsh] at hi
    rw [j0, hL]
    have e1 : (oZ (layoutAt (rec₀ w fr)) 0 + i + 2 ^ (stA p).h * e) % 2 ^ (stA p).h =
        oZ (layoutAt (rec₀ w fr)) 0 + i := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    have e2 : (oZ (layoutAt (rec₀ w fr)) 0 + i + 2 ^ (stA p).h * e) / 2 ^ (stA p).h = e := by
      rw [Nat.add_mul_div_left _ _ pZ, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    show (if _ ∧ _ then _ else 0) = _
    rw [e1, e2, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    rfl
  · obtain ⟨g, j0⟩ := get_one p Q rec₀ w fr H j
    rw [g, hsh] at hi
    rw [j0, hL]
    show (if _ ∧ _ then _ else 0) = _
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    rfl
  · have h0 : 0 < Dp.mems.length := by
      rw [H.mems]
      exact Nat.zero_lt_one
    have k := hn ⟨0, h0⟩
    rw [(get_one p Q rec₀ w fr H ⟨0, h0⟩).1, hsh, hL] at k
    refine ⟨fun e _ => ?_, fun q _ => ?_⟩
    · have e1 : (b + 2 ^ kk (stA p) * e) % 2 ^ kk (stA p) = b := by
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hb
      show (if _ ∧ _ then _ else 0) = _
      rw [e1]
      exact if_neg k
    · exact if_neg k
  · have h0 : 0 < Dp.mems.length := by
      rw [H.mems]
      exact Nat.zero_lt_one
    have k := hn ⟨0, h0⟩
    rw [(get_one p Q rec₀ w fr H ⟨0, h0⟩).1, hsh, hL] at k
    refine ⟨fun e _ => ?_, fun q _ => ?_⟩
    · have e1 : (b + 2 ^ (stA p).h * e) % 2 ^ (stA p).h = b := by
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hb
      show (if _ ∧ _ then _ else 0) = _
      rw [e1]
      exact if_neg k
    · exact if_neg k

/-- **The job's trees are the group's trees** (`groupTrees`), made of the columns of the job's own
trees (`colsFrom`). -/
theorem trees_one :
    (jobOne p Q rec₀).trees₀ w fr C.mem ((jobOne p Q rec₀).first w fr C) =
      groupTrees Dp.ts (logAt Dp.book)
        (colsFrom ((jobOne p Q rec₀).trees₀ w fr C.mem ((jobOne p Q rec₀).first w fr C))
          Dp.ts) := by
  refine (groupTrees_colsFrom _ Dp.ts (logAt Dp.book) (by rw [H.ts]; exact List.nodup_singleton u)
    ?_).symm
  rw [H.ts]
  show [(Q.P.trees.getD 0 {}).logN] = [logAt Dp.book u]
  rw [H.depth]

/-- The one tree's column, read by `colsFrom` at the place u, is the sending's `col` at tree number
0. -/
theorem colsFrom_one (x : ℕ) :
    colsFrom ((jobOne p Q rec₀).trees₀ w fr C.mem ((jobOne p Q rec₀).first w fr C)) Dp.ts u x =
      col Q.P (Q.rows w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) 0 x := by
  unfold colsFrom
  rw [H.ts, List.idxOf_cons_self]
  rfl

/-- **The columns hold the rows' symbols.** -/
theorem cols_one : ColsAt (stA p) Dp
    (colsFrom ((jobOne p Q rec₀).trees₀ w fr C.mem ((jobOne p Q rec₀).first w fr C)) Dp.ts)
    (plainOne Q w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) := by
  obtain ⟨Ly', hL', eL⟩ := lay_some Q.P H.plan
  obtain rfl : Ly = Ly' := Option.some.inj (H.lay.symm.trans hL')
  refine ⟨fun u' hu x _ => ?_, fun j x _ => ?_, fun x _ b hb => ?_⟩
  · rw [H.ts] at hu
    obtain rfl := List.mem_singleton.1 hu
    rw [colsFrom_one p Q rec₀ w fr C H, length_col Q.P _ H.plan 0 x (by rw [eL]; exact H.some0), eL,
      H.width]
  · obtain ⟨g, j0⟩ := get_one p Q rec₀ w fr H j
    rw [g, j0, H.at0, colsFrom_one p Q rec₀ w fr C H]
    have k := sent_memAt Q.P (Q.rows w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) H.plan Ly H.lay 0
      (Nat.lt_trans Nat.zero_lt_one H.two) H.seat
      (plainOne Q w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) 0 x
      (fun _ _ _ _ => by rw [H.seat.shape]; rfl) (fun _ _ _ _ => by rw [H.seat.shape]; rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    rw [H.tree0] at k
    exact k
  · rw [H.at1, colsFrom_one p Q rec₀ w fr C H]
    have k := sent_freshAt Q.P (Q.rows w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) H.plan Ly H.lay
      1 H.two H.fresh (plainOne Q w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) x b
      (by rw [H.rowsF]; exact hb) (fun _ _ => rfl) (fun _ _ => rfl)
    rw [H.tree1] at k
    exact k

end Laws

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.rows_one
#print axioms ProofFile.Honest.K12.get_one
#print axioms ProofFile.Honest.K12.state_one
#print axioms ProofFile.Honest.K12.trees_one
#print axioms ProofFile.Honest.K12.colsFrom_one
#print axioms ProofFile.Honest.K12.cols_one
#print axioms ProofFile.Honest.K12.OneSent
#print axioms ProofFile.Honest.K12.csOfStretch
#print axioms ProofFile.Honest.K12.OneSent.mem
#print axioms ProofFile.Honest.K12.OneSent.rows
#print axioms ProofFile.Honest.K12.layOne
#print axioms ProofFile.Honest.K12.layoutAt
#print axioms ProofFile.Honest.K12.jobOne
#print axioms ProofFile.Honest.K12.plainOne
#print axioms ProofFile.Honest.K12.OneFits
