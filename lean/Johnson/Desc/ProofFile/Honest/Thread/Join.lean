-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Join.lean: the one list that joins the senders' lots for a
`Script` laid by lots (`Script.ofLots`, Honest/Thread/ScriptLots.lean), as a term, with tests on
public data that can fail. The rule of the join: the list holds the senders' whole-message lots
alone, each laid once; a kept copy's message is its first sender's, so a copy has no lot of messages
and has a lot of pads of its own. The shared sending's (K1's) share is written out, over a list of
jobs by the member's number. Every other sender's share is a record of parameters (`Others`).

One term for every size. A job's number is meant to be read off the flat list by the job's own place
(`borderNo`, `byNo`): so the same term can be laid at a small description and at the full-size one.
`joinQ` and the lemmas on it take the jobs with their numbers as a parameter. Where `placesB` and
`foundB` pass, such a list is `byNo`'s (`found_is_byNo`).

  1  `byNo`   jobs with their members' numbers, by `borderNo` (Honest/Thread/Thr.lean)
  2  `Others`, `joinMl`, `joinPl`, `joinTl`, `joinQ`   the list in its three parts; the `Script`
  3  `nums`, `seatsOf`, `agreeB`, `unowned`, `ownedB`, `treeless`, `treesB`, `numsB`, `placesB`,
     `foundB`, `coinsB`   the tests. None applies a lot's text, and none reads a job's data. They
     read a lot's number, a pad's seat, a block's place and its count of trees, the book's count, a
     job's number and place, and its plan and riding tables through `dueR`; `unowned` also the
     numbering `arr` and the list of seats
  4  `msgsAgree_of_nodup`, `padsAgree_of_nodup`, `agree_of_test`   from the test to `MsgsAgree` and
     `PadsAgree`
  5  `nums_k1`, `seats_k1`   the public face of K1's lots
  6  `join_tie_k1`, `join_trees_k1`   K1's hypotheses on the `Script`, at the joined `Script`
  7  `owned_gives`, `k1_answers`, `tl_reads_no_rest`, `nums_gives`, `found_gives`, `places_gives`,
     `found_is_byNo`   what the other tests give
  8  ten negative tests: each test can say no. `ownedB` and `treesB` are tried at `unowned` and at
     `treeless`

Limits.
  * No list is laid here for any description: the flat list, `front`, the numbering `arr`, the list
    of seats, the jobs, the book, the reader `wit`, `own₀` and the other senders' share are
    parameters. `Others.tl` stays a parameter in every lemma: no default is written here for a
    member for which nobody supplies a `TreeLot`.
  * All is the first chain's: the carried record, the chain number 0 in `msgTxt 0` and `Bk.rowsOf
    0`, and part 0 of each address are written in. `front` stays a parameter; at `Letters.thread` it
    is 0.
  * Where the lemmas say nothing. `join_tie_k1`: at an empty list of jobs and at a job that sends no
    message. `join_trees_k1`: at an empty list of jobs, at a member whose block declares no tree,
    and at a job whose number lies beyond the flat list. `owned_gives`: at an empty list of seats.
    `tl_reads_no_rest`: at a list that declares no tree. `found_gives` and `found_is_byNo`: at no
    job. `foundB` and `coinsB` say yes at no job, `numsB` at no job and no number, `treesB` where no
    block declares a tree, `placesB` at no block and at one, `agreeB` at no lot. `ownedB` can pass
    with every lot among the others': the two lemmas on K1 then still say nothing.
  * `agreeB` is stronger than `MsgsAgree` and `PadsAgree`: it refuses any two lots of one number or
    of one seat, agreeing or not. That is the rule of the join. `k1MsgLots` lays a lot for every
    message of every job: at a job whose plan holds a kept copy, at a numbering that gives an
    original and its copies one number, and where the original's lot is laid too, `agreeB` says no.
  * Of the rule's two halves one is tested. "Each laid once" is `agreeB`. `ownedB` asks that a lot
    bears the number or the seat, not that its text answers: that another sender's lot answers at
    every entry of its message is asked by nothing here (for K1's: `k1_answers`). Where none
    answers, `Script.ofLots` puts zero (Honest/Thread/ScriptLots.lean, "Where nobody owns").
  * `join_tie_k1` and `join_trees_k1` ask nothing of the book: each docstring says what that means
    for whoever quotes the lemma. At written data `coinsB` is the test on the book.
  * No test here holds a block's count of trees against the job's plan: at a member that declares
    more, the table laid is the table without a word; at a member that declares fewer, K1's lots
    bear seats of a later member's trees, and `ownedB` counts them as those seats' owners
    (`treesFitB`, Honest/Thread/JoinFit.lean, is that test).
  * That no coin stands at two entries is asked by no form here. No test here reads a lot's fx or a
    `TreeLot`'s off.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Rows
import Johnson.Desc.ProofFile.Honest.K1.Law.TreeLotsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.K1

variable {Bk : ProverCoinCounts} {Cl Wl Xi X Cells Tok : Type}

/-! ## 1 By the place -/

/-- Jobs, each with its member's number: the flat list's length where the job's place is not found
(`foundB` says no there); the first block's of two at one place (`placesB`). -/
def byNo (bs : List (Block S Cl)) (js : List (SendJob (PlaceIn Xi) X)) :
    List (Nat × SendJob (PlaceIn Xi) X) :=
  js.map fun J => (borderNo bs J.P.place, J)

/-! ## 2 The list -/

/-- What the senders beside K1 hand the join: their lots of messages and of pads, their
`TreeLot`s by the member's number, and the numbers of the members for which they supply one. -/
structure Others (Bk : ProverCoinCounts) (Wl : Type) where
  ml : List (MsgLot Bk Wl)
  pl : List (PadLot Bk Wl)
  tl : Nat → TreeLot Bk Wl
  tn : List Nat

/-- **The list's lots of messages.** K1's stand first and win where both answer; `agreeB` refuses a
list in which two lots bear one number. -/
def joinMl (bs : List (Block S Cl)) (front : Nat) (arr : ℕ → ℕ → ℕ) (wit : Wl → PlaceIn Xi)
    (own₀ : X) (jobs : List (Nat × SendJob (PlaceIn Xi) X)) (O : Others Bk Wl) :
    List (MsgLot Bk Wl) :=
  k1MsgLots bs front arr wit own₀ jobs ++ O.ml

/-- **The list's lots of pads.** K1's stand first and win where both answer; `agreeB` refuses a list
in which two lots sit at one seat. -/
def joinPl (bs : List (Block S Cl)) (jobs : List (Nat × SendJob (PlaceIn Xi) X))
    (O : Others Bk Wl) : List (PadLot Bk Wl) :=
  k1PadLots bs jobs ++ O.pl

/-- **The list's `TreeLot`s, by the member's number.** At a number that stands twice among the jobs
the first job's lot is laid; at a number that stands among the jobs and in `O.tn`, K1's, and `O.tl`
is not read there. `numsB` refuses both. -/
def joinTl (wit : Wl → PlaceIn Xi) (own₀ : X) (jobs : List (Nat × SendJob (PlaceIn Xi) X))
    (O : Others Bk Wl) : Nat → TreeLot Bk Wl :=
  k1TreeLots wit own₀ jobs O.tl

/-- **The `Script` laid of the list.** -/
def joinQ (bs : List (Block S Cl)) (front : Nat) (cells : Wl → Cells) (tok : Wl → Tok)
    (arr : ℕ → ℕ → ℕ) (wit : Wl → PlaceIn Xi) (own₀ : X)
    (jobs : List (Nat × SendJob (PlaceIn Xi) X)) (O : Others Bk Wl) :
    Script Bk Wl Cells Tok MsgT :=
  Script.ofLots bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
    (joinMl bs front arr wit own₀ jobs O)

/-! ## 3 The tests -/

/-- A list's public face: the lots' numbers. -/
def nums (ml : List (MsgLot Bk Wl)) : List Nat := ml.map (·.n)

/-- A list's public face: the pads' seats. -/
def seatsOf (pl : List (PadLot Bk Wl)) : List (Nat × Nat) := pl.map fun L => (L.j, L.t)

/-- **"Agree"**: no number stands twice among the lots of messages, no seat twice among the lots of
pads. Stronger than `MsgsAgree` and `PadsAgree`: it refuses any two lots of one number or of one
seat, agreeing or not. -/
def agreeB (ml : List (MsgLot Bk Wl)) (pl : List (PadLot Bk Wl)) : Bool :=
  decide (nums ml).Nodup && decide (seatsOf pl).Nodup

/-- The seats, out of a list of seats, whose message has no lot or whose pad has none. -/
def unowned (arr : ℕ → ℕ → ℕ) (seats : List (Nat × Nat)) (ml : List (MsgLot Bk Wl))
    (pl : List (PadLot Bk Wl)) : List (Nat × Nat) :=
  seats.filter fun s => !((nums ml).contains (arr s.1 s.2) && (seatsOf pl).contains s)

/-- **"Owned"**: there are none. A lot counts as an owner by its number or its seat alone, whether
its text answers or not. -/
def ownedB (arr : ℕ → ℕ → ℕ) (seats : List (Nat × Nat)) (ml : List (MsgLot Bk Wl))
    (pl : List (PadLot Bk Wl)) : Bool :=
  (unowned arr seats ml pl).isEmpty

/-- The members that declare a tree and stand in no list of numbers. cnt: for each member, how many
trees it declares. -/
def treeless (cnt tn : List Nat) : List Nat :=
  (List.range cnt.length).filter fun b => cnt.getD b 0 != 0 && !tn.contains b

/-- There are none. -/
def treesB (bs : List (Block S Cl)) (tn : List Nat) : Bool :=
  (treeless (bs.map fun blk => (blk.oracles.flatMap id).length) tn).isEmpty

/-- No number stands twice among the jobs' numbers and the numbers for which the others supply a
`TreeLot`. -/
def numsB (jobs : List (Nat × SendJob (PlaceIn Xi) X)) (tn : List Nat) : Bool :=
  decide (jobs.map (·.1) ++ tn).Nodup

/-- No place stands twice in the flat list: so `borderNo` finds the one block at a place. -/
def placesB (bs : List (Block S Cl)) : Bool := decide (bs.map (·.place)).Nodup

/-- At each job's number the flat list has a block, and that block stands at the job's place. -/
def foundB (bs : List (Block S Cl)) (jobs : List (Nat × SendJob (PlaceIn Xi) X)) : Bool :=
  jobs.all fun x => (bs[x.1]?).any fun blk => blk.place == x.2.P.place

/-- The book's count at each job's address is just the part's due: the field hasCoins of K1's
record (Honest/K1/Seated.lean), the equation, as a test. -/
def coinsB (Bk : ProverCoinCounts) (jobs : List (Nat × SendJob (PlaceIn Xi) X)) : Bool :=
  jobs.all fun x => decide (dueAt (Bk.rowsOf 0) ⟨x.2.P.place, 0⟩ = dueR x.2.P x.2.ride)

/-! ## 4 From the test to the forms -/

/-- A number that stands once has one lot. -/
theorem msgsAgree_of_nodup {ml : List (MsgLot Bk Wl)} (h : (nums ml).Nodup) : MsgsAgree ml := by
  intro L hL L' hL' e
  unfold nums at h
  obtain rfl : L' = L := List.inj_on_of_nodup_map h hL' hL e
  intro k w hd mask row place y y' q q'
  exact Option.some.inj (q'.symm.trans q)

/-- A seat that stands once has one lot. -/
theorem padsAgree_of_nodup {pl : List (PadLot Bk Wl)} (h : (seatsOf pl).Nodup) :
    PadsAgree pl := by
  intro L hL L' hL' ej et
  unfold seatsOf at h
  obtain rfl : L' = L := List.inj_on_of_nodup_map h hL' hL (by
    show (L'.j, L'.t) = (L.j, L.t)
    rw [ej, et])
  intro k w mask row place y y' q q'
  exact Option.some.inj (q'.symm.trans q)

/-- **Where the test passes, all lots agree.** -/
theorem agree_of_test {ml : List (MsgLot Bk Wl)} {pl : List (PadLot Bk Wl)}
    (h : agreeB ml pl = true) : MsgsAgree ml ∧ PadsAgree pl := by
  unfold agreeB at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact ⟨msgsAgree_of_nodup h.1, padsAgree_of_nodup h.2⟩

/-! ## 5 K1's lots' public face -/

variable (bs : List (Block S Cl)) (front : Nat) (arr : ℕ → ℕ → ℕ) (wit : Wl → PlaceIn Xi) (own₀ : X)
  (jobs : List (Nat × SendJob (PlaceIn Xi) X))

/-- The numbers of K1's lots of messages: plans, seats and numbers alone. -/
theorem nums_k1 : nums (k1MsgLots (Bk := Bk) bs front arr wit own₀ jobs) =
    jobs.flatMap fun x => (List.range x.2.P.sent.size).map fun n =>
      arr (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2 := by
  unfold nums k1MsgLots
  rw [List.map_flatMap]
  refine List.flatMap_congr fun x _ => ?_
  unfold k1MsgLotsAt
  rw [List.map_map]
  rfl

/-- The seats of K1's lots of pads. -/
theorem seats_k1 : seatsOf (k1PadLots (Bk := Bk) (Wl := Wl) bs jobs) =
    jobs.flatMap fun x => (List.range x.2.P.sent.size).map fun n =>
      seatAtMember bs x.1 x.2.P n := by
  unfold seatsOf k1PadLots
  rw [List.map_flatMap]
  refine List.flatMap_congr fun x _ => ?_
  unfold k1PadLotsAt
  rw [List.map_map]
  rfl

/-! ## 6 K1's hypotheses at the joined `Script` -/

variable {bs front arr wit own₀ jobs}

/-- **K1's tie at the joined `Script`**, at each member of the list. It says nothing at an empty
list of jobs or at a job that sends no message. At a book whose count at the part's address does not
cover the part's due this law holds for nothing, and it is never quoted as if it spoke there:
hasCoins is neither asked nor paid here: whoever quotes this law at a book names hasCoins at that
book beside it. -/
theorem join_tie_k1 {O : Others Bk Wl}
    (ha : agreeB (joinMl bs front arr wit own₀ jobs O) (joinPl bs jobs O) = true)
    (cells : Wl → Cells) (tok : Wl → Tok) (Vd : Wl → Prop)
    {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) :
    (∀ n, n < x.2.P.sent.size →
      OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd (front + roundsTo bs x.1)
        (arr (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2)
        (front + roundsTo bs x.1) (msgTxt 0 wit x.2 own₀ n)) ∧
    ∀ n, n < x.2.P.sent.size →
      OwnPads (joinQ bs front cells tok arr wit own₀ jobs O) Vd
        (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2
        (fun k _ => padTxt 0 x.2 n k) :=
  have A := agree_of_test ha
  ⟨msgs_of_lots bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
      (joinMl bs front arr wit own₀ jobs O) arr wit own₀ x
      (hin_msgs_of_agree (fun _ hL => List.mem_append.2 (Or.inl hL)) A.1 hx) Vd,
    pads_of_lots bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
      (joinMl bs front arr wit own₀ jobs O) x
      (hin_pads_of_agree (fun _ hL => List.mem_append.2 (Or.inl hL)) A.2 hx) Vd⟩

/-- **K1's trees at the joined `Script`**, at a thread whose table and fixed are the joined
`Script`'s and whose bs and front are those at which it is laid. It stands at the flat list of a
chain, as K1's authors' lemma beneath it does: narrower than the tests and than `join_tie_k1`. It
says nothing at an empty list of jobs, at a member whose block declares no tree, or at a job whose
number lies beyond the flat list; the count is the block's, and nothing here holds it against the
job's plan. `nums_gives` pays hnd, `found_gives` hblk. A sentence that was set for the lemma
beneath, to the letter, in marks: "At a book whose count at the part's address does not cover the
part's due this law holds for nothing, and it is never quoted as if it spoke there: hasCoins is
neither asked nor paid here: whoever quotes this law at a book names hasCoins at that book beside
it." In this file's own words: nothing is asked of the book here, and at such a book the end is not
empty: it speaks of `treeTbl`'s table without a word. Whoever speaks of coins at k1TreeLots owes
"the book covers the part's coins" by name. -/
theorem join_trees_k1 {V X' Pb : Type} {cF : Chain S ProofFile.Cl} {front : Nat} {arr : ℕ → ℕ → ℕ}
    {O : Others Bk Wl} (cells : Wl → Cells) (tok : Wl → Tok)
    (T : Thread Bk S ProofFile.Cl V Wl X' Pb) (hbs : T.bs = cF.blocksInOrder) (hfr : T.front = front)
    (htab : T.table = (joinQ cF.blocksInOrder front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder front cells tok arr wit own₀ jobs O).fixed)
    (hnd : (jobs.map (·.1)).Nodup) {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs)
    {blk : Block S ProofFile.Cl} (hblk : cF.blocksInOrder[x.1]? = some blk) :
    OwnTrees T x.1 (blk.oracles.flatMap id).length (treeTbl 0 wit x.2 own₀) (fun _ => 0) :=
  ownTrees_at_lots front cells tok (joinPl cF.blocksInOrder jobs O)
    (joinMl cF.blocksInOrder front arr wit own₀ jobs O) wit own₀ O.tl T hbs hfr htab hfix hnd hx hblk

/-! ## 7 What the other tests give -/

/-- **Where "owned" passes, each seat's message has a lot and each seat has a pad's lot.** It says
nothing at an empty list of seats. -/
theorem owned_gives {arr : ℕ → ℕ → ℕ} {seats : List (Nat × Nat)} {ml : List (MsgLot Bk Wl)}
    {pl : List (PadLot Bk Wl)} (h : ownedB arr seats ml pl = true) : ∀ s ∈ seats,
    (∃ L ∈ ml, L.n = arr s.1 s.2) ∧ ∃ L ∈ pl, L.j = s.1 ∧ L.t = s.2 := by
  intro s hs
  unfold ownedB unowned at h
  rw [List.isEmpty_iff, List.filter_eq_nil_iff] at h
  have h1 := h s hs
  rw [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true] at h1
  have a : arr s.1 s.2 ∈ nums ml := List.contains_iff_mem.1 h1.1
  have b : s ∈ seatsOf pl := List.contains_iff_mem.1 h1.2
  obtain ⟨L, hL, e⟩ := List.mem_map.1 a
  obtain ⟨P, hP, e'⟩ := List.mem_map.1 b
  exact ⟨⟨L, hL, e⟩, P, hP, congrArg Prod.fst e', congrArg Prod.snd e'⟩

/-- **Where the book has each part's count, each of K1's messages' texts answers at every entry.** n
is not bounded: `msgTxt` answers wherever the part's cut is there, whatever n is; beyond the plan's
messages no lot of `k1MsgLots` bears that text, and nothing is said of what it answers. -/
theorem k1_answers (h : coinsB Bk jobs = true) {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs)
    (wit : Wl → PlaceIn Xi) (own₀ : X) (n : Nat) (k : Coins Bk) (w : Wl) (hd : List Fmt.Drawn)
    (mask : Bool) (r j : Nat) : (msgTxt 0 wit x.2 own₀ n k w hd mask r j).isSome = true := by
  unfold coinsB at h
  have hC := of_decide_eq_true (List.all_eq_true.1 h x hx)
  obtain ⟨y, hy⟩ := msgTxt_answers hC wit own₀ n k w hd mask r j
  rw [hy]
  rfl

/-- **Where `treesB` passes, no declared tree's lot hangs on what tl says outside tn.** -/
theorem tl_reads_no_rest {O : Others Bk Wl} (ht : treesB bs (jobs.map (·.1) ++ O.tn) = true)
    (O' : Others Bk Wl) (he : ∀ b ∈ O.tn, O'.tl b = O.tl b) : ∀ t, t < treesTo bs bs.length →
    joinTl wit own₀ jobs O' (senderOf bs t) = joinTl wit own₀ jobs O (senderOf bs t) := by
  intro t htt
  obtain ⟨b, j, blk, hb, hblk, hj, rfl⟩ := tree_split bs bs.length (Nat.le_refl _) htt
  rw [senderOf_own hblk hj]
  have hm : b ∈ jobs.map (·.1) ++ O.tn := by
    unfold treesB treeless at ht
    rw [List.isEmpty_iff, List.filter_eq_nil_iff] at ht
    have h1 := ht b (List.mem_range.2 (by rw [List.length_map]; exact hb))
    have hc : (bs.map fun blk => (blk.oracles.flatMap id).length).getD b 0 =
        (blk.oracles.flatMap id).length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hblk]
      rfl
    rw [hc] at h1
    by_contra hn
    apply h1
    rw [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', ← Bool.not_eq_true]
    exact ⟨by omega, fun hc' => hn (List.contains_iff_mem.1 hc')⟩
  unfold joinTl k1TreeLots
  cases hl : jobs.lookup b with
  | some J => rfl
  | none =>
    have hb' : b ∈ O.tn := by
      rcases List.mem_append.1 hm with h | h
      · exfalso
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
        rw [List.lookup_eq_none_iff] at hl
        have := hl p hp
        simp at this
      · exact h
    exact he b hb'

/-- **Where `numsB` passes, no number stands twice among the jobs**: the premise hnd of
`join_trees_k1`. -/
theorem nums_gives {tn : List Nat} (h : numsB jobs tn = true) : (jobs.map (·.1)).Nodup :=
  (of_decide_eq_true h : (jobs.map (·.1) ++ tn).Nodup).of_append_left

/-- **Where `foundB` passes, each job's number bears a block at the job's place.** -/
theorem found_gives (h : foundB bs jobs = true) : ∀ x ∈ jobs,
    ∃ blk, bs[x.1]? = some blk ∧ blk.place = x.2.P.place := by
  intro x hx
  unfold foundB at h
  have h1 := List.all_eq_true.1 h x hx
  cases hb : bs[x.1]? with
  | none => simp [hb] at h1
  | some blk =>
    simp [hb] at h1
    exact ⟨blk, rfl, h1⟩

/-- **Where `placesB` passes, `borderNo` at a block's place is the block's number.** -/
theorem places_gives (h : placesB bs = true) {b : Nat} {blk : Block S Cl}
    (hb : bs[b]? = some blk) : borderNo bs blk.place = b :=
  borderNo_at bs b blk (of_decide_eq_true h) hb

/-- **Where both pass, the list of jobs with their numbers is `byNo`'s.** -/
theorem found_is_byNo (hp : placesB bs = true) (hf : foundB bs jobs = true) :
    byNo bs (jobs.map (·.2)) = jobs := by
  unfold byNo
  rw [List.map_map]
  refine (List.map_congr_left fun x hx => ?_).trans (List.map_id _)
  obtain ⟨blk, hb, hz⟩ := found_gives hf x hx
  show (borderNo bs x.2.P.place, x.2) = x
  rw [← hz, places_gives hp hb]

/-! ## 8 Each test can say no -/

/-- One number twice: "agree" says no. -/
theorem agreeB_no_msgs : agreeB (Bk := Bk) (Wl := Wl)
    [⟨3, 0, fun _ _ _ _ _ _ => none⟩, ⟨3, 0, fun _ _ _ _ _ _ => none⟩] [] = false := by
  show (decide ([3, 3] : List Nat).Nodup && decide ([] : List (Nat × Nat)).Nodup) = false
  decide

/-- One seat twice: "agree" says no. -/
theorem agreeB_no_pads : agreeB (Bk := Bk) (Wl := Wl) []
    [⟨1, 0, fun _ _ _ _ _ => none⟩, ⟨1, 0, fun _ _ _ _ _ => none⟩] = false := by
  show (decide ([] : List Nat).Nodup && decide ([(1, 0), (1, 0)] : List (Nat × Nat)).Nodup) = false
  decide

/-- A message's lot lacks: its seat is printed. -/
theorem unowned_msg : unowned (Bk := Bk) (Wl := Wl) (fun j t => 2 * j + t) [(0, 0), (0, 1)]
    [⟨0, 0, fun _ _ _ _ _ _ => none⟩]
    [⟨0, 0, fun _ _ _ _ _ => none⟩, ⟨0, 1, fun _ _ _ _ _ => none⟩] = [(0, 1)] := by
  show ([(0, 0), (0, 1)] : List (Nat × Nat)).filter (fun s =>
    !(([0] : List Nat).contains (2 * s.1 + s.2) &&
      ([(0, 0), (0, 1)] : List (Nat × Nat)).contains s)) = [(0, 1)]
  decide

/-- A pad's lot lacks: its seat is printed. -/
theorem unowned_pad : unowned (Bk := Bk) (Wl := Wl) (fun j t => 2 * j + t) [(0, 0), (0, 1)]
    [⟨0, 0, fun _ _ _ _ _ _ => none⟩, ⟨1, 0, fun _ _ _ _ _ _ => none⟩]
    [⟨0, 0, fun _ _ _ _ _ => none⟩] = [(0, 1)] := by
  show ([(0, 0), (0, 1)] : List (Nat × Nat)).filter (fun s =>
    !(([0, 1] : List Nat).contains (2 * s.1 + s.2) &&
      ([(0, 0)] : List (Nat × Nat)).contains s)) = [(0, 1)]
  decide

/-- A job whose number bears no block: `foundB` says no. -/
theorem foundB_no (J : SendJob (PlaceIn Xi) X) :
    foundB ([] : List (Block S Cl)) [(0, J)] = false := by
  simp [foundB]

/-- A book that has one coin more than the part's due at the job's address: `coinsB` says no, at
every job. The test asks just the due, not "at least the due". -/
theorem coinsB_no (b : Nat) (J : SendJob (PlaceIn Xi) X) :
    coinsB ⟨[(⟨J.P.place, 0⟩, ⟨(dueR J.P J.ride).f + 1, (dueR J.P J.ride).e⟩)], [], [], [], []⟩
      [(b, J)] = false := by
  have e : dueAt ((⟨[(⟨J.P.place, 0⟩, ⟨(dueR J.P J.ride).f + 1, (dueR J.P J.ride).e⟩)], [], [], [],
      []⟩ : ProverCoinCounts).rowsOf 0) ⟨J.P.place, 0⟩ =
      ⟨(dueR J.P J.ride).f + 1, (dueR J.P J.ride).e⟩ := by
    simp [dueAt, ProverCoinCounts.rowsOf]
  have ne : (⟨(dueR J.P J.ride).f + 1, (dueR J.P J.ride).e⟩ : Due) ≠ dueR J.P J.ride := by
    intro h
    have h' := congrArg Due.f h
    simp at h'
  simp [coinsB, e, ne]

/-- One number twice among the jobs: `numsB` says no. -/
theorem numsB_no_jobs (J : SendJob (PlaceIn Xi) X) : numsB [(2, J), (2, J)] [] = false := by
  simp [numsB]

/-- One number among the jobs and among the others': `numsB` says no. -/
theorem numsB_no_tn (J : SendJob (PlaceIn Xi) X) : numsB [(2, J)] [2] = false := by
  simp [numsB]

/-- One block twice: `placesB` says no. -/
theorem placesB_no (blk : Block S Cl) : placesB [blk, blk] = false := by
  simp [placesB]

/-- A member that declares a tree and stands in no list is printed. -/
theorem treeless_prints : treeless [0, 2, 0, 1] [1] = [3] := by decide

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.byNo
#print axioms ProofFile.Honest.FirstThread.Others
#print axioms ProofFile.Honest.FirstThread.joinMl
#print axioms ProofFile.Honest.FirstThread.joinPl
#print axioms ProofFile.Honest.FirstThread.joinTl
#print axioms ProofFile.Honest.FirstThread.joinQ
#print axioms ProofFile.Honest.FirstThread.nums
#print axioms ProofFile.Honest.FirstThread.seatsOf
#print axioms ProofFile.Honest.FirstThread.agreeB
#print axioms ProofFile.Honest.FirstThread.unowned
#print axioms ProofFile.Honest.FirstThread.ownedB
#print axioms ProofFile.Honest.FirstThread.treeless
#print axioms ProofFile.Honest.FirstThread.treesB
#print axioms ProofFile.Honest.FirstThread.numsB
#print axioms ProofFile.Honest.FirstThread.placesB
#print axioms ProofFile.Honest.FirstThread.foundB
#print axioms ProofFile.Honest.FirstThread.coinsB
#print axioms ProofFile.Honest.FirstThread.msgsAgree_of_nodup
#print axioms ProofFile.Honest.FirstThread.padsAgree_of_nodup
#print axioms ProofFile.Honest.FirstThread.agree_of_test
#print axioms ProofFile.Honest.FirstThread.nums_k1
#print axioms ProofFile.Honest.FirstThread.seats_k1
#print axioms ProofFile.Honest.FirstThread.join_tie_k1
#print axioms ProofFile.Honest.FirstThread.join_trees_k1
#print axioms ProofFile.Honest.FirstThread.owned_gives
#print axioms ProofFile.Honest.FirstThread.k1_answers
#print axioms ProofFile.Honest.FirstThread.tl_reads_no_rest
#print axioms ProofFile.Honest.FirstThread.nums_gives
#print axioms ProofFile.Honest.FirstThread.found_gives
#print axioms ProofFile.Honest.FirstThread.places_gives
#print axioms ProofFile.Honest.FirstThread.found_is_byNo
#print axioms ProofFile.Honest.FirstThread.agreeB_no_msgs
#print axioms ProofFile.Honest.FirstThread.agreeB_no_pads
#print axioms ProofFile.Honest.FirstThread.unowned_msg
#print axioms ProofFile.Honest.FirstThread.unowned_pad
#print axioms ProofFile.Honest.FirstThread.foundB_no
#print axioms ProofFile.Honest.FirstThread.coinsB_no
#print axioms ProofFile.Honest.FirstThread.numsB_no_jobs
#print axioms ProofFile.Honest.FirstThread.numsB_no_tn
#print axioms ProofFile.Honest.FirstThread.placesB_no
#print axioms ProofFile.Honest.FirstThread.treeless_prints
