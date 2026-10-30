-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/JoinFit.lean: one premise for whoever states a hypothesis on
the `Script` at the joined `Script` (`joinQ`, Honest/Thread/Join.lean): "the list is fit"
(`JoinFit`). Where a message has no lot, `Script.ofLots` puts zero without a word, and a hypothesis
that reads that message can then be false. `JoinFit` holds "owned" beside "agree", at a list of
seats that holds every seat that the flat list declares (`flatSeats`): so a lemma that takes it
speaks only of lists in which each of these seats has its lots.

  1  `Others.add`, `Others.add_tl_left`, `Others.add_tl_right` two senders' shares as one
  2  `flatSeats`, `seatsB`, `treesFitB`, `laysB` three tests more on public data: the list of seats
     holds every seat that the flat list declares; each job's block declares as many trees as the
     job's plan has; each job's plan's trees can be laid
  3  `JoinFit` the premise, eleven fields: each is what one test says
  4  `joinFitB`, `trees_gives`, `treesFit_gives`, `coins_gives`, `seats_gives`, `lays_gives`,
     `joinFit_of_test` at written data: ten tests as one (all seven of Join.lean and the three of
     this file), and from it the premise
  5  `join_tie_k1_of`, `join_tie_k1_fit`, `join_trees_k1_fit` K1's hypotheses on the `Script` at a
     fit list
  6  `join_msgs_other`, `join_pads_other`, `joinTl_at_others`, `join_trees_other` every other
     sender's hypotheses at a fit list, at its own lots
  7  `joinFitB_no`, `treesFitB_no`, `seatsB_no` the tests can say no

Limits.
  * `JoinFit` is a definition: the form of a premise. It is proved here of no list.
  * "Owned" asks that a lot bears the number or the seat, not that its text answers (Join.lean,
    Limits).
  * The list of seats stays a parameter. The field whole holds it from below: it holds every seat
    that the flat list declares, tree by tree and tenant by tenant, the trees counted from 0 as
    `treesTo` counts them. Nothing holds it from above: a seat more asks a lot more.
  * The book: the field coins is K1's alone (the field hasCoins of K1's record, at each job). Of
    another sender's counts in the book nothing is asked here.
  * Each lemma spends some fields alone (`join_tie_k1_fit`: msgs and pads; `join_trees_k1_fit`: nums
    and found; the others' lemmas: msgs, pads or nums). The other fields stand there so that no
    lemma is quoted at a list in which a declared seat has no lot, two jobs stand at one place, a
    job's lots stray beyond its own block's trees, or the book lacks a job's due.
  * The others' lemmas say nothing where a lot's text answers nothing. `join_tie_k1_fit`'s second
    half says nothing at a message without a pad's place.
  * That no coin stands at two entries is asked by no form here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.K1

variable {Bk : ProverCoinCounts} {Cl Wl Xi X Cells Tok : Type}

/-! ## 1 Two shares as one -/

/-- **Two senders' shares as one.** At a number that stands in both lists of numbers the first
share's `TreeLot` is laid: `numsB` refuses such a list. At a number in neither, the second's. -/
def Others.add (A B : Others Bk Wl) : Others Bk Wl :=
  { ml := A.ml ++ B.ml
    pl := A.pl ++ B.pl
    tl := fun b => if A.tn.contains b then A.tl b else B.tl b
    tn := A.tn ++ B.tn }

/-- At a number of the first share's. -/
theorem Others.add_tl_left {A B : Others Bk Wl} {b : Nat} (h : b ∈ A.tn) :
    (A.add B).tl b = A.tl b := by
  show (if A.tn.contains b then A.tl b else B.tl b) = A.tl b
  rw [if_pos (List.contains_iff_mem.2 h)]

/-- At a number that is not the first share's. -/
theorem Others.add_tl_right {A B : Others Bk Wl} {b : Nat} (h : b ∉ A.tn) :
    (A.add B).tl b = B.tl b := by
  show (if A.tn.contains b then A.tl b else B.tl b) = B.tl b
  rw [if_neg fun c => h (List.contains_iff_mem.1 c)]

/-! ## 2 Three tests more -/

/-- **The seats that the flat list declares**: tree by tree, the trees counted from 0 in the order
of the list (as `treesTo` counts them), and tenant by tenant. -/
def flatSeats (bs : List (Block S Cl)) : List (Nat × Nat) :=
  (bs.flatMap fun blk => blk.oracles.flatMap id).zipIdx.flatMap fun o =>
    (List.range o.1.tenants.length).map fun t => (o.2, t)

/-- **The list of seats holds every seat that the flat list declares.** -/
def seatsB (bs : List (Block S Cl)) (seats : List (Nat × Nat)) : Bool :=
  (flatSeats bs).all fun s => seats.contains s

/-- **Each job's plan's trees can be laid.** Where they cannot, the plan has no tree, its block
declares none, and every lot of the job would be laid at the next member's first seat. -/
def laysB (jobs : List (Nat × SendJob (PlaceIn Xi) X)) : Bool :=
  jobs.all fun x => VerifiableInference.Desc.Own.treesCan x.2.P.codes x.2.P.sent

/-- **Each job's block declares as many trees as the job's plan has.** Where a block declares more,
the table laid at the surplus tree is the table without a word; where fewer, K1's pads are laid at
trees of the next member. It says yes at a job whose number bears no block: `foundB` refuses there.
-/
def treesFitB (bs : List (Block S Cl)) (jobs : List (Nat × SendJob (PlaceIn Xi) X)) : Bool :=
  jobs.all fun x => (bs[x.1]?).all fun blk =>
    (blk.oracles.flatMap id).length == x.2.P.trees.length

/-! ## 3 The premise -/

/-- **The list is fit.** It is a definition: the form of a premise. -/
structure JoinFit (bs : List (Block S Cl)) (front : Nat) (arr : ℕ → ℕ → ℕ)
    (seats : List (Nat × Nat)) (wit : Wl → PlaceIn Xi) (own₀ : X)
    (jobs : List (Nat × SendJob (PlaceIn Xi) X)) (O : Others Bk Wl) : Prop where
  /-- all lots of one message agree -/
  msgs : MsgsAgree (joinMl bs front arr wit own₀ jobs O)
  /-- all lots of one pad agree -/
  pads : PadsAgree (joinPl bs jobs O)
  /-- each seat's message has a lot, and each seat has a pad's lot -/
  owned : ∀ s ∈ seats, (∃ L ∈ joinMl bs front arr wit own₀ jobs O, L.n = arr s.1 s.2) ∧
    ∃ L ∈ joinPl bs jobs O, L.j = s.1 ∧ L.t = s.2
  /-- no member's number stands twice -/
  nums : (jobs.map (·.1) ++ O.tn).Nodup
  /-- each member that declares a tree has a number in the lists -/
  trees : ∀ b blk, bs[b]? = some blk → (blk.oracles.flatMap id).length ≠ 0 →
    b ∈ jobs.map (·.1) ++ O.tn
  /-- each job's number bears a block at the job's place -/
  found : ∀ x ∈ jobs, ∃ blk, bs[x.1]? = some blk ∧ blk.place = x.2.P.place
  /-- that block declares as many trees as the job's plan has -/
  fits : ∀ x ∈ jobs, ∀ blk, bs[x.1]? = some blk →
    (blk.oracles.flatMap id).length = x.2.P.trees.length
  /-- no place stands twice in the flat list -/
  places : (bs.map (·.place)).Nodup
  /-- the book's count at each job's address is the part's due: hasCoins of K1's record -/
  coins : ∀ x ∈ jobs, dueAt (Bk.rowsOf 0) ⟨x.2.P.place, 0⟩ = dueR x.2.P x.2.ride
  /-- the list of seats holds every seat that the flat list declares -/
  whole : ∀ s ∈ flatSeats bs, s ∈ seats
  /-- each job's plan's trees can be laid -/
  lays : ∀ x ∈ jobs, VerifiableInference.Desc.Own.treesCan x.2.P.codes x.2.P.sent = true

/-! ## 4 At written data -/

/-- **Ten tests as one**: the seven of Join.lean, and `treesFitB`, `seatsB`, `laysB`. -/
def joinFitB (bs : List (Block S Cl)) (front : Nat) (arr : ℕ → ℕ → ℕ) (seats : List (Nat × Nat))
    (wit : Wl → PlaceIn Xi) (own₀ : X) (jobs : List (Nat × SendJob (PlaceIn Xi) X))
    (O : Others Bk Wl) : Bool :=
  agreeB (joinMl bs front arr wit own₀ jobs O) (joinPl bs jobs O) &&
    ownedB arr seats (joinMl bs front arr wit own₀ jobs O) (joinPl bs jobs O) &&
    numsB jobs O.tn && treesB bs (jobs.map (·.1) ++ O.tn) && foundB bs jobs && treesFitB bs jobs &&
    placesB bs && coinsB Bk jobs && seatsB bs seats && laysB jobs

/-- **Where `treesB` passes, each member that declares a tree stands in the list of numbers.** -/
theorem trees_gives {bs : List (Block S Cl)} {tn : List Nat} (h : treesB bs tn = true) :
    ∀ b blk, bs[b]? = some blk → (blk.oracles.flatMap id).length ≠ 0 → b ∈ tn := by
  intro b blk hblk hne
  unfold treesB treeless at h
  rw [List.isEmpty_iff, List.filter_eq_nil_iff] at h
  have hb : b < bs.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hblk
    cases hblk
  have h1 := h b (List.mem_range.2 (by rw [List.length_map]; exact hb))
  have hc : (bs.map fun blk => (blk.oracles.flatMap id).length).getD b 0 =
      (blk.oracles.flatMap id).length := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hblk]
    rfl
  rw [hc] at h1
  by_contra hn
  apply h1
  rw [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', ← Bool.not_eq_true]
  exact ⟨hne, fun hc' => hn (List.contains_iff_mem.1 hc')⟩

variable {bs : List (Block S Cl)} {front : Nat} {arr : ℕ → ℕ → ℕ} {seats : List (Nat × Nat)}
  {wit : Wl → PlaceIn Xi} {own₀ : X} {jobs : List (Nat × SendJob (PlaceIn Xi) X)}
  {O : Others Bk Wl}

/-- **Where `treesFitB` passes, each job's block has the plan's count of trees.** -/
theorem treesFit_gives (h : treesFitB bs jobs = true) : ∀ x ∈ jobs, ∀ blk, bs[x.1]? = some blk →
    (blk.oracles.flatMap id).length = x.2.P.trees.length := by
  intro x hx blk hb
  unfold treesFitB at h
  have h1 := List.all_eq_true.1 h x hx
  rw [hb] at h1
  have h2 : ((blk.oracles.flatMap id).length == x.2.P.trees.length) = true := h1
  exact beq_iff_eq.1 h2

/-- **Where `coinsB` passes, the book's count at each job's address is the part's due**: the field
hasCoins of K1's record (Honest/K1/Seated.lean). -/
theorem coins_gives (h : coinsB Bk jobs = true) : ∀ x ∈ jobs,
    dueAt (Bk.rowsOf 0) ⟨x.2.P.place, 0⟩ = dueR x.2.P x.2.ride := by
  intro x hx
  unfold coinsB at h
  exact of_decide_eq_true (List.all_eq_true.1 h x hx)

/-- **Where `seatsB` passes, the list of seats holds every seat that the flat list declares.** -/
theorem seats_gives (h : seatsB bs seats = true) : ∀ s ∈ flatSeats bs, s ∈ seats := by
  intro s hs
  unfold seatsB at h
  exact List.contains_iff_mem.1 (List.all_eq_true.1 h s hs)

/-- **Where `laysB` passes, each job's plan's trees can be laid.** -/
theorem lays_gives (h : laysB jobs = true) : ∀ x ∈ jobs,
    VerifiableInference.Desc.Own.treesCan x.2.P.codes x.2.P.sent = true := by
  intro x hx
  unfold laysB at h
  exact List.all_eq_true.1 h x hx

/-- **Where the test passes, the list is fit.** -/
theorem joinFit_of_test (h : joinFitB bs front arr seats wit own₀ jobs O = true) :
    JoinFit bs front arr seats wit own₀ jobs O := by
  unfold joinFitB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, ho⟩, hn⟩, ht⟩, hf⟩, hq⟩, hp⟩, hc⟩, hs⟩, hl⟩ := h
  exact ⟨(agree_of_test ha).1, (agree_of_test ha).2, owned_gives ho,
    (of_decide_eq_true hn : (jobs.map (·.1) ++ O.tn).Nodup), trees_gives ht, found_gives hf,
    treesFit_gives hq, (of_decide_eq_true hp : (bs.map (·.place)).Nodup), coins_gives hc,
    seats_gives hs, lays_gives hl⟩

/-! ## 5 K1's hypotheses at a fit list -/

/-- **K1's tie at the joined `Script`**, at each member of the list, where the joined lists agree.
It says nothing at an empty list of jobs or at a job that sends no message; its second half nothing
at a message without a pad's place. At a book whose count at the part's address does not cover the
part's due this law holds for nothing, and it is never quoted as if it spoke there: hasCoins is
neither asked nor paid here: whoever quotes this law at a book names hasCoins at that book beside
it. -/
theorem join_tie_k1_of (hm : MsgsAgree (joinMl bs front arr wit own₀ jobs O))
    (hp : PadsAgree (joinPl bs jobs O)) (cells : Wl → Cells) (tok : Wl → Tok) (Vd : Wl → Prop)
    {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) :
    (∀ n, n < x.2.P.sent.size →
      OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd (front + roundsTo bs x.1)
        (arr (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2)
        (front + roundsTo bs x.1) (msgTxt 0 wit x.2 own₀ n)) ∧
    ∀ n, n < x.2.P.sent.size →
      OwnPads (joinQ bs front cells tok arr wit own₀ jobs O) Vd
        (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2
        (fun k _ => padTxt 0 x.2 n k) :=
  ⟨msgs_of_lots bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
      (joinMl bs front arr wit own₀ jobs O) arr wit own₀ x
      (hin_msgs_of_agree (fun _ hL => List.mem_append.2 (Or.inl hL)) hm hx) Vd,
    pads_of_lots bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
      (joinMl bs front arr wit own₀ jobs O) x
      (hin_pads_of_agree (fun _ hL => List.mem_append.2 (Or.inl hL)) hp hx) Vd⟩

/-- **K1's tie at a fit list.** It says nothing at an empty list of jobs or at a job that sends no
message; its second half nothing at a message without a pad's place. A sentence that was set for the
lemma beneath, to the letter, in marks: "At a book whose count at the part's address does not cover
the part's due this law holds for nothing, and it is never quoted as if it spoke there: hasCoins is
neither asked nor paid here: whoever quotes this law at a book names hasCoins at that book beside
it." In this file's own words: at a fit list the field coins is hasCoins at the list's book. -/
theorem join_tie_k1_fit (F : JoinFit bs front arr seats wit own₀ jobs O) (cells : Wl → Cells)
    (tok : Wl → Tok) (Vd : Wl → Prop) {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) :
    (∀ n, n < x.2.P.sent.size →
      OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd (front + roundsTo bs x.1)
        (arr (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2)
        (front + roundsTo bs x.1) (msgTxt 0 wit x.2 own₀ n)) ∧
    ∀ n, n < x.2.P.sent.size →
      OwnPads (joinQ bs front cells tok arr wit own₀ jobs O) Vd
        (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2
        (fun k _ => padTxt 0 x.2 n k) :=
  join_tie_k1_of F.msgs F.pads cells tok Vd hx

/-- **K1's trees at a fit list**, at a thread whose table and fixed are the joined `Script`'s and
whose bs and front are those at which it is laid: at each job the block at its number stands at the
job's place, and the trees that this block declares are K1's. It says nothing at an empty list of
jobs or at a member whose block declares no tree. A sentence that was set for the lemma beneath, to
the letter, in marks: "At a book whose count at the part's address does not cover the part's due
this law holds for nothing, and it is never quoted as if it spoke there: hasCoins is neither asked
nor paid here: whoever quotes this law at a book names hasCoins at that book beside it." In this
file's own words: this lemma's proof asks nothing of the book, and at a book that lacks the part's
due its end would not be empty: it would speak of `treeTbl`'s table without a word; at a fit list
the field coins is hasCoins at the list's book. Whoever speaks of coins at k1TreeLots owes "the book
covers the part's coins" by name. -/
theorem join_trees_k1_fit {V X' Pb : Type} {cF : Chain S ProofFile.Cl}
    {O : Others Bk Wl} (F : JoinFit cF.blocksInOrder front arr seats wit own₀ jobs O) (cells : Wl → Cells)
    (tok : Wl → Tok) (T : Thread Bk S ProofFile.Cl V Wl X' Pb) (hbs : T.bs = cF.blocksInOrder)
    (hfr : T.front = front)
    (htab : T.table = (joinQ cF.blocksInOrder front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder front cells tok arr wit own₀ jobs O).fixed)
    {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) :
    ∃ blk, cF.blocksInOrder[x.1]? = some blk ∧ blk.place = x.2.P.place ∧
      OwnTrees T x.1 (blk.oracles.flatMap id).length (treeTbl 0 wit x.2 own₀) (fun _ => 0) := by
  obtain ⟨blk, hb, hz⟩ := F.found x hx
  exact ⟨blk, hb, hz,
    join_trees_k1 cells tok T hbs hfr htab hfix F.nums.of_append_left hx hb⟩

/-! ## 6 Every other sender's hypotheses at a fit list -/

/-- **Another sender's message at a fit list**: at each of its lots. Where the lot's text answers
nothing this says nothing. -/
theorem join_msgs_other (F : JoinFit bs front arr seats wit own₀ jobs O) {L : MsgLot Bk Wl}
    (hL : L ∈ O.ml) (cells : Wl → Cells) (tok : Wl → Tok) (Vd : Wl → Prop) (N : Nat) :
    OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd N L.n L.fx L.txt :=
  have m : L ∈ joinMl bs front arr wit own₀ jobs O := List.mem_append.2 (Or.inr hL)
  ofLots_ownMsgs bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
    (joinMl bs front arr wit own₀ jobs O) m (F.msgs L m) Vd N

/-- **Another sender's pad at a fit list**: at each of its lots. Where the lot's text answers
nothing this says nothing. -/
theorem join_pads_other (F : JoinFit bs front arr seats wit own₀ jobs O) {L : PadLot Bk Wl}
    (hL : L ∈ O.pl) (cells : Wl → Cells) (tok : Wl → Tok) (Vd : Wl → Prop) :
    OwnPads (joinQ bs front cells tok arr wit own₀ jobs O) Vd L.j L.t L.txt :=
  have m : L ∈ joinPl bs jobs O := List.mem_append.2 (Or.inr hL)
  ofLots_ownPads bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
    (joinMl bs front arr wit own₀ jobs O) m (F.pads L m) Vd

/-- **At a number of the others' the list's `TreeLot` is the others'.** -/
theorem joinTl_at_others (F : JoinFit bs front arr seats wit own₀ jobs O) {b : Nat}
    (hb : b ∈ O.tn) : joinTl wit own₀ jobs O b = O.tl b :=
  k1TreeLots_rest wit own₀ O.tl fun hj => List.disjoint_of_nodup_append F.nums hj hb

/-- **Another sender's trees at a fit list**, at a thread whose table and fixed are the joined
`Script`'s and whose bs and front are those at which it is laid. It says nothing at a member whose
block declares no tree. -/
theorem join_trees_other {V X' Pb : Type} (F : JoinFit bs front arr seats wit own₀ jobs O)
    (cells : Wl → Cells) (tok : Wl → Tok) (T : Thread Bk S Cl V Wl X' Pb) (hbs : T.bs = bs)
    (hfr : T.front = front)
    (htab : T.table = (joinQ bs front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ bs front cells tok arr wit own₀ jobs O).fixed) {b : Nat}
    (hb : b ∈ O.tn) {blk : Block S Cl} (hblk : bs[b]? = some blk) :
    OwnTrees T b (blk.oracles.flatMap id).length (O.tl b).tbl (O.tl b).off := by
  have h := ofLots_ownTrees bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
    (joinMl bs front arr wit own₀ jobs O) T hbs hfr htab hfix hblk
  rw [joinTl_at_others F hb] at h
  exact h

/-! ## 7 The tests can say no -/

/-- A seat and no lot: the test says no. -/
theorem joinFitB_no (arr : ℕ → ℕ → ℕ) (wit : Wl → PlaceIn Xi) (own₀ : X)
    (tl : Nat → TreeLot Bk Wl) :
    joinFitB ([] : List (Block S Cl)) 0 arr [(0, 0)] wit own₀ [] ⟨[], [], tl, []⟩ = false := by
  simp [joinFitB, ownedB, unowned, joinMl, joinPl, k1MsgLots, k1PadLots, nums, seatsOf]

/-- A block that declares one tree more than the job's plan has: `treesFitB` says no, at every job.
-/
theorem treesFitB_no (blk : Block S Cl) (o : VerifiableInference.Desc.Oracle)
    (J : SendJob (PlaceIn Xi) X) :
    treesFitB [{ blk with oracles := [List.replicate (J.P.trees.length + 1) o] }] [(0, J)] =
      false := by
  simp [treesFitB]

/-- A block that declares one tree of one tenant, and no seat in the list: `seatsB` says no. -/
theorem seatsB_no (blk : Block S Cl) (o : VerifiableInference.Desc.Oracle)
    (t : VerifiableInference.Desc.SymbolComponent) :
    seatsB [{ blk with oracles := [[{ o with tenants := [t] }]] }] [] = false := by
  simp [seatsB, flatSeats]

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.Others.add
#print axioms ProofFile.Honest.FirstThread.Others.add_tl_left
#print axioms ProofFile.Honest.FirstThread.Others.add_tl_right
#print axioms ProofFile.Honest.FirstThread.flatSeats
#print axioms ProofFile.Honest.FirstThread.seatsB
#print axioms ProofFile.Honest.FirstThread.laysB
#print axioms ProofFile.Honest.FirstThread.treesFitB
#print axioms ProofFile.Honest.FirstThread.JoinFit
#print axioms ProofFile.Honest.FirstThread.joinFitB
#print axioms ProofFile.Honest.FirstThread.trees_gives
#print axioms ProofFile.Honest.FirstThread.treesFit_gives
#print axioms ProofFile.Honest.FirstThread.coins_gives
#print axioms ProofFile.Honest.FirstThread.seats_gives
#print axioms ProofFile.Honest.FirstThread.lays_gives
#print axioms ProofFile.Honest.FirstThread.joinFit_of_test
#print axioms ProofFile.Honest.FirstThread.join_tie_k1_of
#print axioms ProofFile.Honest.FirstThread.join_tie_k1_fit
#print axioms ProofFile.Honest.FirstThread.join_trees_k1_fit
#print axioms ProofFile.Honest.FirstThread.join_msgs_other
#print axioms ProofFile.Honest.FirstThread.join_pads_other
#print axioms ProofFile.Honest.FirstThread.joinTl_at_others
#print axioms ProofFile.Honest.FirstThread.join_trees_other
#print axioms ProofFile.Honest.FirstThread.joinFitB_no
#print axioms ProofFile.Honest.FirstThread.treesFitB_no
#print axioms ProofFile.Honest.FirstThread.seatsB_no
