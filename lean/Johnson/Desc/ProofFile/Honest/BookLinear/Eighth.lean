-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLinear/Eighth.lean: WHERE AN ORDER OF PLACES HAS NO PLACE TWICE,
NO TWO SPENDING ENTRIES OF A LIST SHARE A COIN, AND THE TEST clause8Q ACCEPTS THE LIST AT THE ORDER,
THE EIGHTH TEST OF ProverCoinCounts.clauses (Honest/Frame.lean: "a coin that a part spends is handed to a part
in front of it, or to itself as carried") ACCEPTS THAT LIST AT THAT ORDER (clause8Q_of). ONE
DIRECTION ALONE: where clause8Q rejects, nothing follows. GENERAL IN g, the function that names a
place's position: nothing is asked of it. The test as it stands looks at all pairs of entries; the
twin sorts once and holds, at each owner's code, every spending entry against the carried runs met
there, of each of which it has kept one entry and its carriers' least rank. Definitions with code;
statements with their proofs; one closed fact on small lists. Written by the authors of the honest
side of the linear claim's shared rounds (K14), in the frame's folder, not by the frame's authors;
Ahead, Ahead.shares, Addr, Addr.before and the test are the frame's (Honest/Frame.lean); Place is
the library's (Johnson/Desc/Block.lean).

  ok8G g p q      what the eighth test asks of a spending entry p and a carrying entry q, by
                  positions: they share no coin, or q's spender stands neither before p's (beforeG,
                  Honest/BookLinear/Positions.lean) nor is it p's
  sameAddr_of_placed   where g is right at both places: two addresses are equal just where g's
                  numbers and the parts' numbers are (no "no place twice" is wanted)
  eighth_of_ok    **THE STEP FROM ok8G TO THE TEST**: all.Nodup → no two spending entries share a
                  coin → g is right at every entry's spender's place (placedAt, Positions.lean) →
                  ok8G at every spending p and carrying q → the eighth test's Bool at all and l is
                  true. At a carrying q: before_of_placed, sameAddr_of_placed; at a spending q the
                  test asks "share no coin, or …": the premise on the spending entries gives the
                  first
  rankG, rankLt, rankMin   a spender's rank: its place's position by g and its part's number; the
                  order of ranks; the lesser of two
  sameRunE r e    the two entries have one owner, one start, one count: Ahead.shares reads no more
                  of its second argument (shares_sameRunE)
  layRun g e C    a carrying entry laid to the list of runs met so far, each with the least rank of
                  its carriers: at the run of the list's head that rank is lowered; else a new head.
                  A run that comes again apart from its like gets a second head: more looks, nothing
                  lost (layRun_covers, layRun_has)
  byRunG g c sp C l   one pass. c: the code (Addr.code, Honest/BookLinear/Tool.lean) of the entry in
                  front; sp: a spending entry was met at that code; C: the carried runs met at that
                  code. It rejects where a code falls, and where a carrying entry comes behind a
                  spending one of its code; a spending entry is held against every head of C:
                  "shares no coin with it, or its spender's rank is below the kept rank". It
                  recurses structurally
  sortKey8 e      the key of the sort: the owner's code; carrying in front of spending; the run's
                  start and count. Nothing is asked of it
  clause8Q g d all l   the twin: placedAt at every entry's spender's place; then byRunG along sortL
                  (Tool.lean) by sortKey8. d: the sort's rounds
  byRunG_keeps    what a pass that accepts has seen: four clauses; the last: "shares no coin, or p's
                  rank is below q's" AT EVERY PAIR OF A SPENDING AND A CARRYING ENTRY OF THE LIST
                  WITH ONE CODE. (That the list is sorted is not assumed: the pass checks what it
                  needs)
  carried_okQ     **clause8Q g d all l = true → ok8G g p q = true at every spending p and carrying q
                  of l**: "p's rank below q's" gives ok8G's second arm (ok8G_of_rankLt); equal
                  owners have one code; at unequal owners Ahead.shares is false by its first clause:
                  SO NOTHING IS ASKED OF Addr.code
  clause8Q_of     **all.Nodup → no two spending entries share a coin → clause8Q g d all l = true →
                  the eighth test's Bool at all and l is true**: THE CONCLUSION IS THE TEST's Bool
                  AS IT STANDS IN ProverCoinCounts.clauses, with the order and the list as letters: at all :=
                  orderOf F and l := B.ahead it is the eighth premise of clauses_all_of_each
                  (Honest/BookWordOf.lean), to the letter

THE PREMISE ON THE SPENDING ENTRIES is the seventh test's yes, in the form of apart_of_clause7 and
of spent_apart (Honest/BookLinear/Seventh.lean). IT IS NEEDED: the closed fact's last two clauses:
two spending entries that share a coin, the second's spender in front: the twin accepts, the eighth
test rejects.

Kin. BY ITS BODY rankLt is, to the sign, the library's BookPlan.earlierPlace
(Johnson/Desc/BookPlan.lean, among this file's imports), which has laws of its own
(earlierPlace_trans, earlierPlace_ne: Johnson/Desc/BookPlanLaws.lean); it is not called: it speaks
of trees' places (a chain and a root's number), and its laws' file is no import here. And rankLt
(rankG g a) (rankG g b) unfolds to beforeG g a b (Positions.lean): the pass keeps the pair, so that
g is not called anew at every look. Of the linear claim's kind: spent_not_known
(Honest/K14/OwnerWhole.lean): THE OTHER WAY ROUND: the eighth test drawn out of "no test is named as
failing", at a carrying entry; carriers_behind (Honest/K14/BookAtOmega.lean): at the list that the
frame's sharedAhead returns, at one owner, this kind's own test on the order (behindSpenderB)
accepts; that file's head: "no lemma here leads to the eighth test's yes". No law that concludes the
eighth test was found in the frame's files or this kind's. (Closed facts of this kind evaluate all
eleven verdicts at small books: Honest/K14/FreshToy.lean and its fellows: evaluations, no laws.)

Limits. THE TWIN REJECTS LISTS THAT THE TEST ACCEPTS: where g is wrong at a spender's place (the
closed fact: at one list the twin's yes at g, whence the test's yes by clause8Q_of, and its no at g
+ 1); WHATEVER g IS, where a spender's place is not of the order: the twin asks placedAt at every
entry's spender, and the eighth test does not ask "contains" (Addr.before counts such a place as the
last; at a book the fifth test rejects such an entry); where the sort has too few rounds (the closed
fact: no round: rejected; that the test accepts that list: by the authors' reckoning); and where a
start or a count from 2 ^ 40 on runs into the next field of sortKey8: a carrying entry can then be
sorted behind a spending one of its code, and the pass rejects. Two owners that differ in the
place's kind alone have one code: their entries are then held against each other, and since they
share no coin by Ahead.shares' first clause no rejection comes of that. What g is to be at a
description's order is not said. No book is named: that a book's entries pass clause8Q is shown
nowhere here. How many looks the pass takes hangs on how many spending entries and how many distinct
carried runs one owner has. The closed fact is an evaluation in Lean's kernel (decide +kernel).
Nothing on what an evaluation costs. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookLinear.Positions
import Johnson.Desc.ProofFile.Honest.BookLinear.Seventh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

/-! ## 1 From ok8G to the test -/

/-- What the eighth test asks of a spending entry p and a carrying entry q, by positions. -/
def ok8G (g : Place → Nat) (p q : Ahead) : Bool :=
  !p.shares q || !(beforeG g q.spender p.spender ||
    (g q.spender.place == g p.spender.place && q.spender.part == p.spender.part))

/-- Where g is right at both places, two addresses are equal just where g's numbers and the parts'
numbers are. -/
theorem sameAddr_of_placed {g : Place → Nat} {all : List Place} {a b : Addr}
    (ha : placedAt g all a.place = true) (hb : placedAt g all b.place = true) :
    (a == b) = (g a.place == g b.place && a.part == b.part) := by
  have h1 : all[g a.place]? = some a.place := beq_iff_eq.1 ha
  have h2 : all[g b.place]? = some b.place := beq_iff_eq.1 hb
  by_cases c : a = b
  · rw [c]
    simp
  · rw [beq_eq_false_iff_ne.2 c]
    symm
    rw [Bool.and_eq_false_iff]
    by_cases cp : a.place = b.place
    · right
      refine beq_eq_false_iff_ne.2 fun e => c ?_
      cases a
      cases b
      simp only at cp e
      rw [cp, e]
    · left
      refine beq_eq_false_iff_ne.2 fun e => cp ?_
      rw [e, h2] at h1
      exact (Option.some.inj h1).symm

/-- **FROM ok8G TO THE EIGHTH TEST**, general in g: where the order has no place twice, no two
spending entries share a coin, g is right at every spender's place, and ok8G holds at every spending
and every carrying entry. -/
theorem eighth_of_ok {g : Place → Nat} {all : List Place} {l : List Ahead} (hn : all.Nodup)
    (h7 : (l.filter (·.once)).Pairwise fun a b => a.shares b = false)
    (hP : ∀ a ∈ l, placedAt g all a.spender.place = true)
    (hK : ∀ p ∈ l, ∀ q ∈ l, p.once = true → q.once = false → ok8G g p q = true) :
    (l.zipIdx.all fun p => !p.1.once || l.zipIdx.all fun q => p.2 == q.2 || !p.1.shares q.1 ||
      !(q.1.spender.before all p.1.spender ||
        (q.1.spender == p.1.spender && !q.1.once))) = true := by
  have h7' := List.pairwise_iff_getElem.1 (List.pairwise_filter.1 h7)
  rw [List.all_eq_true]
  intro p hp
  rw [Bool.or_eq_true]
  by_cases po : p.1.once = true
  · right
    rw [List.all_eq_true]
    intro q hq
    rw [List.mem_zipIdx_iff_getElem?] at hp hq
    obtain ⟨ip, ep⟩ := List.getElem?_eq_some_iff.1 hp
    obtain ⟨iq, eq⟩ := List.getElem?_eq_some_iff.1 hq
    have mp : p.1 ∈ l := ep ▸ List.getElem_mem ip
    have mq : q.1 ∈ l := eq ▸ List.getElem_mem iq
    simp only [Bool.or_eq_true]
    by_cases qo : q.1.once = true
    · rcases Nat.lt_trichotomy p.2 q.2 with c | c | c
      · left; right
        have := h7' _ _ ip iq c (by rw [ep]; exact po) (by rw [eq]; exact qo)
        rw [ep, eq] at this
        rw [this]
        rfl
      · left; left
        exact beq_iff_eq.2 c
      · left; right
        have := h7' _ _ iq ip c (by rw [eq]; exact qo) (by rw [ep]; exact po)
        rw [ep, eq, shares_comm] at this
        rw [this]
        rfl
    · have qo' : q.1.once = false := by simpa using qo
      have hk := hK p.1 mp q.1 mq po qo'
      unfold ok8G at hk
      rw [← before_of_placed hn (hP _ mq) (hP _ mp), ← sameAddr_of_placed (hP _ mq) (hP _ mp),
        Bool.or_eq_true] at hk
      rcases hk with hk | hk
      · left; right
        exact hk
      · right
        rw [qo']
        simpa using hk
  · left
    simpa using po

/-! ## 2 The twin -/

/-- A spender's rank: its place's position by g, and its part's number. -/
def rankG (g : Place → Nat) (a : Addr) : Nat × Nat := (g a.place, a.part)

/-- The order of ranks: by the position, then by the part. -/
def rankLt (a b : Nat × Nat) : Bool := decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 < b.2))

/-- The lesser of two ranks. -/
def rankMin (a b : Nat × Nat) : Nat × Nat := if rankLt b a then b else a

/-- Two entries have one owner and one run. -/
def sameRunE (r e : Ahead) : Bool := r.owner == e.owner && r.start == e.start && r.count == e.count

/-- A carrying entry laid to the list of runs met so far, each with the least rank of its carriers:
where it has the run of the list's head, that head's rank is lowered; else it is a new head. -/
def layRun (g : Place → Nat) (e : Ahead) : List (Ahead × (Nat × Nat)) → List (Ahead × (Nat × Nat))
  | (r, m) :: C => if sameRunE r e then (r, rankMin m (rankG g e.spender)) :: C
      else (e, rankG g e.spender) :: (r, m) :: C
  | [] => [(e, rankG g e.spender)]

/-- One pass along a list that is sorted by the owner's code, the carrying entries of a code in
front of its spending ones. c: the code in front; sp: a spending entry was met at that code; C: the
carried runs met at that code. -/
def byRunG (g : Place → Nat) : Nat → Bool → List (Ahead × (Nat × Nat)) → List Ahead → Bool
  | _, _, _, [] => true
  | c, sp, C, e :: l =>
    let C' := if e.owner.code == c then C else []
    let sp' := e.owner.code == c && sp
    decide (c ≤ e.owner.code) &&
      (if e.once then C'.all (fun x => !e.shares x.1 || rankLt (rankG g e.spender) x.2) &&
          byRunG g e.owner.code true C' l
       else !sp' && byRunG g e.owner.code false (layRun g e C') l)
termination_by structural _ _ _ l => l

/-- The key of the sort: the owner's code; carrying in front of spending; the run's start and count
in the extension field, then in the base field. Nothing is asked of it. -/
def sortKey8 (e : Ahead) : Nat :=
  ((((e.owner.code * 2 + (if e.once then 1 else 0)) * 2 ^ 40 + e.start.e) * 2 ^ 40 + e.count.e) *
    2 ^ 40 + e.start.f) * 2 ^ 40 + e.count.f

/-- The eighth test's finer twin. -/
def clause8Q (g : Place → Nat) (d : Nat) (all : List Place) (l : List Ahead) : Bool :=
  l.all (fun a => placedAt g all a.spender.place) &&
    byRunG g 0 false [] ((sortL (fun (a b : Nat × Ahead) => decide (a.1 ≤ b.1)) d (2 ^ d)
      (l.map fun e => (sortKey8 e, e))).map (·.2))

/-! ## 3 Its laws -/

/-- The order of ranks, as a proposition. -/
theorem rankLt_iff (a b : Nat × Nat) : rankLt a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  simp [rankLt]

/-- What is below the lesser of two ranks is below both. -/
theorem rankLt_min {y m x : Nat × Nat} (h : rankLt y (rankMin m x) = true) :
    rankLt y m = true ∧ rankLt y x = true := by
  unfold rankMin at h
  split at h
  · rename_i c
    rw [rankLt_iff] at h c ⊢
    rw [rankLt_iff]
    omega
  · rename_i c
    rw [rankLt_iff] at h c ⊢
    rw [rankLt_iff]
    omega

/-- `Ahead.shares` reads of its second argument the owner, the start and the count alone. -/
theorem shares_sameRunE {r e : Ahead} (h : sameRunE r e = true) (p : Ahead) :
    p.shares r = p.shares e := by
  unfold sameRunE at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold Ahead.shares
  rw [h.1.1, h.1.2, h.2]

/-- An entry has its own run. -/
theorem sameRunE_self (e : Ahead) : sameRunE e e = true := by
  simp [sameRunE]

/-- Every run of the list is still there when an entry is laid to it, with a rank that is no
greater. -/
theorem layRun_covers (g : Place → Nat) (e : Ahead) (C : List (Ahead × (Nat × Nat))) :
    ∀ y ∈ C, ∃ y' ∈ layRun g e C, y'.1 = y.1 ∧ ∀ z, rankLt z y'.2 = true → rankLt z y.2 = true := by
  intro y hy
  cases C with
  | nil => cases hy
  | cons x C =>
    obtain ⟨r, m⟩ := x
    rw [layRun]
    split
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨_, List.mem_cons_self .., rfl, fun z hz => (rankLt_min hz).1⟩
      · exact ⟨y, List.mem_cons_of_mem _ hy, rfl, fun _ hz => hz⟩
    · exact ⟨y, List.mem_cons_of_mem _ hy, rfl, fun _ hz => hz⟩

/-- The laid entry's own run is there, with a rank that is no greater than its spender's. -/
theorem layRun_has (g : Place → Nat) (e : Ahead) (C : List (Ahead × (Nat × Nat))) :
    ∃ y' ∈ layRun g e C, sameRunE y'.1 e = true ∧
      ∀ z, rankLt z y'.2 = true → rankLt z (rankG g e.spender) = true := by
  cases C with
  | nil => exact ⟨_, List.mem_cons_self .., sameRunE_self e, fun _ hz => hz⟩
  | cons x C =>
    obtain ⟨r, m⟩ := x
    rw [layRun]
    split
    · rename_i c
      exact ⟨_, List.mem_cons_self .., c, fun z hz => (rankLt_min hz).2⟩
    · exact ⟨_, List.mem_cons_self .., sameRunE_self e, fun _ hz => hz⟩

/-- **What a pass that accepts has seen**: no code below c; every spending entry with code c is held
against every head of C; behind a spending entry of code c no carrying one of that code comes; and
"shares no coin, or p's rank is below q's" at every pair of a spending and a carrying entry of the
list with one code. -/
theorem byRunG_keeps (g : Place → Nat) : ∀ (l : List Ahead) (c : Nat) (sp : Bool)
    (C : List (Ahead × (Nat × Nat))), byRunG g c sp C l = true →
    (∀ e ∈ l, c ≤ e.owner.code) ∧
    (∀ e ∈ l, e.owner.code = c → e.once = true →
      ∀ x ∈ C, (!e.shares x.1 || rankLt (rankG g e.spender) x.2) = true) ∧
    (sp = true → ∀ e ∈ l, e.owner.code = c → e.once = true) ∧
    (∀ p ∈ l, ∀ q ∈ l, p.once = true → q.once = false → p.owner.code = q.owner.code →
      (!p.shares q || rankLt (rankG g p.spender) (rankG g q.spender)) = true)
  | [], _, _, _, _ => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx; cases hx
    · intro x hx; cases hx
    · intro _ x hx; cases hx
    · intro x hx; cases hx
  | e :: l, c, sp, C, h => by
    rw [byRunG] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hc, h⟩ := h
    by_cases ho : e.once = true
    · rw [if_pos ho, Bool.and_eq_true] at h
      obtain ⟨hall, hrec⟩ := h
      obtain ⟨A, B, Dd, Cc⟩ := byRunG_keeps g l _ _ _ hrec
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hc
        · exact Nat.le_trans hc (A x hx)
      · intro x hx hxc hxo y hy
        rcases List.mem_cons.1 hx with rfl | hx'
        · rw [if_pos (beq_iff_eq.2 hxc)] at hall
          exact List.all_eq_true.1 hall y hy
        · have e1 : e.owner.code = c := Nat.le_antisymm (hxc ▸ A x hx') hc
          have b1 := B x hx' (hxc.trans e1.symm) hxo
          rw [if_pos (beq_iff_eq.2 e1)] at b1
          exact b1 y hy
      · intro _ x hx hxc
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ho
        · have e1 : e.owner.code = c := Nat.le_antisymm (hxc ▸ A x hx') hc
          exact Dd rfl x hx' (hxc.trans e1.symm)
      · intro p hp q hq h1 h2 h3
        rcases List.mem_cons.1 hq with rfl | hq'
        · exact absurd ho (by rw [h2]; decide)
        · rcases List.mem_cons.1 hp with rfl | hp'
          · exact absurd (Dd rfl q hq' h3.symm) (by rw [h2]; decide)
          · exact Cc p hp' q hq' h1 h2 h3
    · have ho' : e.once = false := by simpa using ho
      rw [if_neg ho, Bool.and_eq_true] at h
      obtain ⟨hsp, hrec⟩ := h
      obtain ⟨A, B, -, Cc⟩ := byRunG_keeps g l _ _ _ hrec
      have nsp : e.owner.code = c → sp = false := by
        intro e1
        rw [beq_iff_eq.2 e1] at hsp
        simpa using hsp
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hc
        · exact Nat.le_trans hc (A x hx)
      · intro x hx hxc hxo y hy
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact absurd hxo ho
        · have e1 : e.owner.code = c := Nat.le_antisymm (hxc ▸ A x hx') hc
          have b1 := B x hx' (hxc.trans e1.symm) hxo
          rw [if_pos (beq_iff_eq.2 e1)] at b1
          obtain ⟨y', hy', ey, hz⟩ := layRun_covers g e C y hy
          have b2 := b1 y' hy'
          rw [ey, Bool.or_eq_true] at b2
          rw [Bool.or_eq_true]
          exact b2.imp id (hz _)
      · intro hs x hx hxc
        have e1 : e.owner.code = c := by
          rcases List.mem_cons.1 hx with rfl | hx'
          · exact hxc
          · exact Nat.le_antisymm (hxc ▸ A x hx') hc
        exact absurd hs (by rw [nsp e1]; decide)
      · intro p hp q hq h1 h2 h3
        rcases List.mem_cons.1 hp with rfl | hp'
        · exact absurd h1 ho
        · rcases List.mem_cons.1 hq with rfl | hq'
          · obtain ⟨y', hy', sy, hz⟩ := layRun_has g q (if q.owner.code == c then C else [])
            have b2 := B p hp' h3 h1 y' hy'
            rw [shares_sameRunE sy, Bool.or_eq_true] at b2
            rw [Bool.or_eq_true]
            exact b2.imp id (hz _)
          · exact Cc p hp' q hq' h1 h2 h3

/-- "They share no coin, or p's spender's rank is below q's" gives ok8G. -/
theorem ok8G_of_rankLt {g : Place → Nat} {p q : Ahead}
    (h : (!p.shares q || rankLt (rankG g p.spender) (rankG g q.spender)) = true) :
    ok8G g p q = true := by
  unfold ok8G
  rw [Bool.or_eq_true] at h ⊢
  refine h.imp id fun h2 => ?_
  rw [rankLt_iff] at h2
  simp only [rankG] at h2
  simp only [beforeG, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
  omega

/-- **Where the twin accepts: ok8G at every spending and every carrying entry of the list.** -/
theorem carried_okQ {g : Place → Nat} {d : Nat} {all : List Place} {l : List Ahead}
    (h : clause8Q g d all l = true) :
    ∀ p ∈ l, ∀ q ∈ l, p.once = true → q.once = false → ok8G g p q = true := by
  unfold clause8Q at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, -, -, K⟩ := byRunG_keeps g _ _ _ _ h.2
  have hs := (sortL_perm (fun (a b : Nat × Ahead) => decide (a.1 ≤ b.1)) d (2 ^ d)
    (l.map fun e => (sortKey8 e, e))).map (·.2)
  have e : (l.map fun e => (sortKey8 e, e)).map (·.2) = l := by
    rw [List.map_map]
    exact List.map_id l
  rw [e] at hs
  intro p hp q hq h1 h2
  by_cases c : p.owner = q.owner
  · exact ok8G_of_rankLt (K p (hs.mem_iff.2 hp) q (hs.mem_iff.2 hq) h1 h2 (by rw [c]))
  · unfold ok8G Ahead.shares
    rw [beq_eq_false_iff_ne.2 c]
    rfl

/-- **TWIN ∧ SEVENTH → EIGHTH**, general in g: where the order has no place twice, no two spending
entries share a coin and the twin accepts, the eighth test of `ProverCoinCounts.clauses` accepts. -/
theorem clause8Q_of {g : Place → Nat} {d : Nat} {all : List Place} {l : List Ahead} (hn : all.Nodup)
    (h7 : (l.filter (·.once)).Pairwise fun a b => a.shares b = false)
    (h : clause8Q g d all l = true) :
    (l.zipIdx.all fun p => !p.1.once || l.zipIdx.all fun q => p.2 == q.2 || !p.1.shares q.1 ||
      !(q.1.spender.before all p.1.spender ||
        (q.1.spender == p.1.spender && !q.1.once))) = true :=
  eighth_of_ok hn h7 (fun a ha => List.all_eq_true.1 (by
    unfold clause8Q at h
    rw [Bool.and_eq_true] at h
    exact h.1) a ha) (carried_okQ h)

/-! ## 4 Small lists: what the twin must accept, and what it must reject -/

/-- At an order of three places, g the piece's number; one owner; a run of three coins. Accepted:
the run spent at the second place and carried twice at the third; a carried run that shares no coin
with the spent one, its carrier in front. Rejected, by the twin and by the test: carried at a part
of the first place, in front of the spender; the same behind a good carrier of that run (the least
rank is kept); carried by the spender itself. Rejected by the twin: with g one off, where it accepts
at g; with no round of the sort. AND THE SEVENTH IS NEEDED: two spending entries that share a coin,
the second's spender in front: the twin accepts, the test rejects. -/
theorem clause8Q_small :
    clause8Q (fun p => p.piece) 20 [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K3⟩, 0⟩, false⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K3⟩, 1⟩, false⟩] = true ∧
    clause8Q (fun p => p.piece) 20 [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 5⟩, ⟨0, 2⟩, ⟨⟨1, none, 0, .K1⟩, 1⟩, false⟩] = true ∧
    clause8Q (fun p => p.piece) 20 [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 0, .K1⟩, 1⟩, false⟩] = false ∧
    (fun (l : List Ahead) => l.zipIdx.all fun p => !p.1.once || l.zipIdx.all fun q =>
      p.2 == q.2 || !p.1.shares q.1 ||
        !(q.1.spender.before
            [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩] p.1.spender ||
          (q.1.spender == p.1.spender && !q.1.once)))
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 0, .K1⟩, 1⟩, false⟩] = false ∧
    clause8Q (fun p => p.piece) 20 [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K3⟩, 0⟩, false⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 0, .K1⟩, 1⟩, false⟩] = false ∧
    (fun (l : List Ahead) => l.zipIdx.all fun p => !p.1.once || l.zipIdx.all fun q =>
      p.2 == q.2 || !p.1.shares q.1 ||
        !(q.1.spender.before
            [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩] p.1.spender ||
          (q.1.spender == p.1.spender && !q.1.once)))
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K3⟩, 0⟩, false⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 0, .K1⟩, 1⟩, false⟩] = false ∧
    clause8Q (fun p => p.piece) 20 [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, false⟩] = false ∧
    (fun (l : List Ahead) => l.zipIdx.all fun p => !p.1.once || l.zipIdx.all fun q =>
      p.2 == q.2 || !p.1.shares q.1 ||
        !(q.1.spender.before
            [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩] p.1.spender ||
          (q.1.spender == p.1.spender && !q.1.once)))
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, false⟩] = false ∧
    clause8Q (fun p => p.piece + 1) 20 [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K3⟩, 0⟩, false⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩] = false ∧
    clause8Q (fun p => p.piece) 20 [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K3⟩, 0⟩, false⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩] = true ∧
    clause8Q (fun p => p.piece) 0 [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K3⟩, 0⟩, false⟩] = false ∧
    clause8Q (fun p => p.piece) 20 [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩]
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K3⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩] = true ∧
    (fun (l : List Ahead) => l.zipIdx.all fun p => !p.1.once || l.zipIdx.all fun q =>
      p.2 == q.2 || !p.1.shares q.1 ||
        !(q.1.spender.before
            [⟨1, none, 0, .K1⟩, ⟨1, none, 1, .K2⟩, ⟨1, none, 2, .K3⟩] p.1.spender ||
          (q.1.spender == p.1.spender && !q.1.once)))
      [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 2, .K3⟩, 0⟩, true⟩,
       ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩] = false := by
  decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.sameAddr_of_placed
#print axioms ProofFile.Honest.eighth_of_ok
#print axioms ProofFile.Honest.rankLt_iff
#print axioms ProofFile.Honest.rankLt_min
#print axioms ProofFile.Honest.shares_sameRunE
#print axioms ProofFile.Honest.sameRunE_self
#print axioms ProofFile.Honest.layRun_covers
#print axioms ProofFile.Honest.layRun_has
#print axioms ProofFile.Honest.byRunG_keeps
#print axioms ProofFile.Honest.ok8G_of_rankLt
#print axioms ProofFile.Honest.carried_okQ
#print axioms ProofFile.Honest.clause8Q_of
#print axioms ProofFile.Honest.clause8Q_small
