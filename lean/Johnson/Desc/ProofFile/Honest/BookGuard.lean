-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookGuard.lean: one form for what a part that owns coins asks of the
book of coins (`ProverCoinCounts`, Honest/Frame.lean), and one public test over all such parts. Executable
definitions, the forms of two hypotheses, and small lemmas that tie them.

WHY. `Good.fresh` (Honest/Side.lean) speaks of the coins that a later part spends and of the owner's
other coins that are known to that part. The book's own tests (`ProverCoinCounts.clauses`) compare entries by
shared coins alone. An owner whose shown values tie its coins to each other, as every sender of a
coded row does, needs more: that certain OTHER coins of its own are not known to the spender. Which
coins these are depends on the owner's codes and shapes, which the book does not see. So each owner
names them itself: its GUARD.

  1  `CoinRuns`, `inRuns`, `coinRunsOf`, `ProverCoinCounts.spentRuns`, `ProverCoinCounts.knownRuns`: coins as runs of
     numbers, for each of the two fields: what a part spends of an owner's coins; what is known of
     them there
  2  `CoinRuns.Apart`, `CoinRuns.apartB`: no coin lies in both: as a proposition and as a test
  3  `Guard`: an owner's own function: from the coins that are spent, the coins that must not be
     known
  4  `GuardClear`, `guardClearB`: THE ONE FORM: nothing that is spent is known, and nothing that the
     guard names is known
  5  `OwnerTest`, `OwnerTest.ok`: a thread's test: which owners it speaks for, their guards, and
     what else it asks of the book
  6  `OwnerLaw`: THE FORM OF A THREAD's LAW AT ITS OWN TEST, at every owner that the test names
  7  `ProverCoinCounts.owners`, `ownersBare`, `ownersClearBy`: THE PUBLIC TEST over all owners of spending
     entries
  8  `ownersClearBy_pays_at`, `ownersClearBy_pays`: from a thread's law and the test: the law's
     conclusion at every owner that the thread's test names; and, where all listed tests have a law
     with one and the same conclusion, at every owner

WHO HAS TO ASK IT. `ownersClearBy` IS PART OF NO OTHER TEST. `ready`, `run` and `onlineProverFromPublicFiles` do not ask
it. Whoever states a law over a choice of fields that rests on `Good.fresh` names it among the
public premises.

Limits.
  * This file names no guard and lists no test. The list of the threads' tests stands in a file
    above theirs.
  * `ownersClearBy` IS FALSE WHERE AN OWNER OF A SPENDING ENTRY HAS NO TEST. Where several tests
    name an owner all of them are asked. At a book without a spending entry it is true: so the
    number of owners belongs beside its answer.
  * A test is as good as its guard. A guard that is too small does not make the test fail: it
    leaves the thread's `OwnerLaw` without a proof. What a `mine` that is too wide does depends on
    the thread's `fits`: where `fits` rejects at every owner that is not the thread's, the test
    fails there and the law keeps its proof; else the law is left without a proof.
  * A spending entry of length 0 makes its owner an owner, with no coin spent. The form reads coins,
    not entries.
  * That the test says yes at a book made from real public files is proved nowhere here.
  * `ord` is free: a yes at another list than `orderOf F` says less.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

/-! ## 1 Coins as runs -/

/-- Runs of one part's own coins, for each of the two fields: each run by its first number, from 0,
and its length. -/
structure CoinRuns where
  f : List (Nat × Nat)
  e : List (Nat × Nat)

/-- A number lies in one of the runs. -/
def inRuns (l : List (Nat × Nat)) (n : Nat) : Prop := ∃ r ∈ l, r.1 ≤ n ∧ n < r.1 + r.2

/-- The runs of a list of entries. -/
def coinRunsOf (l : List Ahead) : CoinRuns :=
  ⟨l.map fun a => (a.start.f, a.count.f), l.map fun a => (a.start.e, a.count.e)⟩

/-- What the part at p spends of the coins of the part at o. -/
def ProverCoinCounts.spentRuns (B : ProverCoinCounts) (o p : Addr) : CoinRuns := coinRunsOf (B.spentBy o p)

/-- What else of the coins of the part at o is handed to the part at p, or to a part in front. -/
def ProverCoinCounts.knownRuns (B : ProverCoinCounts) (ord : List Place) (o p : Addr) : CoinRuns :=
  coinRunsOf (B.knownBy ord o p)

/-- No coin lies in both. -/
def CoinRuns.Apart (a b : CoinRuns) : Prop :=
  (∀ n, ¬(inRuns a.f n ∧ inRuns b.f n)) ∧ ∀ n, ¬(inRuns a.e n ∧ inRuns b.e n)

/-- Two lists of runs have a number in common. -/
def runsMeet (a b : List (Nat × Nat)) : Bool :=
  a.any fun x => b.any fun y => meets x.1 x.2 y.1 y.2

/-- No coin lies in both: the test. -/
def CoinRuns.apartB (a b : CoinRuns) : Bool := !runsMeet a.f b.f && !runsMeet a.e b.e

theorem meets_iff (a n b m : Nat) :
    meets a n b m = true ↔ ∃ k, (a ≤ k ∧ k < a + n) ∧ b ≤ k ∧ k < b + m := by
  simp only [meets, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hn, hm⟩, h1⟩, h2⟩
    by_cases h : a ≤ b
    · exact ⟨b, ⟨h, by omega⟩, Nat.le_refl b, by omega⟩
    · exact ⟨a, ⟨Nat.le_refl a, by omega⟩, by omega, by omega⟩
  · rintro ⟨k, ⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega

theorem runsMeet_iff (a b : List (Nat × Nat)) :
    runsMeet a b = true ↔ ∃ n, inRuns a n ∧ inRuns b n := by
  simp only [runsMeet, inRuns, List.any_eq_true, meets_iff]
  constructor
  · rintro ⟨x, hx, y, hy, k, hk1, hk2⟩
    exact ⟨k, ⟨x, hx, hk1⟩, ⟨y, hy, hk2⟩⟩
  · rintro ⟨k, ⟨x, hx, hk1⟩, ⟨y, hy, hk2⟩⟩
    exact ⟨x, hx, y, hy, k, hk1, hk2⟩

/-- Where the test says yes no coin lies in both. -/
theorem CoinRuns.apartB_sound {a b : CoinRuns} (h : a.apartB b = true) : a.Apart b := by
  simp only [CoinRuns.apartB, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have h1 := (runsMeet_iff a.f b.f).2 ⟨n, hn⟩
    rw [h.1] at h1
    exact Bool.false_ne_true h1
  · have h1 := (runsMeet_iff a.e b.e).2 ⟨n, hn⟩
    rw [h.2] at h1
    exact Bool.false_ne_true h1

/-- Where no coin lies in both the test says yes. -/
theorem CoinRuns.apartB_complete {a b : CoinRuns} (h : a.Apart b) : a.apartB b = true := by
  simp only [CoinRuns.apartB, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨?_, ?_⟩
  · cases h1 : runsMeet a.f b.f with
    | false => rfl
    | true =>
      obtain ⟨n, hn⟩ := (runsMeet_iff a.f b.f).1 h1
      exact absurd hn (h.1 n)
  · cases h1 : runsMeet a.e b.e with
    | false => rfl
    | true =>
      obtain ⟨n, hn⟩ := (runsMeet_iff a.e b.e).1 h1
      exact absurd hn (h.2 n)

theorem CoinRuns.apartB_iff (a b : CoinRuns) : a.apartB b = true ↔ a.Apart b :=
  ⟨CoinRuns.apartB_sound, CoinRuns.apartB_complete⟩

/-! ## 2 The one form -/

/-- **A guard**: AN OWNER's OWN FUNCTION: from the coins that a part spends, the owner's coins that
must not be known to that part because the owner's shown values tie them to what is spent. -/
abbrev Guard : Type := CoinRuns → CoinRuns

/-- **THE ONE FORM OF THE PREMISE ON THE BOOK**, at an owner o and a spender p: NOTHING THAT IS
SPENT IS KNOWN, and nothing that the owner's guard names for what is spent is known. The first
clause does not pass through the guard: no value of `Guard` can forget what is spent. -/
def GuardClear (g : Guard) (B : ProverCoinCounts) (ord : List Place) (o p : Addr) : Prop :=
  (B.spentRuns o p).Apart (B.knownRuns ord o p) ∧
    (g (B.spentRuns o p)).Apart (B.knownRuns ord o p)

/-- The same: the test. -/
def guardClearB (g : Guard) (B : ProverCoinCounts) (ord : List Place) (o p : Addr) : Bool :=
  (B.spentRuns o p).apartB (B.knownRuns ord o p) &&
    (g (B.spentRuns o p)).apartB (B.knownRuns ord o p)

theorem guardClearB_iff (g : Guard) (B : ProverCoinCounts) (ord : List Place) (o p : Addr) :
    guardClearB g B ord o p = true ↔ GuardClear g B ord o p := by
  simp only [guardClearB, GuardClear, Bool.and_eq_true, CoinRuns.apartB_iff]

/-! ## 3 A thread's test and the form of its law -/

/-- **A thread's test on the book for the owners that it names.** -/
structure OwnerTest where
  name : String
  /-- the owners for which it is laid -/
  mine : Addr → Bool
  /-- the guard at such an owner -/
  guard : Addr → Guard
  /-- what else the owner asks of the book: that its entries lie within its count; which of its
  coins may be spent at all -/
  fits : ProverCoinCounts → List Place → Addr → Bool

/-- The test at one owner: `fits`, and the one form at every spender that spends something of it. -/
def OwnerTest.ok (t : OwnerTest) (B : ProverCoinCounts) (ord : List Place) (o : Addr) : Bool :=
  t.fits B ord o && (B.ahead.map (·.spender)).all fun p =>
    (B.spentBy o p).isEmpty || guardClearB (t.guard o) B ord o p

/-- **THE FORM OF A THREAD's LAW AT ITS OWN TEST**: AT EVERY OWNER THAT THE TEST NAMES AS ITS OWN.
`Fresh`: what the law concludes at a book, an order of places and an owner. The guard stands in the
premise by name. A guard that is too small leaves the proof of this without what it needs. So does a
`mine` that is too wide, unless `fits` rejects at the owners that are not the thread's. -/
def OwnerLaw (t : OwnerTest) (Fresh : ProverCoinCounts → List Place → Addr → Prop) : Prop :=
  ∀ (Bk : ProverCoinCounts) (ord : List Place) (o : Addr), t.mine o = true → t.fits Bk ord o = true →
    (∀ p, Bk.spentBy o p ≠ [] → GuardClear (t.guard o) Bk ord o p) → Fresh Bk ord o

/-- A part that spends something of o is named by the book as a spender. -/
theorem spender_of_spentBy {B : ProverCoinCounts} {o p : Addr} (hp : B.spentBy o p ≠ []) :
    p ∈ B.ahead.map (·.spender) := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hp
  unfold ProverCoinCounts.spentBy at he
  have h1 := List.mem_filter.1 he
  have h2 := h1.2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact List.mem_map.2 ⟨e, h1.1, h2.1.2⟩

/-- What a yes of the test at an owner gives: the last two premises of `OwnerLaw` (not `mine`). -/
theorem OwnerTest.ok_clear {t : OwnerTest} {B : ProverCoinCounts} {ord : List Place} {o : Addr}
    (h : t.ok B ord o = true) :
    t.fits B ord o = true ∧ ∀ p, B.spentBy o p ≠ [] → GuardClear (t.guard o) B ord o p := by
  simp only [OwnerTest.ok, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun p hp => ?_⟩
  have h3 := h.2 p (spender_of_spentBy hp)
  rw [Bool.or_eq_true] at h3
  rcases h3 with h0 | h1
  · exact absurd (List.isEmpty_iff.1 h0) hp
  · exact (guardClearB_iff _ _ _ _ _).1 h1

/-! ## 4 The public test over all owners -/

/-- The owners of the book's spending entries, each once. -/
def ProverCoinCounts.owners (B : ProverCoinCounts) : List Addr := ((B.ahead.filter (·.once)).map (·.owner)).dedup

theorem ProverCoinCounts.mem_owners {B : ProverCoinCounts} {e : Ahead} (he : e ∈ B.ahead) (ho : e.once = true) :
    e.owner ∈ B.owners :=
  List.mem_dedup.2 (List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, ho⟩, rfl⟩)

/-- The owners for which no test is laid. -/
def ownersBare (ts : List OwnerTest) (B : ProverCoinCounts) : List Addr :=
  B.owners.filter fun o => !ts.any (·.mine o)

/-- **THE TEST.** FALSE WHERE AN OWNER OF A SPENDING ENTRY HAS NO TEST. Where several tests name an
owner all of them are asked. -/
def ownersClearBy (ts : List OwnerTest) (B : ProverCoinCounts) (ord : List Place) : Bool :=
  B.owners.all fun o => ts.any (·.mine o) && (ts.filter (·.mine o)).all fun t => t.ok B ord o

/-- At a yes: every owner has a test, and every test that names it says yes. -/
theorem ownersClearBy_at {ts : List OwnerTest} {B : ProverCoinCounts} {ord : List Place}
    (h : ownersClearBy ts B ord = true) (o : Addr) (ho : o ∈ B.owners) :
    (∃ t ∈ ts, t.mine o = true) ∧ ∀ t ∈ ts, t.mine o = true → t.ok B ord o = true := by
  have h1 := List.all_eq_true.1 h o ho
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h1
  exact ⟨h1.1, fun t ht hm => h1.2 t (List.mem_filter.2 ⟨ht, hm⟩)⟩

/-- At a yes no owner is without a test. -/
theorem ownersClearBy_bare {ts : List OwnerTest} {B : ProverCoinCounts} {ord : List Place}
    (h : ownersClearBy ts B ord = true) : ownersBare ts B = [] := by
  refine List.filter_eq_nil_iff.2 fun o ho hb => ?_
  obtain ⟨t, ht, hm⟩ := (ownersClearBy_at h o ho).1
  have h1 : ts.any (·.mine o) = true := List.any_eq_true.2 ⟨t, ht, hm⟩
  rw [h1] at hb
  exact Bool.false_ne_true hb

/-- **THE JOIN, TEST BY TEST**: where a listed test has its thread's law, a yes of the public test
gives that law's conclusion at every owner of a spending entry that the thread's test names. Each
thread has a `Fresh` of its own here. -/
theorem ownersClearBy_pays_at {ts : List OwnerTest} {B : ProverCoinCounts} {ord : List Place}
    {Fresh : ProverCoinCounts → List Place → Addr → Prop} {t : OwnerTest} (ht : t ∈ ts)
    (hL : OwnerLaw t Fresh) (h : ownersClearBy ts B ord = true) :
    ∀ o ∈ B.owners, t.mine o = true → Fresh B ord o := by
  intro o ho hm
  have hk := OwnerTest.ok_clear ((ownersClearBy_at h o ho).2 t ht hm)
  exact hL B ord o hm hk.1 hk.2

/-- **THE JOIN AT ONE CONCLUSION**: where EVERY listed test has a law with the same `Fresh`, a yes
of the test gives it at every owner of a spending entry. -/
theorem ownersClearBy_pays {ts : List OwnerTest} {B : ProverCoinCounts} {ord : List Place}
    {Fresh : ProverCoinCounts → List Place → Addr → Prop} (hL : ∀ t ∈ ts, OwnerLaw t Fresh)
    (h : ownersClearBy ts B ord = true) : ∀ o ∈ B.owners, Fresh B ord o := by
  intro o ho
  obtain ⟨⟨t, ht, hm⟩, hall⟩ := ownersClearBy_at h o ho
  have hk := OwnerTest.ok_clear (hall t ht hm)
  exact hL t ht B ord o hm hk.1 hk.2

end ProofFile.Honest

#print axioms ProofFile.Honest.meets_iff
#print axioms ProofFile.Honest.runsMeet_iff
#print axioms ProofFile.Honest.CoinRuns.apartB_sound
#print axioms ProofFile.Honest.CoinRuns.apartB_complete
#print axioms ProofFile.Honest.CoinRuns.apartB_iff
#print axioms ProofFile.Honest.guardClearB_iff
#print axioms ProofFile.Honest.spender_of_spentBy
#print axioms ProofFile.Honest.OwnerTest.ok_clear
#print axioms ProofFile.Honest.ProverCoinCounts.mem_owners
#print axioms ProofFile.Honest.ownersClearBy_at
#print axioms ProofFile.Honest.ownersClearBy_bare
#print axioms ProofFile.Honest.ownersClearBy_pays_at
#print axioms ProofFile.Honest.ownersClearBy_pays
