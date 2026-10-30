--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyEnds.lean: THE LAST SUB-PROTOCOLS OF THE KEY FILE's SHARED AND THIRD CHAIN ACCEPT, FROM THE
BOOK-KEEPING OF THE STATE IN FRONT OF THEM; with them the test that the third chain's start asks of
the shared chain's end, and the part of the last test that reads the third chain's last state. A
chain's last sub-protocol has no part of a prover: it asks two tests on the carried statement: a
proximity test has begun on every group; every sampled message is in a tested group. Statements and
proofs. Single tests of the verifier's: NOTHING IS SHOWN OF ANY PROVER: no completeness, nothing on
what a view shows.

THE DIRECTION. The library has tests with code on the book-keeping of a chain's state at each border
between two sub-protocols (for the two later chains: `LKFU.Shape23.shape₂`, `shape₃`,
Johnson/RunOne/BorderShapes/LKFU/Shape23.lean: counts, numbers, flags, members: no field value). Its laws
on sub-protocols without a round say what an acceptance GIVES. Here the other direction: the
book-keeping in front GIVES the acceptance.

TWO THINGS LACK IN THE LIBRARY's BOOK-KEEPING, AND ARE NAMED PREMISES HERE.
  `Joined st`: a message that a group lists as a member has that group in its own list of groups.
    The tests at a chain's end read the messages' own lists; the book-keeping holds the groups'
    lists of members. `toy₂Struck_rejected`: without it the tests can reject. `joined_of_listed`: it
    follows from `Listed` (E2E/KeyListed.lean), which the first two chains' first states have and
    which every sub-protocol of the key file's three chains keeps where it accepts.
  `Older n g st`: the library's test at the third chain's borders is said relative to the numbers n,
    g of messages and groups at the first chain's end, and reads none of these but the last two
    messages and the last group. The third chain's end reads them all. `older_of_end₁`
    (E2E/KeyEndFirst.lean) has it at the first chain's last statement, from the book-keeping in
    front of the seal (`End₁`: a premise there); that the third chain's accepted steps keep it is
    not shown here.

What is shown.
  `refuse_ok`, `refuse_no`: a list of named clauses is rejected just where one fails.
  `all_begun`, **`untested_ok`**, `all_grouped`: for any statement with `Joined`: if every group's
    test has begun, and every message either has no sample or is a member of some group: the two
    tests at a chain's end accept; so do the two weaker ones of `K14.tested` and `fin₃`.
  `grpIs_spec`, `msgIs_bare`, `towerIs_spec`: what three of the library's tests say.
  `End₂ S a st`: the eight clauses of `shape₂` at border 11 that are spent; `end₂_of_shape`: they
    are had from `shape₂ S a 11 d`. `End₂.begun`, `tower_home`, `End₂.home`: the two premises from
    them.
  **`end₂_passes`**: where the state in front has `shape₂` at border 11 and `Joined`, the shared
    chain's last sub-protocol (`K12.Seat.last`) accepts and hands the state on as it is.
    **`tested_of_end₂`**: and the test that the third chain's start asks of the shared chain's end
      accepts there.
    `shape₂_behind`: the library's test at border 12 is its test at border 11.
  `End₃ S a n g idx st`, `end₃_of_shape`, `End₃.begun`, `End₃.home`: the like at the third chain's
    border 3, with `Older`.
  **`end₃_passes`**, **`fin₃_passes`**: the third chain's last sub-protocol (`Third.end₃`) accepts
    and hands the state on; the part of the last test that reads that state accepts.
    `shape₃_behind`.
  `joinedB`, `joined_of_B`: `Joined` as a test with code.
  MEMBERS: `toy₂_member`, `toy₃_member`: the premises can be met together. Toys: two stages, no
    answer to a sample, no row.

Limits.
- That a run's states have `shape₂` at border 11, `shape₃` at border 3, `Joined` and `Older` is not
  shown: they are owed by whoever shows that the sub-protocols in front keep them.
- The toys are members of the clauses that are SPENT (`End₂`, `End₃`), not of the library's whole
  tests.
- `shape₂` and `shape₃` bear one form of the table's shape alone (their first clause).
- The first chain's end: E2E/KeyEndFirst.lean.


-/
import E2E.KeyListed
import Johnson.RunOne.BorderShapes.LKFU.Shape23
import Johnson.Desc.K12.Seat.Fill
import Johnson.Desc.Third.Chain

set_option autoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.ChainEnd (Clauses untestedL)
open LKFU.Shape23 (grpIs msgIs towerIs shape₂)

/-- **A member of a group has that group in its own list.** -/
def Joined (st : Statement) : Prop :=
  ∀ (g : Nat) (G : OnBytes.Group) (o : Nat) (x : Oracle), st.groups[g]? = some G →
    o ∈ G.members.toList → st.oracles[o]? = some x → g ∈ x.groups

/-- It follows from the property that every sub-protocol of the key file's chains keeps
(E2E/KeyListed.lean). -/
theorem joined_of_listed (st : Statement) (h : Listed st) : Joined st := by
  intro g G o x hG hm hx
  obtain ⟨x', hx', hg⟩ := h g G o hG (Array.mem_toList_iff.1 hm)
  rw [hx] at hx'
  obtain rfl := Option.some.inj hx'
  exact hg

/-- A list of named clauses that all hold is not rejected. -/
theorem refuse_ok (l : Clauses) (h : ∀ c ∈ l, c.2 = true) :
    VerifiableInference.Desc.ChainEnd.refuse l = .ok () := by
  unfold VerifiableInference.Desc.ChainEnd.refuse
  have e : l.find? (!·.2) = none := List.find?_eq_none.2 fun c hc => by simp [h c hc]
  rw [e]

section Any
variable (st : Statement) (hj : Joined st)
  (hg : ∀ g, g < st.groups.size → ∃ G : OnBytes.Group, st.groups[g]? = some G ∧ G.inRun = true)
  (ho : ∀ o, o < st.oracles.size →
    (∃ x : Oracle, st.oracles[o]? = some x ∧ x.sampled = false) ∨
      ∃ (g : Nat) (G : OnBytes.Group), st.groups[g]? = some G ∧ o ∈ G.members.toList)
include hg

/-- Every group's test has begun. -/
theorem all_begun : st.groups.all (·.inRun) = true := by
  refine Array.all_eq_true_iff_forall_mem.2 fun G hG => ?_
  obtain ⟨g, hlt, e⟩ := Array.mem_iff_getElem.1 hG
  obtain ⟨G', h', r⟩ := hg g hlt
  rw [Array.getElem?_eq_some_iff.2 ⟨hlt, e⟩] at h'
  obtain rfl := Option.some.inj h'
  exact r

include hj ho

/-- **The two tests at a chain's end accept.** -/
theorem untested_ok : VerifiableInference.Desc.ChainEnd.refuse (untestedL st) = .ok () := by
  refine refuse_ok _ fun c hc => ?_
  unfold untestedL at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact all_begun st hg
  · rcases List.mem_cons.1 hc with rfl | hc
    · refine Array.all_eq_true_iff_forall_mem.2 fun x hx => ?_
      obtain ⟨o, hlt, e⟩ := Array.mem_iff_getElem.1 hx
      have ex : st.oracles[o]? = some x := Array.getElem?_eq_some_iff.2 ⟨hlt, e⟩
      rcases ho o hlt with ⟨x', h', hs⟩ | ⟨g, G, hG, hm⟩
      · rw [ex] at h'
        obtain rfl := Option.some.inj h'
        simp [hs]
      · obtain ⟨G', h', r⟩ := hg g (Array.getElem?_eq_some_iff.1 hG).1
        rw [hG] at h'
        obtain rfl := Option.some.inj h'
        refine Bool.or_eq_true_iff.2 (Or.inr (List.any_eq_true.2 ⟨g, hj g G o x hG hm ex, ?_⟩))
        rw [hG]
        exact r
    · cases hc

omit hg in
/-- Every sampled message is in some group. -/
theorem all_grouped : (st.oracles.all fun x => !x.sampled || !x.groups.isEmpty) = true := by
  refine Array.all_eq_true_iff_forall_mem.2 fun x hx => ?_
  obtain ⟨o, hlt, e⟩ := Array.mem_iff_getElem.1 hx
  have ex : st.oracles[o]? = some x := Array.getElem?_eq_some_iff.2 ⟨hlt, e⟩
  rcases ho o hlt with ⟨x', h', hs⟩ | ⟨g, G, hG, hm⟩
  · rw [ex] at h'
    obtain rfl := Option.some.inj h'
    simp [hs]
  · have hmem := hj g G o x hG hm ex
    refine Bool.or_eq_true_iff.2 (Or.inr ?_)
    cases hgr : x.groups with
    | nil => rw [hgr] at hmem; cases hmem
    | cons _ _ => rfl

end Any

/-! ## What four of the library's tests say -/

theorem grpIs_spec {st : Statement} {g : Nat} {ms : List Nat} {p q : Nat} {r : Bool}
    (h : grpIs st g ms p q r = true) :
    ∃ G : OnBytes.Group, st.groups[g]? = some G ∧ G.members.toList = ms ∧ G.inRun = r := by
  unfold grpIs at h
  cases hG : st.groups[g]? with
  | none => rw [hG] at h; cases h
  | some G =>
    rw [hG] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨G, rfl, h.1.1.1.1, h.2⟩

theorem msgIs_bare {st : Statement} {o : Nat} {sp : Bool} (h : msgIs st o none sp = true) :
    ∃ x : Oracle, st.oracles[o]? = some x ∧ x.sampled = false := by
  unfold msgIs at h
  cases hx : st.oracles[o]? with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨x, rfl, h.1.1⟩

theorem towerIs_spec {st : Statement} {m₀ g₀ s a : Nat} (h : towerIs st m₀ g₀ s a = true) (j : Nat)
    (hj : j < s - 1) :
    msgIs st (m₀ + 2 * j) (some a) false = true ∧ msgIs st (m₀ + 2 * j + 1) none true = true ∧
      grpIs st (g₀ + j) [m₀ + 2 * j] 0 0 true = true := by
  unfold towerIs at h
  have t := List.all_eq_true.1 h j (List.mem_range.2 hj)
  simp only [Bool.and_eq_true] at t
  exact ⟨t.1.1, t.1.2, t.2⟩

/-! ## The shared chain's end -/

/-- The clauses of the library's book-keeping at the shared chain's border 11 that are spent. -/
structure End₂ (S : LinShape) (a : Nat) (st : Statement) : Prop where
  msgs : st.oracles.size = 4 + 2 * (S.testU.length - 1) + 1 + 2 * (S.testOmega.length - 1)
  grps : st.groups.size = 2 + (S.testU.length - 1) + (S.testOmega.length - 1)
  m1 : msgIs st 1 none true = true
  gU : grpIs st 0 [0, 3] 0 0 true = true
  gO : grpIs st 1 [2, 3] 0 0 true = true
  tU : towerIs st 4 2 S.testU.length a = true
  mO : msgIs st (4 + 2 * (S.testU.length - 1)) none true = true
  tO : towerIs st (4 + 2 * (S.testU.length - 1) + 1) (2 + (S.testU.length - 1)) S.testOmega.length
    a = true

/-- They are had from the library's test at border 11. -/
theorem end₂_of_shape (S : LinShape) (a : Nat) (d : _root_.Desc.K14.St)
    (h : LKFU.Shape23.ok (shape₂ S a 11 d) = true) : End₂ S a d.st := by
  simp only [LKFU.Shape23.ok, shape₂, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨-, h2, h3, -, -, -, -, -, h9, -, -, -, h13, h14, -, h16, h17, -⟩ := h
  have h9' : msgIs d.st 0 (some a) false = true ∧ msgIs d.st 1 none true = true := by
    simpa using h9
  have h17' : msgIs d.st (4 + 2 * (S.testU.length - 1)) none true = true ∧
      towerIs d.st (4 + 2 * (S.testU.length - 1) + 1) (2 + (S.testU.length - 1))
        S.testOmega.length a = true := by simpa using h17
  exact ⟨by simpa using h2, by simpa using h3, h9'.2, by simpa using h13, by simpa using h14,
    by simpa using h16, h17'.1, h17'.2⟩

section End
variable {S : LinShape} {a : Nat} {st : Statement} (h : End₂ S a st)
include h

/-- Every group's test has begun. -/
theorem End₂.begun (g : Nat) (hg : g < st.groups.size) :
    ∃ G : OnBytes.Group, st.groups[g]? = some G ∧ G.inRun = true := by
  rw [h.grps] at hg
  by_cases h0 : g = 0
  · subst h0
    obtain ⟨G, e, -, r⟩ := grpIs_spec h.gU
    exact ⟨G, e, r⟩
  by_cases h1 : g = 1
  · subst h1
    obtain ⟨G, e, -, r⟩ := grpIs_spec h.gO
    exact ⟨G, e, r⟩
  by_cases h2 : g < 2 + (S.testU.length - 1)
  · obtain ⟨-, -, t⟩ := towerIs_spec h.tU (g - 2) (by omega)
    obtain ⟨G, e, -, r⟩ := grpIs_spec t
    have i : 2 + (g - 2) = g := by omega
    rw [i] at e
    exact ⟨G, e, r⟩
  · obtain ⟨-, -, t⟩ := towerIs_spec h.tO (g - (2 + (S.testU.length - 1))) (by omega)
    obtain ⟨G, e, -, r⟩ := grpIs_spec t
    have i : 2 + (S.testU.length - 1) + (g - (2 + (S.testU.length - 1))) = g := by omega
    rw [i] at e
    exact ⟨G, e, r⟩

omit h in
/-- A message of a proximity test's later stages has no sample or is a member of a group. -/
theorem tower_home {m₀ g₀ s : Nat} (t : towerIs st m₀ g₀ s a = true) (o : Nat) (h1 : m₀ ≤ o)
    (h2 : o < m₀ + 2 * (s - 1)) :
    (∃ x : Oracle, st.oracles[o]? = some x ∧ x.sampled = false) ∨
      ∃ (g : Nat) (G : OnBytes.Group), st.groups[g]? = some G ∧ o ∈ G.members.toList := by
  obtain ⟨-, b, c⟩ := towerIs_spec t ((o - m₀) / 2) (by omega)
  rcases Nat.mod_two_eq_zero_or_one (o - m₀) with hp | hp
  · obtain ⟨G, e, m, -⟩ := grpIs_spec c
    refine Or.inr ⟨_, G, e, ?_⟩
    rw [m]
    exact List.mem_singleton.2 (by omega)
  · have i : m₀ + 2 * ((o - m₀) / 2) + 1 = o := by omega
    rw [i] at b
    exact Or.inl (msgIs_bare b)

/-- Every message has no sample or is a member of a group. -/
theorem End₂.home (o : Nat) (ho : o < st.oracles.size) :
    (∃ x : Oracle, st.oracles[o]? = some x ∧ x.sampled = false) ∨
      ∃ (g : Nat) (G : OnBytes.Group), st.groups[g]? = some G ∧ o ∈ G.members.toList := by
  rw [h.msgs] at ho
  obtain ⟨GU, eU, mU, -⟩ := grpIs_spec h.gU
  obtain ⟨GO, eO, mO, -⟩ := grpIs_spec h.gO
  by_cases h0 : o = 0
  · subst h0
    exact Or.inr ⟨0, GU, eU, by rw [mU]; simp⟩
  by_cases h1 : o = 1
  · subst h1
    exact Or.inl (msgIs_bare h.m1)
  by_cases h2 : o = 2
  · subst h2
    exact Or.inr ⟨1, GO, eO, by rw [mO]; simp⟩
  by_cases h3 : o = 3
  · subst h3
    exact Or.inr ⟨0, GU, eU, by rw [mU]; simp⟩
  by_cases h4 : o < 4 + 2 * (S.testU.length - 1)
  · exact tower_home h.tU o (by omega) h4
  by_cases h5 : o = 4 + 2 * (S.testU.length - 1)
  · subst h5
    exact Or.inl (msgIs_bare h.mO)
  · exact tower_home h.tO o (by omega) (by omega)

end End

/-- **The shared chain's last sub-protocol accepts and hands the state on as it is.** -/
theorem end₂_passes (S : LinShape) (a : Nat) (d : _root_.Desc.K14.St)
    (h : LKFU.Shape23.ok (shape₂ S a 11 d) = true) (hj : Joined d.st)
    (front : List (VerifiableInference.Desc.Block _root_.Desc.K14.St Unit)) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (VerifiableInference.Desc.K12.Seat.last front).decide d rs gs = .ok d := by
  have e := end₂_of_shape S a d h
  show (VerifiableInference.Desc.ChainEnd.refuse (untestedL d.st)).map (fun _ => d) = .ok d
  rw [untested_ok d.st hj e.begun e.home]
  rfl

/-- **The test that the third chain's start asks of the shared chain's end accepts there.** -/
theorem tested_of_end₂ (S : LinShape) (a : Nat) (d : _root_.Desc.K14.St)
    (h : LKFU.Shape23.ok (shape₂ S a 11 d) = true) (hj : Joined d.st) :
    _root_.Desc.K14.tested d = true := by
  have e := end₂_of_shape S a d h
  unfold _root_.Desc.K14.tested
  rw [all_begun d.st e.begun, all_grouped d.st hj e.home]
  rfl

/-- The library's test at the border behind the end is its test in front: the state is the same,
and no clause parts the two borders. -/
theorem shape₂_behind (S : LinShape) (a : Nat) (d : _root_.Desc.K14.St) :
    shape₂ S a 12 d = shape₂ S a 11 d := rfl

/-! ## The third chain's end, and the part of the last test that reads its last state -/

/-- The clauses of the library's book-keeping at the third chain's border 3 that are spent. n, g:
the numbers of messages and of groups at the first chain's end. -/
structure End₃ (S : LinShape) (a n g : Nat) (idx : List Nat) (st : Statement) : Prop where
  msgs : st.oracles.size = n + 1 + 2 * (S.testOwn.length - 1)
  grps : st.groups.size = g + (S.testOwn.length - 1)
  mask : msgIs st (n - 1) none true = true
  own : grpIs st (g - 1) (idx ++ [n - 2] ++ [n]) 0 0 true = true
  tW : towerIs st (n + 1) g S.testOwn.length a = true

/-- They are had from the library's test at border 3. -/
theorem end₃_of_shape (S : LinShape) (a n g t : Nat) (idx : List Nat)
    (s : VerifiableInference.Desc.Third.S₃)
    (h : LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a n g t idx 3 s) = true) :
    End₃ S a n g idx s.st := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₃, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at h
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h10, -, h12, h13⟩ := h
  have h10' : msgIs s.st (n - 2) (some a) false = true ∧ msgIs s.st (n - 1) none true = true := by
    simpa using h10
  exact ⟨by simpa [Nat.add_assoc] using h2, by simpa using h3, h10'.2, by simpa using h12,
    by simpa using h13⟩

/-- **What the third chain's end wants of the first chain's messages and groups**, which the
library's test at the third chain's borders does not read: every group but the last has begun its
test; every message but the last two has no sample or is a member of a group. -/
structure Older (n g : Nat) (st : Statement) : Prop where
  two : 2 ≤ n
  one : 1 ≤ g
  begun : ∀ j, j < g - 1 → ∃ G : OnBytes.Group, st.groups[j]? = some G ∧ G.inRun = true
  home : ∀ o, o < n - 2 → (∃ x : Oracle, st.oracles[o]? = some x ∧ x.sampled = false) ∨
    ∃ (j : Nat) (G : OnBytes.Group), st.groups[j]? = some G ∧ o ∈ G.members.toList

section End3
variable {S : LinShape} {a n g : Nat} {idx : List Nat} {st : Statement} (h : End₃ S a n g idx st)
  (hO : Older n g st)
include h hO

theorem End₃.begun (j : Nat) (hj : j < st.groups.size) :
    ∃ G : OnBytes.Group, st.groups[j]? = some G ∧ G.inRun = true := by
  rw [h.grps] at hj
  have h1 := hO.one
  by_cases c0 : j < g - 1
  · exact hO.begun j c0
  by_cases c1 : j = g - 1
  · subst c1
    obtain ⟨G, e, -, r⟩ := grpIs_spec h.own
    exact ⟨G, e, r⟩
  · obtain ⟨-, -, t⟩ := towerIs_spec h.tW (j - g) (by omega)
    obtain ⟨G, e, -, r⟩ := grpIs_spec t
    have i : g + (j - g) = j := by omega
    rw [i] at e
    exact ⟨G, e, r⟩

theorem End₃.home (o : Nat) (ho : o < st.oracles.size) :
    (∃ x : Oracle, st.oracles[o]? = some x ∧ x.sampled = false) ∨
      ∃ (j : Nat) (G : OnBytes.Group), st.groups[j]? = some G ∧ o ∈ G.members.toList := by
  rw [h.msgs] at ho
  have h2 := hO.two
  obtain ⟨G, e, m, -⟩ := grpIs_spec h.own
  by_cases c0 : o < n - 2
  · exact hO.home o c0
  by_cases c1 : o = n - 2
  · subst c1
    exact Or.inr ⟨_, G, e, by rw [m]; simp⟩
  by_cases c2 : o = n - 1
  · subst c2
    exact Or.inl (msgIs_bare h.mask)
  by_cases c3 : o = n
  · subst c3
    exact Or.inr ⟨_, G, e, by rw [m]; simp⟩
  · obtain ⟨-, b, c⟩ := towerIs_spec h.tW ((o - (n + 1)) / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one (o - (n + 1)) with hp | hp
    · obtain ⟨G', e', m', -⟩ := grpIs_spec c
      refine Or.inr ⟨_, G', e', ?_⟩
      rw [m']
      exact List.mem_singleton.2 (by omega)
    · have i : n + 1 + 2 * ((o - (n + 1)) / 2) + 1 = o := by omega
      rw [i] at b
      exact Or.inl (msgIs_bare b)

end End3

/-- **The third chain's last sub-protocol accepts and hands the state on as it is.** -/
theorem end₃_passes {Cl : Type} (S : LinShape) (a n g t : Nat) (idx : List Nat)
    (s : VerifiableInference.Desc.Third.S₃)
    (h : LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a n g t idx 3 s) = true) (hO : Older n g s.st)
    (hj : Joined s.st)
    (front : List (VerifiableInference.Desc.Block VerifiableInference.Desc.Third.S₃ Cl))
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (VerifiableInference.Desc.Third.end₃ front).decide s rs gs = .ok s := by
  have e := end₃_of_shape S a n g t idx s h
  show (VerifiableInference.Desc.ChainEnd.refuse (untestedL s.st)).map (fun _ => s) = .ok s
  rw [untested_ok s.st hj (e.begun hO) (e.home hO)]
  rfl

/-- **The part of the description's last test that reads the third chain's last state accepts.** -/
theorem fin₃_passes (S : LinShape) (a n g t : Nat) (idx : List Nat)
    (s : VerifiableInference.Desc.Third.S₃)
    (h : LKFU.Shape23.ok (LKFU.Shape23.shape₃ S a n g t idx 3 s) = true) (hO : Older n g s.st)
    (hj : Joined s.st) : VerifiableInference.Desc.Third.fin₃ s = true := by
  have e := end₃_of_shape S a n g t idx s h
  unfold VerifiableInference.Desc.Third.fin₃
  rw [all_begun s.st (e.begun hO), all_grouped s.st hj (e.home hO)]
  rfl

/-- The library's test at the border behind the end is its test in front. -/
theorem shape₃_behind (S : LinShape) (a n g t : Nat) (idx : List Nat)
    (s : VerifiableInference.Desc.Third.S₃) :
    LKFU.Shape23.shape₃ S a n g t idx 4 s = LKFU.Shape23.shape₃ S a n g t idx 3 s := rfl

/-! ## Members: the premises can be met together -/

/-- `Joined` as a test with code. -/
def joinedB (st : Statement) : Bool :=
  (List.range st.groups.size).all fun g =>
    match st.groups[g]? with
    | some G => G.members.toList.all fun o =>
        match st.oracles[o]? with
        | some x => x.groups.contains g
        | none => true
    | none => true

/-- Where the test accepts, `Joined` holds. -/
theorem joined_of_B (st : Statement) (h : joinedB st = true) : Joined st := by
  intro g G o x hG ho hx
  have t := List.all_eq_true.1 h g (List.mem_range.2 (Array.getElem?_eq_some_iff.1 hG).1)
  rw [hG] at t
  have u := List.all_eq_true.1 t o ho
  rw [hx] at u
  exact List.contains_iff_mem.1 u

/-- A sampled message without a sample row, in the groups gs. -/
def toySampled (gs : List Nat) : Oracle := { shape := {}, sampled := true, groups := gs }

/-- A message without a sample, spent as a mask. -/
def toyMask : Oracle := { shape := {}, spentAsMask := true }

/-- A group whose test has begun, without an open row. -/
def toyGroup (ms : Array Nat) : OnBytes.Group := { code := 0, members := ms, inRun := true }

/-- A shape whose test on G_u and whose own test have two stages; all else at the defaults. -/
def toyShape : LinShape :=
  { (default : LinShape) with testU := [default, default], testOwn := [default, default] }

/-- A statement of seven messages and three groups. -/
def toy₂ : Statement :=
  { oracles := #[toySampled [0], toyMask, toySampled [1], toySampled [0, 1], toySampled [2],
      toyMask, toyMask]
    groups := #[toyGroup #[0, 3], toyGroup #[2, 3], toyGroup #[4]] }

/-- **A member**: the clauses that are spent at the shared chain's end and `Joined` hold together. A
toy: no answer to a sample, no row. -/
theorem toy₂_member : End₂ toyShape 0 toy₂ ∧ Joined toy₂ :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, joined_of_B toy₂ rfl⟩

/-- A statement of six messages and three groups; the first chain's: three and two. -/
def toy₃ : Statement :=
  { oracles := #[toySampled [1], toySampled [1], toyMask, toySampled [1], toySampled [2], toyMask]
    groups := #[toyGroup #[], toyGroup #[0, 1, 3], toyGroup #[4]] }

/-- **A member** at the third chain's end. A toy. -/
theorem toy₃_member : End₃ toyShape 0 3 2 [0] toy₃ ∧ Older 3 2 toy₃ ∧ Joined toy₃ := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨by omega, by omega, fun j hj => ?_, fun o ho => ?_⟩,
    joined_of_B toy₃ rfl⟩
  · obtain rfl : j = 0 := by omega
    exact ⟨_, rfl, rfl⟩
  · obtain rfl : o = 0 := by omega
    exact Or.inr ⟨1, _, rfl, by decide⟩

/-- **A guard**: without `Joined` the tests at a chain's end can reject a statement that has all the
clauses which are spent: the same toy with the first message's own list of groups struck. -/
def toy₂Struck : Statement :=
  { oracles := #[toySampled [], toyMask, toySampled [1], toySampled [0, 1], toySampled [2], toyMask,
      toyMask]
    groups := #[toyGroup #[0, 3], toyGroup #[2, 3], toyGroup #[4]] }

/-- A list of named clauses of which one fails is rejected. -/
theorem refuse_no (l : Clauses) (h : ¬ ∀ c ∈ l, c.2 = true) :
    VerifiableInference.Desc.ChainEnd.refuse l ≠ .ok () := by
  unfold VerifiableInference.Desc.ChainEnd.refuse
  split
  · intro c
    cases c
  · rename_i e
    exact fun _ => h fun x hx => by simpa using List.find?_eq_none.1 e x hx

theorem toy₂Struck_rejected : End₂ toyShape 0 toy₂Struck ∧
    VerifiableInference.Desc.ChainEnd.refuse (untestedL toy₂Struck) ≠ .ok () := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, refuse_no _ fun h => ?_⟩
  have h2 := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h3 := Array.all_eq_true_iff_forall_mem.1 h2 (toySampled []) (by simp [toy₂Struck])
  simp [toySampled] at h3

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.joined_of_B
#print axioms AtPublicFiles.AtFiles.toy₂_member
#print axioms AtPublicFiles.AtFiles.toy₃_member
#print axioms AtPublicFiles.AtFiles.refuse_no
#print axioms AtPublicFiles.AtFiles.toy₂Struck_rejected
#print axioms AtPublicFiles.AtFiles.shape₂_behind
#print axioms AtPublicFiles.AtFiles.end₃_of_shape
#print axioms AtPublicFiles.AtFiles.End₃.begun
#print axioms AtPublicFiles.AtFiles.End₃.home
#print axioms AtPublicFiles.AtFiles.end₃_passes
#print axioms AtPublicFiles.AtFiles.fin₃_passes
#print axioms AtPublicFiles.AtFiles.shape₃_behind
#print axioms AtPublicFiles.AtFiles.joined_of_listed
#print axioms AtPublicFiles.AtFiles.refuse_ok
#print axioms AtPublicFiles.AtFiles.all_begun
#print axioms AtPublicFiles.AtFiles.untested_ok
#print axioms AtPublicFiles.AtFiles.all_grouped
#print axioms AtPublicFiles.AtFiles.grpIs_spec
#print axioms AtPublicFiles.AtFiles.msgIs_bare
#print axioms AtPublicFiles.AtFiles.towerIs_spec
#print axioms AtPublicFiles.AtFiles.end₂_of_shape
#print axioms AtPublicFiles.AtFiles.End₂.begun
#print axioms AtPublicFiles.AtFiles.tower_home
#print axioms AtPublicFiles.AtFiles.End₂.home
#print axioms AtPublicFiles.AtFiles.end₂_passes
#print axioms AtPublicFiles.AtFiles.tested_of_end₂
