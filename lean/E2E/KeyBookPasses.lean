-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookPasses.lean: the key file's book of coins (`keyBook K`, E2E/KeyBook.lean) passes ten of
the eleven tests that the frame (Johnson/Desc/ProofFile/Honest/Frame.lean) has on a book: the ten
that read nothing of a description but its rows. This is the theorem `passes`. It is proved from the
way the book is built, without going through the book's entries one by one. It holds at every K
(`KeyPub`: the public data from which the book is computed) that has two lookups and at which the
Boolean `small K` is true: so it is general in the two lookups' faces and in all counts of coins.

Terms. A book (`ProverCoinCounts`, in the frame) has rows, entries and cuts. A row of the book, in one list for
each of the three chains, is the address of a part of the prover (`Addr`: a place, and the part's
number there) with that part's count of coins (`Due`: so many of the base field, so many of the
extension field). An entry (`Ahead`) is a named block of the coins of one part, the owner, that one
part, the spender, is given; its field `once` marks it as spent (true) or as carried (false). A cut
gives, for a place, the number of rounds of each part there. A place (`Place`,
Johnson/Desc/Block.lean) is a sub-protocol's label: chain, link, piece, kind. The rows of a
description are another thing: for each sub-protocol of a chain, its place and its number of rounds.
A face (`K3.Face`, Johnson/Desc/First/Look/K3LookupGeneral.lean) is the structure of a lookup's public
parameters. The tests are taken in the form `clausesAt r₁ r₂ r₃ masks B` (E2E/KeyBookTests.lean), a
function of three lists of a description's rows; `clauses_rows` there shows that the frame's
`ProverCoinCounts.clauses` at a description is `clausesAt` at its rows and at the frame's own third test. Below
the tests are numbered by their position in `clausesAt`, from 1.

How. At the full size 1,950 of the book's 1,975 entries are the two lookups' (a `#guard` in
E2E/KeyBookAtWritten.lean: 983 + 967 + 5 spent, 20 carried); at every K all but 25 are. All of the
lookups' entries are spent, and each has one of two owners: the part that sends the message with the
multiplicities (`⟨msgPlace, 0⟩`) or the part that sends the index-mask message (`⟨idxPlace, 0⟩`). Of
one lookup's entries E2E/KeyBookTile.lean shows, at every face: each lies in one range of its
owner's coins of the extension field, no two share a coin, and their names differ pairwise. Section
5 below shows the same of two lookups' entries together. So the tests on the whole book follow from
`small K`, which evaluates only this: tests 1, 2 and 10, on the book's ten rows and on its cuts;
tests 4, 5, 6 and 9 on each of the 25 other entries; tests 7 and 8 on each pair of these; that the
two ranges end within the two owners' counts; and each of the 25 compared with the lookups' entries
as a whole: a spent one with four numbers (for each of the two owners, the first coin of the range
and the next unused coin after it), a carried one with the two lookups' places. Test 11 takes
nothing from `small K`: the names of the 25 come from a list of keys that does not depend on K.

  `passes`: if `K.faces = [f₀, f₁]` and `small K = true`, then
    `wordAt K.rowsFirst K.rowsShared K.rowsSecond true (keyBook K) = none`: at the rows that
    E2E/KeyBookTests.lean computes from K, and with the third test's answer set to true, no test
    fails at the book
  `small K`: a definition: the Boolean described above; its docstring lists the eleven conjuncts
  `clausesAt_eq`: the eleven Booleans of `clausesAt r₁ r₂ r₃ masks B`, in order, are the ten tests
    below and, in the third position, `masks`. By unfolding
  `tRows`, `tTwice`, `tOnce`, `tFront`, `tCuts`, `tNames`: definitions: tests 1, 2, 7, 8, 10 and 11
  `fWithin`, `fBehind`, `fShared`, `fOutside`: definitions: tests 4, 5, 6 and 9 on one entry; the
    test itself requires this of every entry of the book
  `inFront all y x`, `fine all x y`: definitions: the spender of y comes before the spender of x in
    the order of places `all`, or is the same part and y is carried; and: test 8 finds no fault with
    the pair, x being the entry that is spent
  `wordAt_none`: if every Boolean of `clausesAt` is true, then `wordAt`, the name of the first test
    that fails, is `none`
  `pair_of_pairwise`, `tOnce_of`, `tFront_of`, `tNames_of`: from a statement by `List.Pairwise` to
    the tests' own form, which goes over pairs of positions in a list. Test 7 passes if the spent
    entries are pairwise `Apart` (E2E/KeyBookTile.lean: neither shares a coin with the other), test
    8 if the entries are pairwise `fine` in both directions, test 11 if the names differ pairwise
  `pairwiseB`, `pairwiseB_iff`: a definition: a Boolean relation, tested on every pair of a list in
    the list's order; it is true exactly where `List.Pairwise` holds
  `KeyPub.looks`, `KeyPub.top`, `KeyPub.others`: definitions: the lookups' entries; the two owners'
    next unused coins after them; the 25 other entries, five spent and twenty carried
  `ahead_eq`: the book's entries are `K.looks ++ K.others`
  `clear K r`, `behindLooks all r`: definitions: r has no coin of the extension field in either of
    the two ranges; the spender of r is at neither lookup's place, and at no place before one of
    them in the list `all`
  `allPlaces`: a definition: the places of `fullFirst ++ fullShared ++ fullSecond`
    (E2E/KeyPlaces.lean: the three chains' rows at the full size, as literal lists)
  `InLooks K e`: a definition: e is spent, has no coin of the base field, has its spender at the
    place of lookup 0 or 1, and lies in one of the two ranges (`InBlock`, E2E/KeyBookTile.lean)
  `looks_two`: at two faces `K.looks` is the first lookup's entries (`bookEntries`,
    E2E/KeyBookFace.lean), then the second's, which begin where the first's end; `K.top` is the two
    first coins plus what both lookups take (`takenOwn`, `takenKey`, E2E/KeyBook.lean)
  `looks_first`, `looks_second`, `looks_block`: the first lookup's entries lie in the first part of
    the two ranges, the second's in the rest; so every entry of `K.looks` satisfies `InLooks K`
  `owners_two`: the two owners are two different addresses
  `looks_apart`, `looks_keyed`, `looks_names`: at two faces the entries of `K.looks` are pairwise
    `Apart`; each one's name is the name of a key `Key.run` at its spender's four numbers; their
    names differ pairwise. A key (`Key`, E2E/KeyBookNames.lean) is what an entry's name is made of;
    the four numbers (`quadOf`) are chain, link, piece and part
  `meets_inside`: an interval inside a second one does not meet (`meets`, in the frame) a third that
    the second does not meet, whichever of the two is named first
  `apart_of_clear`, `not_inFront`: an entry e that satisfies `InLooks K` is `Apart` from every r
    with `clear K r = true`, and `inFront allPlaces r e` is false for every r with
    `behindLooks allPlaces r = true`
  `fine_of_apart`, `before_of_lt`: entries that are `Apart` are `fine` in both directions; an
    address at an earlier place of a list is before (`Addr.before`) one at a later place
  `look_within`, `look_places`: an entry that satisfies `InLooks K` passes `fWithin` if the two
    ranges end within the two owners' counts, and passes `fBehind`, `fShared` and `fOutside` at the
    places of the full size
  `TestGroup.keys`, `KeyPub.otherKeys`: definitions: the keys of the carried entries of one
    proximity test's group (`TestGroup`, E2E/KeyBook.lean); the keys of the 25 other entries
  `group_keys`, `others_keys`, `others_keyed`: the entries' names, as lists of characters, are these
    keys' names, in the same order; so each of the 25 has the name of a key in the list
  `otherKeys_closed`, `otherKeys_nodup`, `otherKeys_links`: the list of 25 keys does not depend on
    K: it is the one at the small example `toyPub` (E2E/KeyBookTests.lean); no key is in it twice;
    no `Key.run` in it has a spender at a place in a link
  `others_names`: the names of the 25 other entries differ pairwise, at every K
  `keyRowLists_places_eq_fullSize`, `allPlaces_eq`: at two faces the places of K's three lists of rows are those of
    `fullFirst`, `fullShared` and `fullSecond`; these three lists of places, appended, are
    `allPlaces`

By what. On the lookups' entries: `lay_block`, `lay_apart`, `lay_keyed`, `lay_names`,
`apart_of_blocks`, `apart_of_owner`, `names_of_quads`, `InBlock.wider` (E2E/KeyBookTile.lean). On
names: `name_inj` (two keys with the same name are equal), `runName_key`, `carriedName_key`
(E2E/KeyBookNames.lean). `passes` rewrites the tests by `clausesAt_eq`, `keyRowLists_places_eq_fullSize`, `allPlaces_eq`
and `ahead_eq`. Tests 1, 2 and 10 are conjuncts of `small K`. Tests 4, 5, 6 and 9 split along
`K.looks ++ K.others`: `look_within` and `look_places` for the first list, a conjunct of `small K`
for the second. Tests 7, 8 and 11 go through `tOnce_of`, `tFront_of` and `tNames_of` and split in
three: pairs of the lookups' entries (`looks_apart`, `looks_names`), pairs of the others (the last
conjunct of `small K`; `others_names`), and mixed pairs (`apart_of_clear`, `not_inFront`; for the
names `looks_keyed`, `others_keyed` and `otherKeys_links`: the lookups' entries have keys `Key.run`
with a spender at a place in a link, and no key of the others is such a key). By `decide`:
`owners_two`, `otherKeys_nodup`, `otherKeys_links`, and the facts on the places of the full size in
`look_places`.

Hypotheses of `passes`. hf: `K.faces = [f₀, f₁]`: K has exactly two lookups, at any faces. hs:
`small K = true`.

Limits.
- The third test ("a place states more mask words than its parts have coins") reads a description's
  oracle messages, not its rows. `clausesAt` takes its answer as the parameter `masks`, and `passes`
  is stated with `masks` set to true. Nothing on the third test is shown in this file;
  E2E/KeyBookThird.lean and E2E/KeyBookThirdNamed.lean are about it.
- Two lookups only, as the key file has at the full size (`full_two`, E2E/KeyBookPassesNamed.lean).
  `behindLooks`, `InLooks` and `allPlaces` name the places of lookups 0 and 1: another number of
  lookups needs another list of places.
- `small K` is a hypothesis: it is proved of no K here. At `fullPub` (E2E/KeyBookAtWritten.lean: K
  at the library's sizes of the full size) it is evaluated in Lean's kernel (`full_small`,
  E2E/KeyBookPassesNamed.lean).
- The rows are those computed from K. That they are the rows of a description is not shown here (at
  the full size: `full_rows` and `book_named`, E2E/KeyBookPassesNamed.lean).
- The book is `keyBook K` with its carried entries; the limits that E2E/KeyBook.lean states on these
  entries, and on the book's counts, apply.
- That the tests pass says that the book is consistent with itself and with the rows. It does not
  say that any part of a prover fits the book.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookTile
import E2E.KeyBookTests

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (Face)
open ProofFile.Honest (Addr Ahead Due ProverCoinCounts dueAt meets indexMaskRun foldMaskRun splitMaskRun)

/-! ## 1 The ten tests, one definition each -/

/-- Test 1: every row of the book is at a place of its own chain's list (p₁, p₂, p₃). -/
def tRows (p₁ p₂ p₃ : List Place) (B : ProverCoinCounts) : Bool :=
  B.first.all (fun r => p₁.contains r.1.place) && B.shared.all (fun r => p₂.contains r.1.place) &&
    B.second.all fun r => p₃.contains r.1.place

/-- Test 2: no address has two rows in the book. -/
def tTwice (B : ProverCoinCounts) : Bool :=
  (B.first ++ B.shared ++ B.second).all fun r =>
    ((B.first ++ B.shared ++ B.second).filter fun q => q.1 == r.1).length == 1

/-- Test 4 on one entry: in each field its block ends within its owner's count in `rows`. -/
def fWithin (rows : List (Addr × Due)) (a : Ahead) : Bool :=
  decide (a.start.f + a.count.f ≤ (dueAt rows a.owner).f) &&
    decide (a.start.e + a.count.e ≤ (dueAt rows a.owner).e)

/-- Test 5 on one entry: both places are in the list, and the owner comes before the spender. -/
def fBehind (all : List Place) (a : Ahead) : Bool :=
  all.contains a.owner.place && all.contains a.spender.place && a.owner.before all a.spender

/-- Test 6 on one entry: not both the owner at a place of p₁ and the spender at a place of p₂. -/
def fShared (p₁ p₂ : List Place) (a : Ahead) : Bool :=
  !(p₁.contains a.owner.place && p₂.contains a.spender.place)

/-- Test 9 on one entry: not spent with the owner at a place of p₂ and the spender outside p₂. -/
def fOutside (p₂ : List Place) (a : Ahead) : Bool :=
  !(a.once && p₂.contains a.owner.place && !p₂.contains a.spender.place)

/-- Test 7: no two spent entries at different positions in the list share a coin. -/
def tOnce (es : List Ahead) : Bool :=
  (es.filter (·.once)).zipIdx.all fun p => (es.filter (·.once)).zipIdx.all fun q =>
    p.2 == q.2 || !p.1.shares q.1

/-- The spender of y comes before the spender of x in the order of places `all` (`Addr.before`), or
is the same part and y is carried. -/
def inFront (all : List Place) (y x : Ahead) : Bool :=
  y.spender.before all x.spender || (y.spender == x.spender && !y.once)

/-- Test 8: no spent entry p shares a coin with another entry q at which `inFront all q p` holds. -/
def tFront (all : List Place) (es : List Ahead) : Bool :=
  es.zipIdx.all fun p => !p.1.once || es.zipIdx.all fun q =>
    p.2 == q.2 || !p.1.shares q.1 || !inFront all q.1 p.1

/-- Test 10: a cut sums to its place's rounds in `sizes`, has no 0, and is its place's only cut. -/
def tCuts (sizes : List (Place × Nat)) (B : ProverCoinCounts) : Bool :=
  B.cuts.all fun c =>
    sizes.lookup c.1 == some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
      (B.cuts.filter fun d => d.1 == c.1).length == 1

/-- Test 11: no two entries have the same name. -/
def tNames (es : List Ahead) : Bool :=
  es.all fun a => (es.filter fun b => b.name == a.name).length == 1

/-- The eleven Booleans of `clausesAt`, in order: the ten tests above and, third, `masks`. -/
theorem clausesAt_eq (r₁ r₂ r₃ : List (Place × Nat)) (masks : Bool) (B : ProverCoinCounts) :
    (clausesAt r₁ r₂ r₃ masks B).map (·.2) =
      [tRows (r₁.map (·.1)) (r₂.map (·.1)) (r₃.map (·.1)) B, tTwice B, masks,
        B.ahead.all (fWithin (B.first ++ B.shared ++ B.second)),
        B.ahead.all (fBehind (r₁.map (·.1) ++ r₂.map (·.1) ++ r₃.map (·.1))),
        B.ahead.all (fShared (r₁.map (·.1)) (r₂.map (·.1))), tOnce B.ahead,
        tFront (r₁.map (·.1) ++ r₂.map (·.1) ++ r₃.map (·.1)) B.ahead,
        B.ahead.all (fOutside (r₂.map (·.1))), tCuts (r₁ ++ r₂ ++ r₃) B, tNames B.ahead] := rfl

theorem wordAt_none (r₁ r₂ r₃ : List (Place × Nat)) (masks : Bool) (B : ProverCoinCounts)
    (h : ∀ t ∈ (clausesAt r₁ r₂ r₃ masks B).map (·.2), t = true) :
    wordAt r₁ r₂ r₃ masks B = none := by
  unfold wordAt
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro x hx
  have := h x.2 (List.mem_map_of_mem hx)
  simp [this]

/-! ## 2 From pairwise statements on a list to the tests' own forms -/

theorem pair_of_pairwise {α : Type} {R : α → α → Prop} {l : List α}
    (h : l.Pairwise fun x y => R x y ∧ R y x) {p q : α × Nat} (hp : p ∈ l.zipIdx)
    (hq : q ∈ l.zipIdx) (hne : p.2 ≠ q.2) : R p.1 q.1 := by
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := q
  have hx : l[i]? = some x := List.mem_zipIdx_iff_getElem?.1 hp
  have hy : l[j]? = some y := List.mem_zipIdx_iff_getElem?.1 hq
  have hne : i ≠ j := hne
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hy
  rw [List.pairwise_iff_getElem] at h
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (h i j hi hj hlt).1
  · exact (h j i hj hi hlt).2

theorem tOnce_of (es : List Ahead) (h : (es.filter (·.once)).Pairwise Apart) : tOnce es = true := by
  unfold tOnce
  rw [List.all_eq_true]
  intro p hp
  rw [List.all_eq_true]
  intro q hq
  by_cases e : p.2 = q.2
  · simp [e]
  · have this : p.1.shares q.1 = false := pair_of_pairwise (R := fun x y => x.shares y = false)
      (h.imp fun hxy => ⟨hxy.1, hxy.2⟩) hp hq e
    simp [this]

/-- x is not spent, or shares no coin with y, or `inFront all y x` is false. -/
def fine (all : List Place) (x y : Ahead) : Bool := !x.once || !x.shares y || !inFront all y x

theorem tFront_of (all : List Place) (es : List Ahead)
    (h : es.Pairwise fun x y => fine all x y = true ∧ fine all y x = true) :
    tFront all es = true := by
  unfold tFront
  rw [List.all_eq_true]
  intro p hp
  cases ho : p.1.once with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro q hq
    by_cases e : p.2 = q.2
    · simp [e]
    · have this : fine all p.1 q.1 = true :=
        pair_of_pairwise (R := fun x y => fine all x y = true) h hp hq e
      unfold fine at this
      rw [ho, Bool.not_true, Bool.false_or] at this
      rw [Bool.or_assoc, this, Bool.or_true]

theorem tNames_of (es : List Ahead) (h : es.Pairwise fun x y => x.name ≠ y.name) :
    tNames es = true := by
  unfold tNames
  rw [List.all_eq_true]
  intro a ha
  have hn : (es.map (·.name)).Nodup := List.pairwise_map.2 h
  have hc : (es.map (·.name)).count a.name = 1 :=
    List.count_eq_one_of_mem hn (List.mem_map_of_mem ha)
  have : (es.filter fun b => b.name == a.name).length = (es.map (·.name)).count a.name := by
    rw [List.count, List.countP_map, List.countP_eq_length_filter]
    rfl
  rw [this, hc]
  rfl

/-- A Boolean relation holds of every pair x, y of a list in which x comes before y. -/
def pairwiseB {α : Type} (r : α → α → Bool) : List α → Bool
  | [] => true
  | x :: l => l.all (r x) && pairwiseB r l

theorem pairwiseB_iff {α : Type} (r : α → α → Bool) (l : List α) :
    pairwiseB r l = true ↔ l.Pairwise fun x y => r x y = true := by
  induction l with
  | nil => exact ⟨fun _ => List.Pairwise.nil, fun _ => rfl⟩
  | cons x l ih =>
    show (l.all (r x) && pairwiseB r l) = true ↔ _
    rw [Bool.and_eq_true, List.all_eq_true, ih, List.pairwise_cons]

/-! ## 3 The book's entries as two lists -/

/-- The lookups' entries (`lookups`, E2E/KeyBook.lean). -/
def KeyPub.looks (K : KeyPub) : List Ahead :=
  (lookups K.faces 0 (tableAt K.sMsg 0) (tableAt K.sIdx 0)).1

/-- The two owners' next unused coins after those that the lookups take. -/
def KeyPub.top (K : KeyPub) : Nat × Nat :=
  (lookups K.faces 0 (tableAt K.sMsg 0) (tableAt K.sIdx 0)).2

/-- The 25 other entries: five that are spent, then the twenty that are carried. -/
def KeyPub.others (K : KeyPub) : List Ahead :=
  [spend foldMaskRun "fold" ⟨msgPlace, 0⟩ (tableAt K.sMsg 1) (2 * firstK K.rng + 1) ⟨rngPlace, 0⟩,
    spend indexMaskRun "sum" ⟨idxPlace, 0⟩ K.top.2 (1 + 2 * K.kCol) ⟨battPlace, 1⟩,
    spend splitMaskRun "split" ⟨omegaPlace, 0⟩ (tableAt K.sOmega 1) 1 ⟨splitPlace, 0⟩,
    spend foldMaskRun "fold" ⟨foldedPlace, 0⟩ (tableAt K.sFolded 1) (2 * firstK K.folded + 1)
      ⟨foldedTestPlace, 0⟩,
    spend foldMaskRun "fold" ⟨wPlace, 0⟩ (tableAt K.sW 1) (2 * firstK K.own + 1)
      ⟨ownTestPlace, 0⟩] ++ K.carried

theorem ahead_eq (K : KeyPub) : (keyBook K).ahead = K.looks ++ K.others := by
  show (K.looks ++ _) ++ K.carried = _
  rw [List.append_assoc]
  rfl

/-! ## 4 The Boolean `small` -/

/-- The entry has no extension-field coin in either of the two ranges that the lookups take. -/
def clear (K : KeyPub) (r : Ahead) : Bool :=
  !(r.owner == ⟨msgPlace, 0⟩ &&
      meets (tableAt K.sMsg 0) (K.top.1 - tableAt K.sMsg 0) r.start.e r.count.e) &&
    !(r.owner == ⟨idxPlace, 0⟩ &&
      meets (tableAt K.sIdx 0) (K.top.2 - tableAt K.sIdx 0) r.start.e r.count.e)

/-- The entry's spender is at neither lookup's place and at no place before either in `all`. -/
def behindLooks (all : List Place) (r : Ahead) : Bool :=
  [lookPlace 0, lookPlace 1].all fun pl =>
    r.spender.place != pl &&
      !decide (all.findIdx (· == r.spender.place) < all.findIdx (· == pl))

/-- The places of the key file's three chains, in order, from the lists at the full size. -/
def allPlaces : List Place := (fullFirst ++ fullShared ++ fullSecond).map (·.1)

/-- The Boolean that `passes` takes as a hypothesis. A conjunction, in this order: `tRows`, `tTwice`
and `tCuts` at the book; `fWithin`, `fBehind`, `fShared` and `fOutside` at each of the other
entries; the two owners' next unused coins after the lookups' are at most the owners' counts in the
extension field; each other entry is `clear` if it is spent and `behindLooks` if it is carried; and
of each pair of other entries: if both are spent neither shares a coin with the other, and the two
are `fine` in both directions. The places are those of the lists at the full size; `tCuts` is at K's
own rows. -/
def small (K : KeyPub) : Bool :=
  let B := keyBook K
  let rows := B.first ++ B.shared ++ B.second
  tRows (fullFirst.map (·.1)) (fullShared.map (·.1)) (fullSecond.map (·.1)) B && tTwice B &&
    tCuts (K.rowsFirst ++ K.rowsShared ++ K.rowsSecond) B &&
    K.others.all (fWithin rows) && K.others.all (fBehind allPlaces) &&
    K.others.all (fShared (fullFirst.map (·.1)) (fullShared.map (·.1))) &&
    K.others.all (fOutside (fullShared.map (·.1))) &&
    decide (K.top.1 ≤ (dueAt rows ⟨msgPlace, 0⟩).e) &&
    decide (K.top.2 ≤ (dueAt rows ⟨idxPlace, 0⟩).e) &&
    K.others.all (fun r => if r.once then clear K r else behindLooks allPlaces r) &&
    pairwiseB (fun x y => (!(x.once && y.once) || (!x.shares y && !y.shares x)) &&
      fine allPlaces x y && fine allPlaces y x) K.others

/-! ## 5 The lookups' entries, at two faces -/

/-- The entry satisfies `InBlock` (E2E/KeyBookTile.lean) at the two ranges that the lookups take and
at the place of lookup 0 or 1: it is spent, has no coin of the base field, lies in one of the two
ranges, and its spender is at that place. -/
def InLooks (K : KeyPub) (e : Ahead) : Prop :=
  ∃ i, (i = 0 ∨ i = 1) ∧
    InBlock ⟨msgPlace, 0⟩ ⟨idxPlace, 0⟩ (tableAt K.sMsg 0) K.top.1 (tableAt K.sIdx 0) K.top.2
      (lookPlace i) e

section Two
variable {K : KeyPub} {f₀ f₁ : Face}

theorem looks_two (hf : K.faces = [f₀, f₁]) :
    K.looks = bookEntries (seatOfLookup 0) f₀ (tableAt K.sMsg 0) (tableAt K.sIdx 0) ++
        bookEntries (seatOfLookup 1) f₁ (tableAt K.sMsg 0 + takenOwn (spansOf f₀))
          (tableAt K.sIdx 0 + takenKey (spansOf f₀)) ∧
      K.top = (tableAt K.sMsg 0 + takenOwn (spansOf f₀) + takenOwn (spansOf f₁),
        tableAt K.sIdx 0 + takenKey (spansOf f₀) + takenKey (spansOf f₁)) := by
  unfold KeyPub.looks KeyPub.top
  rw [hf]
  simp [lookups]

theorem owners_two : (⟨msgPlace, 0⟩ : Addr) ≠ ⟨idxPlace, 0⟩ := by decide

theorem looks_first :
    ∀ e ∈ bookEntries (seatOfLookup 0) f₀ (tableAt K.sMsg 0) (tableAt K.sIdx 0),
      InBlock ⟨msgPlace, 0⟩ ⟨idxPlace, 0⟩ (tableAt K.sMsg 0)
        (tableAt K.sMsg 0 + takenOwn (spansOf f₀)) (tableAt K.sIdx 0)
        (tableAt K.sIdx 0 + takenKey (spansOf f₀)) (lookPlace 0) e :=
  fun e he => (lay_block (seatOfLookup 0) (spansOf f₀) 0 _ _ e he).1

theorem looks_second (hf : K.faces = [f₀, f₁]) :
    ∀ e ∈ bookEntries (seatOfLookup 1) f₁ (tableAt K.sMsg 0 + takenOwn (spansOf f₀))
        (tableAt K.sIdx 0 + takenKey (spansOf f₀)),
      InBlock ⟨msgPlace, 0⟩ ⟨idxPlace, 0⟩ (tableAt K.sMsg 0 + takenOwn (spansOf f₀)) K.top.1
        (tableAt K.sIdx 0 + takenKey (spansOf f₀)) K.top.2 (lookPlace 1) e := by
  intro e he
  rw [(looks_two hf).2]
  exact (lay_block (seatOfLookup 1) (spansOf f₁) 0 _ _ e he).1

theorem looks_block (hf : K.faces = [f₀, f₁]) : ∀ e ∈ K.looks, InLooks K e := by
  intro e he
  rw [(looks_two hf).1, List.mem_append] at he
  rcases he with he | he
  · refine ⟨0, Or.inl rfl, (looks_first e he).wider (Nat.le_refl _) ?_ (Nat.le_refl _) ?_⟩ <;>
      (rw [(looks_two hf).2]; simp only; omega)
  · exact ⟨1, Or.inr rfl, (looks_second hf e he).wider (by omega) (Nat.le_refl _) (by omega)
      (Nat.le_refl _)⟩

theorem looks_apart (hf : K.faces = [f₀, f₁]) : K.looks.Pairwise Apart := by
  rw [(looks_two hf).1, List.pairwise_append]
  exact ⟨lay_apart (seatOfLookup 0) owners_two _ _ _ _, lay_apart (seatOfLookup 1) owners_two _ _ _ _,
    fun x hx y hy => apart_of_blocks owners_two (looks_first x hx) (looks_second hf y hy)⟩

theorem looks_keyed (hf : K.faces = [f₀, f₁]) :
    ∀ e ∈ K.looks, ∃ w u, e.name.toList = (Key.run w (quadOf e.spender) u).name := by
  intro e he
  rw [(looks_two hf).1, List.mem_append] at he
  rcases he with he | he
  · exact lay_keyed (seatOfLookup 0) .counts .index rfl rfl _ _ _ _ e he
  · exact lay_keyed (seatOfLookup 1) .counts .index rfl rfl _ _ _ _ e he

theorem looks_names (hf : K.faces = [f₀, f₁]) : K.looks.Pairwise fun x y => x.name ≠ y.name := by
  have hk := looks_keyed hf
  rw [(looks_two hf).1] at hk ⊢
  rw [List.pairwise_append]
  refine ⟨lay_names (seatOfLookup 0) .counts .index rfl rfl _ _ _ _,
    lay_names (seatOfLookup 1) .counts .index rfl rfl _ _ _ _, fun x hx y hy => ?_⟩
  obtain ⟨w, u, hx'⟩ := hk x (List.mem_append_left _ hx)
  obtain ⟨w', u', hy'⟩ := hk y (List.mem_append_right _ hy)
  refine names_of_quads hx' hy' fun hq => ?_
  have h2 : x.spender.place.link = y.spender.place.link := congrArg (fun q : Quad => q.2.1) hq
  rw [(looks_first x hx).2.2.2.1, (looks_second hf y hy).2.2.2.1] at h2
  exact absurd h2 (by decide)

end Two

/-! ## 6 One of the lookups' entries: the tests on one entry, and pairs with another entry -/

theorem meets_inside {a A s n b m : Nat} (h1 : a ≤ s) (h2 : s + n ≤ A)
    (h : meets a (A - a) b m = false) : meets s n b m = false ∧ meets b m s n = false := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨meets_zero_left _ _ _, meets_zero_right _ _ _⟩
  by_cases hm : m = 0
  · subst hm
    exact ⟨meets_zero_right _ _ _, meets_zero_left _ _ _⟩
  have key : ¬ (a < b + m ∧ b < a + (A - a)) := by
    rintro ⟨x, y⟩
    have hA : A - a ≠ 0 := by omega
    have : meets a (A - a) b m = true := by simp [meets, x, y, hm, hA]
    rw [h] at this
    cases this
  have k1 : ¬ (s < b + m ∧ b < s + n) := by
    rintro ⟨x, y⟩
    exact key ⟨by omega, by omega⟩
  constructor
  · by_cases x : s < b + m
    · have y : ¬ (b < s + n) := fun y => k1 ⟨x, y⟩
      simp [meets, y]
    · simp [meets, x]
  · by_cases x : s < b + m
    · have y : ¬ (b < s + n) := fun y => k1 ⟨x, y⟩
      simp [meets, y]
    · simp [meets, x]

theorem apart_of_clear {K : KeyPub} {e r : Ahead} (he : InLooks K e) (hr : clear K r = true) :
    Apart e r := by
  obtain ⟨i, -, -, -, e3, -, e5⟩ := he
  simp only [clear, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hr
  obtain ⟨c1, c2⟩ := hr
  have fin : ∀ (a A : Nat), a ≤ e.start.e → e.start.e + e.count.e ≤ A →
      meets a (A - a) r.start.e r.count.e = false → Apart e r := by
    intro a A h1 h2 hm
    obtain ⟨m1, m2⟩ := meets_inside h1 h2 hm
    exact ⟨by simp [Ahead.shares, e3, meets_zero_left, m1],
      by simp [Ahead.shares, e3, meets_zero_right, m2]⟩
  rcases e5 with ⟨o, h1, h2⟩ | ⟨o, h1, h2⟩
  · rcases c1 with c | c
    · exact apart_of_owner (by rw [o]; exact fun h => by simp [← h] at c)
    · exact fin _ _ h1 h2 c
  · rcases c2 with c | c
    · exact apart_of_owner (by rw [o]; exact fun h => by simp [← h] at c)
    · exact fin _ _ h1 h2 c

theorem fine_of_apart (all : List Place) {x y : Ahead} (h : Apart x y) :
    fine all x y = true ∧ fine all y x = true := by
  simp [fine, h.1, h.2]

theorem before_of_lt (all : List Place) (x y : Addr)
    (h : all.findIdx (· == x.place) < all.findIdx (· == y.place)) : x.before all y = true := by
  simp [Addr.before, h]

theorem look_within {K : KeyPub} {e : Ahead} (he : InLooks K e) (rows : List (Addr × Due))
    (h1 : K.top.1 ≤ (dueAt rows ⟨msgPlace, 0⟩).e) (h2 : K.top.2 ≤ (dueAt rows ⟨idxPlace, 0⟩).e) :
    fWithin rows e = true := by
  obtain ⟨i, -, -, e2, e3, -, e5⟩ := he
  unfold fWithin
  rw [e2, e3, Bool.and_eq_true]
  rw [decide_eq_true_eq, decide_eq_true_eq]
  refine ⟨Nat.zero_le _, ?_⟩
  rcases e5 with ⟨o, -, h⟩ | ⟨o, -, h⟩ <;> rw [o] <;> omega

theorem look_places {K : KeyPub} {e : Ahead} (he : InLooks K e) :
    fBehind allPlaces e = true ∧
      fShared (fullFirst.map (·.1)) (fullShared.map (·.1)) e = true ∧
      fOutside (fullShared.map (·.1)) e = true := by
  obtain ⟨i, hi, -, -, -, e4, e5⟩ := he
  have ho : e.owner.place = msgPlace ∨ e.owner.place = idxPlace := by
    rcases e5 with ⟨o, -, -⟩ | ⟨o, -, -⟩ <;> rw [o]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hb : e.owner.before allPlaces e.spender = true := by
    apply before_of_lt
    rw [e4]
    rcases ho with o | o <;> rcases hi with rfl | rfl <;> rw [o] <;> decide
  have hA : allPlaces.contains e.owner.place = true := by rcases ho with o | o <;> rw [o] <;> decide
  have hB : allPlaces.contains (lookPlace i) = true := by rcases hi with rfl | rfl <;> decide
  have hC : (fullShared.map (·.1)).contains (lookPlace i) = false := by
    rcases hi with rfl | rfl <;> decide
  have hD : (fullShared.map (·.1)).contains e.owner.place = false := by
    rcases ho with o | o <;> rw [o] <;> decide
  unfold fBehind fShared fOutside
  rw [hb, e4, hA, hB, hC, hD, Bool.and_false, Bool.and_false, Bool.false_and]
  exact ⟨rfl, rfl, rfl⟩

theorem not_inFront {K : KeyPub} {e r : Ahead} (he : InLooks K e)
    (hr : behindLooks allPlaces r = true) : inFront allPlaces r e = false := by
  obtain ⟨i, hi, -, -, -, e4, -⟩ := he
  simp only [behindLooks, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    bne_iff_ne, ne_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hr
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hr
  have hp : r.spender.place ≠ e.spender.place ∧
      ¬ (allPlaces.findIdx (· == r.spender.place) < allPlaces.findIdx (· == e.spender.place)) := by
    rw [e4]
    rcases hi with rfl | rfl
    · exact ⟨a1, a2⟩
    · exact ⟨b1, b2⟩
  have hs : r.spender ≠ e.spender := fun h => hp.1 (by rw [h])
  simp [inFront, Addr.before, hp.1, hp.2, hs]

/-! ## 7 The other entries' names -/

/-- The keys of a group's entries, in the order of `TestGroup.entries`. -/
def TestGroup.keys (G : TestGroup) : List Key :=
  G.members.map (fun m => .carried m.2.2 (quadOf m.1) (quadOf ⟨G.place, 0⟩)) ++
    G.members.map (fun m => .carried m.2.2 (quadOf m.1) (quadOf ⟨G.place, 1⟩)) ++
    [.carried G.fresh.2.2 (quadOf G.fresh.1) (quadOf ⟨G.place, 1⟩)]

theorem group_keys (G : TestGroup) :
    G.entries.map (fun e => e.name.toList) = G.keys.map Key.name := by
  have h0 : ∀ p : Nat, ((fun e : Ahead => e.name.toList) ∘
      fun m : Addr × Sending × Nat => carry m.1 m.2.1 m.2.2 ⟨G.place, p⟩) =
      (Key.name ∘ fun m : Addr × Sending × Nat =>
        Key.carried m.2.2 (quadOf m.1) (quadOf ⟨G.place, p⟩)) := by
    intro p
    funext m
    exact carriedName_key _ _ _
  have h1 : (carry G.fresh.1 G.fresh.2.1 G.fresh.2.2 ⟨G.place, 1⟩).name.toList =
      (Key.carried G.fresh.2.2 (quadOf G.fresh.1) (quadOf ⟨G.place, 1⟩)).name :=
    carriedName_key _ _ _
  unfold TestGroup.entries TestGroup.keys
  rw [List.map_append, List.map_append, List.map_append, List.map_append, List.map_map,
    List.map_map, List.map_map, List.map_map, h0 0, h0 1, List.map_cons, List.map_cons,
    List.map_nil, List.map_nil, h1]

/-- The keys of the 25 other entries, in the order of `KeyPub.others`. -/
def KeyPub.otherKeys (K : KeyPub) : List Key :=
  [.run .fold (quadOf ⟨rngPlace, 0⟩) "fold", .run .index (quadOf ⟨battPlace, 1⟩) "sum",
    .run .split (quadOf ⟨splitPlace, 0⟩) "split", .run .fold (quadOf ⟨foldedTestPlace, 0⟩) "fold",
    .run .fold (quadOf ⟨ownTestPlace, 0⟩) "fold"] ++ K.groups.flatMap TestGroup.keys

theorem others_keys (K : KeyPub) :
    K.others.map (fun e => e.name.toList) = K.otherKeys.map Key.name := by
  have hc : K.carried.map (fun e => e.name.toList) =
      (K.groups.flatMap TestGroup.keys).map Key.name := by
    unfold KeyPub.carried
    rw [List.map_flatMap, List.map_flatMap]
    congr 1
    funext G
    exact group_keys G
  unfold KeyPub.others KeyPub.otherKeys
  rw [List.map_append, List.map_append, hc]
  congr 1
  simp only [List.map_cons, List.map_nil]
  exact congrArg₂ List.cons (runName_key .fold _ _) (congrArg₂ List.cons (runName_key .index _ _)
    (congrArg₂ List.cons (runName_key .split _ _) (congrArg₂ List.cons (runName_key .fold _ _)
      (congrArg₂ List.cons (runName_key .fold _ _) rfl))))

/-- The keys do not depend on K: they are those at the small example `toyPub`. -/
theorem otherKeys_closed (K : KeyPub) : K.otherKeys = toyPub.otherKeys := rfl

theorem otherKeys_nodup : toyPub.otherKeys.Nodup := by decide

/-- No key `Key.run` among them has a spender at a place in a link. -/
theorem otherKeys_links : ∀ k ∈ toyPub.otherKeys, ∀ w q u, k = Key.run w q u → q.2.1 = none := by
  have h : (toyPub.otherKeys.all fun k => match k with
      | .run _ q _ => q.2.1.isNone
      | .carried _ _ _ => true) = true := by decide
  intro k hk w q u e
  have := List.all_eq_true.1 h k hk
  rw [e] at this
  exact Option.isNone_iff_eq_none.1 this

theorem others_names (K : KeyPub) : K.others.Pairwise fun x y => x.name ≠ y.name := by
  have h : (K.others.map fun e => e.name.toList).Nodup := by
    rw [others_keys, otherKeys_closed]
    exact otherKeys_nodup.map fun _ _ h => name_inj h
  have h' := List.pairwise_map.1 h
  exact h'.imp fun hxy e => hxy (by rw [e])

theorem others_keyed (K : KeyPub) :
    ∀ r ∈ K.others, ∃ k ∈ toyPub.otherKeys, r.name.toList = k.name := by
  intro r hr
  have : r.name.toList ∈ K.others.map fun e => e.name.toList := List.mem_map_of_mem hr
  rw [others_keys, otherKeys_closed, List.mem_map] at this
  obtain ⟨k, hk, e⟩ := this
  exact ⟨k, hk, e.symm⟩

/-! ## 8 The main theorem -/

theorem keyRowLists_places_eq_fullSize {K : KeyPub} {f₀ f₁ : Face} (hf : K.faces = [f₀, f₁]) :
    K.rowsFirst.map (·.1) = fullFirst.map (·.1) ∧ K.rowsShared.map (·.1) = fullShared.map (·.1) ∧
      K.rowsSecond.map (·.1) = fullSecond.map (·.1) := by
  refine ⟨?_, rfl, rfl⟩
  unfold KeyPub.rowsFirst
  rw [hf]
  rfl

theorem allPlaces_eq :
    fullFirst.map (·.1) ++ fullShared.map (·.1) ++ fullSecond.map (·.1) = allPlaces := by
  simp [allPlaces]

/-- **The key file's book passes the ten tests that read rows**, at the rows computed from K and
with the third test's answer set to true: at any two faces, if `small K` is true. -/
theorem passes (K : KeyPub) (f₀ f₁ : Face) (hf : K.faces = [f₀, f₁]) (hs : small K = true) :
    wordAt K.rowsFirst K.rowsShared K.rowsSecond true (keyBook K) = none := by
  simp only [small, decide_eq_true_eq, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩, s10⟩, s11⟩ := hs
  obtain ⟨q1, q2, q3⟩ := keyRowLists_places_eq_fullSize hf
  have hL := looks_block hf
  have hO := (pairwiseB_iff _ _).1 s11
  rw [List.all_eq_true] at s10
  -- one of the lookups' entries paired with one of the other entries
  have cross : ∀ x ∈ K.looks, ∀ y ∈ K.others,
      (y.once = true → Apart x y) ∧ fine allPlaces x y = true ∧ fine allPlaces y x = true := by
    intro x hx y hy
    have h := s10 y hy
    cases ho : y.once with
    | true =>
      rw [ho, if_pos rfl] at h
      have ha := apart_of_clear (hL x hx) h
      exact ⟨fun _ => ha, fine_of_apart _ ha⟩
    | false =>
      rw [ho] at h
      have hn := not_inFront (hL x hx) (by simpa using h)
      exact ⟨fun c => Bool.noConfusion c, (by simp [fine, hn]), (by simp [fine, ho])⟩
  apply wordAt_none
  intro t ht
  rw [clausesAt_eq, q1, q2, q3, allPlaces_eq, ahead_eq] at ht
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s1
  · exact s2
  · rfl
  · rw [List.all_append, Bool.and_eq_true]
    exact ⟨List.all_eq_true.2 fun e he => look_within (hL e he) _ s8 s9, s4⟩
  · rw [List.all_append, Bool.and_eq_true]
    exact ⟨List.all_eq_true.2 fun e he => (look_places (hL e he)).1, s5⟩
  · rw [List.all_append, Bool.and_eq_true]
    exact ⟨List.all_eq_true.2 fun e he => (look_places (hL e he)).2.1, s6⟩
  · apply tOnce_of
    rw [List.filter_append, List.pairwise_append]
    refine ⟨(looks_apart hf).sublist List.filter_sublist, ?_, ?_⟩
    · refine (hO.sublist List.filter_sublist).imp_of_mem ?_
      intro x y hx hy h
      have ox := (List.mem_filter.1 hx).2
      have oy := (List.mem_filter.1 hy).2
      simp only [ox, oy, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.not_eq_true'] at h
      exact ⟨h.1.1.1, h.1.1.2⟩
    · intro x hx y hy
      exact (cross x (List.mem_filter.1 hx).1 y (List.mem_filter.1 hy).1).1 (List.mem_filter.1 hy).2
  · apply tFront_of
    rw [List.pairwise_append]
    refine ⟨(looks_apart hf).imp fun h => fine_of_apart _ h, hO.imp fun h => ?_, ?_⟩
    · simp only [Bool.and_eq_true] at h
      exact ⟨h.1.2, h.2⟩
    · intro x hx y hy
      exact (cross x hx y hy).2
  · rw [List.all_append, Bool.and_eq_true]
    exact ⟨List.all_eq_true.2 fun e he => (look_places (hL e he)).2.2, s7⟩
  · exact s3
  · apply tNames_of
    rw [List.pairwise_append]
    refine ⟨looks_names hf, others_names K, fun x hx y hy e => ?_⟩
    obtain ⟨w, u, hx'⟩ := looks_keyed hf x hx
    obtain ⟨k, hk, hy'⟩ := others_keyed K y hy
    rw [e, hy'] at hx'
    have hq := otherKeys_links k hk w _ u (name_inj hx')
    obtain ⟨i, -, -, -, -, e4, -⟩ := hL x hx
    have : x.spender.place.link = none := hq
    rw [e4] at this
    cases this

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.clausesAt_eq
#print axioms AtPublicFiles.KeyBook.looks_block
#print axioms AtPublicFiles.KeyBook.looks_apart
#print axioms AtPublicFiles.KeyBook.looks_names
#print axioms AtPublicFiles.KeyBook.others_names
#print axioms AtPublicFiles.KeyBook.passes
#print axioms AtPublicFiles.KeyBook.tRows
#print axioms AtPublicFiles.KeyBook.tTwice
#print axioms AtPublicFiles.KeyBook.fWithin
#print axioms AtPublicFiles.KeyBook.fBehind
#print axioms AtPublicFiles.KeyBook.fShared
#print axioms AtPublicFiles.KeyBook.fOutside
#print axioms AtPublicFiles.KeyBook.tOnce
#print axioms AtPublicFiles.KeyBook.inFront
#print axioms AtPublicFiles.KeyBook.tFront
#print axioms AtPublicFiles.KeyBook.tCuts
#print axioms AtPublicFiles.KeyBook.tNames
#print axioms AtPublicFiles.KeyBook.wordAt_none
#print axioms AtPublicFiles.KeyBook.pair_of_pairwise
#print axioms AtPublicFiles.KeyBook.tOnce_of
#print axioms AtPublicFiles.KeyBook.fine
#print axioms AtPublicFiles.KeyBook.tFront_of
#print axioms AtPublicFiles.KeyBook.tNames_of
#print axioms AtPublicFiles.KeyBook.pairwiseB
#print axioms AtPublicFiles.KeyBook.pairwiseB_iff
#print axioms AtPublicFiles.KeyBook.KeyPub.looks
#print axioms AtPublicFiles.KeyBook.KeyPub.top
#print axioms AtPublicFiles.KeyBook.KeyPub.others
#print axioms AtPublicFiles.KeyBook.ahead_eq
#print axioms AtPublicFiles.KeyBook.clear
#print axioms AtPublicFiles.KeyBook.behindLooks
#print axioms AtPublicFiles.KeyBook.allPlaces
#print axioms AtPublicFiles.KeyBook.small
#print axioms AtPublicFiles.KeyBook.InLooks
#print axioms AtPublicFiles.KeyBook.looks_two
#print axioms AtPublicFiles.KeyBook.owners_two
#print axioms AtPublicFiles.KeyBook.looks_first
#print axioms AtPublicFiles.KeyBook.looks_second
#print axioms AtPublicFiles.KeyBook.looks_keyed
#print axioms AtPublicFiles.KeyBook.meets_inside
#print axioms AtPublicFiles.KeyBook.apart_of_clear
#print axioms AtPublicFiles.KeyBook.fine_of_apart
#print axioms AtPublicFiles.KeyBook.before_of_lt
#print axioms AtPublicFiles.KeyBook.look_within
#print axioms AtPublicFiles.KeyBook.look_places
#print axioms AtPublicFiles.KeyBook.not_inFront
#print axioms AtPublicFiles.KeyBook.TestGroup.keys
#print axioms AtPublicFiles.KeyBook.group_keys
#print axioms AtPublicFiles.KeyBook.KeyPub.otherKeys
#print axioms AtPublicFiles.KeyBook.others_keys
#print axioms AtPublicFiles.KeyBook.otherKeys_closed
#print axioms AtPublicFiles.KeyBook.otherKeys_nodup
#print axioms AtPublicFiles.KeyBook.otherKeys_links
#print axioms AtPublicFiles.KeyBook.others_keyed
#print axioms AtPublicFiles.KeyBook.keyRowLists_places_eq_fullSize
#print axioms AtPublicFiles.KeyBook.allPlaces_eq
