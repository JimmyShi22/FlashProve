-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: (K-ledger) THE LEDGER IS THE BOOK AT THE TWO PLACES. A hidden value of a lookup has a mask entry on two
  sides. The prover's side: the coin that the key file's book of coins (`keyBook`, E2E/KeyBook.lean) lends the row's part
  for it. The verifier's side: the home that the sub-protocol in front of the lookup (`caller`, Johnson/Desc/Key/Link.lean)
  deals it out of two messages' ledgers of mask entries. Here: hidden value by hidden value, both name ONE OWNER AND ONE
  TAKE OF THAT OWNER. Without it every law on the row alone stays true while the rows that the lookup leaves for the
  ranges' test speak of other mask entries than those that the prover spent.

E2E/Lookup/Key/LedgerIsTheKeyBook.lean. Theorems with proofs. Four definitions with code, the last a proposition; ten
theorems. Helper lemmas and two private definitions stand above their use. On public data and on lists of numbers; no coin's
value but in sections 3 and 5, no witness.

  `takenBeforeLookup data number`     how many coins the lookups in front of lookup number `number` take of the two owners
  `keyBookHomes data number`          where each owner's coins FOR THIS LOOKUP begin: the letter `home` of
                                      Honest/K3/Parts/OwnedHomes.lean, at the key's book
  `homeOfCoin …`                      the verifier's mask entry of a book's coin: the owner's message, and the number that
                                      the ledger hands out at that take (`takenNo`, OnBytes/Iop/LedgerPlaces.lean)
 1 The book's side
  `spansTakeTheSlotsOfTheTwoOwners`   a lookup takes `slots − 2 · parts` coins of the first owner and `2 · parts` of the
                                      second: the book's two counts are the verifier's two takings
  `keyBookStartsFitTheOwnedRow`       **`startsFitBy` (Parts/OwnedMasks.lean) accepts the key's book** at `startsOf` of
                                      `keyBookHomes`: the second of the two premises "on a book that another hand makes"
  `keyBookRefusesStartsMovedByOne`    THE CONTROL: with the first owner's start moved by one coin the test refuses
 2 The verifier's side
  `homesFromFollowsTheDeal`           `homesFrom` (Johnson/Desc/First/Look/K3Key.lean) along a list of marks takes the c-th
                                      member of the list that the mark names, c by `deal` from 0, 0
  `callersHomesAreTheBooksCoins`      **the equation**: the homes that `caller` lays behind k₁ and k₂ takes are, hidden value
                                      by hidden value, `homeOfCoin` of the coins of the book's entries for that lookup
  `callersHomesAtTheState`            the same read off `caller`'s decision, at a state that meets `Mid` (E2E/KeyRowsFit.lean)
  `takesInFrontOfALookupAreTheBooks`  at the two lookups the k₁, k₂ of `Mid` (0, 0; then the first link's two takings) are
                                      `takenBeforeLookup`
 3 The row's coins
  `lookupMasksAreTheOwnersCoinsAtTheKeyBook`  `masksOwners` (Parts/OwnedHomes.lean) with both premises on the book paid: at
                                      the written sizes the mask under slot j is the coin of slot j's owner, in that owner's count
 4 What is left, by name
  `SenderLaysItsCoinsInTheOrderOfTaking`   A DEBT OF THE TWO OWNERS' SENDERS, AS A PROPOSITION; CLAIMED OF NOTHING: the mask
                                      entry that the sent message holds at the number of take n is the sender's coin number
                                      (the table's start + n): the frame's own form `SenderLays`
                                      (Honest/Law/Rule/TiesFall.lean) at the key's book; the reader of the message is a letter.
 5 The sentence itself
  `keyBookEntriesAtALookupAreItsBookEntries`   the book's entries at a lookup's place are `bookEntries` from the two tables'
                                      starts behind `takenBeforeLookup`
  `theLedgerIsTheKeyBook`             **with one number n**: under slot j `caller`'s state lays the mask entry of the slot's
                                      owner's message at the number of take n, and `maskOf` reads that owner's coin number
                                      (its table's start + n)

ONE OFFSET. The book's counters begin at `tableAt data.sMsg 0` and `tableAt data.sIdx 0`, the ledgers' takes at 0. The
statements subtract the table's start; none assumes that it is 0.

CAN THE PREMISES HOLD TOGETHER AT THE STORED KEY FILE? Sections 1 and 2 but for `callersHomesAtTheState` have the premises
of E2E/Lookup/Key/LookupSidePaysAtTheKeyBook.lean (see its head) and "every part has a level", which `parts_full`
(E2E/KeyFacesFull.lean, by the kernel) gives at the written sizes: twelve parts of 36, twelve of 35. `Mid`: `mid_of_front`
has it at link 0 behind the two sendings' accepts, `link_keeps` carries it to link 1 under that theorem's own premises
(`Left`, `Off`, `hearV`'s accept), WHICH THIS FILE SHOWS OF NO RUN. `theLedgerIsTheKeyBook` has the premises of
`callersHomesAtTheState`, with `takenBeforeLookup` for k₁ and k₂, and those of section 1; that the lookup's face is the
caller's stays a named premise.

Limits. Which number; not which value: that the message which the sender sends holds the coin at that number is section
4's debt. Nothing on whether a verifier accepts.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.Lookup.Key.LookupSidePaysAtTheKeyBook
import E2E.KeyRowsFit
import Johnson.Desc.K13.Honest.TakenList
import Johnson.Desc.ProofFile.Honest.K3.Parts.OwnedHomes
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Lookup.Key
open ProofFile.Honest
open ProofFile.Honest.K3 (keyOwners stages LookJobs lookRow ptsOf pointsAt)
open ProofFile.Honest.K3.Law (Course MasksAre CoinsAre entriesAt lentE)
open ProofFile.Honest.K3.Parts (startsFitBy startsOf maskOf)
open AtPublicFiles.KeyBook
open AtPublicFiles.KeyLookup (Mid)
open VerifiableInference.Desc.K3 (Face faceOfLkp fromKeys homesFrom homes)
open VerifiableInference.Desc.Key (FirstState Lookup caller)
open OnBytes (Slot takenNo)

/-! ## 0 The definitions -/

/-- How many coins the lookups in front of lookup number `number` take of the first owner and of the second. -/
def takenBeforeLookup (data : KeyPub) (number : Nat) : Nat × Nat :=
  (((data.faces.take number).map fun f => takenOwn (spansOf f)).sum,
    ((data.faces.take number).map fun f => takenKey (spansOf f)).sum)

/-- **Where each owner's coins for this lookup begin**: the owner's address, and its first free coin in front of the
lookup. The index-mask message's name gives the second owner; every other name the first. -/
def keyBookHomes (data : KeyPub) (number : Nat) (owner : String) : Addr × Due :=
  if owner == indexMaskRun then
    (⟨idxPlace, 0⟩, ⟨0, tableAt data.sIdx 0 + (takenBeforeLookup data number).2⟩)
  else (⟨msgPlace, 0⟩, ⟨0, tableAt data.sMsg 0 + (takenBeforeLookup data number).1⟩)

/-- **The verifier's mask entry of a book's coin.** second: the coin is the second owner's. coin: its number among the
owner's coins of the extension field. The two messages' numbers, numbers of mask rows and tables' starts are letters. -/
def homeOfCoin (ownMessage keyMessage ownMaskRows keyMaskRows ownTable keyTable : Nat) (coin : Bool × Nat) : Slot :=
  if coin.1 then ⟨keyMessage, takenNo keyMaskRows (coin.2 - keyTable)⟩
  else ⟨ownMessage, takenNo ownMaskRows (coin.2 - ownTable)⟩

/-! ## 1 The book's side -/

theorem filterOfNotCountsFalse (marks : List Bool) : (marks.filter (!·)).length = marks.count false := by
  induction marks with
  | nil => rfl
  | cons x l ih => cases x <;> simp [ih]

theorem filterOfSelfCountsTrue (marks : List Bool) : (marks.filter (·)).length = marks.count true := by
  induction marks with
  | nil => rfl
  | cons x l ih => cases x <;> simp [ih]

/-- **The book's two counts at a lookup are the verifier's two takings.** Conditional: every part of the keys has a
level. -/
theorem spansTakeTheSlotsOfTheTwoOwners (face : Face) (levels : ∀ v ∈ face.parts, 1 ≤ v) :
    takenOwn (spansOf face) = face.slots - 2 * face.parts.length ∧
      takenKey (spansOf face) = 2 * face.parts.length := by
  have hTrue := AtPublicFiles.KeyLookup.fromKeys_true levels
  have hLength := AtPublicFiles.KeyLookup.fromKeys_length face
  have hBoth := AtPublicFiles.KeyLookup.count_tf (fromKeys face)
  unfold takenOwn takenKey
  rw [homes_spans, filterOfNotCountsFalse, filterOfSelfCountsTrue]
  constructor <;> omega

theorem takenOfADraw (name : String) (n : Nat) (l : List Span) :
    takenOwn (.draw name n :: l) = takenOwn l ∧ takenKey (.draw name n :: l) = takenKey l := by
  constructor <;> simp [takenOwn, takenKey, Span.homes]

theorem takenOfASum (k : VerifiableInference.Desc.Part.MaskedSum.Call) (second : Bool) (l : List Span) :
    takenOwn (.sum k second :: l) =
        ownRun k + (if second then 0 else (k.ends.map (·.n)).getD 0) + takenOwn l ∧
      takenKey (.sum k second :: l) = (if second then (k.ends.map (·.n)).getD 0 else 0) + takenKey l := by
  unfold takenOwn takenKey
  simp only [filterOfNotCountsFalse, filterOfSelfCountsTrue, List.flatMap_cons, Span.homes,
    List.count_append, List.count_replicate]
  cases second <;> simp

/-- The owners and starts that the entries of a span bear, in the entries' order, at the two counters in front of the
span. -/
private def ownersAndStartsOfASpan (S : Seat) (a b : Nat) : Span → List (Addr × Due)
  | .draw _ _ => []
  | .sum k second => (S.own, ⟨0, a⟩) ::
      (if k.ends.isNone then []
       else if second then [(S.key, ⟨0, b⟩)] else [(S.own, ⟨0, a + ownRun k⟩)])

theorem noEntryOfLaterSpansAtAnEarlierPart (S : Seat) (ps : List Span) (p a b q : Nat) (h : q < p) :
    (layFrom S ps p a b).filter (fun e => e.spender == ⟨S.place, q⟩) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he hq
  have h2 := (lay_spender S ps p a b e he).2
  have hEq : e.spender = ⟨S.place, q⟩ := by simpa using hq
  rw [hEq] at h2
  exact absurd h2 (by simpa using h)

/-- **The entries that name part number p + j bear the owners and starts of span number j**, at the counters behind the
spans in front of it. -/
theorem startsOfTheEntriesAtASpan (S : Seat) (ps : List Span) (p a b j : Nat) (s : Span)
    (hs : ps[j]? = some s) :
    ((layFrom S ps p a b).filter fun e => e.spender == ⟨S.place, p + j⟩).map
        (fun e => (e.owner, e.start)) =
      ownersAndStartsOfASpan S (a + takenOwn (ps.take j)) (b + takenKey (ps.take j)) s := by
  induction ps generalizing p a b j with
  | nil => cases hs
  | cons t l ih =>
    cases j with
    | zero =>
      obtain rfl : t = s := by simpa using hs
      cases t with
      | draw n m =>
        have h0 := noEntryOfLaterSpansAtAnEarlierPart S l (p + 1) a b p (Nat.lt_succ_self p)
        simp only [layFrom, Nat.add_zero, h0]
        rfl
      | sum k second =>
        have h0 := noEntryOfLaterSpansAtAnEarlierPart S l (p + 1)
          (a + ownRun k + if second then 0 else (k.ends.map (·.n)).getD 0)
          (b + if second then (k.ends.map (·.n)).getD 0 else 0) p (Nat.lt_succ_self p)
        simp only [layFrom, List.filter_append, List.map_append, h0, List.append_nil, Nat.add_zero]
        have hz1 : takenOwn (List.take 0 (Span.sum k second :: l)) = 0 := rfl
        have hz2 : takenKey (List.take 0 (Span.sum k second :: l)) = 0 := rfl
        rw [hz1, hz2]
        cases he : k.ends with
        | none => simp [ownersAndStartsOfASpan, he]
        | some e => cases second <;> simp [ownersAndStartsOfASpan, he]
    | succ j =>
      have hs' : l[j]? = some s := by simpa using hs
      have e : p + (j + 1) = (p + 1) + j := by omega
      cases t with
      | draw n m =>
        have ih' := ih (p + 1) a b j hs'
        rw [List.take_succ_cons, (takenOfADraw n m _).1, (takenOfADraw n m _).2, e]
        simpa only [layFrom] using ih'
      | sum k second =>
        have ih' := ih (p + 1) (a + ownRun k + if second then 0 else (k.ends.map (·.n)).getD 0)
          (b + if second then (k.ends.map (·.n)).getD 0 else 0) j hs'
        rw [← e] at ih'
        have ea : a + takenOwn (List.take (j + 1) (Span.sum k second :: l)) =
            (a + ownRun k + if second then 0 else (k.ends.map (·.n)).getD 0) +
              takenOwn (l.take j) := by
          rw [List.take_succ_cons, (takenOfASum k second _).1]
          simp only [Nat.add_assoc]
        have eb : b + takenKey (List.take (j + 1) (Span.sum k second :: l)) =
            (b + if second then (k.ends.map (·.n)).getD 0 else 0) + takenKey (l.take j) := by
          rw [List.take_succ_cons, (takenOfASum k second _).2]
          simp only [Nat.add_assoc]
        rw [ea, eb, ← ih']
        simp only [layFrom, List.filter_append, List.map_append]
        cases k.ends with
        | none => simp
        | some e => cases second <;> simp

theorem spendersOfTheLookupsEntries : ∀ (faces : List Face) (i a b : Nat),
    ∀ e ∈ (lookups faces i a b).1, ∃ n, i ≤ n ∧ e.spender.place = lookPlace n
  | [], _, _, _ => fun e he => by cases he
  | f :: fs, i, a, b => fun e he => by
    simp only [lookups, List.mem_append] at he
    rcases he with he | he
    · exact ⟨i, Nat.le_refl i, (lay_spender (seatOfLookup i) (spansOf f) 0 a b e he).1⟩
    · obtain ⟨n, h1, h2⟩ := spendersOfTheLookupsEntries fs (i + 1) _ _ e he
      exact ⟨n, by omega, h2⟩

theorem lookPlaceTellsItsNumber {n m : Nat} (h : lookPlace n = lookPlace m) : n = m := by
  simpa [lookPlace] using h

/-- **Of all the lookups' entries those that a test keeps at a lookup's place are that lookup's own**, at the counters
behind the faces in front of it. keep: a test that keeps entries whose spender stands at that place, and no other. -/
theorem entriesOfTheLookupsAtAPlace : ∀ (faces : List Face) (number i a b : Nat) (f : Face)
    (keep : Ahead → Bool), (∀ e, keep e = true → e.spender.place = lookPlace (i + number)) →
    faces[number]? = some f →
    (lookups faces i a b).1.filter keep =
      (bookEntries (seatOfLookup (i + number)) f
        (a + ((faces.take number).map fun g => takenOwn (spansOf g)).sum)
        (b + ((faces.take number).map fun g => takenKey (spansOf g)).sum)).filter keep
  | [], _, _, _, _, _, _, _, h => by cases h
  | g :: fs, 0, i, a, b, f, keep, hKeep, h => by
    obtain rfl : g = f := by simpa using h
    have hNone : (lookups fs (i + 1) (a + takenOwn (spansOf g)) (b + takenKey (spansOf g))).1.filter
        keep = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he hq
      obtain ⟨n, h1, h2⟩ := spendersOfTheLookupsEntries fs (i + 1) _ _ e he
      rw [hKeep e hq] at h2
      have := lookPlaceTellsItsNumber h2
      omega
    simp only [lookups, List.filter_append, Nat.add_zero, hNone, List.append_nil, List.take_zero,
      List.map_nil, List.sum_nil]
  | g :: fs, number + 1, i, a, b, f, keep, hKeep, h => by
    have h' : fs[number]? = some f := by simpa using h
    have hNone : (bookEntries (seatOfLookup i) g a b).filter keep = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he hq
      have h2 := (lay_spender (seatOfLookup i) (spansOf g) 0 a b e he).1
      rw [hKeep e hq] at h2
      have := lookPlaceTellsItsNumber h2
      omega
    have ih := entriesOfTheLookupsAtAPlace fs number (i + 1) (a + takenOwn (spansOf g))
      (b + takenKey (spansOf g)) f keep
      (fun e he => by rw [hKeep e he, show i + 1 + number = i + (number + 1) by omega]) h'
    rw [show i + 1 + number = i + (number + 1) by omega] at ih
    simp only [lookups, List.filter_append, hNone, List.nil_append, List.take_succ_cons,
      List.map_cons, List.sum_cons]
    rw [ih]
    simp only [Nat.add_assoc]

/-- **What a test keeps of the book's entries at a lookup's place are the lookups' entries alone.** -/
theorem keptEntriesOfTheKeyBookAreTheLookups (data : KeyPub) (carried : Bool) (number : Nat)
    (keep : Ahead → Bool) (hKeep : ∀ e, keep e = true → e.spender.place = lookPlace number) :
    (keyBook data carried).ahead.filter keep =
      (lookups data.faces 0 (tableAt data.sMsg 0) (tableAt data.sIdx 0)).1.filter keep := by
  have hNone : ∀ l : List Ahead, (∀ e ∈ l, e.spender.place ≠ lookPlace number) →
      l.filter keep = [] := by
    intro l hl
    rw [List.filter_eq_nil_iff]
    intro e he hq
    exact hl e he (hKeep e hq)
  have hGroups : ∀ G ∈ data.groups, G.place ≠ lookPlace number := by
    intro G hG
    simp only [KeyPub.groups, List.mem_cons, List.not_mem_nil, or_false] at hG
    rcases hG with rfl | rfl | rfl | rfl <;>
      simp [rngPlace, foldedTestPlace, omegaTestPlace, ownTestPlace, lookPlace]
  have hCarried : (if carried then data.carried else []).filter keep = [] := by
    cases carried with
    | false => simp
    | true =>
      simp only [if_true]
      refine hNone _ fun e he => ?_
      obtain ⟨G, hG, he⟩ := List.mem_flatMap.1 he
      have hPlace : e.spender.place = G.place := by
        simp only [TestGroup.entries, List.mem_append, List.mem_map, List.mem_singleton] at he
        rcases he with (⟨m, -, rfl⟩ | ⟨m, -, rfl⟩) | rfl <;> rfl
      rw [hPlace]
      exact hGroups G hG
  unfold keyBook KeyPub.spent
  simp only [List.filter_append, hCarried, List.append_nil]
  refine (congrArg (_ ++ ·) (hNone _ fun e he => ?_)).trans (List.append_nil _)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    simp [spend, rngPlace, battPlace, splitPlace, foldedTestPlace, ownTestPlace, lookPlace]

/-- **The book's entries at a part of a lookup's place are the lookups' alone.** -/
theorem entriesOfTheKeyBookAtALookupsPlace (data : KeyPub) (carried : Bool) (number j : Nat) :
    entriesAt (keyBook data carried) (lookPlace number) j =
      (lookups data.faces 0 (tableAt data.sMsg 0) (tableAt data.sIdx 0)).1.filter
        (fun e => e.spender == ⟨lookPlace number, j⟩) :=
  keptEntriesOfTheKeyBookAreTheLookups data carried number _ fun e he => by
    have hEq : e.spender = ⟨lookPlace number, j⟩ := by simpa using he
    rw [hEq]

/-- **The owners and starts of the book's entries at a stage of a lookup.** -/
theorem startsOfTheKeyBookAtAStage (data : KeyPub) (carried : Bool) (number : Nat) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) (j : Nat) (s : K3.Stage)
    (hj : (stages lookup.face)[j]? = some s) :
    (entriesAt (keyBook data carried) lookup.place j).map (fun e => (e.owner, e.start)) =
      ownersAndStartsOfASpan (seatOfLookup number)
        (tableAt data.sMsg 0 + (takenBeforeLookup data number).1 +
          takenOwn ((spansOf lookup.face).take j))
        (tableAt data.sIdx 0 + (takenBeforeLookup data number).2 +
          takenKey ((spansOf lookup.face).take j))
        (spanOf lookup.face s) := by
  have hs : (spansOf lookup.face)[j]? = some (spanOf lookup.face s) := by
    rw [← spans_of_stages lookup.face stands.planes, List.getElem?_map, hj]
    rfl
  have hLook := entriesOfTheLookupsAtAPlace data.faces number 0 (tableAt data.sMsg 0)
    (tableAt data.sIdx 0) lookup.face (fun e => e.spender == ⟨lookPlace number, j⟩)
    (fun e he => by
      have hEq : e.spender = ⟨lookPlace number, j⟩ := by simpa using he
      rw [hEq, Nat.zero_add])
    stands.face
  rw [Nat.zero_add] at hLook
  have hSpan := startsOfTheEntriesAtASpan (seatOfLookup number) (spansOf lookup.face) 0
    (tableAt data.sMsg 0 + ((data.faces.take number).map fun g => takenOwn (spansOf g)).sum)
    (tableAt data.sIdx 0 + ((data.faces.take number).map fun g => takenKey (spansOf g)).sum)
    j _ hs
  rw [Nat.zero_add] at hSpan
  rw [stands.place, entriesOfTheKeyBookAtALookupsPlace, hLook]
  exact hSpan

/-- The stretches of a list of stages, hidden value by hidden value. -/
private def stretchesOf (o : K3.Owners) (f : Face) (l : List K3.Stage) : List String :=
  l.flatMap fun s => List.replicate (s.own f) (o s).1 ++ List.replicate (s.tail f) (o s).2

theorem multiplicitiesAreNotTheIndexMasks : (K3.multRun == indexMaskRun) = false := by
  decide

theorem indexMasksAreNotTheMultiplicities : (indexMaskRun == K3.multRun) = false := by
  decide

theorem firstOwnerIsTheMultiplicities (f : Face) (s : K3.Stage) : (keyOwners f s).1 = K3.multRun := by
  cases s <;> rfl

theorem secondOwnerFollowsTheLastKey (f : Face) (s : K3.Stage) :
    (keyOwners f s).2 = if lastKey f s then indexMaskRun else K3.multRun := by
  cases s <;> rfl

/-- **Each owner's count along a list of stages is the book's taking along their spans.** -/
theorem stretchesCountTheTakings (f : Face) : ∀ l : List K3.Stage,
    (stretchesOf (keyOwners f) f l).count K3.multRun = takenOwn (l.map (spanOf f)) ∧
      (stretchesOf (keyOwners f) f l).count indexMaskRun = takenKey (l.map (spanOf f))
  | [] => by simp [stretchesOf, takenOwn, takenKey]
  | s :: l => by
    obtain ⟨ih1, ih2⟩ := stretchesCountTheTakings f l
    have hCons : stretchesOf (keyOwners f) f (s :: l) =
        (List.replicate (s.own f) (keyOwners f s).1 ++ List.replicate (s.tail f) (keyOwners f s).2) ++
          stretchesOf (keyOwners f) f l := by
      simp [stretchesOf]
    rw [hCons, List.count_append, List.count_append, List.count_append, List.count_append, ih1, ih2,
      firstOwnerIsTheMultiplicities, secondOwnerFollowsTheLastKey, List.map_cons]
    cases hk : s.call f with
    | none =>
      have hOwn : s.own f = 0 := by simp [K3.Stage.own, hk]
      have hTail : s.tail f = 0 := by simp [K3.Stage.tail, hk]
      have hSpan : spanOf f s = .draw s.name (s.draws f) := by simp [spanOf, hk]
      rw [hOwn, hTail, hSpan, (takenOfADraw _ _ _).1, (takenOfADraw _ _ _).2]
      simp
    | some k =>
      have hOwn : s.own f = ownRun k := by simp [K3.Stage.own, hk]
      have hTail : s.tail f = (k.ends.map (·.n)).getD 0 := by simp [K3.Stage.tail, hk]
      have hSpan : spanOf f s = .sum k (lastKey f s) := by simp [spanOf, hk]
      rw [hOwn, hTail, hSpan, (takenOfASum _ _ _).1, (takenOfASum _ _ _).2]
      cases lastKey f s <;>
        simp [List.count_replicate, multiplicitiesAreNotTheIndexMasks,
          indexMasksAreNotTheMultiplicities]

/-- The letter unrolled, cut at a stage. -/
theorem unrolledAtAStage (o : K3.Owners) (f : Face) (j : Nat) (s : K3.Stage)
    (hj : (stages f)[j]? = some s) :
    ∃ post, ProofFile.Honest.K3.Parts.unroll o f = stretchesOf o f ((stages f).take j) ++
      (List.replicate (s.own f) (o s).1 ++ (List.replicate (s.tail f) (o s).2 ++ post)) := by
  obtain ⟨hjl, hg⟩ := List.getElem?_eq_some_iff.1 hj
  refine ⟨stretchesOf o f ((stages f).drop (j + 1)), ?_⟩
  have e : stages f = (stages f).take j ++ s :: (stages f).drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j (stages f), List.drop_eq_getElem_cons hjl, hg]
  show stretchesOf o f (stages f) = _
  conv_lhs => rw [e]
  simp [stretchesOf, List.flatMap_append, List.append_assoc]

theorem firstSlotIsTheStretchesInFront (o : K3.Owners) (f : Face) (j : Nat) (s : K3.Stage)
    (hj : (stages f)[j]? = some s) :
    K3.firstSlot f s = (stretchesOf o f ((stages f).take j)).length := by
  obtain ⟨hjl, hg⟩ := List.getElem?_eq_some_iff.1 hj
  have hIndex : K3.indexOf f s = j := by
    rw [← hg]
    exact K3.indexOf_getElem f j hjl
  unfold K3.firstSlot
  rw [hIndex]
  exact (ProofFile.Honest.K3.Parts.unroll_length o f _).symm

/-- In front of a stage the first owner has been counted as the book takes it. -/
theorem firstOwnerCountInFrontOfAStage (f : Face) (planes : 2 ≤ f.planes) (j : Nat) (s : K3.Stage)
    (hj : (stages f)[j]? = some s) :
    ((ProofFile.Honest.K3.Parts.unroll (keyOwners f) f).take (K3.firstSlot f s)).count K3.multRun =
      takenOwn ((spansOf f).take j) := by
  obtain ⟨post, e⟩ := unrolledAtAStage (keyOwners f) f j s hj
  rw [firstSlotIsTheStretchesInFront (keyOwners f) f j s hj, e, List.take_append,
    List.take_of_length_le (Nat.le_refl _), Nat.sub_self, List.take_zero, List.append_nil,
    (stretchesCountTheTakings f _).1, ← spans_of_stages f planes, List.map_take]

/-- Behind a stage's first stretch the owner of its second stretch has been counted as the book takes it. -/
theorem secondOwnerCountInFrontOfItsStretch (f : Face) (planes : 2 ≤ f.planes) (j : Nat) (s : K3.Stage)
    (hj : (stages f)[j]? = some s) :
    ((ProofFile.Honest.K3.Parts.unroll (keyOwners f) f).take (K3.firstSlot f s + s.own f)).count
        (keyOwners f s).2 =
      if lastKey f s then takenKey ((spansOf f).take j)
      else takenOwn ((spansOf f).take j) + s.own f := by
  obtain ⟨post, e⟩ := unrolledAtAStage (keyOwners f) f j s hj
  have hLength : K3.firstSlot f s + s.own f =
      (stretchesOf (keyOwners f) f ((stages f).take j) ++
        List.replicate (s.own f) (keyOwners f s).1).length := by
    rw [List.length_append, List.length_replicate, firstSlotIsTheStretchesInFront (keyOwners f) f j s hj]
  have e' : ProofFile.Honest.K3.Parts.unroll (keyOwners f) f =
      (stretchesOf (keyOwners f) f ((stages f).take j) ++
        List.replicate (s.own f) (keyOwners f s).1) ++
        (List.replicate (s.tail f) (keyOwners f s).2 ++ post) := by
    rw [e, List.append_assoc]
  have hMap : ((stages f).take j).map (spanOf f) = (spansOf f).take j := by
    rw [← spans_of_stages f planes, List.map_take]
  rw [hLength, e', List.take_append, List.take_of_length_le (Nat.le_refl _), Nat.sub_self,
    List.take_zero, List.append_nil, List.count_append, firstOwnerIsTheMultiplicities,
    secondOwnerFollowsTheLastKey]
  obtain ⟨h1, h2⟩ := stretchesCountTheTakings f ((stages f).take j)
  rw [hMap] at h1 h2
  cases lastKey f s with
  | false => simp [h1]
  | true => simp [h2, List.count_replicate, multiplicitiesAreNotTheIndexMasks]

/-- **What the table of starts gives a stage's stretches, at every home of the two owners.** -/
theorem runsOfTheOwnedRowAtAStage (number : Nat) (lookup : K3.At) (planes : 2 ≤ lookup.face.planes)
    (home : String → Addr × Due) (X Y : Nat) (hFirst : home K3.multRun = (⟨msgPlace, 0⟩, ⟨0, X⟩))
    (hSecond : home indexMaskRun = (⟨idxPlace, 0⟩, ⟨0, Y⟩)) (j : Nat) (s : K3.Stage)
    (hj : (stages lookup.face)[j]? = some s) :
    (ProofFile.Honest.K3.Parts.runsAtOwned (keyOwners lookup.face) lookup s j).zipIdx.map
        (fun r => if r.2 == 0 then (startsOf (keyOwners lookup.face) lookup.face home s).1
          else (startsOf (keyOwners lookup.face) lookup.face home s).2) =
      ownersAndStartsOfASpan (seatOfLookup number) (X + takenOwn ((spansOf lookup.face).take j))
        (Y + takenKey ((spansOf lookup.face).take j)) (spanOf lookup.face s) := by
  have hStartFirst : (startsOf (keyOwners lookup.face) lookup.face home s).1 =
      (⟨msgPlace, 0⟩, ⟨0, X + takenOwn ((spansOf lookup.face).take j)⟩) := by
    unfold startsOf
    simp only [firstOwnerIsTheMultiplicities, hFirst,
      firstOwnerCountInFrontOfAStage lookup.face planes j s hj]
    rfl
  have hStartSecond : (startsOf (keyOwners lookup.face) lookup.face home s).2 =
      if lastKey lookup.face s then
        ((⟨idxPlace, 0⟩, ⟨0, Y + takenKey ((spansOf lookup.face).take j)⟩) : Addr × Due)
      else (⟨msgPlace, 0⟩, ⟨0, X + takenOwn ((spansOf lookup.face).take j) + s.own lookup.face⟩) := by
    unfold startsOf
    simp only [secondOwnerCountInFrontOfItsStretch lookup.face planes j s hj]
    rw [secondOwnerFollowsTheLastKey]
    cases lastKey lookup.face s with
    | false => simp [hFirst, Nat.add_assoc]
    | true => simp [hSecond]
  cases hk : s.call lookup.face with
  | none =>
    have hRuns : ProofFile.Honest.K3.Parts.runsAtOwned (keyOwners lookup.face) lookup s j = [] := by
      simp [ProofFile.Honest.K3.Parts.runsAtOwned, hk]
    have hSpan : spanOf lookup.face s = .draw s.name (s.draws lookup.face) := by simp [spanOf, hk]
    rw [hRuns, hSpan]
    rfl
  | some k =>
    have hRuns : ProofFile.Honest.K3.Parts.runsAtOwned (keyOwners lookup.face) lookup s j =
        ProofFile.Honest.K3.Law.runsOf (K3.sumNameBy (keyOwners lookup.face) s lookup.place j)
          (K3.endNameBy (keyOwners lookup.face) s lookup.place j) k := by
      simp [ProofFile.Honest.K3.Parts.runsAtOwned, hk]
    have hSpan : spanOf lookup.face s = .sum k (lastKey lookup.face s) := by simp [spanOf, hk]
    have hOwn : s.own lookup.face = ownRun k := by simp [K3.Stage.own, hk]
    rw [hRuns, hSpan]
    cases he : k.ends with
    | none =>
      simp [ProofFile.Honest.K3.Law.runsOf, endRuns, he, ownersAndStartsOfASpan, hStartFirst, seatOfLookup]
    | some e =>
      cases hl : lastKey lookup.face s <;>
        simp [ProofFile.Honest.K3.Law.runsOf, endRuns, he, ownersAndStartsOfASpan, hStartFirst,
          hStartSecond, seatOfLookup, hl, hOwn]

theorem keyBookHomeOfTheFirstOwner (data : KeyPub) (number : Nat) :
    keyBookHomes data number K3.multRun =
      (⟨msgPlace, 0⟩, ⟨0, tableAt data.sMsg 0 + (takenBeforeLookup data number).1⟩) := by
  unfold keyBookHomes
  rw [multiplicitiesAreNotTheIndexMasks]
  rfl

theorem keyBookHomeOfTheSecondOwner (data : KeyPub) (number : Nat) :
    keyBookHomes data number indexMaskRun =
      (⟨idxPlace, 0⟩, ⟨0, tableAt data.sIdx 0 + (takenBeforeLookup data number).2⟩) := by
  unfold keyBookHomes
  rw [beq_self_eq_true]
  rfl

/-- **THE TEST `startsFitBy` ACCEPTS THE KEY FILE's BOOK**: each entry's owner and start are those of the table that
counts each owner's coins in the order of sending. General in the book's data. -/
theorem keyBookStartsFitTheOwnedRow (data : KeyPub) (carried : Bool) (number : Nat) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) :
    startsFitBy (keyOwners lookup.face) (keyBook data carried) lookup
      (startsOf (keyOwners lookup.face) lookup.face (keyBookHomes data number)) = true := by
  unfold startsFitBy
  rw [List.all_eq_true]
  rintro ⟨s, j⟩ hx
  have hj : (stages lookup.face)[j]? = some s := List.mem_zipIdx_iff_getElem?.1 hx
  dsimp only
  rw [beq_iff_eq, startsOfTheKeyBookAtAStage data carried number lookup stands j s hj,
    runsOfTheOwnedRowAtAStage number lookup stands.planes (keyBookHomes data number) _ _
      (keyBookHomeOfTheFirstOwner data number) (keyBookHomeOfTheSecondOwner data number) j s hj]

theorem firstCounterOfASumSpan (S : Seat) (a b a' b' : Nat)
    (k : VerifiableInference.Desc.Part.MaskedSum.Call) (second : Bool)
    (h : ownersAndStartsOfASpan S a b (.sum k second) = ownersAndStartsOfASpan S a' b' (.sum k second)) :
    a = a' := by
  simp only [ownersAndStartsOfASpan, List.cons.injEq, Prod.mk.injEq, Due.mk.injEq] at h
  exact h.1.2.2

/-- **The control: with the first owner's start moved by one coin the test refuses.** -/
theorem keyBookRefusesStartsMovedByOne (data : KeyPub) (carried : Bool) (number : Nat) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) :
    startsFitBy (keyOwners lookup.face) (keyBook data carried) lookup
      (startsOf (keyOwners lookup.face) lookup.face fun owner =>
        if owner == indexMaskRun then keyBookHomes data number owner
        else ((keyBookHomes data number owner).1, (keyBookHomes data number owner).2.plus ⟨0, 1⟩)) = false := by
  have hTie : K3.Stage.tie 0 ∈ stages lookup.face := by
    have h : K3.Stage.tie 0 ∈ (List.range (lookup.face.planes - 1)).map K3.Stage.tie :=
      List.mem_map.2 ⟨0, List.mem_range.2 (by have := stands.planes; omega), rfl⟩
    unfold stages
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  have hIndex : (stages lookup.face).idxOf (K3.Stage.tie 0) < (stages lookup.face).length :=
    List.idxOf_lt_length_iff.2 hTie
  have hj : (stages lookup.face)[(stages lookup.face).idxOf (K3.Stage.tie 0)]? =
      some (K3.Stage.tie 0) := by
    rw [List.getElem?_eq_getElem hIndex, List.getElem_idxOf hIndex]
  rw [Bool.eq_false_iff]
  intro hFits
  unfold startsFitBy at hFits
  rw [List.all_eq_true] at hFits
  have hMember : (K3.Stage.tie 0, (stages lookup.face).idxOf (K3.Stage.tie 0)) ∈
      (stages lookup.face).zipIdx := List.mem_zipIdx_iff_getElem?.2 hj
  have hx := hFits _ hMember
  dsimp only at hx
  rw [beq_iff_eq, startsOfTheKeyBookAtAStage data carried number lookup stands _ _ hj,
    runsOfTheOwnedRowAtAStage number lookup stands.planes _
      (tableAt data.sMsg 0 + (takenBeforeLookup data number).1 + 1)
      (tableAt data.sIdx 0 + (takenBeforeLookup data number).2) ?_ ?_ _ _ hj] at hx
  · have hSpanOfTheTie : spanOf lookup.face (K3.Stage.tie 0) =
        .sum (VerifiableInference.Desc.K3.noVar 3 3) false := rfl
    rw [hSpanOfTheTie] at hx
    have hCounter := firstCounterOfASumSpan _ _ _ _ _ _ _ hx
    omega
  · simp only [multiplicitiesAreNotTheIndexMasks, keyBookHomeOfTheFirstOwner]
    rfl
  · simp only [beq_self_eq_true, if_true, keyBookHomeOfTheSecondOwner]

/-! ## 2 The verifier's side -/

theorem homesFromFollowsTheDealFrom : ∀ (marks : List Bool) (own key : List Slot) (a b : Nat),
    (marks.filter (!·)).length + a ≤ own.length → (marks.filter (·)).length + b ≤ key.length →
    homesFrom marks (own.drop a) (key.drop b) =
      (deal marks a b).map fun x => if x.1 then key.getD x.2 default else own.getD x.2 default
  | [], _, _, _, _, _, _ => by simp [homesFrom, deal]
  | false :: marks, own, key, a, b, ho, hk => by
    have hFilter : ((false :: marks).filter (!·)).length = (marks.filter (!·)).length + 1 := by simp
    have hFilter' : ((false :: marks).filter (·)).length = (marks.filter (·)).length := by simp
    rw [hFilter] at ho
    rw [hFilter'] at hk
    have ha : a < own.length := by omega
    rw [List.drop_eq_getElem_cons ha]
    have ih := homesFromFollowsTheDealFrom marks own key (a + 1) b (by omega) hk
    simp only [homesFrom, deal, List.map_cons, ih]
    simp [List.getD_eq_getElem?_getD, ha]
  | true :: marks, own, key, a, b, ho, hk => by
    have hFilter : ((true :: marks).filter (!·)).length = (marks.filter (!·)).length := by simp
    have hFilter' : ((true :: marks).filter (·)).length = (marks.filter (·)).length + 1 := by simp
    rw [hFilter] at ho
    rw [hFilter'] at hk
    have hb : b < key.length := by omega
    rw [List.drop_eq_getElem_cons hb]
    have ih := homesFromFollowsTheDealFrom marks own key a (b + 1) ho (by omega)
    simp only [homesFrom, deal, List.map_cons, ih]
    simp [List.getD_eq_getElem?_getD, hb]

/-- **`homesFrom` follows the deal**: along a list of marks it takes, at each mark, the next member of the list that the
mark names. Conditional: both lists are long enough. General: no lookup is named. -/
theorem homesFromFollowsTheDeal (marks : List Bool) (own key : List Slot)
    (ownLong : (marks.filter (!·)).length ≤ own.length) (keyLong : (marks.filter (·)).length ≤ key.length) :
    homesFrom marks own key =
      (deal marks 0 0).map fun x => if x.1 then key.getD x.2 default else own.getD x.2 default := by
  have h := homesFromFollowsTheDealFrom marks own key 0 0 (by omega) (by omega)
  simpa using h

theorem dealMovedBy (marks : List Bool) (a b x y : Nat) :
    deal marks (a + x) (b + y) =
      (deal marks x y).map fun c => (c.1, if c.1 then b + c.2 else a + c.2) := by
  induction marks generalizing x y with
  | nil => rfl
  | cons m l ih =>
    cases m with
    | false =>
      show (false, a + x) :: deal l (a + x + 1) (b + y) = _
      rw [Nat.add_assoc a x 1, ih]
      simp [deal]
    | true =>
      show (true, b + y) :: deal l (a + x) (b + y + 1) = _
      rw [Nat.add_assoc b y 1, ih]
      simp [deal]

theorem dealStaysBelowTheCounts : ∀ (marks : List Bool) (a b : Nat) (x : Bool × Nat),
    x ∈ deal marks a b →
      (x.1 = false → a ≤ x.2 ∧ x.2 < a + marks.count false) ∧
        (x.1 = true → b ≤ x.2 ∧ x.2 < b + marks.count true)
  | [], _, _, x, h => by cases h
  | false :: marks, a, b, x, h => by
    have hCount : (false :: marks).count false = marks.count false + 1 := by simp
    have hCount' : (false :: marks).count true = marks.count true := by simp
    rw [hCount, hCount']
    simp only [deal, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2⟩ := dealStaysBelowTheCounts marks (a + 1) b x h
      exact ⟨fun e => by have := h1 e; omega, h2⟩
  | true :: marks, a, b, x, h => by
    have hCount : (true :: marks).count false = marks.count false := by simp
    have hCount' : (true :: marks).count true = marks.count true + 1 := by simp
    rw [hCount, hCount']
    simp only [deal, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2⟩ := dealStaysBelowTheCounts marks a (b + 1) x h
      exact ⟨h1, fun e => by have := h2 e; omega⟩

/-- **THE HOMES THAT THE VERIFIER DEALS ARE THE BOOK's COINS, HIDDEN VALUE BY HIDDEN VALUE.** The two lists are what the
ground's taking hands out behind k₁ and k₂ takes (`takeMasksP_numbers`, Johnson/Desc/K13/Honest/TakenList.lean); the book's
entries begin k₁ and k₂ coins behind the two tables' starts. General in the face, the lookup's number and all numbers. -/
theorem callersHomesAreTheBooksCoins (face : Face) (levels : ∀ v ∈ face.parts, 1 ≤ v)
    (number ownMessage keyMessage ownMaskRows keyMaskRows ownTable keyTable k₁ k₂ : Nat) :
    (homes face
        (((List.range (face.slots - 2 * face.parts.length)).map fun j => takenNo ownMaskRows (k₁ + j)).map
          fun j => ⟨ownMessage, j⟩)
        (((List.range (2 * face.parts.length)).map fun j => takenNo keyMaskRows (k₂ + j)).map
          fun j => ⟨keyMessage, j⟩)).toList =
      (unroll (seatOfLookup number) (bookEntries (seatOfLookup number) face (ownTable + k₁) (keyTable + k₂))).map
        (homeOfCoin ownMessage keyMessage ownMaskRows keyMaskRows ownTable keyTable) := by
  have hTrue := AtPublicFiles.KeyLookup.fromKeys_true levels
  have hLength := AtPublicFiles.KeyLookup.fromKeys_length face
  have hBoth := AtPublicFiles.KeyLookup.count_tf (fromKeys face)
  have hMoved := dealMovedBy (fromKeys face) (ownTable + k₁) (keyTable + k₂) 0 0
  simp only [Nat.add_zero] at hMoved
  rw [unroll_look, hMoved]
  simp only [homes, List.toList_toArray]
  rw [homesFromFollowsTheDeal _ _ _
    (by rw [filterOfNotCountsFalse]; simp; omega) (by rw [filterOfSelfCountsTrue]; simp; omega),
    List.map_map (l := deal (fromKeys face) 0 0)]
  apply List.map_congr_left
  rintro ⟨flag, c⟩ hx
  obtain ⟨h1, h2⟩ := dealStaysBelowTheCounts _ _ _ _ hx
  cases flag with
  | false =>
    have hc : c < face.slots - 2 * face.parts.length := by
      have := (h1 rfl).2
      simp only [] at this
      omega
    simp [homeOfCoin, List.getD_eq_getElem?_getD, hc, Nat.add_assoc]
  | true =>
    have hc : c < 2 * face.parts.length := by
      have := (h2 rfl).2
      simp only [] at this
      omega
    simp [homeOfCoin, List.getD_eq_getElem?_getD, hc, Nat.add_assoc]

/-- **The same, read off `caller`'s decision** at a state that meets `Mid`: whatever state `caller` returns there bears
these homes. -/
theorem callersHomesAtTheState (one : OnBytes.Params.OneTime) (codes : OnBytes.Codes) (number : Nat) (x : Lookup)
    {s s' : FirstState} {a b k₁ k₂ B V : Nat} {ownShape keyShape : OnBytes.OracleShape}
    (mid : Mid one codes s number a b k₁ k₂ B V ownShape keyShape)
    (levels : ∀ v ∈ (faceOfLkp x).parts, 1 ≤ v)
    (rounds : List Fmt.RoundView) (columns : List (List (Nat × List UInt64)))
    (accepts : (caller one number x).decide s rounds columns = .ok s') (ownTable keyTable : Nat) :
    s'.base.home.toList =
      (unroll (seatOfLookup number)
        (bookEntries (seatOfLookup number) (faceOfLkp x) (ownTable + k₁) (keyTable + k₂))).map
        (homeOfCoin one.ranges.messageId s.idx ownShape.maskRows keyShape.maskRows ownTable keyTable) := by
  cases e1 : VerifiableInference.Desc.Ground.takeMasksP s.d one.ranges.messageId
      ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length) with
  | none =>
    simp only [caller, VerifiableInference.Desc.Key.quietAt, mid.fork, mid.keys, e1,
      VerifiableInference.Desc.named, VerifiableInference.Desc.need, Option.isNone_none,
      beq_self_eq_true, bind, Except.bind, pure, Except.pure, if_true] at accepts
    cases accepts
  | some p =>
    obtain ⟨o, d₁⟩ := p
    cases e2 : VerifiableInference.Desc.Ground.takeMasksP d₁ s.idx (2 * (faceOfLkp x).parts.length) with
    | none =>
      simp only [caller, VerifiableInference.Desc.Key.quietAt, mid.fork, mid.keys, e1, e2,
        VerifiableInference.Desc.named, VerifiableInference.Desc.need, Option.isNone_none,
        beq_self_eq_true, bind, Except.bind, pure, Except.pure, if_true] at accepts
      cases accepts
    | some q =>
      obtain ⟨k, d₂⟩ := q
      obtain ⟨y, l, hy, hyShape, -⟩ := mid.own
      have hNumbersOwn := VerifiableInference.Desc.K13.Honest.takeMasksP_numbers mid.ownAt hy e1
      obtain ⟨-, -, hSame, -, -⟩ := AtPublicFiles.KeyLookup.takeMasks_laws e1
      have hSameKey := hSame s.idx mid.ne
      have hAtKey := AtPublicFiles.KeyLookup.ledgerAt_same mid.idxAt hSameKey
      obtain ⟨z, l', hz, hzShape, -⟩ := mid.idx.same hSameKey
      have hNumbersKey := VerifiableInference.Desc.K13.Honest.takeMasksP_numbers hAtKey hz e2
      simp only [] at hNumbersOwn hNumbersKey
      rw [hyShape] at hNumbersOwn
      rw [hzShape] at hNumbersKey
      have hSize : (homes (faceOfLkp x) (o.map fun j => (⟨one.ranges.messageId, j⟩ : Slot))
          (k.map fun j => (⟨s.idx, j⟩ : Slot))).size = (faceOfLkp x).slots :=
        AtPublicFiles.KeyLookup.homes_size levels (by rw [List.length_map, hNumbersOwn]; simp)
          (by rw [List.length_map, hNumbersKey]; simp)
      simp only [caller, VerifiableInference.Desc.Key.quietAt, mid.fork, mid.keys, e1, e2, hSize,
        VerifiableInference.Desc.named, VerifiableInference.Desc.need, Option.isNone_none,
        beq_self_eq_true, bind, Except.bind, pure, Except.pure, if_true, Except.ok.injEq] at accepts
      subst accepts
      show (homes (faceOfLkp x) (o.map fun j => (⟨one.ranges.messageId, j⟩ : Slot))
          (k.map fun j => (⟨s.idx, j⟩ : Slot))).toList = _
      rw [hNumbersOwn, hNumbersKey]
      exact callersHomesAreTheBooksCoins _ levels number _ _ _ _ _ _ _ _

/-- **The takes in front of a lookup are the book's**: 0 and 0 at the first; the first lookup's two takings at the
second: the numbers that `mid_of_front` and `link_keeps` (E2E/KeyRowsFit.lean) give `Mid`. -/
theorem takesInFrontOfALookupAreTheBooks (data : KeyPub) (first second : Face) (faces : data.faces = [first, second])
    (levels : ∀ v ∈ first.parts, 1 ≤ v) :
    takenBeforeLookup data 0 = (0, 0) ∧
      takenBeforeLookup data 1 = (first.slots - 2 * first.parts.length, 2 * first.parts.length) := by
  have hSpans := spansTakeTheSlotsOfTheTwoOwners first levels
  constructor
  · simp [takenBeforeLookup]
  · simp [takenBeforeLookup, faces, hSpans.1, hSpans.2]

/-! ## 3 The row's coins -/

/-- **AT THE KEY FILE's BOOK THE MASK UNDER EACH OF THE LOOKUP's SLOTS IS ITS OWNER's COIN, EACH OWNER IN ITS OWN COUNT.**
`masksOwners` with both premises on the book paid. Conditional: the written sizes; the course's lookup stands at the book;
what the row's parts spend is what the book's entries name; the course's coins are the row's. `spent` and `coinsAre` are
typed at `lookRow`, the row of one owner, as in `masksOwners`. Their payers at the owned seat, none called here:
`bookLendsTheOwnedSeatInTheFirstChain` (Honest/K3/Key/OwnedSeatMeetsThePlaceTests.lean), then `spent_owned` over `plainOf`
(Honest/K3/Parts/OwnedPlays.lean), then `rowSpent_unlift`. -/
theorem lookupMasksAreTheOwnersCoinsAtTheKeyBook {W : Type} (course : Course W) (data : KeyPub)
    (written : fullPub = some data) (number : Nat) (stands : LookupStandsAtTheKeyBook data number course.a)
    (coins : Coins (keyBook data))
    (rowCoins : RowCoins (lookRow (V := Unit) ⟨ptsOf, pointsAt⟩ course.J course.a))
    (spent : ProofFile.Honest.K3.Law.rowSpent _ rowCoins = (List.range (stages course.f).length).map fun i =>
      (entriesAt (keyBook data) course.a.place i).map (lentE (coins.look 0)))
    (coinsAre : CoinsAre course rowCoins) :
    MasksAre course
      (maskOf (keyOwners course.f) course.f (keyBookHomes data number) (coins.look 0) course.first) := by
  have hDue : (fun x => (coins.look 0 x).1) = dueAt (keyBook data).first :=
    funext (ProofFile.Honest.K3.Law.look_due_first (keyBook data) coins)
  have hFits := keyBookFitsTheOwnedRow data written number course.a stands
  rw [← hDue] at hFits
  exact ProofFile.Honest.K3.Parts.masksOwners course (keyOwners course.f) (keyBook data)
    ((keyBook data).rowsOf 0) (coins.look 0) (keyBookHomes data number) rowCoins hFits
    (keyBookStartsFitTheOwnedRow data true number course.a stands) spent coinsAre

/-! ## 4 What is left, by name -/

/-- **A debt of an owner's sender, as a proposition; claimed of nothing**: the frame's own form `SenderLays`
(Honest/Law/Rule/TiesFall.lean) at the key file's book and first chain, read at the numbers that the ledger hands out.
owner: the sender's address. entry: the mask entry that the sent message holds at a number of the ledger's, of a run's
coins, the input and the challenges heard. At the number of take n stands the owner's coin number `table + n`, for every
take below `takes`. -/
def SenderLaysItsCoinsInTheOrderOfTaking {W : Type} (data : KeyPub) (owner : Addr) (maskRows table takes : Nat)
    (entry : Coins (keyBook data) → W → List Fmt.Drawn → Nat → OnBytes.E) : Prop :=
  SenderLays (keyBook data) 0 owner table (fun k w h n => entry k w h (takenNo maskRows n)) (· < takes)

/-! ## 5 The sentence itself -/

/-- **THE BOOK's ENTRIES AT A LOOKUP's PLACE ARE THAT LOOKUP's ENTRIES**, from the two tables' starts behind the takes in
front of the lookup. -/
theorem keyBookEntriesAtALookupAreItsBookEntries (data : KeyPub) (carried : Bool) (number : Nat) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) :
    (keyBook data carried).ahead.filter (fun e => e.spender.place == lookPlace number) =
      bookEntries (seatOfLookup number) lookup.face (tableAt data.sMsg 0 + (takenBeforeLookup data number).1)
        (tableAt data.sIdx 0 + (takenBeforeLookup data number).2) := by
  have hKeep : ∀ e : Ahead, (e.spender.place == lookPlace number) = true →
      e.spender.place = lookPlace number := fun e he => by simpa using he
  have hLook := entriesOfTheLookupsAtAPlace data.faces number 0 (tableAt data.sMsg 0)
    (tableAt data.sIdx 0) lookup.face (fun e => e.spender.place == lookPlace number)
    (fun e he => by rw [Nat.zero_add]; exact hKeep e he) stands.face
  rw [Nat.zero_add] at hLook
  rw [keptEntriesOfTheKeyBookAreTheLookups data carried number _ hKeep, hLook]
  refine List.filter_eq_self.2 fun e he => ?_
  have hPlace := (lay_spender (seatOfLookup number) (spansOf lookup.face) _ _ _ e he).1
  simpa using hPlace

theorem dealAtAPosition : ∀ (marks : List Bool) (a b j : Nat), j < marks.length →
    (deal marks a b)[j]? = some (marks.getD j false,
      if marks.getD j false then b + (marks.take j).count true else a + (marks.take j).count false)
  | [], _, _, _, h => by simp at h
  | false :: l, a, b, 0, _ => by simp [deal]
  | true :: l, a, b, 0, _ => by simp [deal]
  | false :: l, a, b, j + 1, h => by
    have ih := dealAtAPosition l (a + 1) b j (by simpa using h)
    have hFalse : (false :: l.take j).count false = (l.take j).count false + 1 := by simp
    have hTrue : (false :: l.take j).count true = (l.take j).count true := by simp
    rw [show deal (false :: l) a b = (false, a) :: deal l (a + 1) b from rfl, List.getElem?_cons_succ,
      ih]
    simp only [List.getD_cons_succ, List.take_succ_cons, hFalse, hTrue]
    cases l.getD j false <;> simp <;> omega
  | true :: l, a, b, j + 1, h => by
    have ih := dealAtAPosition l a (b + 1) j (by simpa using h)
    have hFalse : (true :: l.take j).count false = (l.take j).count false := by simp
    have hTrue : (true :: l.take j).count true = (l.take j).count true + 1 := by simp
    rw [show deal (true :: l) a b = (true, b) :: deal l a (b + 1) from rfl, List.getElem?_cons_succ,
      ih]
    simp only [List.getD_cons_succ, List.take_succ_cons, hFalse, hTrue]
    cases l.getD j false <;> simp <;> omega

theorem marksCountTheIndexMasks : ∀ l : List String,
    (l.map (· == indexMaskRun)).count true = l.count indexMaskRun
  | [] => rfl
  | w :: l => by
    have ih := marksCountTheIndexMasks l
    rw [List.map_cons, List.count_cons, List.count_cons, ih]
    cases (w == indexMaskRun) <;> rfl

theorem marksCountTheMultiplicities : ∀ l : List String,
    (∀ w ∈ l, w = K3.multRun ∨ w = indexMaskRun) →
    (l.map (· == indexMaskRun)).count false = l.count K3.multRun
  | [], _ => rfl
  | w :: l, h => by
    have ih := marksCountTheMultiplicities l fun v hv => h v (List.mem_cons_of_mem _ hv)
    rcases h w List.mem_cons_self with rfl | rfl
    · rw [List.map_cons, multiplicitiesAreNotTheIndexMasks, List.count_cons_self,
        List.count_cons_self, ih]
    · rw [List.map_cons, beq_self_eq_true, List.count_cons_of_ne (by decide : true ≠ false),
        List.count_cons_of_ne (by decide : indexMaskRun ≠ K3.multRun), ih]

theorem membersOfTheKeyLetter (f : Face) :
    ∀ w ∈ ProofFile.Honest.K3.Parts.unroll (keyOwners f) f, w = K3.multRun ∨ w = indexMaskRun := by
  intro w hw
  unfold ProofFile.Honest.K3.Parts.unroll at hw
  obtain ⟨s, -, hw⟩ := List.mem_flatMap.1 hw
  rcases List.mem_append.1 hw with h | h
  · left
    rw [(List.mem_replicate.1 h).2, firstOwnerIsTheMultiplicities]
  · rw [(List.mem_replicate.1 h).2, secondOwnerFollowsTheLastKey]
    cases lastKey f s with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl

/-- **THE LEDGER IS THE KEY FILE's BOOK, HIDDEN VALUE BY HIDDEN VALUE, WITH ONE NUMBER.** At a state that meets `Mid` behind
the takes of the lookups in front (`takenBeforeLookup`), whatever state `caller` returns lays under slot j the mask entry of
the slot's owner's message at the number of take n, and `maskOf` reads at slot j that owner's coin number (its table's start
+ n). Section 4's debt is what then makes the mask entry hold that coin. Conditional: the lookup stands at the book; its face
is the caller's (named, `face`); `Mid`; every part of the keys has a level; `caller` accepts. -/
theorem theLedgerIsTheKeyBook (one : OnBytes.Params.OneTime) (codes : OnBytes.Codes) (number : Nat) (x : Lookup)
    {s s' : FirstState} {a b B V : Nat} {ownShape keyShape : OnBytes.OracleShape} (data : KeyPub) (lookup : K3.At)
    (stands : LookupStandsAtTheKeyBook data number lookup) (face : lookup.face = faceOfLkp x)
    (mid : Mid one codes s number a b (takenBeforeLookup data number).1 (takenBeforeLookup data number).2 B V
      ownShape keyShape)
    (levels : ∀ v ∈ lookup.face.parts, 1 ≤ v) (rounds : List Fmt.RoundView)
    (columns : List (List (Nat × List UInt64)))
    (accepts : (caller one number x).decide s rounds columns = .ok s')
    (look : Addr → (d : Due) × Cs d) (first : Nat) :
    ∀ j, j < lookup.face.slots → ∃ n,
      s'.base.home[j]? = some
        (if (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" == indexMaskRun then
          ⟨s.idx, takenNo keyShape.maskRows n⟩
         else ⟨one.ranges.messageId, takenNo ownShape.maskRows n⟩) ∧
      maskOf (keyOwners lookup.face) lookup.face (keyBookHomes data number) look first (first + j) =
        ProofFile.Honest.K3.Law.rd ((coinsE (look (keyBookHomes data number
                  ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "")).1).2).getD
                ((if (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" == indexMaskRun then
                    tableAt data.sIdx 0
                  else tableAt data.sMsg 0) + n) OnBytes.zeroE) := by
  intro j hj
  have hMarks := ProofFile.Honest.K3.Parts.unroll_key lookup.face stands.planes
  have hLength : (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).length =
      lookup.face.slots := by
    rw [← List.length_map (f := (· == indexMaskRun)), hMarks, AtPublicFiles.KeyLookup.fromKeys_length]
  have hPosition : j < (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).length := by
    rw [hLength]
    exact hj
  have hHomes := callersHomesAtTheState one codes number x mid (face ▸ levels) rounds columns accepts 0 0
  rw [unroll_look, ← face, ← hMarks] at hHomes
  have hDeal := dealAtAPosition
    ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).map (· == indexMaskRun))
    (0 + (takenBeforeLookup data number).1) (0 + (takenBeforeLookup data number).2) j
    (by rw [List.length_map]; exact hPosition)
  have hAt : s'.base.home[j]? = (List.map
      (homeOfCoin one.ranges.messageId s.idx ownShape.maskRows keyShape.maskRows 0 0)
      (deal ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).map (· == indexMaskRun))
        (0 + (takenBeforeLookup data number).1) (0 + (takenBeforeLookup data number).2)))[j]? := by
    rw [← hHomes, Array.getElem?_toList]
  rw [List.getElem?_map, hDeal, Option.map_some] at hAt
  have hMark : ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).map
      (· == indexMaskRun)).getD j false =
      ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" == indexMaskRun) := by
    simp [List.getD_eq_getElem?_getD, hPosition]
  rw [hMark, ← List.map_take] at hAt
  have hMember : (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" ∈
      ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face := by
    rw [List.getD_eq_getElem _ _ hPosition]
    exact List.getElem_mem hPosition
  cases hFlag : ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" ==
      indexMaskRun) with
  | true =>
    have hOwner : (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" =
        indexMaskRun := by simpa using hFlag
    rw [hFlag, marksCountTheIndexMasks] at hAt
    refine ⟨(takenBeforeLookup data number).2 +
      ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).take j).count indexMaskRun,
      ?_, ?_⟩
    · rw [hAt]
      simp [homeOfCoin]
    · unfold maskOf
      rw [Nat.add_sub_cancel_left, hOwner, keyBookHomeOfTheSecondOwner, if_pos rfl]
      simp only [Nat.add_assoc]
  | false =>
    have hOwner : (ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).getD j "" =
        K3.multRun := by
      rcases membersOfTheKeyLetter lookup.face _ hMember with h | h
      · exact h
      · rw [h] at hFlag
        simp at hFlag
    rw [hFlag, marksCountTheMultiplicities _
      fun w hw => membersOfTheKeyLetter lookup.face w (List.mem_of_mem_take hw)] at hAt
    refine ⟨(takenBeforeLookup data number).1 +
      ((ProofFile.Honest.K3.Parts.unroll (keyOwners lookup.face) lookup.face).take j).count K3.multRun,
      ?_, ?_⟩
    · rw [hAt]
      simp [homeOfCoin]
    · unfold maskOf
      rw [Nat.add_sub_cancel_left, hOwner, keyBookHomeOfTheFirstOwner,
        if_neg (by simp)]
      simp only [Nat.add_assoc]

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.spansTakeTheSlotsOfTheTwoOwners
#print axioms AtPublicFiles.Lookup.Key.keyBookStartsFitTheOwnedRow
#print axioms AtPublicFiles.Lookup.Key.keyBookRefusesStartsMovedByOne
#print axioms AtPublicFiles.Lookup.Key.homesFromFollowsTheDeal
#print axioms AtPublicFiles.Lookup.Key.callersHomesAreTheBooksCoins
#print axioms AtPublicFiles.Lookup.Key.callersHomesAtTheState
#print axioms AtPublicFiles.Lookup.Key.takesInFrontOfALookupAreTheBooks
#print axioms AtPublicFiles.Lookup.Key.lookupMasksAreTheOwnersCoinsAtTheKeyBook
#print axioms AtPublicFiles.Lookup.Key.keyBookEntriesAtALookupAreItsBookEntries
#print axioms AtPublicFiles.Lookup.Key.theLedgerIsTheKeyBook
