--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/TreesAsked.lean: THE PUBLIC ITEM "ledger.treesAre" BEHIND THE LOOKUP ON
THE CALLS (K3; 25 places) AND BEHIND AN ATTENTION SEGMENT's OWN ROUNDS (K5; 12 places), FROM THE
PROMISE's PUBLIC TEST IN FRONT. A rule; and, by the kernel at the written full list and the composed
list of extra public tests (`moreAll`), that the item is asked in front of these 37 places.

What is said.
  `taItem m`: the item: `.more (some m) "ledger.treesAre"`.
  `askedAt M links ps k`: what the promise's public test at border k runs over: `ePubAt`'s own list
    (Johnson/Desc/First/EPubAt.lean), named. `ePubAt_mem`: the test's yes, at a member.
  `treesAre_behind`: **THE RULE: `KeepsTrees s s'` (TreesRide.lean), the item asked at border k, the
    test's yes at k and s: then the composed public test at the item says yes at s'.**
  `callsIx l`, `k5Ix g`: the numbers of the lookup on the calls of segment l, and of K5 at attention
    segment 2 g + 1, in the flat list. `spots_full`: what stands there, by the list's own kinds,
    segments and pieces.
  `asked_calls`, `asked_k5`: **the item of the segment is asked in front of each.**
  `owed_just`: at the full list the item is asked BEHIND a place of the six quiet kinds at just 50
    places: K3: these 25; K5: these 12; K4: 12; K6: 1. (None at K8, K11, K3's lookup on the digits.)
  Two tests that fail, by the kernel: `unasked_at_maker`: in front of the place that makes segment
    0's item (number 2) it is NOT asked; `unasked_behind_span`: nor at border 6, behind the second
    sending, which drops it.

Limits. Facts on the tables at the written full list alone. That a seated sub-protocol's accepting
step gives `KeepsTrees` is TreesRide.lean's, at the makers' values. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.TreesRide
import Johnson.Desc.First.EPubAt
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound (moreAll linksFull)
open VerifiableInference.Desc.First (S ModelPart Pub More PubData pubAll ePubAt pubSets pubOfItems
  openSets start flatPlacesOf pubStep pubRowM stepOpen rowOf)

/-- The item. -/
abbrev taItem (m : ℕ) : Pub := .more (some m) "ledger.treesAre"

/-- What the promise's public test at border k runs over. -/
def askedAt (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : List Pub :=
  (pubSets M links ps)[k]?.getD [] ++ pubOfItems ((openSets links ps (start links))[k]?.getD [])

theorem ePubAt_mem {P : Type} {pub : Pub → P × S → Bool} {M : More} {links : List ModelPart}
    {ps : List Place} {k : ℕ} {a : P × S} (h : ePubAt pub M links ps k a = true) {q : Pub}
    (hq : q ∈ askedAt M links ps k) : pub q a = true :=
  List.all_eq_true.1 h q hq

/-- **THE RULE.** -/
theorem treesAre_behind {P : Type} (D : PubData) (base : Pub → P × S → Bool) (links : List ModelPart)
    (ps : List Place) (z : P) (k m : ℕ) {s s' : S} (hK : KeepsTrees s s')
    (hq : taItem m ∈ askedAt moreAll links ps k)
    (h : ePubAt (pubAll D base) moreAll links ps k (z, s) = true) :
    pubAll D base (taItem m) (z, s') = true :=
  pubAll_treesAre_keeps D base z m hK (ePubAt_mem h hq)

/-! ### at the written full list -/

/-- The written full list of places. -/
abbrev plW : List Place := flatPlacesOf linksFull true

/-- The number of the lookup on the calls of segment l. -/
def callsIx (l : ℕ) : ℕ := if l = 24 then 340 else 14 * l + 3

/-- The number of K5 at attention segment 2 g + 1. -/
def k5Ix (g : ℕ) : ℕ := 14 * (2 * g + 1) + 4

/-- A test with code: what stands at these numbers. -/
def spotsB : Bool :=
  ((List.range 25).all fun l => (plW[callsIx l]?).any fun p =>
    p.kind == KindName.K3 && p.link == some l && decide (p.piece < 7)) &&
  (List.range 12).all fun g => (plW[k5Ix g]?).any fun p =>
    p.kind == KindName.K5 && p.link == some (2 * g + 1)

set_option maxRecDepth 1000000 in
theorem spots_full : spotsB = true := by decide +kernel

/-- The test: the item is asked in front of each of the 37. -/
def askedB : Bool :=
  ((List.range 25).all fun l => (askedAt moreAll linksFull plW (callsIx l)).contains (taItem l)) &&
  (List.range 12).all fun g =>
    (askedAt moreAll linksFull plW (k5Ix g)).contains (taItem (2 * g + 1))

set_option maxRecDepth 1000000 in
theorem askedB_full : askedB = true := by decide +kernel

/-- **In front of the lookup on the calls.** -/
theorem asked_calls {l : ℕ} (hl : l < 25) :
    taItem l ∈ askedAt moreAll linksFull plW (callsIx l) := by
  have h := (Bool.and_eq_true_iff.1 askedB_full).1
  simpa using List.all_eq_true.1 h l (List.mem_range.2 hl)

/-- **In front of K5.** -/
theorem asked_k5 {g : ℕ} (hg : g < 12) :
    taItem (2 * g + 1) ∈ askedAt moreAll linksFull plW (k5Ix g) := by
  have h := (Bool.and_eq_true_iff.1 askedB_full).2
  simpa using List.all_eq_true.1 h g (List.mem_range.2 hg)

/-- Is it an item of this sort? -/
def isTa : Pub → Bool
  | .more (some _) n => n == "ledger.treesAre"
  | _ => false

/-- What is asked behind the place at number k. -/
def askedBehind (k : ℕ) (p : Place) : List Pub :=
  pubStep ((pubSets moreAll linksFull plW)[k]?.getD []) (pubRowM moreAll linksFull p) ++
    pubOfItems (stepOpen ((openSets linksFull plW (start linksFull))[k]?.getD [])
      (rowOf linksFull p))

/-- The numbers of the places of a kind behind which an item of the sort is asked. -/
def owedAt (K : KindName) : List ℕ :=
  (List.range plW.length).filter fun k => (plW[k]?).any fun p =>
    p.kind == K && (askedBehind k p).any isTa

set_option maxRecDepth 1000000 in
/-- **Where the sort is owed among the six quiet kinds.** -/
theorem owed_just :
    owedAt .K3 = (List.range 25).map callsIx ∧ owedAt .K5 = (List.range 12).map k5Ix ∧
      (owedAt .K4).length = 12 ∧ (owedAt .K6).length = 1 ∧ owedAt .K8 = [] ∧ owedAt .K11 = [] := by
  decide +kernel

/-! ### two tests that fail -/

set_option maxRecDepth 1000000 in
theorem unasked_at_maker : (askedAt moreAll linksFull plW 2).contains (taItem 0) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem unasked_behind_span : (askedAt moreAll linksFull plW 6).contains (taItem 0) = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.treesAre_behind
#print axioms VerifiableInference.Desc.LinkJoin.spots_full
#print axioms VerifiableInference.Desc.LinkJoin.asked_calls
#print axioms VerifiableInference.Desc.LinkJoin.asked_k5
#print axioms VerifiableInference.Desc.LinkJoin.owed_just
#print axioms VerifiableInference.Desc.LinkJoin.unasked_at_maker
#print axioms VerifiableInference.Desc.LinkJoin.unasked_behind_span
