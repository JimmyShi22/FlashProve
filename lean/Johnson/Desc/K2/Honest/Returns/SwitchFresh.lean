-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SwitchFresh.lean: A YES OF THE CODE SWITCH's OWN DECISION LEAVES THE
TREES THAT IT LAYS ITSELF OPENED AT NO LIST: by its text (Johnson/Top/H0/Tw/K2C/Asks.lean,
`OpenAsks.out`) it counts a list more at the trees of the messages that it opens; shown here: it
turns no other tree; where these messages are older than its sending and the book's two tables fit,
these trees are older too. On the kind's text: no plan, no walk. The library's law on the book over
that yes (`yes_book`) says `SameNumbers`, which lets every tree's count of lists turn. A tool for
`AllOpen`'s clause "a tree of one list has not been opened" (Returns/ReadOpen.lean). Statements with
their proofs.

  `openOne_off`, `opens_off` the opening of one tree, and of a list of trees, leaves every other
                    tree as it is, whole. THE LIBRARY's `openOne_same`, `opens_same`: their lines
                    stand here again at this sentence
  `readOld_off` a yes of the reading · no opened message's place in the book names the tree number z
                    ⊢ the tree at z is as it was
  `switchE_fresh` the switch behind its guard: premises: the front book's two tables fit
                    (`BookFits`) · the opened messages' numbers are below its number of places ⊢ a
                    tree of the book behind at a number from the front book's number of trees on has
                    `lists` = 0
  `yes_fresh` THE TOP: the same of `decideWith sendByL8 p s rs gs = .ok s'`, at all three sorts of
                    place: premises: the book's two tables fit (`BookFits`) · at the front that the
                    kind takes off s (`FrontOf p s x`): the messages that x's carried rows name are
                    placed in s's book

By, the library's: `openOne_iff` (Johnson/Top/H0/Tw/K2C/Asks.lean) · `readOld_inv`,
`switchBehind_inv`, `switchE_inv`, `link_inv`, `head_inv`, `finish_inv`
(Johnson/Top/H0/Tw/K2C/Closed.lean) · `sendByL8_iff`, `sendOpen_iff`
(Johnson/Top/H0/Tw/K2C/SendsOpen.lean) · `sendP_book` (Johnson/Top/H0/Tw/K2C/BookKept.lean) ·
`FrontOf` (Johnson/Top/H0/Tw/K2C/SendsOn.lean) · `bindOk`, `stands`
(Johnson/Top/H0/Tw/K2C/Laws.lean) · `recvP_seat` (Johnson/Desc/Book/BookFitsGround.lean), `Seated`
(Johnson/Desc/Book/Seated.lean), `placed_of_fits` (Johnson/Desc/Book/BookFits.lean) ·
`array_mapM_inv` (OnBytes/Slice/BlkOpenN.lean) · `listOfT_eq` (OnBytes/Chain/Draws.lean),
`listOf_mem` (Fmt/Rules6Laws.lean). This folder's `recvP_fresh` (Returns/FreshTrees.lean).
`yes_fresh`'s walk over the three sorts of place is the library's `yes_front`'s
(Johnson/Top/H0/Tw/K2C/SendsOn.lean). A NEAR RELATIVE, NOT CALLED: `ReadSeat.bookRead`
(Johnson/Prover/Link/ReadRide.lean): one more list counted at another tree leaves what that house's
carrier says of a tree; its one step on the book is `openOne_off`'s. That folder stands in the
younger of the two sealed libraries over which this file is compiled, not in the elder.

Limits. Nothing on the older trees. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.FreshTrees
import Johnson.Top.H0.Tw.K2C.BookKept
import Johnson.Top.H0.Tw.K2C.SendsOn
import OnBytes.Slice.BlkOpenN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 flat behindArgs readOld_inv
  switchBehind_inv switchE_inv link_inv head_inv finish_inv stands sendByL8_iff sendOpen_iff
  sendP_book bindOk FrontOf)
open VerifiableInference.Desc.Book (BookFits placed_of_fits recvP_seat)
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 openOne readOld switchE Front Col)

/-- The opening of one tree leaves every other tree as it is. -/
theorem openOne_off {T : Statement} {ft : Nat} {pos : Positions} {B0 : TreeBook} {t : Nat}
    {s s' : TreeBook × List OpenedColumn × Array (Nat × Array Nat × Array (Array F))}
    (h : openOne T ft pos B0 t s = .ok s') {z : Nat} (hz : z ≠ t) :
    s'.1.trees[z]? = s.1.trees[z]? := by
  obtain ⟨tree, tree0, a⟩ := (_root_.Tw.K2.openOne_iff _ _ _ _ _ _ _).1 h
  rw [a.out]
  show (s.1.trees.modify t _)[z]? = _
  rw [Array.getElem?_modify, if_neg (Ne.symm hz)]

theorem opens_off {T : Statement} {ft : Nat} {pos : Positions} {B0 : TreeBook} :
    ∀ (l : List Nat) (s s' : TreeBook × List OpenedColumn × Array (Nat × Array Nat × Array (Array F))),
      l.foldlM (fun a t => openOne T ft pos B0 t a) s = .ok s' →
      ∀ z, z ∉ l → s'.1.trees[z]? = s.1.trees[z]?
  | [], s, s', h, _, _ => by
    cases h
    rfl
  | t :: l, s, s', h, z, hz => by
    rw [List.foldlM_cons] at h
    obtain ⟨m, h1, h2⟩ := bindOk h
    rw [opens_off l m s' h2 z (fun k => hz (List.mem_cons_of_mem _ k)),
      openOne_off h1 (fun e => hz (e ▸ List.mem_cons_self))]

/-- **A yes of the reading leaves every tree that holds no opened message.** -/
theorem readOld_off {i : SwIn} {pos : Positions} {B : TreeBook} {left y}
    (h : readOld i pos = .ok (B, left, y)) {z : Nat}
    (hz : ∀ o ∈ (singleRowsOracles i.old).toList, ∀ pl, i.book.place[o]? = some pl → pl.1 ≠ z) :
    B.trees[z]? = i.book.trees[z]? := by
  obtain ⟨places, cols, opened, k⟩ := readOld_inv h
  refine opens_off _ _ _ k.hOpen z fun hm => ?_
  rw [listOfT_eq, Fmt.listOf_mem] at hm
  simp only [Array.toList_map, List.mem_map] at hm
  obtain ⟨pl, hpl, e⟩ := hm
  obtain ⟨n, hn, en⟩ := List.getElem_of_mem hpl
  obtain ⟨k1, k2⟩ := OnBytes.Slice.array_mapM_inv _ _ _ k.hPlaces
  have hn' : n < (singleRowsOracles i.old).size := by
    rw [← k1]
    simpa using hn
  have q := k2 n hn'
  have hp : places[n]? = some pl := by
    rw [Array.getElem?_eq_getElem (by rw [k1]; exact hn')]
    simpa using en
  rw [hp] at q
  exact hz _ (Array.getElem_mem_toList hn') pl q e

/-- **The switch behind its guard leaves what it lays itself opened at no list.** -/
theorem switchE_fresh {P9 : _root_.Tw.K2.Par9} {s9 : _root_.Tw.K2.S9} {x : Front}
    {rS rL : Fmt.RoundView} {cols : List OpenedColumn} {w : SwOut} {roots : Nat}
    (hw : switchE switchBehind P9 sendByL8 s9 x rS rL cols = .ok (w, roots))
    (hfit : BookFits s9.book)
    (hin : ∀ o ∈ (singleRowsOracles x.f.rows).toList, o < s9.book.place.size)
    {j : Nat} {t : Tree} (hj : s9.book.trees.size ≤ j) (ht : w.book.trees[j]? = some t) :
    t.lists = 0 := by
  obtain ⟨y, k⟩ := switchE_inv hw
  obtain ⟨ids, took, d', hs, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
  obtain ⟨_, _, sd, an, hx⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
  obtain ⟨d₁, h1, e1, -⟩ := sendP_book hx
  obtain ⟨-, lay, -, Se⟩ := recvP_seat _ _ _ _ _ h1
  obtain ⟨c, y', S1, S2, S3, rows, b⟩ := switchBehind_inv k.hBehind
  have hoff : w.book.trees[j]? = d'.book.trees[j]? := by
    refine readOld_off b.hRead fun o ho pl hpl e => ?_
    have hpl' : d'.book.place[o]? = some pl := hpl
    rw [e1, Se.places o (hin o ho)] at hpl'
    have := placed_of_fits hfit o pl hpl'
    omega
  rw [hoff, e1] at ht
  exact recvP_fresh _ _ _ _ _ h1 hj ht

/-- **A yes of the kind's own decision leaves what it lays itself opened at no list.** -/
theorem yes_fresh {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') (hfit : BookFits s.book)
    (hin : ∀ x : Front, FrontOf p s x →
      ∀ o ∈ (singleRowsOracles x.f.rows).toList, o < s.book.place.size)
    {j : Nat} {t : Tree} (hj : s.book.trees.size ≤ j) (ht : s'.book.trees[j]? = some t) :
    t.lists = 0 := by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
    rw [k.hOut] at ht
    exact switchE_fresh k.hSwitch hfit (hin x (Or.inl ⟨hp, k.hFront⟩)) hj ht
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    rw [k.hOut] at ht
    exact switchE_fresh k.hSwitch hfit
      (hin _ (Or.inr (Or.inl ⟨hp, a, G, k.hHere, k.hGroup, rfl⟩))) hj ht
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    rw [k.hOut] at ht
    exact switchE_fresh k.hSwitch hfit
      (hin _ (Or.inr (Or.inr ⟨hp, a, G, k.hHere, k.hLaid, rfl⟩))) hj ht

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.openOne_off
#print axioms VerifiableInference.Desc.K2.Honest.Returns.opens_off
#print axioms VerifiableInference.Desc.K2.Honest.Returns.readOld_off
#print axioms VerifiableInference.Desc.K2.Honest.Returns.switchE_fresh
#print axioms VerifiableInference.Desc.K2.Honest.Returns.yes_fresh
