-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/BookRides.lean: **THE TWO INVARIANTS OF THE BOOK RIDE**: "the book is in order
and counts with the roots" (`BookStep`, Johnson/Desc/Sound/BookInOrder.lean: "K12.bookInOrder") and
"the seats are carried", in the prefix form ("K12.seatsCarried"): through a step that leaves the
book and the roots, and through a receiving. Definitions, statements and proofs. Over readers (a
book, a count of roots): no chain, no kind and no block is named.
  `Laid`, `laidOf codes sends`: the plan's side: for a chain's sendings in the order of sending: the
    messages' (tree, part) in the order of their numbers, and the trees' shapes, by the verifier's
    own layout, the trees counted on from sending to sending.
  `SeatsPrefix L B` | `seatsPrefixB`: the book's places are a prefix of L's, and its trees' shapes a
    prefix of L's. `seatsPrefix_empty`: true of the empty book.
  `BookRidesOn ft L B roots`: both.
  `rides_same`: **WHOEVER SENDS NOTHING**: B' = B and roots' = roots: both ride.
  `recv_places`, `recv_shapes`: what a receiving appends to the book's places and to its shapes.
  `seatsPrefix_append`: through any step that appends to the places and to the shapes what the
    plan's lists go on with: for whoever says what a sending writes in words of its own.
  `seatsPrefix_recv`: through a receiving: where the plan's lists go on, behind what the book holds,
    with this sending's layout.
  `laidOf_append`, `laidOf_goes_on`: the plan's lists do go on so: at sends = pre ++ sent :: post,
    behind what pre lays.
  `rides_received`: **WHOEVER SENDS**: the step is a receiving (`Received`,
    Johnson/Desc/Sound/FenceSend.lean) of the plan's next sending, and the book holds just what the
    sendings in front lay: both ride.
Limits. Nothing on soundness. That a block's yes leaves the book, or is a receiving of the plan's
next sending, is a fact on that block's text: none is shown here.

-/
import Johnson.Desc.Sound.SeatsCarried

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes
open OnBytes.Slice (treesSent partsLaid treesSent_old partsLaid_public)
open VerifiableInference.Desc.Sound
open _root_.Desc.K14.Law.Fence (recvBook_counts treesSent_new_shape)

/-- The plan's side: the messages' (tree, part), and the trees' shapes. -/
structure Laid where
  places : List (ℕ × ℕ) := []
  shapes : List TreeShape := []

/-- What one sending lays, its trees counted from base on. -/
def placesOf (base n : ℕ) (lay : TreeLay) : List (ℕ × ℕ) :=
  (List.range n).map fun i => (base + lay.tree.getD i 0, lay.part.getD i 0)

/-- A chain's sendings, laid one behind the other, the trees counted from base on. -/
def laidFrom (codes : Codes) : ℕ → List (Array OracleNotice) → Option Laid
  | _, [] => some {}
  | base, sent :: rest =>
    (layTrees codes sent).bind fun lay =>
      (laidFrom codes (base + lay.shapes.size) rest).map fun R =>
        { places := placesOf base sent.size lay ++ R.places
          shapes := lay.shapes.toList ++ R.shapes }

/-- From the chain's first tree on. -/
def laidOf (codes : Codes) (sends : List (Array OracleNotice)) : Option Laid :=
  laidFrom codes 0 sends

/-- **The seats are carried, of what the book holds so far.** -/
def SeatsPrefix (L : Laid) (B : TreeBook) : Prop :=
  B.place.toList = L.places.take B.place.size ∧ B.place.size ≤ L.places.length ∧
    B.trees.toList.map (·.shape) = L.shapes.take B.trees.size ∧ B.trees.size ≤ L.shapes.length

/-- The same as a test with code. -/
def seatsPrefixB (L : Laid) (B : TreeBook) : Bool :=
  B.place.toList == L.places.take B.place.size && decide (B.place.size ≤ L.places.length) &&
    B.trees.toList.map (·.shape) == L.shapes.take B.trees.size &&
    decide (B.trees.size ≤ L.shapes.length)

theorem seatsPrefix_iff (L : Laid) (B : TreeBook) : seatsPrefixB L B = true ↔ SeatsPrefix L B := by
  unfold seatsPrefixB SeatsPrefix
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]

theorem seatsPrefix_empty (L : Laid) : SeatsPrefix L { trees := #[], place := #[] } := by
  refine ⟨?_, Nat.zero_le _, ?_, Nat.zero_le _⟩ <;> simp

/-- Both invariants. -/
def BookRidesOn (ft : ℕ) (L : Laid) (B : TreeBook) (roots : ℕ) : Prop :=
  BookStep ft B roots ∧ SeatsPrefix L B

/-- **Whoever sends nothing.** -/
theorem rides_same (ft : ℕ) (L : Laid) (B B' : TreeBook) (roots roots' : ℕ) (e₁ : B' = B)
    (e₂ : roots' = roots) (h : BookRidesOn ft L B roots) : BookRidesOn ft L B' roots' := by
  rw [e₁, e₂]
  exact h

/-- What a receiving appends to the places. -/
theorem recv_places (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots : ℕ) :
    (recvBook ft bk sent lay n0 roots).place.toList =
      bk.place.toList ++ placesOf bk.trees.size sent.size lay := by
  show (bk.place ++ (Array.range sent.size).map _).toList = _
  simp [placesOf, Array.toList_range]

/-- What it appends to the shapes. -/
theorem recv_shapes (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots : ℕ) :
    (recvBook ft bk sent lay n0 roots).trees.toList.map (·.shape) =
      bk.trees.toList.map (·.shape) ++ lay.shapes.toList := by
  have hsz := (recvBook_counts ft bk sent lay n0 roots).2
  apply List.ext_getElem?
  intro z
  have h1 : ((recvBook ft bk sent lay n0 roots).trees[z]?).map (·.shape) =
      ((treesSent ft lay.shapes.toList roots bk.trees)[z]?).map (·.shape) := by
    have h0 := congrArg (Option.map Prod.fst)
      (partsLaid_public sent lay n0 bk.trees.size
        (treesSent ft lay.shapes.toList roots bk.trees) z)
    rw [Option.map_map, Option.map_map] at h0
    exact h0
  rw [List.getElem?_map, Array.getElem?_toList, h1]
  by_cases hz : z < bk.trees.size
  · rw [treesSent_old _ _ _ _ z hz, List.getElem?_append_left (by simpa using hz),
      List.getElem?_map, Array.getElem?_toList]
  · obtain ⟨τ, rfl⟩ : ∃ τ, z = bk.trees.size + τ := ⟨z - bk.trees.size, by omega⟩
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_map, Array.length_toList, Nat.add_sub_cancel_left]
    by_cases hτ : τ < lay.shapes.size
    · exact treesSent_new_shape ft _ roots bk.trees τ (by rw [Array.length_toList]; exact hτ)
    · have hn : (recvBook ft bk sent lay n0 roots).trees[bk.trees.size + τ]? = none :=
        Array.getElem?_eq_none (by rw [hsz]; omega)
      rw [← h1, hn, List.getElem?_eq_none (by rw [Array.length_toList]; omega)]
      rfl

/-- A prefix goes on. -/
theorem take_goes_on {α : Type} (l A N : List α) (h : A = l.take A.length)
    (hN : (l.drop A.length).take N.length = N) : A ++ N = l.take (A.length + N.length) := by
  rw [List.take_add, ← h, hN]

theorem le_of_goes_on {α : Type} (l N : List α) (a : ℕ) (ha : a ≤ l.length)
    (hN : (l.drop a).take N.length = N) : a + N.length ≤ l.length := by
  have h1 := congrArg List.length hN
  rw [List.length_take, List.length_drop] at h1
  omega

/-- **Through any step that appends**: the book behind has the book's places and then N, its trees'
shapes and then M, and the plan's lists go on with N and M. For whoever says what a sending writes
in words of its own. -/
theorem seatsPrefix_append (L : Laid) (B B' : TreeBook) (N : List (ℕ × ℕ)) (M : List TreeShape)
    (h : SeatsPrefix L B) (ep : B'.place.toList = B.place.toList ++ N)
    (es : B'.trees.toList.map (·.shape) = B.trees.toList.map (·.shape) ++ M)
    (hp : (L.places.drop B.place.size).take N.length = N)
    (hs : (L.shapes.drop B.trees.size).take M.length = M) : SeatsPrefix L B' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have la : B.place.toList.length = B.place.size := Array.length_toList
  have lb : (B.trees.toList.map (·.shape)).length = B.trees.size := by simp
  have c1 : B'.place.size = B.place.size + N.length := by
    have := congrArg List.length ep
    rw [List.length_append, Array.length_toList, Array.length_toList] at this
    exact this
  have c2 : B'.trees.size = B.trees.size + M.length := by
    have := congrArg List.length es
    rw [List.length_append, List.length_map, List.length_map, Array.length_toList,
      Array.length_toList] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ep, c1]
    have := take_goes_on L.places B.place.toList N (by rw [la]; exact h1) (by rw [la]; exact hp)
    rw [la] at this
    exact this
  · rw [c1]
    exact le_of_goes_on L.places N B.place.size h2 hp
  · rw [es, c2]
    have := take_goes_on L.shapes (B.trees.toList.map (·.shape)) M (by rw [lb]; exact h3)
      (by rw [lb]; exact hs)
    rw [lb] at this
    exact this
  · rw [c2]
    exact le_of_goes_on L.shapes M B.trees.size h4 hs

/-- **Through a receiving**, where the plan's lists go on with this sending's layout. -/
theorem seatsPrefix_recv (L : Laid) (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice)
    (lay : TreeLay) (n0 roots : ℕ) (h : SeatsPrefix L bk)
    (hp : (L.places.drop bk.place.size).take sent.size = placesOf bk.trees.size sent.size lay)
    (hs : (L.shapes.drop bk.trees.size).take lay.shapes.size = lay.shapes.toList) :
    SeatsPrefix L (recvBook ft bk sent lay n0 roots) :=
  seatsPrefix_append L bk _ _ _ h (recv_places ft bk sent lay n0 roots)
    (recv_shapes ft bk sent lay n0 roots) (by simpa [placesOf] using hp)
    (by rw [Array.length_toList]; exact hs)

/-- The plan's lists at a list of sendings in two parts. -/
theorem laidFrom_append (codes : Codes) : ∀ (pre post : List (Array OracleNotice)) (base : ℕ)
    (L : Laid), laidFrom codes base (pre ++ post) = some L →
    ∃ A R, laidFrom codes base pre = some A ∧
      laidFrom codes (base + A.shapes.length) post = some R ∧
      L.places = A.places ++ R.places ∧ L.shapes = A.shapes ++ R.shapes
  | [], post, base, L, h => ⟨{}, L, rfl, by simpa using h, by simp, by simp⟩
  | sent :: pre, post, base, L, h => by
    have h' : ((layTrees codes sent).bind fun lay =>
        (laidFrom codes (base + lay.shapes.size) (pre ++ post)).map fun R =>
          ({ places := placesOf base sent.size lay ++ R.places
             shapes := lay.shapes.toList ++ R.shapes } : Laid)) = some L := h
    obtain ⟨lay, hl, h1⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨R0, hR0, rfl⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨A, R, hA, hR, e1, e2⟩ := laidFrom_append codes pre post _ R0 hR0
    refine ⟨{ places := placesOf base sent.size lay ++ A.places
              shapes := lay.shapes.toList ++ A.shapes }, R, ?_, ?_, ?_, ?_⟩
    · show ((layTrees codes sent).bind fun lay => _) = _
      rw [hl]
      show ((laidFrom codes (base + lay.shapes.size) pre).map _) = _
      rw [hA]
      rfl
    · have e : base + (lay.shapes.toList ++ A.shapes).length =
          base + lay.shapes.size + A.shapes.length := by
        rw [List.length_append, Array.length_toList]
        omega
      show laidFrom codes (base + (lay.shapes.toList ++ A.shapes).length) post = some R
      rw [e]
      exact hR
    · show placesOf base sent.size lay ++ R0.places = _
      rw [e1, List.append_assoc]
    · show lay.shapes.toList ++ R0.shapes = _
      rw [e2, List.append_assoc]

/-- **The plan's lists go on with the next sending's layout**, behind what the sendings in front
lay. -/
theorem laidOf_goes_on (codes : Codes) (pre post : List (Array OracleNotice))
    (sent : Array OracleNotice) (L : Laid) (h : laidOf codes (pre ++ sent :: post) = some L) :
    ∃ A lay, laidOf codes pre = some A ∧ layTrees codes sent = some lay ∧
      (L.places.drop A.places.length).take sent.size = placesOf A.shapes.length sent.size lay ∧
      (L.shapes.drop A.shapes.length).take lay.shapes.size = lay.shapes.toList := by
  obtain ⟨A, R, hA, hR, e1, e2⟩ := laidFrom_append codes pre (sent :: post) 0 L h
  have hR' : ((layTrees codes sent).bind fun lay =>
      (laidFrom codes (0 + A.shapes.length + lay.shapes.size) post).map fun R' =>
        ({ places := placesOf (0 + A.shapes.length) sent.size lay ++ R'.places
           shapes := lay.shapes.toList ++ R'.shapes } : Laid)) = some R := hR
  obtain ⟨lay, hl, h1⟩ := Option.bind_eq_some_iff.1 hR'
  obtain ⟨R', _, rfl⟩ := Option.map_eq_some_iff.1 h1
  refine ⟨A, lay, hA, hl, ?_, ?_⟩
  · rw [e1, List.drop_left']
    · show ((placesOf (0 + A.shapes.length) sent.size lay ++ R'.places).take sent.size) = _
      rw [Nat.zero_add, List.take_left']
      simp [placesOf]
    · rfl
  · rw [e2, List.drop_left']
    · show ((lay.shapes.toList ++ R'.shapes).take lay.shapes.size) = _
      rw [List.take_left']
      exact Array.length_toList
    · rfl

/-- **Whoever sends**: the step is a receiving of the plan's next sending, and the book holds just
what the sendings in front lay. -/
theorem rides_received (ft : ℕ) (pre post : List (Array OracleNotice)) (sent : Array OracleNotice)
    (lay : TreeLay) (L A : Laid) (st st' : Statement) (bk bk' : TreeBook) (roots roots' : ℕ)
    (hL : laidOf st.codes (pre ++ sent :: post) = some L) (hA : laidOf st.codes pre = some A)
    (hr : Received ft sent lay st bk roots st' bk' roots')
    (c1 : bk.place.size = A.places.length) (c2 : bk.trees.size = A.shapes.length)
    (h : BookRidesOn ft L bk roots) : BookRidesOn ft L bk' roots' := by
  refine ⟨bookStep_received ft sent lay st st' bk bk' roots roots' hr h.1, ?_⟩
  obtain ⟨A', lay', hA', hl', g1, g2⟩ := laidOf_goes_on st.codes pre post sent L hL
  obtain rfl := Option.some.inj (hA.symm.trans hA')
  obtain ⟨hl, _, _, rfl, _⟩ := hr
  obtain rfl := Option.some.inj (hl.symm.trans hl')
  exact seatsPrefix_recv L ft bk sent lay _ roots h.2 (by rw [c1, c2]; exact g1)
    (by rw [c2]; exact g2)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.rides_same
#print axioms VerifiableInference.Desc.K12.Coin.recv_shapes
#print axioms VerifiableInference.Desc.K12.Coin.seatsPrefix_append
#print axioms VerifiableInference.Desc.K12.Coin.seatsPrefix_recv
#print axioms VerifiableInference.Desc.K12.Coin.laidOf_goes_on
#print axioms VerifiableInference.Desc.K12.Coin.rides_received
