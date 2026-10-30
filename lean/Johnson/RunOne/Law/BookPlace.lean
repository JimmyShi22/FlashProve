-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/BookPlace.lean: THE PLACE
OF THE LOOKUPS' OWN MESSAGE IN THE BOOK IS (1, 0): tree 1, part 0. Johnson/RunOne/Law/BookAt15.lean
gives the place by the layouts of the key file's two first sendings: (the first sending's trees) +
(the tree of the second sending's first message), and that message's part. Here the three numbers.

Main names:
  single_tree: the layout of ONE oracle message has one tree.
  tree_first: a first message WITH MAIN ROWS lies in tree 0 of its sending's layout.
  part_first: a first message is part 0 of its tree.
  admitted_two: at a state that was reached at border 2 the plan's ranges ARE admitted
    (Wf.admitted): the second sending's sub-protocol has asked it.
  book_15_at: at a state of the first chain that was reached at border 15 (two lookups): the book
    places message 1 at (1, 0); the tree number 1 is there; the key file's IOP as written in Lean
    (Key.descriptionFromSource X N P) tells of tree 1; what it tells fits the tree's shape.
  seatIs_15_at: so SeatIs no book m j₀ 0 o, of every member m tied to (1, 0), where no 1 = j₀.

All three laws on layTrees are general in the codes and in the messages.
Premise of book_15_at and seatIs_15_at: two lookups. That the own message has a main row comes off
Wf.admitted, and that off the history.
Limits. Nothing on soundness.

-/
import Johnson.RunOne.Law.BookAt15
import Johnson.RunOne.Law.K12OneTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.BookPlace
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Own (passStep treeOf treeOfPass_eq getD_setIfInBounds)
open VerifiableInference.Desc.K12.Coin (ShapeIs SeatIs)
open VerifiableInference.Desc.Key (FirstState Source lookupsOf)
open VerifiableInference.Desc.K3.KeyLaw (bindX needX)
open VerifiableInference.Desc.Key (Claim sendOwnMessage openRangesGroup)
open Johnson.RunOne.Sound (fk_msg_at)
open Johnson.RunOne.Law.FrontSteps (messageOf_first mainRows_pos sent_codes)
open Johnson.RunOne.Law.AllAtO (fk_two₁)
open Johnson.RunOne.Law.BookStays (book_back)
open Johnson.RunOne.Law.BookAt2 (seat_core)
open Johnson.RunOne.Law.K12OneTree (of_ite_pure of_ite_none)
open Johnson.RunOne.Law.BookAt15 (book_15 seatIs_of_shape)
open LPFD (Hist₁ Reached)

/-- **The layout of one oracle message has one tree.** -/
theorem single_tree (codes : Codes) (n : OracleNotice) (lay : TreeLay)
    (h : layTrees codes #[n] = some lay) : lay.shapes.size = 1 := by
  unfold layTrees at h
  dsimp only at h
  obtain ⟨filled, hf, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := of_ite_pure h
  show (filled.1.map _).size = 1
  rw [Array.size_map,
    Johnson.RunOne.Law.K12OneTree.foldlM_keeps (fun s => s.1.size) _ ?_ _ _ _ hf]
  · by_cases hm : n.shape.mainRows = 0 <;> simp [List.range_succ, hm]
  · intro s i s' hs
    obtain rfl := of_ite_none hs
    simp

/-- A step of a pass at another message leaves message 0's entry. -/
theorem passStep_zero (codes : Codes) (sent : Array OracleNotice) (mo : Bool)
    (s : Array TreeShape × Array ℕ × Array ℕ) (i : ℕ) (hi : i ≠ 0) :
    (passStep codes sent mo s i).2.2.getD 0 0 = s.2.2.getD 0 0 := by
  unfold passStep
  split
  · rfl
  · split
    · show (s.2.2.setIfInBounds i _).getD 0 0 = _
      rw [getD_setIfInBounds, if_neg fun h => hi h.1]
    · show (s.2.2.setIfInBounds i _).getD 0 0 = _
      rw [getD_setIfInBounds, if_neg fun h => hi h.1]

theorem fold_zero (codes : Codes) (sent : Array OracleNotice) (mo : Bool) :
    ∀ (l : List ℕ) (s : Array TreeShape × Array ℕ × Array ℕ), (∀ i ∈ l, i ≠ 0) →
      (l.foldl (passStep codes sent mo) s).2.2.getD 0 0 = s.2.2.getD 0 0
  | [], _, _ => rfl
  | i :: l, s, h => by
    rw [List.foldl_cons, fold_zero codes sent mo l _ fun j hj => h j (List.mem_cons_of_mem _ hj),
      passStep_zero codes sent mo s i (h i List.mem_cons_self)]

/-- **A first message with main rows lies in tree 0.** -/
theorem tree_first (codes : Codes) (sent : Array OracleNotice) (hpos : 0 < sent.size)
    (hm : (sent.getD 0 default).shape.mainRows ≠ 0) : (treeOf codes sent).2.2.getD 0 0 = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, sent.size = n + 1 := ⟨sent.size - 1, by omega⟩
  have hne : ∀ i ∈ (List.range n).map Nat.succ, i ≠ 0 := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
    exact Nat.succ_ne_zero j
  have hm' : ((sent.getD 0 default).shape.mainRows == 0) = false := beq_eq_false_iff_ne.2 hm
  have hskip : ∀ s, passStep codes sent true s 0 = s := by
    intro s
    unfold passStep
    rw [if_pos (by rw [hm']; rfl)]
  unfold treeOf
  rw [treeOfPass_eq, treeOfPass_eq, hn, List.range_succ_eq_map, List.foldl_cons, List.foldl_cons,
    fold_zero _ _ _ _ _ hne, hskip, fold_zero _ _ _ _ _ hne]
  unfold passStep
  rw [if_neg (by rw [hm']; decide)]
  show ((Array.replicate (n + 1) 0).setIfInBounds 0 (#[] : Array TreeShape).size).getD 0 0 = 0
  rw [getD_setIfInBounds]
  split <;> simp

/-- **A first message is part 0 of its tree.** -/
theorem part_first (codes : Codes) (sent : Array OracleNotice) (lay : TreeLay)
    (h : layTrees codes sent = some lay) (hpos : 0 < sent.size) : lay.part.getD 0 0 = 0 := by
  have e := layTrees_part codes sent lay h 0 hpos
  rw [Array.getD_eq_getD_getElem?, e]
  rfl

/-- A yes of the second sending's sub-protocol: the plan's ranges are admitted. -/
theorem admitted_of_yes {one : OneTime} {Np : VerifiableInference.Desc.Key.Pieces}
    {gB : List (List ℕ)} {s1 s2 : FirstState} {p₁ p₂ : Fmt.RoundView}
    {gs1 : List (List (ℕ × List UInt64))}
    (h1 : (sendOwnMessage (Cl := Claim) one Np gB).decide s1 [p₁, p₂] gs1 = .ok s2) :
    Wf.admitted one.codes one.ranges (Wf.matrixOf one.lin) = true := by
  obtain ⟨m1, hk1, hq1⟩ := bindX h1
  obtain ⟨ids1, d1, hd1, es, -, -⟩ := seat_core hk1
  have hc := (sent_codes hd1).2
  have hq : openRangesGroup one m1 = .ok s2 := hq1
  unfold openRangesGroup at hq
  dsimp only at hq
  obtain ⟨_, ha, -⟩ := bindX hq
  have e := needX ha
  rw [es, hc] at e
  exact e

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **At a state that was reached at border 2 the plan's ranges are admitted.** -/
theorem admitted_two (D : WholeD) (a)
    (h : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D 2 a) :
    Wf.admitted X.Y.k.oneTime.codes X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) =
      true := by
  obtain ⟨a1, b1, rs1, cols1, -, hb1, hd1, hf1⟩ := Reached.last (k := 1) h
  rw [List.getElem?_map] at hb1
  obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.1 hb1
  obtain ⟨-, hy1⟩ := VerifiableInference.Desc.Plain.held_decide c1 a1 _ _ a hd1
  obtain ⟨p₁, p₂, rfl⟩ := fk_two₁ X N P c1 hc1 hf1
  obtain ⟨gB, hgB⟩ := fk_msg_at X N P
  obtain rfl := Option.some.inj (hgB.symm.trans hc1)
  exact admitted_of_yes hy1

/-- **THE PLACE IS (1, 0).** -/
theorem book_15_at (D : WholeD) (hn : (lookupsOf X.Y.k.oneTime).length = 2) (a)
    (h : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D 15 a) :
    ∃ T o, (show FirstState from a.2).d.book.place[1]? = some (1, 0) ∧
      (show FirstState from a.2).d.book.trees[1]? = some T ∧
      (VerifiableInference.Desc.Key.descriptionFromSource X N P).oracleAt 1 = some o ∧ ShapeIs T.shape o := by
  obtain ⟨a0, h0', -, -⟩ := book_back (N := N) (P := P) D 13 (by rw [hn]) a h
  have hW := admitted_two D a0 h0'
  obtain ⟨layI, layB, T, o, hlI, hlB, hp, hT, -, ho, hS⟩ := book_15 (N := N) (P := P) D hn a h
  obtain ⟨lm, hlm⟩ := messageOf_first X.Y.k.oneTime.ranges
  have hpos : 0 < (Wf.messageOf X.Y.k.oneTime.ranges).size := by
    rw [← Array.length_toList, hlm]
    exact Nat.succ_pos _
  have h0 : (Wf.messageOf X.Y.k.oneTime.ranges).getD 0 default = X.Y.k.oneTime.ranges.message := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hlm]
    rfl
  have e1 : layI.shapes.size = 1 := single_tree _ _ _ hlI
  have e2 : layB.tree.getD 0 0 = 0 := by
    rw [(Own.treesMade_gives (by rw [Own.treesMade_eq]; exact hlB)).1]
    exact tree_first _ _ hpos (by rw [h0]; exact Nat.pos_iff_ne_zero.1 (mainRows_pos hW))
  have e3 : layB.part.getD 0 0 = 0 := part_first _ _ _ hlB hpos
  rw [e1, e2] at hp hT ho
  rw [e3] at hp
  exact ⟨T, o, hp, hT, ho, hS⟩

/-- **SeatIs at (1, 0).** -/
theorem seatIs_15_at (D : WholeD) (hn : (lookupsOf X.Y.k.oneTime).length = 2) (a)
    (h : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D 15 a) :
    ∃ T o, (show FirstState from a.2).d.book.place[1]? = some (1, 0) ∧
      (show FirstState from a.2).d.book.trees[1]? = some T ∧
      (VerifiableInference.Desc.Key.descriptionFromSource X N P).oracleAt 1 = some o ∧
      ∀ (no : ℕ → ℕ) (m : H2K.First.Seat1) (j₀ : ℕ), no 1 = j₀ → m.t = 1 → m.part = 0 →
        m.tsh = T.shape → SeatIs no (show FirstState from a.2).d.book m j₀ 0 o := by
  obtain ⟨T, o, hp, hT, ho, hS⟩ := book_15_at (N := N) (P := P) D hn a h
  exact ⟨T, o, hp, hT, ho, fun no m j₀ hno hmt hmp hts =>
    seatIs_of_shape no _ m 1 0 j₀ T o hT hS hno hmt hmp hts⟩

end Johnson.RunOne.Law.BookPlace

#print axioms Johnson.RunOne.Law.BookPlace.single_tree
#print axioms Johnson.RunOne.Law.BookPlace.passStep_zero
#print axioms Johnson.RunOne.Law.BookPlace.fold_zero
#print axioms Johnson.RunOne.Law.BookPlace.tree_first
#print axioms Johnson.RunOne.Law.BookPlace.part_first
#print axioms Johnson.RunOne.Law.BookPlace.admitted_of_yes
#print axioms Johnson.RunOne.Law.BookPlace.admitted_two
#print axioms Johnson.RunOne.Law.BookPlace.book_15_at
#print axioms Johnson.RunOne.Law.BookPlace.seatIs_15_at
