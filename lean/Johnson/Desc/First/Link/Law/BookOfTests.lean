-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/BookOfTests.lean: THE BOOK's SIDE OF `MaskSeat` (`BookMask`,
MaskSeatOf.lean), `FreshSeat` (OpenWordFront.lean) AND `Opens` (FrontAnswers.lean) FROM THREE TESTS
ON THE VERIFIER's STATE AND FACTS ON THE PLAN's LIST: `bookSeat_of_tests`
(Johnson/Top/H0/K2Caller/KeptSeatOf.lean), which pays `BookSeat`, with its middle taken out as a
lemma of its own and spent three times more. Theorems.

  `book_at`: **the three tests atFirstBook | atFirstSeats | atFirstFits
    (Johnson/Desc/K12/Door/DoorBools.lean) at the state t · the book B behind the switch's sending ·
    the message old is below the state's book's places · the plan's list has (tp, tn) at old and the
    shape sh0 at tp ⊢ B has (tp, tn) at old, and at tp a tree of the shape sh0 with the number
    firstTree + tp.** The proof of `bookSeat_of_tests`, up to there.
  `bookMask_of_tests`, `freshSeat_of_tests`, `opens_of_tests`: the three, from it.
Limits. The three tests are premises. By KeptSeatOf.lean's head: the fields bookInOrder |
seatsCarried | bookFits of the table's FoldFacts conclude them at a reached state; BUT the tests are
asked AT THE STATE t THAT THE WAY IN LETS IN, and FoldFacts speaks of the state at the border: at a
place whose way in is not the identity one step lies between. The facts on the plan's list and «the
oracles' reading by key is Strs.col» are premises too. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.MaskSeatOf
import Johnson.Desc.First.Link.Law.OpenWordFront
import Johnson.Desc.First.Link.Law.FrontAnswers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (Strs)
open _root_.Tw.K2 (switchNotices)

/-- **WHAT THE BOOK BEHIND THE SENDING HAS AT AN OLD MESSAGE.** -/
theorem book_at (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front)
    (L : VerifiableInference.Desc.K12.Door.Laid)
    (hIn : VerifiableInference.Desc.K12.Door.atFirstBook (First.K2.par9 p).firstTree t = true)
    (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats L t = true)
    (hFi : VerifiableInference.Desc.K12.Door.atFirstFits t = true) (B : TreeBook)
    (hB : First.K2.bookAt (First.K2.par9 p).firstTree fx.st t.book t.roots
      (switchNotices fx.T fx.others) = some B)
    (old : ℕ) (hold : old < t.book.place.size) (tp tn : ℕ) (hL : L.places[old]? = some (tp, tn))
    (sh0 : TreeShape) (hLs : L.shapes[tp]? = some sh0) :
    ∃ T', B.place[old]? = some (tp, tn) ∧ B.trees[tp]? = some T' ∧ T'.shape = sh0 ∧
      T'.number = (First.K2.par9 p).firstTree + tp := by
  unfold VerifiableInference.Desc.K12.Door.atFirstBook
    VerifiableInference.Desc.K12.Door.bookInOrderB at hIn
  unfold VerifiableInference.Desc.K12.Door.atFirstSeats
    VerifiableInference.Desc.K12.Door.seatsCarriedB at hSe
  unfold VerifiableInference.Desc.K12.Door.atFirstFits
    VerifiableInference.Desc.Sound.bookFitsB at hFi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at hIn hSe hFi
  obtain ⟨⟨⟨s1, -⟩, s3⟩, -⟩ := hSe
  have hpl : t.book.place[old]? = some (tp, tn) := by
    rw [← Array.getElem?_toList, s1, List.getElem?_take, if_pos hold]
    exact hL
  have hf := hFi old hold
  rw [hpl] at hf
  cases htr : t.book.trees[tp]? with
  | none => simp [htr] at hf
  | some tr0 =>
    have htp : tp < t.book.trees.size := (Array.getElem?_eq_some_iff.1 htr).1
    have hs0 : tr0.shape = sh0 := by
      have e := congrArg (fun l => l[tp]?) s3
      simp only [List.getElem?_map, Array.getElem?_toList, htr, Option.map_some,
        List.getElem?_take, if_pos htp, hLs] at e
      exact Option.some.inj e
    have hn0 : tr0.number = (First.K2.par9 p).firstTree + tp := by
      have e := hIn.2 tp htp
      rw [htr] at e
      simpa using e
    unfold First.K2.bookAt at hB
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hB
    obtain ⟨-, -, hk⟩ := H2K.Out.recvP_keeps (ids := x.1) (d1 := x.2) hx
    obtain ⟨T', t1, t2, t3, -⟩ := hk.tree tp tr0 htr
    exact ⟨T', hk.place old _ hpl, t1, t2.trans hs0, t3.trans hn0⟩

/-- The leaf that the text reads at the position x. -/
theorem leaf_at {logT logN a positions x : ℕ} (ha : logT = a) (hp : positions ≤ 2 ^ logN)
    (hx : x < positions) : (if logT == logN then x else x % 2 ^ logT) = x % 2 ^ a := by
  subst ha
  split
  · rename_i h
    have e : logT = logN := by simpa using h
    rw [e]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx hp)).symm
  · rfl

section
variable (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front)
  (L : VerifiableInference.Desc.K12.Door.Laid)
  (hIn : VerifiableInference.Desc.K12.Door.atFirstBook (First.K2.par9 p).firstTree t = true)
  (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats L t = true)
  (hFi : VerifiableInference.Desc.K12.Door.atFirstFits t = true) (B : TreeBook)
  (hB : First.K2.bookAt (First.K2.par9 p).firstTree fx.st t.book t.roots
    (switchNotices fx.T fx.others) = some B)
include hIn hSe hFi hB

/-- **BookMask FROM THE TESTS.** -/
theorem bookMask_of_tests (orc : ℕ → ℕ → List UInt64) (Y : Strs) (old : ℕ) (sh : OracleShape)
    (seat : ℕ × ℕ) (positions a : ℕ) (o : VerifiableInference.Desc.Oracle)
    (hold : old < t.book.place.size) (tp : ℕ) (hL : L.places[old]? = some (tp, seat.2))
    (sh0 : TreeShape) (hLs : L.shapes[tp]? = some sh0) (xo : OnBytes.Oracle)
    (hxo : (First.K2.skelOf fx).oracles[old]? = some xo) (hsh : xo.shape = sh)
    (ha : sh0.logN = a) (hp : positions ≤ 2 ^ p.logN)
    (horc : ∀ x, x < positions → orc tp (x % 2 ^ a) = Y.col seat.1 (x % 2 ^ a))
    (hskip : sh0.mainWidth + (sh0.maskSymbols.extract 0 seat.2).foldl (· + ·) 0 =
      o.maskSkip seat.2) :
    BookMask p t fx orc Y old sh seat positions a o := by
  obtain ⟨T', b1, b2, b3, b4⟩ := book_at p t fx L hIn hSe hFi B hB old hold tp seat.2 hL sh0 hLs
  refine ⟨B, tp, T', xo, hB, b1, b2, hxo, hsh, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [b3]
    exact leaf_at ha hp hx
  · rw [b4, Nat.add_sub_cancel_left]
    exact horc x hx
  · rw [b3]
    exact hskip

/-- **FreshSeat FROM THE TESTS.** -/
theorem freshSeat_of_tests (orc : ℕ → ℕ → List UInt64) (Y : Strs) (tree skip aF rowsF : ℕ)
    (positions : ℕ) (hold : fx.f.rows.fresh < t.book.place.size) (tp tn : ℕ)
    (hL : L.places[fx.f.rows.fresh]? = some (tp, tn)) (sh0 : TreeShape)
    (hLs : L.shapes[tp]? = some sh0) (xo : OnBytes.Oracle)
    (hxo : (First.K2.skelOf fx).oracles[fx.f.rows.fresh]? = some xo)
    (hsh : xo.shape.maskRows = rowsF) (ha : sh0.logN = aF) (hp : positions ≤ 2 ^ p.logN)
    (horc : ∀ x, x < positions → orc tp (x % 2 ^ aF) = Y.col tree (x % 2 ^ aF))
    (hskip : sh0.mainWidth + (sh0.maskSymbols.extract 0 tn).foldl (· + ·) 0 = skip) :
    FreshSeat p t fx orc Y tree skip aF rowsF positions := by
  obtain ⟨T', b1, b2, b3, b4⟩ := book_at p t fx L hIn hSe hFi B hB fx.f.rows.fresh hold tp tn hL
    sh0 hLs
  refine ⟨B, tp, tn, T', xo, hB, b1, b2, hxo, hsh, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [b3]
    exact leaf_at ha hp hx
  · rw [b4, Nat.add_sub_cancel_left]
    exact horc x hx
  · rw [b3]
    exact hskip

/-- **Opens FROM THE TESTS.** -/
theorem opens_of_tests
    (h : ∀ o ∈ (singleRowsOracles fx.f.rows).toList, o < t.book.place.size ∧
      ∃ tp tn sh0 xo, L.places[o]? = some (tp, tn) ∧ L.shapes[tp]? = some sh0 ∧
        (First.K2.skelOf fx).oracles[o]? = some xo) :
    Opens p t fx B where
  book := hB
  place := fun o ho => by
    obtain ⟨h1, tp, tn, sh0, xo, h2, h3, h4⟩ := h o ho
    obtain ⟨T', b1, b2, _, _⟩ := book_at p t fx L hIn hSe hFi B hB o h1 tp tn h2 sh0 h3
    exact ⟨(tp, tn), T', xo, b1, b2, h4⟩

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.book_at
#print axioms VerifiableInference.Desc.LinkJoin.bookMask_of_tests
#print axioms VerifiableInference.Desc.LinkJoin.freshSeat_of_tests
#print axioms VerifiableInference.Desc.LinkJoin.opens_of_tests
