-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.FirstBookW
import Johnson.Desc.Third.Law.StartBook
import Johnson.Desc.Third.Law.Sharp
import Johnson.Desc.Third.Law.Sources
/-
Johnson/Desc/K12/Law/BookWHand.lean: WHO HANDS «THE BOOK IS IN ORDER» (BookOrdW, Johnson/Desc/K12/Law/FirstBookW.lean) TO THE LAST CHAIN's OWN PROXIMITY TEST: from the book that the chain's start is handed as the first chain's, across the start and the two blocks without a round that stand in front of the test. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  k14Second_first      a yes of K14's second part: no root was received and s.book.trees.size + 1 = s.loc.firstTree: the block's own guard (firstStepB)
  bookOrdW_k14Second   a yes of K14's second part from s to s' · every tree of s.book bears its place's number ⇒ ∃ x q t: the border x lay in s · Omega's place q and tree t in the shared chain's book · BookOrdW s.book.trees.size t.number s'.book ∧ s'.book.trees.size = s.book.trees.size + 1 ∧ s'.loc.firstTree = s.book.trees.size + 1 ∧ s'.roots = 0
  bookOrdW_door        the start's, K14's second part's and the sources' block's yeses in a row · every tree of the book handed in bears its place's number ⇒ at the record s₂ that the own test is handed: BookOrdW roots₁ ω s₂.book, ω the number of Omega's tree in the shared chain's book · s₂.loc.firstTree = roots₁ + 1 · s₂.book.trees.size = roots₁ + 1 · s₂.roots = 0
THE LETTERS ARE TIED: R₁ IS roots₁, the count of roots handed in (= the handed book's number of trees: the start's own test rootsB); the first own tree's number is R₁ + 1 at the record.
THE PREMISE LEFT: «every tree of the book handed in bears its place's number»: BookOrd 0 at the FIRST chain's last record: left to the frame's and the links' files: shown by nobody. That the book handed in is the first chain's last is the caller's (Johnson/Desc/Third/Law/StartBook.lean's own limit). That the PLACE's numbers (π.nums.firstTree; the R₁ and ω of takenOrderB) are the record's: not shown.
The book behind K14's second part comes from two laws together (Johnson/Desc/Third/Law/Book.lean · Sharp.lean): bookSays_k14Second (Omega's tree's number; every older tree as it was) and sharp_k14Second (one tree more; Omega's place is (the old number of trees, 0); the roots stay).
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Slice
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc VerifiableInference.Desc.Third VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.Ground (adoptP adoptL elsewhereP joinP addRowP)

theorem k14Second_first {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    s.roots = 0 ∧ s.book.trees.size + 1 = s.loc.firstTree := by
  simp only [batchLinearConstraintsSecondPart] at h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, hn, _⟩ := ok_of_bind h
  have := true_of_need hn
  unfold firstStepB at this
  simpa using this


theorem bookOrdW_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (hB : ∀ (z : Nat) (T : Tree), s.book.trees[z]? = some T → T.number = z) :
    ∃ (x : Border) (q : Nat × Nat) (t : Tree), s.loc.border = some x ∧
      x.shared.book.place[x.shared.omega]? = some q ∧ x.shared.book.trees[q.1]? = some t ∧
      BookOrdW s.book.trees.size t.number s'.book ∧
      s'.book.trees.size = s.book.trees.size + 1 ∧ s'.loc.firstTree = s.book.trees.size + 1 ∧
      s'.roots = 0 := by
  obtain ⟨hr0, hft⟩ := k14Second_first p s s' rs gs h
  obtain ⟨x, q, t, q', hx, hq, ht, _, hq', _, ⟨tO, hO, hn, _⟩, _, ftr⟩ :=
    bookSays_k14Second p s s' rs gs h
  obtain ⟨s1, s2, _, s4⟩ := sharp_k14Second p s s' rs gs h
  have eq' : q' = (s.book.trees.size, 0) := Option.some.inj (hq'.symm.trans s4)
  rw [eq'] at hO
  have hloc : s'.loc.firstTree = s.loc.firstTree := by
    obtain ⟨_, _, _, _, _, _, _, _, e⟩ := k14Second_inv p s s' rs gs h
    rw [e]
  refine ⟨x, q, t, hx, hq, ht, ?_, s2, by rw [hloc, hft], by rw [s1, hr0]⟩
  intro z T hT
  by_cases c : z < s.book.trees.size
  · rw [ftr z c] at hT
    rw [if_neg (by omega)]
    exact hB z T hT
  · have hz : z < s'.book.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
    have ez : z = s.book.trees.size := by omega
    rw [if_pos ez]
    rw [ez, hO] at hT
    rw [← Option.some.inj hT]
    exact hn


theorem bookOrdW_door {Cl : Type} (p : P₁₄) (own : Block S₃ Cl) (st₁ : Statement)
    (book₁ : TreeBook) (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow)
    (o : SharedOut) (s₀ s₁ s₂ : S₃) (r₀ r₁ : List Fmt.RoundView)
    (g₀ g₁ : List (List (Nat × List UInt64)))
    (hs : start₃E p.codes p.S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (h₀ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ r₀ g₀ = .ok s₁)
    (h₁ : (takenSources own).decide s₁ r₁ g₁ = .ok s₂)
    (hB : ∀ (z : Nat) (T : Tree), book₁.trees[z]? = some T → T.number = z) :
    ∃ (q : Nat × Nat) (t : Tree), o.book.place[o.omega]? = some q ∧ o.book.trees[q.1]? = some t ∧
      BookOrdW roots₁ t.number s₂.book ∧ s₂.book.trees.size = roots₁ + 1 ∧
      s₂.loc.firstTree = roots₁ + 1 ∧ s₂.roots = 0 := by
  obtain ⟨eb, _, eft⟩ := start₃E_book _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨_, hsz⟩ := k14Second_first p s₀ s₁ r₀ g₀ h₀
  have hR : book₁.trees.size = roots₁ := by
    rw [eb, eft] at hsz
    omega
  obtain ⟨x, q, t, hx, hq, ht, hO, h2, h3, h4⟩ :=
    bookOrdW_k14Second p s₀ s₁ r₀ g₀ h₀ (by rw [eb]; exact hB)
  obtain rfl := takenSources_same own s₁ s₂ r₁ g₁ h₁
  obtain ⟨f, _, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨_, _, e0⟩ := start₃_inv _ _ _ _ hst
  have hxo : x.shared = o := by
    rw [e0] at hx
    exact (congrArg Border.shared (Option.some.inj hx)).symm
  rw [hxo] at hq ht
  rw [eb, hR] at hO h2 h3
  exact ⟨q, t, hq, ht, hO, h2, h3, h4⟩

end H2K.First

#print axioms H2K.First.bookOrdW_k14Second
#print axioms H2K.First.bookOrdW_door
