-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Over Johnson/Top/H0/K2Caller/CarryClosed.lean, whose
`rest` lays the live copy's flag "a link is under way" to false: there
"the way in reads the live copy itself" is false: hence `rest_frame`.
Johnson/Top/H0/Walk/FrameCarryFence.lean: THE FENCE `CarryFence`
(Johnson/Top/H0/Walk/FrameCarryBack.lean) FROM FACTS ON THE VERIFIER's STATE THAT HOLD AT REACHED
STATES. Statements and proofs.
  `zip_of_mapM`, `zip_of_mapM_arr`: where a list (an array) is mapped through a partial function
    with success, each pair of the zip is an argument with its value.
  `bookAt_keeps`: the book behind a sending keeps every elder message's place and every elder
    tree's shape, number and parts: `bookSentP_keeps` (Johnson/Desc/K12/Law/SwTies.lean), called.
  `carryFence_of`: **the fence at a state u**, from five premises:
    hOrd   the book is in order: the tree at place z bears the number firstTree + z
           (`K12.Door.atFirstBook`: the letters of the field bookInOrder of `FoldFacts`)
    hFit   every place of the book names a tree that the book holds
           (`K12.Door.atFirstFits`: the letters of the field bookFits)
    hRows  the carried rows of the front name messages that have a place in the book
    hSize  the book holds at most base trees
    hKey   in the frame's list of trees, the first entry with a key below base has a number below
           base
  `rest_book`, `rest_roots`: the way in turns neither the book nor the number of roots.
  `rest_frame`: the frame that it reads is the LIVE copy's (`S.live`), at every state.
  `fence_of_in`: **the premise hF of `carry_goesBack_of` | `_cleared` | `_same`, to the letter**,
    general in In.
  `firstFront_rows`, `rows_of_sent`, `fence_of_in_link`: at a place that stands at a link the
    front's carried rows are those of the frame that the way in reads: the live copy's: so hRows may
    be asked there: every number that `s.live.frame.rows` names is below the number of the book's
    places.
How. A carried row's message has a place in the book in front (hRows); the sending appends, so the
book behind has that place and that tree; the tree is held (hFit) and bears firstTree + its index
(hOrd); the index is below the number of trees, so below base (hSize); hKey ends it.
Limits. The five are premises: THAT THEY HOLD AT ANY STATE IS NOT SHOWN HERE. hRows is a fact on the
frame's rows; hKey on the frame's list of trees. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameCarryBack
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.K12.Law.SwTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (frontAt bookAt par9)
open VerifiableInference.Desc.First.K2Caller
open _root_.Tw.K2 (switchNotices)
open OnBytes.Slice (BookKeeps)

/-- Where a list is mapped through a partial function with success, each pair of the zip is an
argument with its value. -/
theorem zip_of_mapM {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ z ∈ l.zip r, z.1 ∈ l ∧ f z.1 = some z.2
  | [], r, _, z, hz => by simp at hz
  | a :: l, r, h, z, hz => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none =>
      rw [ha] at h
      cases h
    | some b =>
      rw [ha] at h
      cases hl : l.mapM f with
      | none =>
        rw [hl] at h
        cases h
      | some bs =>
        rw [hl] at h
        obtain rfl : b :: bs = r := Option.some.inj h
        rw [List.zip_cons_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨List.mem_cons_self, ha⟩
        · obtain ⟨h1, h2⟩ := zip_of_mapM f l bs hl z hz
          exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- That at arrays. -/
theorem zip_of_mapM_arr {α β : Type} (f : α → Option β) (l : Array α) (r : Array β)
    (h : l.mapM f = some r) (z : α × β) (hz : z ∈ l.zip r) : z.1 ∈ l ∧ f z.1 = some z.2 := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : l.toList.mapM f with
  | none =>
    rw [hl] at h
    cases h
  | some bs =>
    rw [hl] at h
    obtain rfl : bs.toArray = r := Option.some.inj h
    have hz' : z ∈ l.toList.zip bs := by
      have := Array.mem_toList_iff.2 hz
      rwa [Array.toList_zip] at this
    obtain ⟨h1, h2⟩ := zip_of_mapM f l.toList bs hl z hz'
    exact ⟨Array.mem_toList_iff.1 h1, h2⟩

/-- **The book behind a sending keeps what the book in front said.** -/
theorem bookAt_keeps {ft roots : ℕ} {St : Statement} {Bk B : TreeBook}
    {n : Array OracleNotice} (h : bookAt ft St Bk roots n = some B) : BookKeeps Bk B := by
  unfold bookAt VerifiableInference.Desc.Ground.recvP at h
  dsimp only at h
  split at h
  · rw [Option.map_map] at h
    obtain ⟨lay, -, e⟩ := Option.map_eq_some_iff.1 h
    subst e
    exact H2K.Sw.bookSentP_keeps ft roots St Bk n lay
  · cases h

/-- **THE FENCE AT A STATE, FROM FIVE FACTS.** -/
theorem carryFence_of (Z : ProofFile.Pub) (m base : ℕ) (u : S)
    (hOrd : VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Z m)).firstTree u = true)
    (hFit : VerifiableInference.Desc.K12.Door.atFirstFits u = true)
    (hRows : ∀ fx, frontAt (ProofFile.pAtK2 Z m) u = some fx →
      ∀ o ∈ singleRowsOracles fx.f.rows, o < u.book.place.size)
    (hSize : u.book.trees.size ≤ base)
    (hKey : ∀ k L, k < base →
      (ProofFile.allAt Z).find? (fun L => ProofFile.keyAt Z L.no == k) = some L → L.no < base) :
    CarryFence Z m base u := by
  intro fx B places hfx hB hP z hz tree ht L hL
  obtain ⟨hmem, hpl⟩ := zip_of_mapM_arr (fun o => B.place[o]?) _ places hP z hz
  have hK := bookAt_keeps hB
  have ho := hRows fx hfx z.1 hmem
  -- the message's place in the book in front
  obtain ⟨q, hq⟩ : ∃ q, u.book.place[z.1]? = some q := ⟨_, Array.getElem?_eq_getElem ho⟩
  obtain rfl : q = z.2 := Option.some.inj ((hK.place _ _ hq).symm.trans hpl)
  -- its tree is held
  have hf := List.all_eq_true.1 hFit z.1 (List.mem_range.2 ho)
  rw [hq] at hf
  dsimp only at hf
  cases ht0 : u.book.trees[z.2.1]? with
  | none =>
    rw [ht0] at hf
    cases hf
  | some t =>
    have hlt : z.2.1 < u.book.trees.size := by
      rcases Nat.lt_or_ge z.2.1 u.book.trees.size with h1 | h1
      · exact h1
      · rw [Array.getElem?_eq_none h1] at ht0
        cases ht0
    obtain ⟨T', hT', -, hnum, -⟩ := hK.tree _ _ ht0
    obtain rfl : T' = tree := Option.some.inj (hT'.symm.trans ht)
    -- and bears its own index
    have hord := (Bool.and_eq_true _ _ ▸ hOrd).2
    have h1 := List.all_eq_true.1 hord z.2.1 (List.mem_range.2 hlt)
    rw [ht0] at h1
    have h2 : t.number = (par9 (ProofFile.pAtK2 Z m)).firstTree + z.2.1 := beq_iff_eq.1 h1
    have h3 : T'.number - (par9 (ProofFile.pAtK2 Z m)).firstTree = z.2.1 := by
      rw [hnum, h2]
      omega
    rw [h3] at hL
    exact hKey z.2.1 L (Nat.lt_of_lt_of_le hlt hSize) hL

theorem rest_book (s : S) : (rest s).book = s.book := by
  unfold rest
  split <;> rfl

theorem rest_roots (s : S) : (rest s).roots = s.roots := by
  unfold rest
  split <;> rfl

/-- **The frame that the way in reads is the live copy's**, inside a link and outside. (Inside a
link the way in lays the copy's flag "a link is under way" to false: so the two states of the calls
part there, in that flag alone; their frames do not.) -/
theorem rest_frame (s : S) : (rest s).check.frame = s.live.frame := by
  unfold rest
  split
  · rfl
  · rename_i h
    cases hh : s.here with
    | lay a => simp [S.inLink, S.fork?, hh] at h
    | att a => simp [S.inLink, S.fork?, hh] at h
    | head a =>
      cases ho : a.opened with
      | true => simp [S.inLink, S.fork?, hh, ho] at h
      | false => simp [S.live, S.link?, hh, ho]
    | between => simp [S.live, S.link?, hh]
    | fin a => simp [S.live, S.link?, hh]
    | mem a => simp [S.live, S.link?, hh]

/-- **THE PREMISE hF OF THE RULE, TO THE LETTER**, general in In. -/
theorem fence_of_in {P : Type} (Z : ProofFile.Pub) (m base : ℕ) (In : P × S → Strs → Prop)
    (hIn : ∀ p s y, In (p, s) y →
      VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Z m)).firstTree s = true ∧
      VerifiableInference.Desc.K12.Door.atFirstFits s = true ∧
      (∀ fx, frontAt (ProofFile.pAtK2 Z m) (rest s) = some fx →
        ∀ o ∈ singleRowsOracles fx.f.rows, o < s.book.place.size) ∧
      s.book.trees.size ≤ base)
    (hKey : ∀ k L, k < base →
      (ProofFile.allAt Z).find? (fun L => ProofFile.keyAt Z L.no == k) = some L → L.no < base) :
    ∀ p s y, In (p, s) y → CarryFence Z m base (rest s) := by
  intro p s y h
  obtain ⟨h1, h2, h3, h4⟩ := hIn p s y h
  refine carryFence_of Z m base (rest s) ?_ ?_ ?_ ?_ hKey
  · unfold VerifiableInference.Desc.K12.Door.atFirstBook at h1 ⊢
    rw [rest_book, rest_roots]
    exact h1
  · unfold VerifiableInference.Desc.K12.Door.atFirstFits at h2 ⊢
    rw [rest_book]
    exact h2
  · rw [rest_book]
    exact h3
  · rw [rest_book]
    exact h4

/-- The front's maker leaves the frame's carried rows. -/
theorem firstFront_rows {St : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : _root_.Tw.K2.firstFront St f = .ok x) : x.f.rows = f.rows := by
  unfold _root_.Tw.K2.firstFront at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · dsimp only at h
        split at h
        · cases h
        · obtain rfl := Except.ok.inj h
          rfl
      · cases h
      · cases h

/-- **hRows from a fact on the state's own frame**, at a place that stands at a link. -/
theorem rows_of_sent (Z : ProofFile.Pub) (m : ℕ) (hp : (ProofFile.pAtK2 Z m).stands = .link) (u : S)
    (hR : ∀ o ∈ singleRowsOracles u.check.frame.rows, o < u.book.place.size) :
    ∀ fx, frontAt (ProofFile.pAtK2 Z m) u = some fx →
      ∀ o ∈ singleRowsOracles fx.f.rows, o < u.book.place.size := by
  intro fx hfx o ho
  unfold frontAt at hfx
  rw [hp] at hfx
  dsimp only at hfx
  cases hf : _root_.Tw.K2.firstFront u.st u.check.frame with
  | error e =>
    rw [hf] at hfx
    cases hfx
  | ok x =>
    rw [hf] at hfx
    obtain rfl : x = fx := Option.some.inj hfx
    rw [firstFront_rows hf] at ho
    exact hR o ho

/-- **hF at a place that stands at a link, with the rows' fact on the LIVE copy's frame**: inside a
link the walk's copy is stale, and the way in reads the live one. -/
theorem fence_of_in_link {P : Type} (Z : ProofFile.Pub) (m base : ℕ)
    (hp : (ProofFile.pAtK2 Z m).stands = .link) (In : P × S → Strs → Prop)
    (hIn : ∀ p s y, In (p, s) y →
      VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Z m)).firstTree s = true ∧
      VerifiableInference.Desc.K12.Door.atFirstFits s = true ∧
      (∀ o ∈ singleRowsOracles s.live.frame.rows, o < s.book.place.size) ∧
      s.book.trees.size ≤ base)
    (hKey : ∀ k L, k < base →
      (ProofFile.allAt Z).find? (fun L => ProofFile.keyAt Z L.no == k) = some L → L.no < base) :
    ∀ p s y, In (p, s) y → CarryFence Z m base (rest s) :=
  fence_of_in Z m base In (fun p s y h => by
    obtain ⟨h1, h2, h3, h4⟩ := hIn p s y h
    refine ⟨h1, h2, ?_, h4⟩
    have := rows_of_sent Z m hp (rest s) (by rw [rest_book, rest_frame]; exact h3)
    rw [rest_book] at this
    exact this) hKey

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.zip_of_mapM_arr
#print axioms Johnson.Desc.First.Walk.Tied.bookAt_keeps
#print axioms Johnson.Desc.First.Walk.Tied.carryFence_of
#print axioms Johnson.Desc.First.Walk.Tied.rest_frame
#print axioms Johnson.Desc.First.Walk.Tied.fence_of_in
#print axioms Johnson.Desc.First.Walk.Tied.rows_of_sent
#print axioms Johnson.Desc.First.Walk.Tied.fence_of_in_link
