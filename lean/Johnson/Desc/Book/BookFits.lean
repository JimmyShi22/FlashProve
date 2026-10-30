-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/BookFits.lean: an invariant of the book of trees (OnBytes/Iop/Ground.lean:
TreeBook): EVERY ORACLE MESSAGE STANDS IN ITS TREE's LIST OF PARTS AT ITS OWN PART NUMBER; that it
goes along where a prover's message is entered, by receiving or by adopting; and what follows from
it. Definitions, statements and proofs, ON PLAIN DATA: no routine is run here.
IN THE LIBRARY ALREADY (OnBytes/Tie/Pv/Keeps/FitBook.lean: FitAt): its first clause says that the
place of a message names a tree that HOLDS the message. It says nothing of the place's second
member; OnBytes/Iop/LayTreesLaws.lean says nothing of TreeLay.part; and neither speaks of
adopting. BookFits is the stronger clause
(bookFits_holds). wrongPart_*: a book at which FitAt's first clause holds and BookFits fails.
  BookFits B      for every place (tree number, part number) of a message i: the tree is there, and
                  its list of parts has i at that part number.
  bookFits_empty, bookFits_holds.
  placed_of_fits  a place's tree number is below the number of trees.
  places_inj      two messages have two places.
  tenant_of_fits  where the message's tree has ONE part: the part number is 0 and the part is the
                  message.
  cnt, cnt_eq     how many of the first k messages lie in tree number tau.
  LayFits n L     of a layout of n messages: each message's tree is one of the trees, AND ITS PART
                  NUMBER IS THE NUMBER OF EARLIER MESSAGES IN THE SAME TREE. (Nothing on the two
                  arrays' sizes: they are read as the ground reads them, 0 past their ends.)
  fill_cnt, layTrees_some_part, layTrees_fits   THE NEW LAW ON OnBytes.layTrees: what it returns
                  has LayFits. (The filling loop takes a message's part number from the length of
                  its tree's list of main symbols, which grows by one with each message.)
  enterStep, entered_spec   the loop that enters the messages as parts, with the step on a tree a
                  LETTER that pushes the message's number onto parts: the receiving's step (which
                  also turns a mark) and the adopting's are both such.
  bookFits_entered  BookFits goes along where n messages are entered: new trees without parts
                  behind the old ones; the messages' numbers from the number of places on.
  bookFits_kept   it goes along a reading or an opening (Blk.BookKept, OnBytes/Iop/OpenLaws.lean).
  past_fails, stranger_fails, wrongPart_holds, wrongPart_fails, wrongPart_tenant, noPlace_meets :
                  silly books.
What is not said. It says nothing on a tree that no place names, nor that a tree's parts hold
nothing else. That any routine writes such a book: see Johnson/Desc/Book/BookFitsGround.lean. That
a chain's book has it: a chain's walk is not read here. Nothing on what a tree's leaves hold, on
roots or on a tree's number. Nothing on soundness or on hiding.
-/
import OnBytes.Tie.Pv.Keeps.LayOne
import OnBytes.Iop.OpenLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open OnBytes.Params (laidOf)
open OnBytes.Tie.Pv.Keeps.Fit (fillStep Blank laid_spec lay_lt getD_push getD_modify
  getD_modify_ne)

/-! ## The invariant -/

/-- **Every message stands in its tree's list of parts at its own part number.** -/
def BookFits (B : TreeBook) : Prop :=
  ∀ (i : Nat) (q : Nat × Nat), B.place[i]? = some q →
    ∃ t : Tree, B.trees[q.1]? = some t ∧ t.parts[q.2]? = some i

theorem bookFits_empty : BookFits {} :=
  fun _ _ h => absurd (Array.getElem?_eq_some_iff.1 h).1 (Nat.not_lt_zero _)

/-- It gives `FitAt`'s first clause (OnBytes/Tie/Pv/Keeps/FitBook.lean). -/
theorem bookFits_holds {B : TreeBook} (h : BookFits B) (o τ p : Nat)
    (hq : B.place[o]? = some (τ, p)) : ∃ t : Tree, B.trees[τ]? = some t ∧ o ∈ t.parts.toList := by
  obtain ⟨t, a, b⟩ := h o (τ, p) hq
  exact ⟨t, a, List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact b)⟩

theorem placed_of_fits {B : TreeBook} (h : BookFits B) (i : Nat) (q : Nat × Nat)
    (hq : B.place[i]? = some q) : q.1 < B.trees.size := by
  obtain ⟨_, a, _⟩ := h i q hq
  exact (Array.getElem?_eq_some_iff.1 a).1

/-- **Two messages have two places.** -/
theorem places_inj {B : TreeBook} (h : BookFits B) {i j : Nat} {q : Nat × Nat}
    (hi : B.place[i]? = some q) (hj : B.place[j]? = some q) : i = j := by
  obtain ⟨t, a, b⟩ := h i q hi
  obtain ⟨t', a', b'⟩ := h j q hj
  obtain rfl : t = t' := Option.some.inj (a.symm.trans a')
  exact Option.some.inj (b.symm.trans b')

theorem single_of {l : List Nat} {o : Nat} (h1 : l.length = 1) (h2 : l[0]? = some o) :
    l = [o] := by
  cases l with
  | nil => simp at h1
  | cons x r =>
    cases r with
    | nil =>
      simp at h2
      rw [h2]
    | cons _ _ => simp at h1

/-- **A message whose tree has one part is that part, at number 0.** -/
theorem tenant_of_fits {B : TreeBook} (h : BookFits B) {i : Nat} {q : Nat × Nat} {t : Tree}
    (hq : B.place[i]? = some q) (ht : B.trees[q.1]? = some t) (h1 : t.parts.size = 1) :
    q.2 = 0 ∧ t.parts.toList = [i] := by
  obtain ⟨t', a, b⟩ := h i q hq
  rw [ht] at a
  obtain rfl : t = t' := Option.some.inj a
  have lt := (Array.getElem?_eq_some_iff.1 b).1
  have e : q.2 = 0 := by omega
  rw [e] at b
  exact ⟨e, single_of (by rw [Array.length_toList]; exact h1)
    (by rw [Array.getElem?_toList]; exact b)⟩

/-! ## A layout's part numbers -/

/-- How many of the first k messages lie in tree number tau. -/
def cnt (tree : Array Nat) (τ : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => cnt tree τ k + (if tree.getD k 0 = τ then 1 else 0)

theorem cnt_eq (tree : Array Nat) (τ : Nat) : ∀ k,
    cnt tree τ k = ((List.range k).filter fun j => tree.getD j 0 == τ).length
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, ← cnt_eq tree τ k]
    show cnt tree τ k + (if tree.getD k 0 = τ then 1 else 0) = _
    by_cases e : tree.getD k 0 = τ
    · rw [if_pos e, List.filter_cons_of_pos (p := fun j => tree.getD j 0 == τ) (a := k)
        (beq_iff_eq.2 e), List.filter_nil]
      rfl
    · rw [if_neg e, List.filter_cons_of_neg (p := fun j => tree.getD j 0 == τ) (a := k)
        (fun h => e (beq_iff_eq.1 h)), List.filter_nil]
      rfl

/-- Each message's tree is one of the trees, and its part number is the number of earlier messages
in the same tree. -/
def LayFits (n : Nat) (L : TreeLay) : Prop :=
  ∀ i, i < n → L.tree.getD i 0 < L.shapes.size ∧
    L.part.getD i 0 = cnt L.tree (L.tree.getD i 0) i

/-- The filling loop, from trees without symbols. -/
theorem fill_cnt (codes : Codes) (sent : Array OracleNotice) (A0 : Array TreeShape)
    (w0 tree : Array Nat) (hB : Blank A0) (hr : ∀ j, j < sent.size → tree.getD j 0 < A0.size) :
    ∀ (k : Nat) (s : Array TreeShape × Array Nat × Array Nat), k ≤ sent.size →
      (List.range k).foldlM (fillStep codes sent tree) (A0, #[], w0) = some s →
      s.1.size = A0.size ∧
      (∀ τ, τ < A0.size → (s.1.getD τ {}).mainSymbols.size = cnt tree τ k) ∧
      s.2.1.size = k ∧ ∀ j, j < k → s.2.1.getD j 0 = cnt tree (tree.getD j 0) j
  | 0, s, _, h => by
    obtain rfl : (A0, #[], w0) = s := Option.some.inj h
    refine ⟨rfl, fun τ _ => ?_, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    show (A0.getD τ {}).mainSymbols.size = 0
    rw [(hB τ).2.1]
    rfl
  | k + 1, s, hk, h => by
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨s0, h0, h1⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sz, ms, ps, pj⟩ := fill_cnt codes sent A0 w0 tree hB hr k s0 (Nat.le_of_succ_le hk) h0
    have h1' : fillStep codes sent tree s0 k = some s := by
      rw [List.foldlM_cons] at h1
      obtain ⟨y1, a1, a2⟩ := Option.bind_eq_some_iff.1 h1
      obtain rfl : y1 = s := Option.some.inj a2
      exact a1
    have hτ : tree.getD k 0 < A0.size := hr k hk
    unfold fillStep at h1'
    dsimp only at h1'
    split at h1'
    · cases h1'
    · obtain rfl := Option.some.inj h1'
      refine ⟨by rw [Array.size_modify]; exact sz, fun τ hτ' => ?_,
        by rw [Array.size_push]; exact congrArg (· + 1) ps, fun j hj => ?_⟩
      · show _ = cnt tree τ k + (if tree.getD k 0 = τ then 1 else 0)
        by_cases e : tree.getD k 0 = τ
        · subst e
          rw [getD_modify _ _ _ _ (by rw [sz]; exact hτ), if_pos rfl, ← ms _ hτ]
          exact Array.size_push ..
        · rw [getD_modify_ne _ _ _ _ _ e, if_neg e, ms τ hτ']
          rfl
      · rw [getD_push, ps]
        by_cases e : j = k
        · subst e
          rw [if_pos rfl]
          exact ms _ hτ
        · rw [if_neg e]
          exact pj j (by omega)

/-- What layTrees returns, with its part numbers. -/
theorem layTrees_some_part {codes : Codes} {sent : Array OracleNotice} {T : TreeLay}
    (h : layTrees codes sent = some T) :
    ∃ filled, (List.range sent.size).foldlM (fillStep codes sent (laidOf codes sent).2.2)
        ((laidOf codes sent).1, #[], Array.replicate (laidOf codes sent).1.size 0) = some filled ∧
      T.tree = (laidOf codes sent).2.2 ∧ T.part = filled.2.1 := by
  unfold layTrees at h
  dsimp only at h
  obtain ⟨filled, hf, h2⟩ := Option.bind_eq_some_iff.mp h
  split at h2
  · rw [← Option.some.inj h2]
    exact ⟨filled, hf, rfl, rfl⟩
  · cases h2

/-- **THE LAW ON layTrees: a message's part number is the number of earlier messages in its
tree.** -/
theorem layTrees_fits {codes : Codes} {sent : Array OracleNotice} {L : TreeLay}
    (h : layTrees codes sent = some L) : LayFits sent.size L := by
  intro i hi
  obtain ⟨filled, hf, eT, eP⟩ := layTrees_some_part h
  refine ⟨lay_lt h hi, ?_⟩
  have hB : Blank (laidOf codes sent).1 := (laid_spec (codes := codes) hi).1.1
  have hr : ∀ j, j < sent.size → (laidOf codes sent).2.2.getD j 0 < (laidOf codes sent).1.size :=
    fun j hj => (laid_spec (codes := codes) hj).2.1
  rw [eP, eT]
  exact (fill_cnt codes sent _ _ _ hB hr sent.size filled (Nat.le_refl _) hf).2.2.2 i hi

/-! ## The messages are entered as parts -/

/-- One turn of the loop that enters the messages as parts. step: what is done to the tree. -/
def enterStep (tree : Array Nat) (base : Nat) (step : Tree → Nat → Tree) (T : Array Tree)
    (i : Nat) : Array Tree :=
  T.modify (base + tree.getD i 0) fun x => step x i

theorem enterStep_size (tree : Array Nat) (base : Nat) (step : Tree → Nat → Tree)
    (T : Array Tree) (i : Nat) : (enterStep tree base step T i).size = T.size := by
  unfold enterStep
  rw [Array.size_modify]

theorem enterStep_ne (tree : Array Nat) (base : Nat) (step : Tree → Nat → Tree) (T : Array Tree)
    (i j : Nat) (h : base + tree.getD i 0 ≠ j) : (enterStep tree base step T i)[j]? = T[j]? := by
  unfold enterStep
  rw [Array.getElem?_modify, if_neg h]

theorem enterStep_eq (tree : Array Nat) (base : Nat) (step : Tree → Nat → Tree) (T : Array Tree)
    (i : Nat) (t : Tree) (h : T[base + tree.getD i 0]? = some t) :
    (enterStep tree base step T i)[base + tree.getD i 0]? = some (step t i) := by
  unfold enterStep
  rw [Array.getElem?_modify, if_pos rfl, h]
  rfl

theorem entered_spec (tree : Array Nat) (n0 base : Nat) (step : Tree → Nat → Tree)
    (hstep : ∀ x i, (step x i).parts = x.parts.push (n0 + i)) (T1 : Array Tree) :
    ∀ k, ((List.range k).foldl (enterStep tree base step) T1).size = T1.size ∧
      (∀ j, j < base → ((List.range k).foldl (enterStep tree base step) T1)[j]? = T1[j]?) ∧
      ∀ (τ : Nat) (t1 : Tree), T1[base + τ]? = some t1 →
        ∃ t2 : Tree, ((List.range k).foldl (enterStep tree base step) T1)[base + τ]? = some t2 ∧
          t2.parts.size = t1.parts.size + cnt tree τ k ∧
          ∀ j, j < k → tree.getD j 0 = τ →
            t2.parts[t1.parts.size + cnt tree τ j]? = some (n0 + j) := by
  intro k
  induction k with
  | zero =>
    exact ⟨rfl, fun _ _ => rfl, fun τ t1 h =>
      ⟨t1, h, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩⟩
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨sz, old, new⟩ := ih
    refine ⟨?_, fun j hj => ?_, fun τ t1 h => ?_⟩
    · rw [enterStep_size]
      exact sz
    · rw [enterStep_ne _ _ _ _ _ _ (by omega)]
      exact old j hj
    · obtain ⟨t2, a, s, m⟩ := new τ t1 h
      by_cases e : tree.getD k 0 = τ
      · subst e
        refine ⟨step t2 k, enterStep_eq _ _ _ _ _ _ a, ?_, fun j hj ej => ?_⟩
        · rw [hstep, Array.size_push, s]
          show _ = t1.parts.size + (cnt tree (tree.getD k 0) k +
            (if tree.getD k 0 = tree.getD k 0 then 1 else 0))
          rw [if_pos rfl]
          omega
        · rw [hstep, Array.getElem?_push]
          by_cases ejk : j = k
          · subst ejk
            rw [if_pos s.symm]
          · have q := m j (by omega) ej
            have lt := (Array.getElem?_eq_some_iff.1 q).1
            rw [if_neg (by omega)]
            exact q
      · refine ⟨t2, by rw [enterStep_ne _ _ _ _ _ _ (by omega)]; exact a, ?_, fun j hj ej => ?_⟩
        · rw [s]
          show _ = t1.parts.size + (cnt tree τ k + (if tree.getD k 0 = τ then 1 else 0))
          rw [if_neg e]
          rfl
        · have ne : j ≠ k := fun q => e (q ▸ ej)
          exact m j (by omega) ej

/-- **BookFits GOES ALONG WHERE A PROVER's MESSAGE IS ENTERED.** n0: the number of the first of the
messages: the number of places so far. T1: the old trees, and behind them the new ones, still
without parts. -/
theorem bookFits_entered (B : TreeBook) (hB : BookFits B) (n n0 : Nat) (h0 : n0 = B.place.size)
    (L : TreeLay) (hL : LayFits n L) (T1 : Array Tree)
    (hsz : T1.size = B.trees.size + L.shapes.size)
    (hold : ∀ j, j < B.trees.size → T1[j]? = B.trees[j]?)
    (hnew : ∀ j t, B.trees.size ≤ j → T1[j]? = some t → t.parts = #[])
    (step : Tree → Nat → Tree) (hstep : ∀ x i, (step x i).parts = x.parts.push (n0 + i)) :
    BookFits
      { trees := (List.range n).foldl (enterStep L.tree B.trees.size step) T1
        place := B.place ++ (Array.range n).map fun i =>
          (B.trees.size + L.tree.getD i 0, L.part.getD i 0) } := by
  obtain ⟨_, old, new⟩ := entered_spec L.tree n0 B.trees.size step hstep T1 n
  intro i q hq
  have hq' : (B.place ++ (Array.range n).map fun i =>
      (B.trees.size + L.tree.getD i 0, L.part.getD i 0))[i]? = some q := hq
  show ∃ t : Tree, ((List.range n).foldl (enterStep L.tree B.trees.size step) T1)[q.1]? = some t ∧
    t.parts[q.2]? = some i
  by_cases lt : i < B.place.size
  · rw [Array.getElem?_append_left lt] at hq'
    obtain ⟨t, a, b⟩ := hB i q hq'
    have lt' := (Array.getElem?_eq_some_iff.1 a).1
    exact ⟨t, by rw [old q.1 lt', hold q.1 lt']; exact a, b⟩
  · rw [Array.getElem?_append_right (Nat.le_of_not_lt lt), Array.getElem?_map] at hq'
    obtain ⟨j, hj, e⟩ := Option.map_eq_some_iff.1 hq'
    obtain ⟨hj', ej⟩ := Array.getElem?_eq_some_iff.1 hj
    rw [Array.size_range] at hj'
    rw [Array.getElem_range] at ej
    subst ej
    obtain ⟨r1, r2⟩ := hL _ hj'
    have hin : B.trees.size + L.tree.getD (i - B.place.size) 0 < T1.size := by
      rw [hsz]
      omega
    obtain ⟨t2, a2, _, m2⟩ := new (L.tree.getD (i - B.place.size) 0) _
      (Array.getElem?_eq_getElem hin)
    have hp := hnew _ _ (Nat.le_add_right _ _) (Array.getElem?_eq_getElem hin)
    have m3 := m2 (i - B.place.size) hj' rfl
    rw [hp] at m3
    have e1 : (#[] : Array Nat).size + cnt L.tree (L.tree.getD (i - B.place.size) 0)
        (i - B.place.size) = cnt L.tree (L.tree.getD (i - B.place.size) 0) (i - B.place.size) :=
      Nat.zero_add _
    have e2 : n0 + (i - B.place.size) = i := by omega
    rw [e1, e2, ← r2] at m3
    subst e
    exact ⟨t2, a2, m3⟩

/-- It goes along a reading or an opening. -/
theorem bookFits_kept {B B' : TreeBook} (h : Blk.BookKept B B') (hB : BookFits B) :
    BookFits B' := by
  intro i q hq
  rw [h.place] at hq
  obtain ⟨t, a, b⟩ := hB i q hq
  obtain ⟨T', k, _, _, e3, _, _⟩ := h.trees q.1 t a
  exact ⟨T', k, by rw [e3]; exact b⟩

/-! ## Silly books -/

/-- A place that points past the trees. -/
theorem past_fails : ¬ BookFits { trees := #[], place := #[(0, 0)] } := by
  intro h
  obtain ⟨_, a, _⟩ := h 0 (0, 0) (by simp)
  exact absurd (Array.getElem?_eq_some_iff.1 a).1 (Nat.not_lt_zero _)

/-- A place that points at a tree without the message. -/
theorem stranger_fails :
    ¬ BookFits { trees := #[{ shape := {}, parts := #[7] }], place := #[(0, 0)] } := by
  intro h
  obtain ⟨t, a, b⟩ := h 0 (0, 0) (by simp)
  have e : ({ shape := {}, parts := #[7] } : Tree) = t := by simpa using a
  rw [← e] at b
  simp at b

/-- The tree holds the message; the part number is wrong. -/
def wrongPart : TreeBook := { trees := #[{ shape := {}, parts := #[0] }], place := #[(0, 5)] }

/-- **`FitAt`'s first clause holds of it.** -/
theorem wrongPart_holds (o τ p : Nat) (h : wrongPart.place[o]? = some (τ, p)) :
    ∃ t : Tree, wrongPart.trees[τ]? = some t ∧ o ∈ t.parts.toList := by
  unfold wrongPart at h ⊢
  match o, h with
  | 0, h =>
    simp at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨{ shape := {}, parts := #[0] }, by simp, by simp⟩
  | o + 1, h => simp at h

/-- **BookFits fails of it.** -/
theorem wrongPart_fails : ¬ BookFits wrongPart := by
  intro h
  obtain ⟨t, a, b⟩ := h 0 (0, 5) (by simp [wrongPart])
  have e : ({ shape := {}, parts := #[0] } : Tree) = t := by simpa [wrongPart] using a
  rw [← e] at b
  simp at b

/-- **And the message's tree has one part, while its part number is not 0.** -/
theorem wrongPart_tenant : ∃ (q : Nat × Nat) (t : Tree), wrongPart.place[0]? = some q ∧
    wrongPart.trees[q.1]? = some t ∧ t.parts.size = 1 ∧ q.2 ≠ 0 :=
  ⟨(0, 5), { shape := {}, parts := #[0] }, by simp [wrongPart], by simp [wrongPart], rfl,
    by simp⟩

/-- Trees and no place: it is met idly. -/
theorem noPlace_meets (T : Array Tree) : BookFits { trees := T, place := #[] } :=
  fun _ _ h => absurd (Array.getElem?_eq_some_iff.1 h).1 (Nat.not_lt_zero _)

end VerifiableInference.Desc.Book
