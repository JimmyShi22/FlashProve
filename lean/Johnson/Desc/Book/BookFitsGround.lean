-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/BookFitsGround.lean: the invariant BookFits (Johnson/Desc/Book/BookFits.lean:
every oracle message stands in its tree's list of parts at its own part number) GOES ALONG EVERY
ROUTINE OF THE PLAIN GROUND (Johnson/Desc/First/Base/Ground.lean). Statements and proofs.
  sentTrees_size, sentTrees_old, sentTrees_new : the receiving's first loop (they follow
                  FitBook.lean's three).
  pushes_spec     the adopting's first loop: new trees without parts behind the old ones.
  recvP_fits      messages are received: BookFits goes along.
  adoptP_fits     messages whose trees another chain has sent come in: BookFits goes along: FOR ANY
                  NUMBER OF MESSAGES AND TREES.
  Both spend the routine's own clause "statement and book are in step": so the number of a new
  message is its index among the places, and no further invariant is asked.
  recvP_seat, adoptP_seat (the structure Seated: Johnson/Desc/Book/Seated.lean) : WHERE A NEW
                  MESSAGE IS SEATED: at a yes the i-th new message's
                  place is (the old number of trees + its tree in the layout, its part in the
                  layout); the part is the number of earlier messages of this sending in that tree;
                  every older place and tree is as it was; as many trees more as the layout has.
                  ALSO: JUST n places more (count) · EACH NEW
                  TREE's FOUR FIELDS (made): its shape is the layout's; its number and source (the
                  receiving: the chain's first tree's number + the roots received + tau, its own
                  root number; the adopting: as given); its parts are just its messages of this
                  sending, in order · the numbers that the routine hands back (ids).
  sentTrees_made, pushes_made, entered_keeps, entered_made : for that.
  newGroupP_book, admitP_book, joinP_book, addRowP_book, addRowsFrom_book, addRowsP_book,
  takeMaskP_book, takeMasksInto_book, takeMasksP_book, closeLedgerP_book, spendAsMaskP_book,
  beginRunP_book, elsewhereP_book : no other routine of the ground writes the book.
What is not said. THE GROUND IS NOT THE ONLY WRITER OF A CHAIN's BOOK: records are copied into one
another; a reading lays the book that it returns (there: bookFits_kept); the shared chain copies a
book back out of `verify-on-bytes`'s routines. That a chain's book has BookFits wants that chain's
walk, which is not read here. Nothing on soundness or on hiding.
-/
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Book.Seated
import Johnson.Desc.Own.TreesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Ground

variable {L : Type}

/-! ## The trees of a prover's message

Three small facts on treesSent (OnBytes/Slice/BlkSendRun.lean). THEY FOLLOW treesSent_size, _old and
_new of OnBytes/Tie/Pv/Keeps/FitBook.lean, statement and proof; typed again here under names
of their own so that this file's cone stays small. -/

theorem sentTrees_size (first : Nat) : ∀ (l : List TreeShape) (r : Nat) (A : Array Tree),
    (treesSent first l r A).size = A.size + l.length
  | [], _, _ => rfl
  | s :: l, r, A => by
    show (treesSent first l (r + 1) (A.push _)).size = _
    rw [sentTrees_size first l, Array.size_push, List.length_cons]
    omega

theorem sentTrees_old (first : Nat) : ∀ (l : List TreeShape) (r : Nat) (A : Array Tree) (i : Nat),
    i < A.size → (treesSent first l r A)[i]? = A[i]?
  | [], _, _, _, _ => rfl
  | s :: l, r, A, i, h => by
    show (treesSent first l (r + 1) (A.push _))[i]? = _
    rw [sentTrees_old first l _ _ i (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_neg (by omega)]

theorem sentTrees_new (first : Nat) : ∀ (l : List TreeShape) (r : Nat) (A : Array Tree) (τ : Nat)
    (s' : TreeShape), l[τ]? = some s' →
    ∃ t : Tree, (treesSent first l r A)[A.size + τ]? = some t ∧ t.shape = s' ∧ t.parts = #[]
  | [], _, _, _, _, h => by cases h
  | s :: l, r, A, 0, s', h => by
    obtain rfl : s = s' := Option.some.inj h
    refine ⟨{ shape := s, number := first + r, src := .own r }, ?_, rfl, rfl⟩
    show (treesSent first l (r + 1) (A.push _))[A.size + 0]? = _
    rw [sentTrees_old first l _ _ _ (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_pos (Nat.add_zero _)]
  | s :: l, r, A, τ + 1, s', h => by
    obtain ⟨t, a, b, c⟩ := sentTrees_new first l (r + 1)
      (A.push { shape := s, number := first + r, src := .own r }) τ s' h
    refine ⟨t, ?_, b, c⟩
    rw [Array.size_push, show A.size + 1 + τ = A.size + (τ + 1) by omega] at a
    exact a

/-! ## The two routines that write the book -/

/-- New trees without parts, pushed behind the old ones. -/
theorem pushes_spec (f : Nat → Tree) (hf : ∀ i, (f i).parts = #[]) (A : Array Tree) :
    ∀ m, ((List.range m).foldl (fun T i => T.push (f i)) A).size = A.size + m ∧
      (∀ j, j < A.size → ((List.range m).foldl (fun T i => T.push (f i)) A)[j]? = A[j]?) ∧
      ∀ j t, A.size ≤ j → ((List.range m).foldl (fun T i => T.push (f i)) A)[j]? = some t →
        t.parts = #[] := by
  intro m
  induction m with
  | zero =>
    refine ⟨rfl, fun _ _ => rfl, fun j t hj h => ?_⟩
    exact absurd (Array.getElem?_eq_some_iff.1 h).1 (Nat.not_lt_of_le hj)
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨sz, old, new⟩ := ih
    refine ⟨by rw [Array.size_push, sz]; omega, fun j hj => ?_, fun j t hj h => ?_⟩
    · rw [Array.getElem?_push, if_neg (by omega)]
      exact old j hj
    · rw [Array.getElem?_push] at h
      split at h
      · rw [← Option.some.inj h]
        exact hf m
      · exact new j t hj h

/-- **Messages are received: BookFits goes along.** -/
theorem recvP_fits (firstTree : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP firstTree d sent = some (ids, d')) (hB : BookFits d.book) :
    BookFits d'.book := by
  unfold recvP at h
  rw [Own.treesMade_eq] at h
  split at h
  · rename_i hok
    simp only [ok, recvL, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, beq_iff_eq] at hok
    cases hl : layTrees d.st.codes sent with
    | none => simp [hl] at h
    | some lay =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine bookFits_entered d.book hB sent.size d.st.oracles.size hok.2 lay (layTrees_fits hl)
        (treesSent firstTree lay.shapes.toList d.roots d.book.trees) ?_
        (fun j hj => sentTrees_old firstTree _ _ _ j hj) (fun j t hj ht => ?_)
        (fun x i => { x with
          parts := x.parts.push (d.st.oracles.size + i)
          oneList := x.oneList || (sent.getD i default).shape.answers == 0 }) (fun _ _ => rfl)
      · rw [sentTrees_size, Array.length_toList]
      · have lt := (Array.getElem?_eq_some_iff.1 ht).1
        rw [sentTrees_size, Array.length_toList] at lt
        obtain ⟨τ, rfl⟩ : ∃ τ, j = d.book.trees.size + τ := ⟨j - d.book.trees.size, by omega⟩
        have lt' : τ < lay.shapes.size := by omega
        obtain ⟨t1, a1, _, p1⟩ := sentTrees_new firstTree lay.shapes.toList d.roots d.book.trees τ
          lay.shapes[τ] (by rw [Array.getElem?_toList, Array.getElem?_eq_getElem lt'])
        rw [ht] at a1
        rw [Option.some.inj a1]
        exact p1
  · cases h

/-- **Messages of another chain come in: BookFits goes along**, for any number of messages. -/
theorem adoptP_fits (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat)
    (h : adoptP d sent given = some (ids, d')) (hB : BookFits d.book) : BookFits d'.book := by
  unfold adoptP at h
  rw [Own.treesMade_eq] at h
  split at h
  · rename_i hok
    cases hl : layTrees d.st.codes sent with
    | none => simp [hl] at h
    | some lay =>
      simp only [ok, adoptL, Own.treesMade_eq, hl, has, Option.map_some, Option.getD_some,
        List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hok
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨sz, old, new⟩ := pushes_spec
        (fun i => { shape := lay.shapes.getD i {}, number := (given.getD i (0, .own 0)).1,
                    src := (given.getD i (0, .own 0)).2 }) (fun _ => rfl) d.book.trees given.size
      exact bookFits_entered d.book hB sent.size d.st.oracles.size hok.2.2.1 lay
        (layTrees_fits hl) _ (by rw [sz, hok.2.2.2.2]) old new
        (fun x i => { x with parts := x.parts.push (d.st.oracles.size + i) }) (fun _ _ => rfl)
  · cases h

/-! ## Where a new message is seated, and what the new trees are -/

/-- A new tree of the receiving: its shape, number and source; no parts yet. -/
theorem sentTrees_made (first : Nat) : ∀ (l : List TreeShape) (r : Nat) (A : Array Tree) (τ : Nat)
    (s' : TreeShape), l[τ]? = some s' →
    ∃ t : Tree, (treesSent first l r A)[A.size + τ]? = some t ∧ t.shape = s' ∧
      t.number = first + (r + τ) ∧ t.src = .own (r + τ) ∧ t.parts = #[]
  | [], _, _, _, _, h => by cases h
  | s :: l, r, A, 0, s', h => by
    obtain rfl : s = s' := Option.some.inj h
    refine ⟨{ shape := s, number := first + r, src := .own r }, ?_, rfl, rfl, rfl, rfl⟩
    show (treesSent first l (r + 1) (A.push _))[A.size + 0]? = _
    rw [sentTrees_old first l _ _ _ (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_pos (Nat.add_zero _)]
  | s :: l, r, A, τ + 1, s', h => by
    obtain ⟨t, a, b, c, e, f⟩ := sentTrees_made first l (r + 1)
      (A.push { shape := s, number := first + r, src := .own r }) τ s' h
    refine ⟨t, ?_, b, ?_, ?_, f⟩
    · rw [Array.size_push, show A.size + 1 + τ = A.size + (τ + 1) by omega] at a
      exact a
    · rw [c, show r + 1 + τ = r + (τ + 1) by omega]
    · rw [e, show r + 1 + τ = r + (τ + 1) by omega]

/-- A new tree of the adopting's first loop. -/
theorem pushes_made (f : Nat → Tree) (A : Array Tree) : ∀ m τ, τ < m →
    ((List.range m).foldl (fun T i => T.push (f i)) A)[A.size + τ]? = some (f τ) := by
  intro m
  induction m with
  | zero => exact fun τ h => absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro τ hτ
    have sz : ∀ k, ((List.range k).foldl (fun T i => T.push (f i)) A).size = A.size + k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ihk =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_push,
          ihk]
        omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.getElem?_push,
      sz m]
    by_cases e : τ = m
    · subst e
      rw [if_pos rfl]
    · rw [if_neg (by omega)]
      exact ih τ (by omega)

/-- The loop that enters the parts keeps each tree's shape, number and source. -/
theorem entered_keeps (tree : Array Nat) (base : Nat) (step : Tree → Nat → Tree)
    (hk : ∀ x i, (step x i).shape = x.shape ∧ (step x i).number = x.number ∧
      (step x i).src = x.src) (T1 : Array Tree) :
    ∀ (k j : Nat) (t1 : Tree), T1[j]? = some t1 →
      ∃ t2 : Tree, ((List.range k).foldl (enterStep tree base step) T1)[j]? = some t2 ∧
        t2.shape = t1.shape ∧ t2.number = t1.number ∧ t2.src = t1.src := by
  intro k
  induction k with
  | zero => exact fun j t1 h => ⟨t1, h, rfl, rfl, rfl⟩
  | succ k ih =>
    intro j t1 h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨t2, a, s1, s2, s3⟩ := ih j t1 h
    by_cases e : base + tree.getD k 0 = j
    · subst e
      obtain ⟨k1, k2, k3⟩ := hk t2 k
      exact ⟨step t2 k, enterStep_eq _ _ _ _ _ _ a, k1.trans s1, k2.trans s2, k3.trans s3⟩
    · rw [enterStep_ne _ _ _ _ _ _ e]
      exact ⟨t2, a, s1, s2, s3⟩

/-- A new tree behind both loops: as it was made, with just its messages as parts, in order. -/
theorem entered_made (tree : Array Nat) (n0 base : Nat) (step : Tree → Nat → Tree)
    (hstep : ∀ x i, (step x i).parts = x.parts.push (n0 + i))
    (hk : ∀ x i, (step x i).shape = x.shape ∧ (step x i).number = x.number ∧
      (step x i).src = x.src) (T1 : Array Tree) (n τ : Nat) (t1 : Tree)
    (h1 : T1[base + τ]? = some t1) (hp : t1.parts = #[]) :
    ∃ t : Tree, ((List.range n).foldl (enterStep tree base step) T1)[base + τ]? = some t ∧
      t.shape = t1.shape ∧ t.number = t1.number ∧ t.src = t1.src ∧
      t.parts.size = cnt tree τ n ∧
      ∀ j, j < n → tree.getD j 0 = τ → t.parts[cnt tree τ j]? = some (n0 + j) := by
  obtain ⟨_, _, new⟩ := entered_spec tree n0 base step hstep T1 n
  obtain ⟨t2, a2, z2, m2⟩ := new τ t1 h1
  obtain ⟨t3, a3, k1, k2, k3⟩ := entered_keeps tree base step hk T1 n (base + τ) t1 h1
  obtain rfl : t2 = t3 := Option.some.inj (a2.symm.trans a3)
  have e0 : t1.parts.size = 0 := by rw [hp]; rfl
  rw [e0, Nat.zero_add] at z2
  refine ⟨t2, a2, k1, k2, k3, z2, fun j hj e => ?_⟩
  have q := m2 j hj e
  rw [e0, Nat.zero_add] at q
  exact q

theorem places_new {α : Type} (P : Array α) (n : Nat) (g : Nat → α) (i : Nat) (hi : i < n) :
    (P ++ (Array.range n).map g)[P.size + i]? = some (g i) := by
  rw [Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Array.getElem?_map, Array.getElem?_eq_getElem (by rw [Array.size_range]; exact hi),
    Array.getElem_range]
  rfl

/-- **Where the receiving seats the new messages.** -/
theorem recvP_seat (firstTree : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP firstTree d sent = some (ids, d')) :
    ids = (Array.range sent.size).map (· + d.st.oracles.size) ∧
    ∃ lay, layTrees d.st.codes sent = some lay ∧
      Seated d.book d'.book sent.size d.st.oracles.size lay
        (fun τ => firstTree + (d.roots + τ)) (fun τ => .own (d.roots + τ)) := by
  unfold recvP at h
  rw [Own.treesMade_eq] at h
  split at h
  · rename_i hok
    simp only [ok, recvL, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, beq_iff_eq] at hok
    cases hl : layTrees d.st.codes sent with
    | none => simp [hl] at h
    | some lay =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hid, rfl⟩ := h
      obtain ⟨sz, old, _⟩ := entered_spec lay.tree d.st.oracles.size d.book.trees.size
        (fun x i => { x with
          parts := x.parts.push (d.st.oracles.size + i)
          oneList := x.oneList || (sent.getD i default).shape.answers == 0 }) (fun _ _ => rfl)
        (treesSent firstTree lay.shapes.toList d.roots d.book.trees) sent.size
      refine ⟨hid.symm, lay, rfl, layTrees_fits hl, hok.2, fun i hi => ?_, fun j hj => ?_,
        fun j hj => ?_, ?_, ?_, fun τ hτ => ?_⟩
      · rw [hok.2]
        exact places_new _ _ _ i hi
      · exact Array.getElem?_append_left hj
      · exact (old j hj).trans (sentTrees_old firstTree _ _ _ j hj)
      · exact sz.trans (by rw [sentTrees_size, Array.length_toList])
      · show (d.book.place ++ _).size = _
        rw [Array.size_append, Array.size_map, Array.size_range]
      · obtain ⟨t1, a1, s1, n1, r1, p1⟩ := sentTrees_made firstTree lay.shapes.toList d.roots
          d.book.trees τ lay.shapes[τ]
          (by rw [Array.getElem?_toList, Array.getElem?_eq_getElem hτ])
        obtain ⟨t, a, e1, e2, e3, e4, e5⟩ := entered_made lay.tree d.st.oracles.size
          d.book.trees.size (fun x i => { x with
            parts := x.parts.push (d.st.oracles.size + i)
            oneList := x.oneList || (sent.getD i default).shape.answers == 0 }) (fun _ _ => rfl)
          (fun _ _ => ⟨rfl, rfl, rfl⟩) _ sent.size τ t1 a1 p1
        refine ⟨t, a, ?_, e2.trans n1, e3.trans r1, e4, e5⟩
        rw [e1, s1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hτ]
        rfl
  · cases h

/-- **Where the adopting seats the new messages.** -/
theorem adoptP_seat (d d' : DState L) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) (ids : Array Nat)
    (h : adoptP d sent given = some (ids, d')) :
    ids = (Array.range sent.size).map (· + d.st.oracles.size) ∧
    ∃ lay, layTrees d.st.codes sent = some lay ∧
      Seated d.book d'.book sent.size d.st.oracles.size lay
        (fun τ => (given.getD τ (0, .own 0)).1) (fun τ => (given.getD τ (0, .own 0)).2) := by
  unfold adoptP at h
  rw [Own.treesMade_eq] at h
  split at h
  · rename_i hok
    cases hl : layTrees d.st.codes sent with
    | none => simp [hl] at h
    | some lay =>
      simp only [ok, adoptL, Own.treesMade_eq, hl, has, Option.map_some, Option.getD_some,
        List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hok
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hid, rfl⟩ := h
      obtain ⟨sz1, old1, _⟩ := pushes_spec
        (fun i => { shape := lay.shapes.getD i {}, number := (given.getD i (0, .own 0)).1,
                    src := (given.getD i (0, .own 0)).2 }) (fun _ => rfl) d.book.trees given.size
      obtain ⟨sz, old, _⟩ := entered_spec lay.tree d.st.oracles.size d.book.trees.size
        (fun x i => { x with parts := x.parts.push (d.st.oracles.size + i) }) (fun _ _ => rfl)
        ((List.range given.size).foldl (fun T i => T.push
          { shape := lay.shapes.getD i {}, number := (given.getD i (0, .own 0)).1,
            src := (given.getD i (0, .own 0)).2 }) d.book.trees) sent.size
      refine ⟨hid.symm, lay, rfl, layTrees_fits hl, hok.2.2.1, fun i hi => ?_, fun j hj => ?_,
        fun j hj => ?_, ?_, ?_, fun τ hτ => ?_⟩
      · rw [hok.2.2.1]
        exact places_new _ _ _ i hi
      · exact Array.getElem?_append_left hj
      · exact (old j hj).trans (old1 j hj)
      · exact sz.trans (by rw [sz1, hok.2.2.2.2])
      · show (d.book.place ++ _).size = _
        rw [Array.size_append, Array.size_map, Array.size_range]
      · have a1 := pushes_made
          (fun i => { shape := lay.shapes.getD i {}, number := (given.getD i (0, .own 0)).1,
                      src := (given.getD i (0, .own 0)).2 }) d.book.trees given.size τ
          (by rw [← hok.2.2.2.2]; exact hτ)
        obtain ⟨t, a, e1, e2, e3, e4, e5⟩ := entered_made lay.tree d.st.oracles.size
          d.book.trees.size (fun x i => { x with parts := x.parts.push (d.st.oracles.size + i) })
          (fun _ _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) _ sent.size τ _ a1 rfl
        exact ⟨t, a, e1, e2, e3, e4, e5⟩
  · cases h

/-! ## No other routine writes the book -/

theorem newGroupP_book (d d' : DState L) (code maskCode n : Nat)
    (h : newGroupP d code maskCode = some (n, d')) : d'.book = d.book := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · cases h

theorem admitP_book (d d' : DState L) (o : Nat) (rows : Array Row)
    (h : admitP d o rows = some d') : d'.book = d.book := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    rfl
  · cases h

theorem joinP_book (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') : d'.book = d.book := by
  unfold joinP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.map_some, Option.some.injEq] at h
      subst h
      rfl
  · cases h

theorem addRowP_book (d d' : DState L) (g : Nat) (row : Row)
    (h : addRowP d g row = some d') : d'.book = d.book := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

theorem addRowsFrom_book (g : Nat) (rows : List Row) : ∀ (d d' : DState L),
    addRowsFrom g rows d = some d' → d'.book = d.book := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    rfl
  | cons row l ih =>
    intro d d' h
    simp only [addRowsFrom] at h
    cases h1 : addRowP d g row with
    | none => simp [h1] at h
    | some e =>
      simp only [h1, Option.bind_some] at h
      exact (ih e d' h).trans (addRowP_book d e g row h1)

theorem addRowsP_book (d d' : DState L) (g : Nat) (rows : List Row)
    (h : addRowsP d g rows = some d') : d'.book = d.book := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_book g rows d d' h
  · cases h

theorem takeMaskP_book (d d' : DState L) (o n : Nat)
    (h : takeMaskP d o = some (n, d')) : d'.book = d.book := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
  · cases h

theorem takeMasksInto_book (o : Nat) (count : Nat) : ∀ (d d' : DState L) (acc : Array Nat)
    (r : List Nat), takeMasksInto o count d acc = some (r, d') → d'.book = d.book := by
  induction count with
  | zero =>
    intro d d' acc r h
    simp only [takeMasksInto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | succ n ih =>
    intro d d' acc r h
    simp only [takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e h1
      exact (ih e d' _ r h).trans (takeMaskP_book d e o i h1)

theorem takeMasksP_book (d d' : DState L) (o count : Nat) (r : List Nat)
    (h : takeMasksP d o count = some (r, d')) : d'.book = d.book :=
  takeMasksInto_book o count d d' #[] r h

theorem closeLedgerP_book (d d' : DState L) (o : Nat)
    (h : closeLedgerP d o = some d') : d'.book = d.book := by
  unfold closeLedgerP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

theorem spendAsMaskP_book (d d' : DState L) (o : Nat)
    (h : spendAsMaskP d o = some d') : d'.book = d.book := by
  unfold spendAsMaskP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

theorem beginRunP_book (d d' : DState L) (g : Nat) (r : RunInput)
    (h : beginRunP d g = some (r, d')) : d'.book = d.book := by
  unfold beginRunP at h
  split at h
  · cases hg : d.st.groups[g]? with
    | none => simp [hg] at h
    | some G =>
      simp only [hg, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
  · cases h

theorem elsewhereP_book (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : d'.book = d.book := by
  unfold elsewhereP at h
  split at h
  · cases hy : other.oracles[theirs]? with
    | none => simp [hy] at h
    | some y =>
      simp only [hy, Option.map_some, Option.some.injEq] at h
      subst h
      rfl
  · cases h

end VerifiableInference.Desc.Book
