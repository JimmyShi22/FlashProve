-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Sharp.lean: what K14's second part lays into the last chain's record, said
more sharply than `Says` and `BookSays` say it. A definition of Prop and theorems.

Why. Tables of this chain's joints read, of the record behind the block: the count
of roots; how many trees the book has; at which tree and which part Omega is placed; that the row
(Dot) is a plain row; where Omega stands among the own group's members; how many sample rows Omega's
copy has and that it has not served as a mask. `BookSays` gives of Omega's place only that its tree
is no older one; `Says` gives of (Dot) only that it is no sample row, and of the members an
insertion behind the smaller numbers.

Main names:
  `foldlM_one`, `layTrees_part_one`, `laidOf_one_fresh`, `layTrees_part_zero`: the planner lays one
    message alone as part 0 of its tree.
  `adoptP_one_sharp`: adoptP's yes at one message and one given tree: one tree more, one place more,
    the new place is (the old number of trees, 0), the count of roots stays.
  `Sharp s s'`, `sharp_k14Second`: the same of the block. `SharpLaw`: as a property of a block.
  `addLaid_kind`, `linDotRow_plain`: the row (Dot) is a plain row.
  `omega_copy`: Omega's copy has as many sample rows as Omega has in the shared statement, its
    shape and its pad; it is sampled, has no ledger and has not served as a mask.
  `insert_at_end`, `joins_at_end`: where every member of the own group has a smaller number than
    the new message, Omega is the last member.
  `sharp_irrefl`, `idle₃_not_sharp`, `deaf₃_sharp`: the block that says yes to all fails
    `SharpLaw`; the block that says no to all meets it. Every law of the form "a yes gives" is met
    by a block that never says yes: that this block does say yes is shown by a run on honest files,
    not by a law.

Limits. The new tree's shape and its list of parts are not stated. That part 0 of Omega's tree in
the shared chain's book is Omega is not stated: the text asks there "a tree to itself" and does not
read the part's number. `joins_at_end` has a premise that no law of these files states: that every
member's number is below the statement's number of messages. Whoever spends the theorem owes it: a
table of joints must hold it in its book-keeping in front of the block (the key file's table
does: its shapeB₃ at border 0 lists the members and counts the messages). The marks `kept` are not
stated.
Nothing on what a row, a place or a tree means. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc.Later
open VerifiableInference.Desc.Ground (adoptP elsewhereP joinP addRowP)

namespace VerifiableInference.Desc.Third.Law

/-! ## One message alone is part 0 of its tree -/

/-- A loop in Option over one member is its one step. -/
theorem foldlM_one {α β : Type} (step : β → α → Option β) (a : α) (s s' : β)
    (e : [a].foldlM step s = some s') : step s a = some s' := by
  rw [List.foldlM_cons] at e
  obtain ⟨t, ht, e2⟩ := Option.bind_eq_some_iff.mp e
  rw [List.foldlM_nil] at e2
  rw [ht, ← Option.some.inj e2]

/-- What layTrees returns as the one message's part is the number of parts that its tree held when
the two passes had run. -/
theorem layTrees_part_one {codes : Codes} {n : OracleNotice} {T : TreeLay}
    (h : layTrees codes #[n] = some T) :
    T.part = #[((Params.laidOf codes #[n]).1.getD
      ((Params.laidOf codes #[n]).2.2.getD 0 0) {}).mainSymbols.size] := by
  unfold layTrees at h
  dsimp only at h
  obtain ⟨filled, hf, h2⟩ := Option.bind_eq_some_iff.mp h
  have e1 := Params.ite_none_pure (foldlM_one _ 0 _ _ hf)
  by_cases hc : ((filled.1.map fun t =>
      if t.mainWidth == 0 then { t with logN := t.logNzk } else t).all
        fun t => t.maskWidth == 0 || decide (t.logNzk ≤ t.logN)) = true
  · rw [if_pos hc] at h2
    rw [← Option.some.inj h2, ← e1]
    rfl
  · rw [if_neg hc] at h2
    cases h2

/-- The tree that the two passes open for one message alone holds no part yet. -/
theorem laidOf_one_fresh (codes : Codes) (n : OracleNotice) :
    ((Params.laidOf codes #[n]).1.getD
      ((Params.laidOf codes #[n]).2.2.getD 0 0) {}).mainSymbols.size = 0 := by
  rw [laidOf_one]
  cases hm : (n.shape.mainRows == 0) <;>
    simp [Params.laidOf, Params.layPass, Params.layStep, hm]

/-- One message alone is laid as part 0. -/
theorem layTrees_part_zero {codes : Codes} {n : OracleNotice} {T : TreeLay}
    (h : layTrees codes #[n] = some T) : T.part.getD 0 0 = 0 := by
  rw [layTrees_part_one h, laidOf_one_fresh]
  rfl

/-! ## The plain ground's four functions and the count of roots -/

theorem elsewhereP_roots {L : Type} (d d' : DState L) (mine : Nat) (other : Statement)
    (theirs : Nat) (h : elsewhereP d mine other theirs = some d') : d'.roots = d.roots := by
  unfold elsewhereP at h
  split at h
  · cases hy : other.oracles[theirs]? with
    | none =>
      rw [hy] at h
      cases h
    | some y =>
      rw [hy] at h
      have e := Option.some.inj h
      subst e
      rfl
  · cases h

theorem joinP_roots {L : Type} (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') : d'.roots = d.roots := by
  unfold joinP at h
  split at h
  · cases hG : d.st.groups[g]? with
    | none =>
      rw [hG] at h
      cases h
    | some G =>
      rw [hG] at h
      have e := Option.some.inj h
      subst e
      rfl
  · cases h

theorem addRowP_roots {L : Type} (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : d'.roots = d.roots := by
  unfold addRowP at h
  split at h
  · have e := Option.some.inj h
    subst e
    rfl
  · cases h

/-- adoptP's yes at ONE message and ONE given tree, sharply: one tree more; one place more; the new
place is the new tree's number and part 0; the count of roots stays. -/
theorem adoptP_one_sharp {L : Type} (d : DState L) (n : OracleNotice) (num : Nat) (src : Fmt.Src)
    (a : Array Nat × DState L) (h : adoptP d #[n] #[(num, src)] = some a) :
    a.2.book.trees.size = d.book.trees.size + 1 ∧
    a.2.book.place.size = d.book.place.size + 1 ∧
    a.2.book.place[d.book.place.size]? = some (d.book.trees.size, 0) ∧
    a.2.roots = d.roots := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, hl, e⟩ := Option.map_eq_some_iff.1 h
    -- the ground names the planner's maker, or that maker taken over under a name of its own
    have hl' : layTrees d.st.codes #[n] = some lay := by
      first
        | exact hl
        | exact (VerifiableInference.Desc.Own.treesMade_eq _ _).symm.trans hl
    have k0 : lay.tree.getD 0 0 = 0 := by
      rw [layTrees_tree hl']
      exact laidOf_one _ _
    have p0 : lay.part.getD 0 0 = 0 := layTrees_part_zero hl'
    subst e
    refine ⟨?_, ?_, ?_, rfl⟩
    · simp
    · simp
    · simp only [Array.getD_eq_getD_getElem?] at k0 p0
      simp [k0, p0]
  · cases h

/-! ## The block -/

/-- **What K14's second part has laid, sharply.** s: the record in front; s': the record behind. -/
def Sharp (s s' : S₃) : Prop :=
  s'.roots = s.roots ∧
  s'.book.trees.size = s.book.trees.size + 1 ∧
  s'.book.place.size = s.book.place.size + 1 ∧
  s'.book.place[s.st.oracles.size]? = some (s.book.trees.size, 0)

theorem sharp_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    Sharp s s' := by
  obtain ⟨x, a, dot, b, _, ha, _, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  obtain ⟨q, t, y, a0, d₁, _, _, _, h0, _, h1, h2⟩ := takeOver_inv _ _ _ _ _ ha
  obtain ⟨t1, t2, t3, t4⟩ := adoptP_one_sharp _ _ _ _ _ h0
  obtain ⟨hstep, _⟩ := adoptP_one_book _ _ _ _ _ h0
  have eb : b.book = a0.2.book :=
    (addRowP_book _ _ _ _ hb).trans ((joinP_book _ _ _ _ _ h2).trans (elsewhereP_book _ _ _ _ _ h1))
  have er : b.roots = a0.2.roots :=
    (addRowP_roots _ _ _ _ hb).trans
      ((joinP_roots _ _ _ _ _ h2).trans (elsewhereP_roots _ _ _ _ _ h1))
  have hstep' : s.st.oracles.size = s.book.place.size := hstep
  refine ⟨?_, ?_, ?_, ?_⟩
  · show b.roots = _
    rw [er]
    exact t4
  · show b.book.trees.size = _
    rw [eb]
    exact t1
  · show b.book.place.size = _
    rw [eb]
    exact t2
  · show b.book.place[s.st.oracles.size]? = _
    rw [eb, hstep']
    exact t3

/-- **The same, as a property of a block.** -/
def SharpLaw {Cl : Type} (b : Block S₃ Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → Sharp s s'

theorem sharpLaw_k14Second {Cl : Type} (p : P₁₄) : SharpLaw (batchLinearConstraintsSecondPart (Cl := Cl) p) :=
  fun s rs gs s' h => sharp_k14Second p s s' rs gs h

/-! ## The row (Dot) is a plain row -/

/-- Adding placed tensors does not change a row's kind. -/
theorem addLaid_kind (o : Nat) (lay : VectorLay) : ∀ (l : List Tensor) (row : OnBytes.Row),
    (addLaid row o lay l).kind = row.kind
  | [], _ => rfl
  | t :: l, row => addLaid_kind o lay l (row.add o .main (lay.onTable t))

theorem linDotRow_plain (S : Params.LinShape) (weights : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (row : OnBytes.Row)
    (h : linDotRow S weights psi omega omegaLay w wLay = some row) : row.kind = .plain := by
  unfold linDotRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, cut, _, hrow⟩ := h
  rw [← hrow, addLaid_kind, addLaid_kind]

/-! ## Omega's copy -/

/-- **Omega's copy**: as many sample rows as Omega has in the shared statement, its shape and its
pad; sampled; no ledger; it has not served as a mask. -/
theorem omega_copy (p : P₁₄) (s s' : S₃) (h : Says p s s') :
    ∃ (x : Border) (y c : OnBytes.Oracle), s.loc.border = some x ∧
      x.shared.st.oracles[x.shared.omega]? = some y ∧
      s'.st.oracles[s.st.oracles.size]? = some c ∧
      c.sampled = true ∧ c.sampleRows.size = y.sampleRows.size ∧ c.shape = y.shape ∧
      c.pad = y.pad ∧ c.ledger.isNone = true ∧ c.spentAsMask = false := by
  obtain ⟨x, y, _, _, hx, _, hy, _, _, ho, _⟩ := h
  exact ⟨x, y, _, hx, hy, ho, rfl, by simp, rfl, rfl, rfl, rfl⟩

/-! ## Omega is the last member, where every member's number is smaller -/

theorem insert_at_end (m : Array Nat) (k : Nat) (h : ∀ i ∈ m.toList, i < k) :
    m.insertIdxIfInBounds (m.filter (· < k)).size k = m.push k := by
  rcases m with ⟨l⟩
  have hl : l.filter (fun i => decide (i < k)) = l :=
    List.filter_eq_self.2 fun a ha => decide_eq_true (h a ha)
  apply Array.toList_inj.1
  simp [hl]

/-- **Where every member of the own group has a smaller number than the new message, Omega is the
group's last member; the open rows are those in front, then (Dot), a plain row; no test has begun.**
-/
theorem joins_at_end (p : P₁₄) (s s' : S₃) (h : Says p s s')
    (hm : ∀ G : OnBytes.Group, s.st.groups[s.loc.own]? = some G →
      ∀ i ∈ G.members.toList, i < s.st.oracles.size) :
    ∃ (G G' : OnBytes.Group) (dot : OnBytes.Row), s.st.groups[s.loc.own]? = some G ∧
      s'.st.groups[s.loc.own]? = some G' ∧ G'.members = G.members.push s.st.oracles.size ∧
      G'.rows = G.rows.push dot ∧ dot.kind = .plain ∧ G'.inRun = false := by
  obtain ⟨_, _, G, dot, _, _, _, _, _, _, hG, hrun, hd, _, hg, _⟩ := h
  exact ⟨G, _, dot, hG, hg, insert_at_end _ _ (hm G hG), rfl,
    linDotRow_plain _ _ _ _ _ _ _ _ hd, hrun⟩

/-! ## The statement at the two silly members -/

/-- Sharp holds of no record and itself: the book has one tree more behind. -/
theorem sharp_irrefl (s : S₃) : ¬ Sharp s s := by
  intro h
  have t := h.2.1
  omega

theorem idle₃_not_sharp (s : S₃) : ¬ SharpLaw idle₃ :=
  fun h => sharp_irrefl s (h s [] [] s rfl)

/-- The block that says no to all meets it, as it meets every law of the form "a yes gives". -/
theorem deaf₃_sharp : SharpLaw deaf₃ :=
  fun _ _ _ _ h => (by cases h)

end VerifiableInference.Desc.Third.Law
