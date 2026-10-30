-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Book.lean: what K14's second part has laid into the last chain's book of
trees. A definition of Prop and theorems.

Main names:
  `BookSays s s'`: in the shared chain's book Omega has a place and a tree t there; behind the block
    the book has a place for Omega's number here; it is no older tree's; a tree stands there, with
    t's number and t's source. THE FRAME: every older place and tree of the book is as it was.
  `layTrees_tree`, `laidOf_one`: the planner lays one message alone into tree 0 (over
    OnBytes/Params/Fit/LayPasses.lean). The ground calls the description's own text of that maker
    (Own.treesMade); Own.treesMade_eq (Johnson/Desc/Own/TreesAgree.lean) carries it to layTrees.
  `bookSays_k14Second`.
  `idle_not_bookSays`: the block that says yes to all fails it.

Limits. The new tree's shape and parts are not stated. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Says
import OnBytes.Params.Fit.LayPasses
import Johnson.Desc.Own.TreesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc.Later
open VerifiableInference.Desc.Ground (adoptP adoptL elsewhereP joinP addRowP)

namespace VerifiableInference.Desc.Third.Law

/-! ## The plain ground's four functions and the book -/

theorem elsewhereP_book {L : Type} (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : d'.book = d.book := by
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

theorem joinP_book {L : Type} (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') : d'.book = d.book := by
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

theorem addRowP_book {L : Type} (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : d'.book = d.book := by
  unfold addRowP at h
  split at h
  · have e := Option.some.inj h
    subst e
    rfl
  · cases h

/-- A tree pushed behind an array, then one entry changed in its parts alone: what stands at or
behind the old size has the pushed tree's number and source; what stands in front is as it was, if
the changed entry is not in front. -/
theorem pushed_tree (T : Array Tree) (X : Tree) (k : Nat) (f : Tree → Tree)
    (hf : ∀ t : Tree, (f t).number = t.number ∧ (f t).src = t.src) :
    (∀ (j : Nat) (tO : Tree), ((T.push X).modify (T.size + k) f)[T.size + j]? = some tO →
      tO.number = X.number ∧ tO.src = X.src) ∧
    ∀ i : Nat, i < T.size → ((T.push X).modify (T.size + k) f)[i]? = T[i]? := by
  constructor
  · intro j tO h
    obtain ⟨t0, h0, hc⟩ := of_modify (T.push X) (T.size + k) f (T.size + j) tO h
    have e0 : t0 = X := by
      rw [Array.getElem?_push] at h0
      by_cases ej : T.size + j = T.size
      · rw [if_pos ej] at h0
        exact (Option.some.inj h0).symm
      · rw [if_neg ej, Array.getElem?_eq_none (Nat.le_add_right _ _)] at h0
        cases h0
    rcases hc with ⟨_, e⟩ | ⟨_, e⟩
    · rw [e, e0]
      exact hf X
    · rw [e, e0]
      exact ⟨rfl, rfl⟩
  · intro i hi
    have hne : T.size + k ≠ i := by omega
    have hne' : i ≠ T.size := by omega
    rw [Array.getElem?_modify, if_neg hne, Array.getElem?_push, if_neg hne']

/-- What layTrees returns as each message's tree is what the two passes leave. (After
layTrees_size.) -/
theorem layTrees_tree {codes : Codes} {sent : Array OracleNotice} {T : TreeLay}
    (h : layTrees codes sent = some T) : T.tree = (Params.laidOf codes sent).2.2 := by
  unfold layTrees at h
  dsimp only at h
  obtain ⟨filled, hf, h2⟩ := Option.bind_eq_some_iff.mp h
  by_cases hc : ((filled.1.map fun t =>
      if t.mainWidth == 0 then { t with logN := t.logNzk } else t).all
        fun t => t.maskWidth == 0 || decide (t.logNzk ≤ t.logN)) = true
  · rw [if_pos hc] at h2
    rw [← Option.some.inj h2]
    rfl
  · rw [if_neg hc] at h2
    cases h2

/-- One message alone is laid into tree 0. -/
theorem laidOf_one (codes : Codes) (n : OracleNotice) :
    ((Params.laidOf codes #[n]).2.2).getD 0 0 = 0 := by
  cases hm : (n.shape.mainRows == 0) <;>
    simp [Params.laidOf, Params.layPass, Params.layStep, hm]

/-- adoptP's yes at ONE message and ONE given tree: the book behind it. -/
theorem adoptP_one_book {L : Type} (d : DState L) (n : OracleNotice) (num : Nat) (src : Fmt.Src)
    (a : Array Nat × DState L) (h : adoptP d #[n] #[(num, src)] = some a) :
    d.st.oracles.size = d.book.place.size ∧
    (∃ (q' : Nat × Nat) (tO : Tree), a.2.book.place[d.book.place.size]? = some q' ∧
      d.book.trees.size ≤ q'.1 ∧ a.2.book.trees[q'.1]? = some tO ∧ tO.number = num ∧ tO.src = src) ∧
    (∀ i : Nat, i < d.book.place.size → a.2.book.place[i]? = d.book.place[i]?) ∧
    ∀ i : Nat, i < d.book.trees.size → a.2.book.trees[i]? = d.book.trees[i]? := by
  unfold adoptP at h
  split at h
  · rename_i hok
    have t := ok_mem hok _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hstep : d.st.oracles.size = d.book.place.size := eq_of_beq t
    cases hl : VerifiableInference.Desc.Own.treesMade d.st.codes #[n] with
    | none =>
      rw [hl] at h
      cases h
    | some lay =>
      rw [hl] at h
      have e := Option.some.inj h
      subst e
      have hp := pushed_tree d.book.trees
        { shape := lay.shapes.getD 0 {}, number := num, src := src } (lay.tree.getD 0 0)
        (fun x => { x with parts := x.parts.push (d.st.oracles.size + 0) }) (fun _ => ⟨rfl, rfl⟩)
      have hk0 : lay.tree.getD 0 0 = 0 := by
        rw [layTrees_tree ((VerifiableInference.Desc.Own.treesMade_eq _ _).symm.trans hl)]
        exact laidOf_one _ _
      have hk : ((d.book.trees.push
            { shape := lay.shapes.getD 0 {}, number := num, src := src }).modify
          (d.book.trees.size + lay.tree.getD 0 0)
          (fun x => { x with parts := x.parts.push (d.st.oracles.size + 0) }))[d.book.trees.size +
            lay.tree.getD 0 0]? =
          some { shape := lay.shapes.getD 0 {}, number := num, src := src
                 parts := (#[] : Array Nat).push (d.st.oracles.size + 0) } := by
        rw [hk0]
        have hX : (d.book.trees.push
            ({ shape := lay.shapes.getD 0 {}, number := num, src := src } :
              Tree))[d.book.trees.size +
              0]? = some { shape := lay.shapes.getD 0 {}, number := num, src := src } := by
          simp
        exact modify_same _ _ _ _ hX
      refine ⟨hstep, ⟨(d.book.trees.size + lay.tree.getD 0 0, lay.part.getD 0 0),
        { shape := lay.shapes.getD 0 {}, number := num, src := src
          parts := (#[] : Array Nat).push (d.st.oracles.size + 0) }, ?_,
        Nat.le_add_right _ _, ?_, rfl, rfl⟩, ?_, ?_⟩
      · simp
      · simpa using hk
      · intro i hi
        simp [Array.getElem?_append_left hi]
      · intro i hi
        have := hp.2 i hi
        simpa using this
  · cases h

/-! ## The block -/

/-- **What K14's second part has laid into the book.** -/
def BookSays (s s' : S₃) : Prop :=
  ∃ (x : Border) (q : Nat × Nat) (t : Tree) (q' : Nat × Nat),
    s.loc.border = some x ∧
    x.shared.book.place[x.shared.omega]? = some q ∧ x.shared.book.trees[q.1]? = some t ∧
    s.st.oracles.size = s.book.place.size ∧
    s'.book.place[s.st.oracles.size]? = some q' ∧ s.book.trees.size ≤ q'.1 ∧
    (∃ tO : Tree, s'.book.trees[q'.1]? = some tO ∧ tO.number = t.number ∧ tO.src = t.src) ∧
    (∀ i : Nat, i < s.book.place.size → s'.book.place[i]? = s.book.place[i]?) ∧
    ∀ i : Nat, i < s.book.trees.size → s'.book.trees[i]? = s.book.trees[i]?

theorem bookSays_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    BookSays s s' := by
  obtain ⟨x, a, dot, b, hx, ha, _, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  obtain ⟨q, t, y, a0, d₁, hq, ht, _, h0, _, h1, h2⟩ := takeOver_inv _ _ _ _ _ ha
  obtain ⟨hstep, ⟨q', tO, hq', hle, hO, hn, hsr⟩, fp, ft⟩ := adoptP_one_book _ _ _ _ _ h0
  have eb : b.book = a0.2.book :=
    (addRowP_book _ _ _ _ hb).trans ((joinP_book _ _ _ _ _ h2).trans (elsewhereP_book _ _ _ _ _ h1))
  have hstep' : s.st.oracles.size = s.book.place.size := hstep
  refine ⟨x, q, t, q', hx, hq, ht, hstep', ?_, hle, ?_, ?_, ?_⟩
  · show b.book.place[s.st.oracles.size]? = _
    rw [eb, hstep']
    exact hq'
  · refine ⟨tO, ?_, hn, hsr⟩
    show b.book.trees[q'.1]? = _
    rw [eb]
    exact hO
  · intro i hi
    show b.book.place[i]? = _
    rw [eb]
    exact fp i hi
  · intro i hi
    show b.book.trees[i]? = _
    rw [eb]
    exact ft i hi

/-- The idle yes-sayer fails it: where statement and book are in step no place stands at the next
free number. -/
theorem idle_not_bookSays (s : S₃) : ¬ BookSays s s := by
  intro h
  obtain ⟨_, _, _, q', _, _, _, hstep, hq', _⟩ := h
  rw [hstep, Array.getElem?_eq_none (Nat.le_refl _)] at hq'
  cases hq'

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.layTrees_tree
#print axioms VerifiableInference.Desc.Third.Law.laidOf_one
#print axioms VerifiableInference.Desc.Third.Law.pushed_tree
#print axioms VerifiableInference.Desc.Third.Law.adoptP_one_book
#print axioms VerifiableInference.Desc.Third.Law.bookSays_k14Second
#print axioms VerifiableInference.Desc.Third.Law.idle_not_bookSays
