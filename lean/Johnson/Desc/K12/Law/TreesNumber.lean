-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.G.RoundsOfPlan
/-
Johnson/Desc/K12/Law/TreesNumber.lean: THE NUMBERING LAW OF treesSent (Johnson/G/RoundsOfPlan.lean): A TREE's NUMBER IN A CHAIN IS BELOW THE COUNT OF ROOTS OF THE ROUNDS IN FRONT OF INDEX i JUST WHERE THE TREE IS SENT IN A ROUND IN FRONT OF i. It reads the maker's text alone. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  made_getD        the maker's array of counts holds, at i, how many trees have the round i
  sorted_front     in a list sorted by a key, member number n has its key below i just where n is below the count of members with a key below i
  countP_lt_succ · countP_lt_sum   that count is the sum of the counts a round
  treesSent_front  treesSent at_ c P extra = .ok ts · i ≤ P.rounds.length · (t, n) ∈ ts ⇒ (t.round < i ↔ n < ((P.rounds.take i).map (·.roots)).sum)
HOW: treesSent sorts the trees by their rounds (mergeSort), refuses unless each round has as many trees as its entry has roots, and numbers them in that order (zipIdx).
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Made
open OnBytes OnBytes.Params Johnson.G.OfPlan

theorem made_getD : ∀ (ts : List Sent) (A : Array Nat) (i : Nat), i < A.size →
    (ts.foldl (fun (n : Array Nat) t => n.modify t.round (· + 1)) A).getD i 0 =
      A.getD i 0 + ts.countP (fun t => t.round == i)
  | [], A, i, _ => by simp
  | t :: ts, A, i, hi => by
    rw [List.foldl_cons, made_getD ts (A.modify t.round (· + 1)) i (by rw [Array.size_modify]; exact hi),
      List.countP_cons]
    have e : (A.modify t.round (· + 1)).getD i 0 =
        A.getD i 0 + (if (t.round == i) = true then 1 else 0) := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
      by_cases c : t.round = i
      · subst c
        simp [Array.getElem?_eq_getElem hi]
      · simp [c]
    rw [e]
    omega

theorem sorted_front {α : Type} (k : α → Nat) (i : Nat) : ∀ (l : List α),
    l.Pairwise (fun a b => k a ≤ k b) → ∀ (n : Nat) (t : α), l[n]? = some t →
      (k t < i ↔ n < l.countP fun a => decide (k a < i))
  | [], _, n, t, h => by simp at h
  | a :: l, hp, n, t, h => by
    rw [List.pairwise_cons] at hp
    rw [List.countP_cons]
    by_cases c : k a < i
    · simp only [c, decide_true, if_true]
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        simp [c]
      | succ n =>
        rw [List.getElem?_cons_succ] at h
        rw [sorted_front k i l hp.2 n t h]
        omega
    · have h0 : l.countP (fun a => decide (k a < i)) = 0 := by
        rw [List.countP_eq_zero]
        intro b hb
        have := hp.1 b hb
        simp only [decide_eq_true_eq]
        omega
      simp only [c, decide_false, Bool.false_eq_true, if_false, h0, Nat.add_zero, Nat.not_lt_zero,
        iff_false]
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact c
      | succ n =>
        rw [List.getElem?_cons_succ] at h
        have := hp.1 t (List.mem_of_getElem? h)
        omega

theorem countP_lt_succ {α : Type} (k : α → Nat) (i : Nat) : ∀ l : List α,
    l.countP (fun a => decide (k a < i + 1)) =
      l.countP (fun a => decide (k a < i)) + l.countP (fun a => k a == i)
  | [] => rfl
  | a :: l => by
    rw [List.countP_cons, List.countP_cons, List.countP_cons, countP_lt_succ k i l]
    by_cases c1 : k a < i
    · have c2 : k a < i + 1 := by omega
      have c3 : ¬ k a = i := by omega
      simp [c1, c2, c3]
      omega
    · by_cases c3 : k a = i
      · simp [c3]
        omega
      · have c2 : ¬ k a < i + 1 := by omega
        simp [c1, c2, c3]

/-- Where each round below the list's length has as many members as its entry has roots. -/
theorem countP_lt_sum (ts : List Sent) (es : List Fmt.Entry)
    (h : ∀ j (e : Fmt.Entry), es[j]? = some e → ts.countP (fun t => t.round == j) = e.roots) :
    ∀ i, i ≤ es.length →
      ts.countP (fun t => decide (t.round < i)) = ((es.take i).map (·.roots)).sum
  | 0, _ => by simp
  | i + 1, hi => by
    have hlt : i < es.length := by omega
    rw [countP_lt_succ (fun t : Sent => t.round) i ts, countP_lt_sum ts es h i (by omega),
      h i es[i] (List.getElem?_eq_getElem hlt), List.take_add_one, List.getElem?_eq_getElem hlt,
      List.map_append, List.sum_append]
    simp


theorem treesSent_front {at_ : String} {c : Johnson.G.ChainSends} {P : Fmt.Plan} {extra : List Sent}
    {ts : List (Sent × Nat)} (h : treesSent at_ c P extra = .ok ts) (i : Nat)
    (hi : i ≤ P.rounds.length) (t : Sent) (n : Nat) (hm : (t, n) ∈ ts) :
    t.round < i ↔ n < ((P.rounds.take i).map (·.roots)).sum := by
  unfold treesSent at h
  dsimp only at h
  cases hl : c.sends.mapM (sentAt at_ c.codes (P.entries.length - P.rounds.length)) with
  | error e => rw [hl] at h; cases h
  | ok l =>
    rw [hl] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hfind
      split at h
      swap
      · cases h
      · cases h
        have hsort : ((l.flatten ++ extra).mergeSort fun a b => decide (a.round ≤ b.round)).Pairwise
            (fun a b => a.round ≤ b.round) := by
          have := List.pairwise_mergeSort (le := fun a b : Sent => decide (a.round ≤ b.round))
            (fun a b c h1 h2 => by
              simp only [decide_eq_true_eq] at h1 h2 ⊢
              omega)
            (fun a b => by
              simp only [Bool.or_eq_true, decide_eq_true_eq]
              omega) (l.flatten ++ extra)
          exact this.imp fun h => of_decide_eq_true h
        have hn : ((l.flatten ++ extra).mergeSort fun a b => decide (a.round ≤ b.round))[n]? =
            some t := by
          have := List.mem_zipIdx_iff_getElem?.1 hm
          simpa using this
        rw [sorted_front (fun t : Sent => t.round) i _ hsort n t hn]
        rw [countP_lt_sum _ P.rounds ?_ i hi]
        intro j e he
        have hj : j < P.rounds.length := (List.getElem?_eq_some_iff.1 he).1
        have h0 := List.find?_eq_none.1 hfind (e, j) (List.mem_zipIdx_iff_getElem?.2 (by simpa using he))
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h0
        rw [made_getD _ _ j (by rw [Array.size_replicate]; exact hj)] at h0
        simpa [Array.getD_eq_getD_getElem?, hj] using h0

end H2K.Made

#print axioms H2K.Made.treesSent_front
