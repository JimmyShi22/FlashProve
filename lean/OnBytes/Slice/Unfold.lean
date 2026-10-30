-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Unfold.lean: the written link's verdict, unfolded on a written transcript.

The written protocol (Run/PlanQX.lean: `skeletonOverBothExternalStrings`, with hash blocks as verifier messages) accepts if
all tests of work pass, two tests on the openings of the stored tables pass, and a decision says
yes to a view. The view holds the rounds, and the columns of the trees at the positions that the
draws ask for. Here the decision is the entry file's (Fmt/M3Dec.lean: `dec`). A proof of soundness
goes through the rounds one by one, and it needs the columns as functions of what the prover has
sent so far. The view is not of that kind: which columns it lists depends on all rounds. This file
replaces it by a view that lists every column.

Main definitions.
 `seen`      what the decision sees of a transcript and the two stored tables.
 `storedOf`  the column of a stored table at a position.
 `whole`     the view with the same rounds, every column of every tree that the transcript sends and
             every column of both stored tables.
 `joinT`     two written transcripts joined, over the joined list of rounds.
Main theorems.
 `accept_eq`      the verdict is the conjunction of the four tests, the last at `seen`.
 `seen_rounds`, `seen_own`, `seen_stored`   the rounds that the decision sees are the written
                  rounds; a column that it sees is the column of that tree, or of that stored table.
 `whole_own`, `whole_stored`   what the whole view shows, as equations.
 `colAtS_here`, `colAtS_next`, `colAtS_skip`   a tree's column, round by round.
 `iopp_mono`, `lastAt_mono`, `decBy_mono`   a yes stays a yes when a view shows more columns.
 `accept_whole`, `refuses_of_whole`   if the written protocol accepts, all tests of work pass and
                  the decision says yes at the whole view.
 `batchLit_whole`   at the whole view the batched row does not depend on the transcript.
 `rsOf_app`, `pass_joinT`, `colAtS_join_lt`, `colAtS_join_ge`   rounds, tests of work and columns
                  of a joined transcript; a tree of the first part does not depend on the second.
Not claimed. The converse of `accept_whole`: the whole view shows more than the verifier reads, so a
yes there is no yes of the written protocol. Nothing on soundness. `seen_stored` speaks of the two
stored tables alone, the numbers 0 and 1.
-/
import OnBytes.Slice.Stage
import OnBytes.Slice.Parse
import OnBytes.Slice.ColMono
import Run.PlanQX

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Run

/-! ## A list that shows a given function of two numbers -/

/-- The values of a function of two numbers at all arguments below A and B, as triples: the two
arguments, then the value. -/
def tabOf {β : Type} (A B : ℕ) (f : ℕ → ℕ → Option β) : List (ℕ × ℕ × β) :=
  (List.range A).flatMap fun n => (List.range B).filterMap fun x => (f n x).map fun c => (n, x, c)

/-- What is in the list. -/
theorem mem_tabOf {β : Type} (A B : ℕ) (f : ℕ → ℕ → Option β) (o : ℕ × ℕ × β) :
    o ∈ tabOf A B f ↔ o.1 < A ∧ o.2.1 < B ∧ f o.1 o.2.1 = some o.2.2 := by
  unfold tabOf
  constructor
  · intro h
    obtain ⟨n, hn, h⟩ := List.mem_flatMap.1 h
    obtain ⟨x, hx, h⟩ := List.mem_filterMap.1 h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨List.mem_range.1 hn, List.mem_range.1 hx, hc⟩
  · rintro ⟨h1, h2, h3⟩
    refine List.mem_flatMap.2 ⟨o.1, List.mem_range.2 h1, List.mem_filterMap.2
      ⟨o.2.1, List.mem_range.2 h2, ?_⟩⟩
    rw [h3]
    rfl

/-- Looking a pair of arguments up in the list gives the function's value, if the function has no
value outside the bounds. -/
theorem find_tabOf {β : Type} (A B : ℕ) (f : ℕ → ℕ → Option β)
    (hf : ∀ n x c, f n x = some c → n < A ∧ x < B) (n x : ℕ) :
    ((tabOf A B f).find? fun o => o.1 == n && o.2.1 == x).map (·.2.2) = f n x := by
  cases hfind : (tabOf A B f).find? fun o => o.1 == n && o.2.1 == x with
  | none =>
    cases hfx : f n x with
    | none => rfl
    | some c =>
      have hm : (n, x, c) ∈ tabOf A B f :=
        (mem_tabOf A B f _).2 ⟨(hf n x c hfx).1, (hf n x c hfx).2, hfx⟩
      have := List.find?_eq_none.1 hfind _ hm
      simp at this
  | some o =>
    have hp := List.find?_some hfind
    have hm := (mem_tabOf A B f o).1 (List.mem_of_find?_eq_some hfind)
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [← hp.1, ← hp.2, hm.2.2]
    rfl

/-! ## What the decision sees -/

section
variable (ds : List PQ.RD) (a : ℕ) (xs : List PQ.XO) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str)
  (τ : Tr (PQ.uL (ckP .two) ds))

/-- What the entry file's decision sees of a written transcript and the two stored tables: the
rounds, and the columns at the positions that the draws ask for. -/
def seen : Fmt.M3.View := Fmt.M3.ofView (Fmt.M1.ofView (PQ.viewX (ckP .two) ds a xs y τ))

/-- The column of stored table number w (0: the first table, 1: the copy) at the position x. A
symbol of a stored table is a position with a column; this is the column. -/
def storedOf (w x : ℕ) : Option (List UInt64) :=
  if h : x < 2 ^ a then
    if w = 0 then some (y.1 ⟨x, h⟩).2 else if w = 1 then some (y.2 ⟨x, h⟩).2 else none
  else none

/-- A bound on the positions of all trees of a list of rounds. -/
def posMax : List PQ.RD → ℕ
  | [] => 0
  | d :: ds => max (PQ.posN d.tree) (posMax ds)

/-- The whole view: the same rounds, with every column of every tree that the transcript sends
and every column of the two stored tables. -/
def whole : Fmt.M3.View :=
  ⟨rsOf ds τ, tabOf ds.length (posMax ds) (PQ.colAtS (ckP .two) ds τ),
    tabOf 2 (2 ^ a) (storedOf a y)⟩

/-- The written protocol's verdict, by unfolding. -/
theorem accept_eq (P : Fmt.M3.Par) (m0 : (PQ.s0 (ckP .two)).up.Msg)
    (c0 : (PQ.s0 (ckP .two)).up.Chal) :
    (PQ.skeletonOverBothExternalStrings (ckP .two) ds a xs (Fmt.M3.dec P)).up.loc.accept () y (m0, c0, τ) =
      (PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) &&
        PQ.everyOpeningHasItsDraws xs (PQ.drawnSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ)) &&
        PQ.symbolsCarryTheirPositions a ds xs (PQ.drawnSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ)) y &&
        Fmt.M3.decBy Fmt.M1.blocks P (seen ds a xs y τ)
          (Fmt.M3.batchLit P (seen ds a xs y τ))) := rfl

end

/-- A tree has a column only at a tree's number below the number of rounds and at a position below
the bound. -/
theorem colAtS_bound : ∀ (ds : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds)) (n x : ℕ)
    (c : List UInt64), PQ.colAtS (ckP .two) ds τ n x = some c → n < ds.length ∧ x < posMax ds
  | [], _, _, _, _, h => by simp [PQ.colAtS] at h
  | d :: ds, (m, c0, τ), n, x, c, h => by
    simp only [PQ.colAtS] at h
    split at h
    · split at h
      · next hn =>
        split at h
        · next hx => exact ⟨by rw [hn]; exact Nat.succ_pos _, lt_of_lt_of_le hx (le_max_left _ _)⟩
        · cases h
      · next hn =>
        have ih := colAtS_bound ds τ (n - 1) x c h
        refine ⟨?_, lt_of_lt_of_le ih.2 (le_max_right _ _)⟩
        rw [List.length_cons]
        omega
    · have ih := colAtS_bound ds τ n x c h
      exact ⟨lt_trans ih.1 (Nat.lt_succ_self _), lt_of_lt_of_le ih.2 (le_max_right _ _)⟩

/-- A stored column exists only at a table's number below 2 and at a position below the length. -/
theorem storedOf_bound (a : ℕ) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) (w x : ℕ) (c : List UInt64)
    (h : storedOf a y w x = some c) : w < 2 ∧ x < 2 ^ a := by
  unfold storedOf at h
  split at h
  · next hx =>
    split at h
    · next hw => exact ⟨by omega, hx⟩
    · split at h
      · next hw => exact ⟨by omega, hx⟩
      · cases h
  · cases h

/-- The rounds of the library's view, read as the decision reads them. -/
theorem rs_map : ∀ (ds : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds)),
    (PQ.rvSL (ckP .two) ds τ).map
      (fun r => (⟨Fmt.M1.sentOf r.vals, r.drawn.elems, r.drawn.poss⟩ : Fmt.M1.RV)) = rsOf ds τ
  | [], _ => rfl
  | d :: ds, (m, c, τ) => congrArg (rvOf d m c :: ·) (rs_map ds τ)

section
variable (ds : List PQ.RD) (a : ℕ) (xs : List PQ.XO) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str)
  (τ : Tr (PQ.uL (ckP .two) ds))

/-- The rounds that the decision sees are the written rounds. -/
theorem seen_rounds : (seen ds a xs y τ).rounds = rsOf ds τ := rs_map ds τ

/-- An entry of the view's list of columns is a column of a stored table under that table's key, or
a column of one of the transcript's own trees. -/
theorem mem_opened (o : ℕ × ℕ × List UInt64)
    (h : o ∈ (PQ.viewX (ckP .two) ds a xs y τ).opened) :
    (o.1 = 2 ^ 16 ∧ storedOf a y 0 o.2.1 = some o.2.2) ∨
    (o.1 = 2 ^ 16 + 1 ∧ storedOf a y 1 o.2.1 = some o.2.2) ∨
    (o.1 ≠ 2 ^ 16 ∧ o.1 ≠ 2 ^ 16 + 1 ∧ PQ.colAtS (ckP .two) ds τ o.1 o.2.1 = some o.2.2) := by
  simp only [PQ.viewX] at h
  obtain ⟨kx, _, hk⟩ := List.mem_filterMap.1 h
  by_cases h0 : kx.1 = PQ.storedKey false
  · rw [if_pos h0] at hk
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hk
    refine Or.inl ⟨h0, ?_⟩
    unfold PQ.xPos at hp
    split at hp
    · next hx =>
      obtain rfl := Option.some.inj hp
      show storedOf a y 0 kx.2 = _
      unfold storedOf
      rw [dif_pos hx, if_pos rfl]
      rfl
    · cases hp
  · rw [if_neg h0] at hk
    by_cases h1 : kx.1 = PQ.storedKey true
    · rw [if_pos h1] at hk
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hk
      refine Or.inr (Or.inl ⟨h1, ?_⟩)
      unfold PQ.xPos at hp
      split at hp
      · next hx =>
        obtain rfl := Option.some.inj hp
        show storedOf a y 1 kx.2 = _
        unfold storedOf
        rw [dif_pos hx, if_neg Nat.one_ne_zero, if_pos rfl]
        rfl
      · cases hp
    · rw [if_neg h1] at hk
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hk
      exact Or.inr (Or.inr ⟨h0, h1, hc⟩)

/-- A column that the decision sees of tree number n is that tree's column. -/
theorem seen_own (n x : ℕ) (w : List UInt64)
    (h : Fmt.M1.colAt (seen ds a xs y τ).own n x = some w) :
    PQ.colAtS (ckP .two) ds τ n x = some w := by
  unfold Fmt.M1.colAt at h
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h
  have hp := List.find?_some ho
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hm : o ∈ (PQ.viewX (ckP .two) ds a xs y τ).opened.filter fun o => decide (o.1 < 2 ^ 16) :=
    List.mem_of_find?_eq_some ho
  obtain ⟨hm1, hlt⟩ := List.mem_filter.1 hm
  have hlt' : o.1 < 2 ^ 16 := of_decide_eq_true hlt
  rcases mem_opened ds a xs y τ o hm1 with h1 | h1 | h1
  · omega
  · omega
  · rw [← hp.1, ← hp.2]
    exact h1.2.2

/-- A column that the decision sees of a stored table is that table's column. Stated for the
two tables' numbers 0 and 1: the view files every key from 2^16 on under the stored columns, so a
higher number could name a tree of the transcript. -/
theorem seen_stored (w x : ℕ) (hw : w < 2) (c : List UInt64)
    (h : Fmt.M3.storedAt (seen ds a xs y τ) w x = some c) : storedOf a y w x = some c := by
  unfold Fmt.M3.storedAt at h
  obtain ⟨o', ho, rfl⟩ := Option.map_eq_some_iff.1 h
  have hp := List.find?_some ho
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hm : o' ∈ ((PQ.viewX (ckP .two) ds a xs y τ).opened.filter
      fun o => decide (2 ^ 16 ≤ o.1)).map fun o => (o.1 - 2 ^ 16, o.2) :=
    List.mem_of_find?_eq_some ho
  obtain ⟨o, hmo, rfl⟩ := List.mem_map.1 hm
  obtain ⟨hm1, hge⟩ := List.mem_filter.1 hmo
  have hge' : 2 ^ 16 ≤ o.1 := of_decide_eq_true hge
  have hw1 : o.1 - 2 ^ 16 = w := hp.1
  have hx1 : o.2.1 = x := hp.2
  rcases mem_opened ds a xs y τ o hm1 with h1 | h1 | h1
  · have hw0 : w = 0 := by omega
    rw [hw0, ← hx1]
    exact h1.2
  · have hw0 : w = 1 := by omega
    rw [hw0, ← hx1]
    exact h1.2
  · omega

/-- The whole view has the written rounds. -/
theorem whole_rounds : (whole ds a y τ).rounds = rsOf ds τ := rfl

/-- The whole view shows every column of the transcript's own trees. -/
theorem whole_own (n x : ℕ) :
    Fmt.M1.colAt (whole ds a y τ).own n x = PQ.colAtS (ckP .two) ds τ n x :=
  find_tabOf _ _ _ (colAtS_bound ds τ) n x

/-- The whole view shows every column of the two stored tables. -/
theorem whole_stored (w x : ℕ) : Fmt.M3.storedAt (whole ds a y τ) w x = storedOf a y w x :=
  find_tabOf _ _ _ (storedOf_bound a y) w x

end

/-! ## The trees' columns, round by round -/

section
variable (d : PQ.RD) (ds : List PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal)
  (τ : Tr (PQ.uL (ckP .two) ds))

/-- Tree number 0 is the tree of the first round that sends one. -/
theorem colAtS_here (hd : d.tree.isSome = true) (x : ℕ) :
    PQ.colAtS (ckP .two) (d :: ds) (m, c, τ) 0 x =
      if x < PQ.posN d.tree then some (colW d m.1 x) else none := by
  simp only [PQ.colAtS, hd, if_true]
  unfold colW
  split <;> rfl

/-- After a round that sends a tree the numbers of the trees go down by one. -/
theorem colAtS_next (hd : d.tree.isSome = true) (n x : ℕ) :
    PQ.colAtS (ckP .two) (d :: ds) (m, c, τ) (n + 1) x = PQ.colAtS (ckP .two) ds τ n x := by
  simp only [PQ.colAtS, hd, if_true, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]

/-- A round that sends no tree is passed over. -/
theorem colAtS_skip (hd : d.tree.isSome = false) (n x : ℕ) :
    PQ.colAtS (ckP .two) (d :: ds) (m, c, τ) n x = PQ.colAtS (ckP .two) ds τ n x := by
  simp only [PQ.colAtS, hd, Bool.false_eq_true, if_false]

end

/-! ## Joined transcripts -/

/-- Two written transcripts, joined, as a transcript of the joined list of rounds. -/
def joinT : (ds₁ ds₂ : List PQ.RD) → Tr (PQ.uL (ckP .two) ds₁) → Tr (PQ.uL (ckP .two) ds₂) →
    Tr (PQ.uL (ckP .two) (ds₁ ++ ds₂))
  | [], _, _, b => b
  | _ :: ds₁, ds₂, (m, c, τ), b => (m, c, joinT ds₁ ds₂ τ b)

/-- The shape of a joined list of rounds is the two shapes joined. -/
theorem uL_append : ∀ ds₁ ds₂ : List PQ.RD,
    PQ.uL (ckP .two) (ds₁ ++ ds₂) = PQ.uL (ckP .two) ds₁ ++ PQ.uL (ckP .two) ds₂
  | [], _ => rfl
  | d :: ds₁, ds₂ => congrArg (wRound d :: ·) (uL_append ds₁ ds₂)

/-- One more round in front of two transcripts that are the same. -/
theorem heq_cons {r : Round} {s t : Shape} (h : s = t) (m : r.Msg) (c : r.Chal) (u : Tr s)
    (v : Tr t) (huv : HEq u v) : HEq ((m, c, u) : Tr (r :: s)) ((m, c, v) : Tr (r :: t)) := by
  subst h
  rw [eq_of_heq huv]

/-- The joined transcript is the library's. -/
theorem joinT_heq : ∀ (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁))
    (b : Tr (PQ.uL (ckP .two) ds₂)), HEq (joinT ds₁ ds₂ τ b) (Tr.app τ b)
  | [], _, _, _ => HEq.rfl
  | _ :: ds₁, ds₂, (m, c, τ), b =>
    heq_cons (uL_append ds₁ ds₂) m c _ _ (joinT_heq ds₁ ds₂ τ b)

/-- The rounds of a joined transcript are the rounds of its parts. -/
theorem rsOf_joinT : ∀ (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁))
    (b : Tr (PQ.uL (ckP .two) ds₂)),
    rsOf (ds₁ ++ ds₂) (joinT ds₁ ds₂ τ b) = rsOf ds₁ τ ++ rsOf ds₂ b
  | [], _, _, _ => rfl
  | d :: ds₁, ds₂, (m, c, τ), b => congrArg (rvOf d m c :: ·) (rsOf_joinT ds₁ ds₂ τ b)

/-- The rounds of a joined transcript. At closed lists of rounds the hypothesis is HEq.rfl. -/
theorem rsOf_app (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁))
    (b : Tr (PQ.uL (ckP .two) ds₂)) (τ' : Tr (PQ.uL (ckP .two) (ds₁ ++ ds₂)))
    (h : HEq τ' (Tr.app τ b)) : rsOf (ds₁ ++ ds₂) τ' = rsOf ds₁ τ ++ rsOf ds₂ b := by
  rw [eq_of_heq (h.trans (joinT_heq ds₁ ds₂ τ b).symm)]
  exact rsOf_joinT ds₁ ds₂ τ b

/-- All tests of work of a joined transcript pass if and only if they pass in both parts. -/
theorem pass_joinT : ∀ (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁))
    (b : Tr (PQ.uL (ckP .two) ds₂)),
    PQ.passSL (ckP .two) (ds₁ ++ ds₂) (PQ.rhoSL (ckP .two) (ds₁ ++ ds₂) (joinT ds₁ ds₂ τ b)) =
      (PQ.passSL (ckP .two) ds₁ (PQ.rhoSL (ckP .two) ds₁ τ) &&
        PQ.passSL (ckP .two) ds₂ (PQ.rhoSL (ckP .two) ds₂ b))
  | [], _, _, _ => (Bool.true_and _).symm
  | d :: ds₁, ds₂, (m, c, τ), b => by
    show (GChal.pass (b := d.entry.work) c && PQ.passSL (ckP .two) (ds₁ ++ ds₂)
      (PQ.rhoSL (ckP .two) (ds₁ ++ ds₂) (joinT ds₁ ds₂ τ b))) =
      (GChal.pass (b := d.entry.work) c && PQ.passSL (ckP .two) ds₁ (PQ.rhoSL (ckP .two) ds₁ τ) &&
        PQ.passSL (ckP .two) ds₂ (PQ.rhoSL (ckP .two) ds₂ b))
    rw [pass_joinT ds₁ ds₂ τ b, Bool.and_assoc]

/-- The number of trees that a list of rounds sends. -/
def nTrees : List PQ.RD → ℕ
  | [] => 0
  | d :: ds => (if d.tree.isSome then 1 else 0) + nTrees ds

/-- A tree of the first part does not depend on the second part. -/
theorem colAtS_join_lt : ∀ (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁))
    (b : Tr (PQ.uL (ckP .two) ds₂)) (n x : ℕ), n < nTrees ds₁ →
    PQ.colAtS (ckP .two) (ds₁ ++ ds₂) (joinT ds₁ ds₂ τ b) n x = PQ.colAtS (ckP .two) ds₁ τ n x
  | [], _, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | d :: ds₁, ds₂, (m, c, τ), b, n, x, hn => by
    show PQ.colAtS (ckP .two) (d :: (ds₁ ++ ds₂)) (m, c, joinT ds₁ ds₂ τ b) n x =
      PQ.colAtS (ckP .two) (d :: ds₁) (m, c, τ) n x
    cases hd : d.tree.isSome with
    | false =>
      rw [colAtS_skip _ _ _ _ _ hd, colAtS_skip _ _ _ _ _ hd]
      refine colAtS_join_lt ds₁ ds₂ τ b n x ?_
      simpa [nTrees, hd] using hn
    | true =>
      cases n with
      | zero => rw [colAtS_here _ _ _ _ _ hd, colAtS_here _ _ _ _ _ hd]
      | succ n =>
        rw [colAtS_next _ _ _ _ _ hd, colAtS_next _ _ _ _ _ hd]
        refine colAtS_join_lt ds₁ ds₂ τ b n x ?_
        simp only [nTrees, hd, if_true] at hn
        omega

/-- The trees of the second part follow those of the first. -/
theorem colAtS_join_ge : ∀ (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁))
    (b : Tr (PQ.uL (ckP .two) ds₂)) (n x : ℕ),
    PQ.colAtS (ckP .two) (ds₁ ++ ds₂) (joinT ds₁ ds₂ τ b) (nTrees ds₁ + n) x =
      PQ.colAtS (ckP .two) ds₂ b n x
  | [], ds₂, _, b, n, x => by
    show PQ.colAtS (ckP .two) ds₂ b (0 + n) x = _
    rw [Nat.zero_add]
  | d :: ds₁, ds₂, (m, c, τ), b, n, x => by
    show PQ.colAtS (ckP .two) (d :: (ds₁ ++ ds₂)) (m, c, joinT ds₁ ds₂ τ b)
      (nTrees (d :: ds₁) + n) x = _
    cases hd : d.tree.isSome with
    | false =>
      have hn : nTrees (d :: ds₁) + n = nTrees ds₁ + n := by simp [nTrees, hd]
      rw [colAtS_skip _ _ _ _ _ hd, hn]
      exact colAtS_join_ge ds₁ ds₂ τ b n x
    | true =>
      have hn : nTrees (d :: ds₁) + n = nTrees ds₁ + n + 1 := by
        simp only [nTrees, hd, if_true]
        omega
      rw [hn, colAtS_next _ _ _ _ _ hd]
      exact colAtS_join_ge ds₁ ds₂ τ b n x

/-! ## The decision keeps its yes when more columns are shown -/

section
open Fmt.M1

/-- If a view shows more columns, it shows more of whatever is cut from a tree's columns. -/
theorem below_bind {α : Type} (V V' : View)
    (h : ∀ n x w, colAt V n x = some w → colAt V' n x = some w) (tree : ℕ)
    (g : List UInt64 → Option α) :
    Below (fun x => (colAt V tree x).bind g) (fun x => (colAt V' tree x).bind g) := by
  intro x w hw
  obtain ⟨c, hc, hg⟩ := Option.bind_eq_some_iff.1 hw
  show (colAt V' tree x).bind g = some w
  rw [h _ _ _ hc]
  exact hg

/-- Showing more is kept under a map of the values. -/
theorem below_map {α β : Type} (c c' : ℕ → Option α) (h : Below c c') (g : α → β) :
    Below (fun x => (c x).map g) (fun x => (c' x).map g) := by
  intro x w hw
  obtain ⟨u, hu, hg⟩ := Option.map_eq_some_iff.1 hw
  show (c' x).map g = some w
  rw [h _ _ hu]
  exact congrArg some hg

/-- The same for the columns of the last tree. -/
theorem below_lastCol (V V' : View)
    (h : ∀ n x w, colAt V n x = some w → colAt V' n x = some w) (tree : ℕ) :
    Below (lastCol V tree) (lastCol V' tree) := by
  intro x w hw
  unfold lastCol at hw ⊢
  cases hc : colAt V tree x with
  | none =>
    rw [hc] at hw
    simp at hw
  | some c =>
    rw [hc] at hw
    rw [h _ _ _ hc]
    exact hw

/-- The proximity test keeps its yes when more columns are shown. -/
theorem iopp_mono (f : Fmt.Fld) (V V' : View)
    (h : ∀ n x w, colAt V n x = some w → colAt V' n x = some w) :
    ∀ (st : List Stage) (tree mF mE : ℕ) (G : GRow) (rs : Rs),
      iopp blocks f V st tree mF mE G rs = true → iopp blocks f V' st tree mF mE G rs = true
  | [], _, _, _, _, _, hy => by simp [iopp] at hy
  | [s], tree, mF, mE, G, rs, hy => by
    obtain ⟨tauS, lam, ps, rs1, v, h1, h2, h3⟩ := (iopp_base_iff _ _ _ _ _ _ _ _ _).1 hy
    exact (iopp_base_iff _ _ _ _ _ _ _ _ _).2 ⟨tauS, lam, ps, rs1, v, h1, h2,
      baseOK_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (below_lastCol V V' h tree) h3⟩
  | s :: s' :: more, tree, mF, mE, G, rs, hy => by
    obtain ⟨sigma, eps, ps, rs1, qs, g, rs2, z, beta, rs3, alpha, theta, xs, rs4, G', h1, h2, h3,
      h4, h5, h6⟩ := (iopp_step_iff _ _ _ _ _ _ _ _ _ _ _).1 hy
    exact (iopp_step_iff _ _ _ _ _ _ _ _ _ _ _).2 ⟨sigma, eps, ps, rs1, qs, g, rs2, z, beta, rs3,
      alpha, theta, xs, rs4, G', h1, h2, h3, h4,
      csStep_mono _ _ _ _ _ _ _ _ _ (below_bind V V' h tree _) _ h5,
      iopp_mono f V V' h (s' :: more) _ _ _ _ _ h6⟩

/-- The same for the test on a group. -/
theorem lastAt_mono (f : Fmt.Fld) (V V' : View)
    (h : ∀ n x w, colAt V n x = some w → colAt V' n x = some w) (st : List Stage)
    (ms : List Fmt.M2.Mem) (fresh tree : ℕ) (G : GRow) (rs : Rs)
    (hy : Fmt.M2.lastAt blocks f st ms fresh tree V G rs = true) :
    Fmt.M2.lastAt blocks f st ms fresh tree V' G rs = true := by
  match st, hy with
  | [], hy => simp [Fmt.M2.lastAt] at hy
  | [_], hy => simp [Fmt.M2.lastAt] at hy
  | s :: s' :: more, hy =>
    obtain ⟨sigma, eps, ps, rs1, qs, g, rs2, z, beta, rs3, alpha, theta, xs, rs4, G', h1, h2, h3,
      h4, h5, h6⟩ := (lastAt_iff _ _ _ _ _ _ _ _ _ _ _).1 hy
    exact (lastAt_iff _ _ _ _ _ _ _ _ _ _ _).2 ⟨sigma, eps, ps, rs1, qs, g, rs2, z, beta, rs3,
      alpha, theta, xs, rs4, G', h1, h2, h3, h4,
      csStep_mono _ _ _ _ _ _ _ _ _ (below_map _ _ (below_bind V V' h tree _) _) _ h5,
      iopp_mono f V V' h (s' :: more) _ _ _ _ _ h6⟩

/-- The decision keeps its yes when more columns are shown. -/
theorem decBy_mono (P : Fmt.M3.Par) (V V' : Fmt.M3.View) (hr : V'.rounds = V.rounds)
    (ho : ∀ n x w, colAt V.own n x = some w → colAt V'.own n x = some w)
    (hs : ∀ w x c, w < 2 → Fmt.M3.storedAt V w x = some c → Fmt.M3.storedAt V' w x = some c)
    (hy : Fmt.M3.decBy blocks P V (Fmt.M3.batchLit P V) = true) :
    Fmt.M3.decBy blocks P V' (Fmt.M3.batchLit P V') = true := by
  obtain ⟨hsz, vg, rs1, z, beta, rs2, y0, yj, e3, p3, rs3, vx, rs4, vp, rs5, s6, theta, p6, rs6, R,
    h1, h2, h3, h4, h5, h6, h7, h8⟩ := (decBy_iff _ _ _ _).1 hy
  exact (decBy_iff _ _ _ _).2 ⟨hsz, vg, rs1, z, beta, rs2, y0, yj, e3, p3, rs3, vx, rs4, vp, rs5,
    s6, theta, p6, rs6, R, hr ▸ h1, h2, h3, h4, h5, h6,
    batchLit_mono P V V' hs _ _ _ _ _ _ _ _ R h7, lastAt_mono _ _ _ ho _ _ _ _ _ _ h8⟩

end

/-- The rows of the draws depend on a view's stored columns alone. -/
theorem colRows_stored (P : Fmt.M3.Par) (V V' : Fmt.M3.View) (h : V.stored = V'.stored)
    (gamma : List Fmt.M1.E) : ∀ l : List (ℕ × ℕ),
    Fmt.M3.colRows P V gamma l = Fmt.M3.colRows P V' gamma l
  | [] => rfl
  | (w, x) :: l => by
    simp only [Fmt.M3.colRows, Fmt.M3.storedAt, h, colRows_stored P V V' h gamma l]

/-- The batched row depends on a view's stored columns alone. -/
theorem batchLit_stored (P : Fmt.M3.Par) (V V' : Fmt.M3.View) (h : V.stored = V'.stored) :
    Fmt.M3.batchLit P V = Fmt.M3.batchLit P V' := by
  funext gamma z beta y0 yj xs phi theta
  simp only [Fmt.M3.batchLit, Fmt.M3.rowsLit, colRows_stored P V V' h]

/-- At the whole view the batched row does not depend on the transcript. -/
theorem batchLit_whole (P : Fmt.M3.Par) (ds : List PQ.RD) (a : ℕ)
    (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) (τ : Tr (PQ.uL (ckP .two) ds)) :
    Fmt.M3.batchLit P (whole ds a y τ) = Fmt.M3.batchLit P (whole [] a y ()) :=
  batchLit_stored P _ _ rfl

/-- The decision, unfolded. If the written protocol accepts, all tests of work pass and the
decision says yes at the whole view. -/
theorem accept_whole (ds : List PQ.RD) (a : ℕ) (xs : List PQ.XO)
    (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) (τ : Tr (PQ.uL (ckP .two) ds)) (P : Fmt.M3.Par)
    (m0 : (PQ.s0 (ckP .two)).up.Msg) (c0 : (PQ.s0 (ckP .two)).up.Chal)
    (h : (PQ.skeletonOverBothExternalStrings (ckP .two) ds a xs (Fmt.M3.dec P)).up.loc.accept () y (m0, c0, τ) = true) :
    PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = true ∧
      Fmt.M3.decBy Fmt.M1.blocks P (whole ds a y τ)
        (Fmt.M3.batchLit P (whole ds a y τ)) = true := by
  rw [accept_eq] at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1.1.1, decBy_mono P (seen ds a xs y τ) (whole ds a y τ) (seen_rounds ds a xs y τ).symm
    (fun n x w hw => ?_) (fun w x c hw hc => ?_) h.2⟩
  · rw [whole_own]
    exact seen_own ds a xs y τ n x w hw
  · rw [whole_stored]
    exact seen_stored ds a xs y τ w x hw c hc

/-- The same, read the other way: the written protocol refuses if a test of work fails or the
decision says no at the whole view. -/
theorem refuses_of_whole (ds : List PQ.RD) (a : ℕ) (xs : List PQ.XO)
    (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) (τ : Tr (PQ.uL (ckP .two) ds)) (P : Fmt.M3.Par)
    (m0 : (PQ.s0 (ckP .two)).up.Msg) (c0 : (PQ.s0 (ckP .two)).up.Chal)
    (h : (PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) &&
      Fmt.M3.decBy Fmt.M1.blocks P (whole ds a y τ) (Fmt.M3.batchLit P (whole ds a y τ))) = false) :
    (PQ.skeletonOverBothExternalStrings (ckP .two) ds a xs (Fmt.M3.dec P)).up.loc.accept () y (m0, c0, τ) = false := by
  refine Bool.eq_false_iff.2 fun hacc => ?_
  obtain ⟨h1, h2⟩ := accept_whole ds a xs y τ P m0 c0 hacc
  rw [h1, h2] at h
  cases h


end OnBytes.Slice

#print axioms OnBytes.Slice.accept_eq
#print axioms OnBytes.Slice.seen_rounds
#print axioms OnBytes.Slice.seen_own
#print axioms OnBytes.Slice.seen_stored
#print axioms OnBytes.Slice.whole_own
#print axioms OnBytes.Slice.whole_stored
#print axioms OnBytes.Slice.colAtS_here
#print axioms OnBytes.Slice.colAtS_next
#print axioms OnBytes.Slice.colAtS_skip
#print axioms OnBytes.Slice.rsOf_app
#print axioms OnBytes.Slice.pass_joinT
#print axioms OnBytes.Slice.colAtS_join_lt
#print axioms OnBytes.Slice.colAtS_join_ge
#print axioms OnBytes.Slice.iopp_mono
#print axioms OnBytes.Slice.lastAt_mono
#print axioms OnBytes.Slice.decBy_mono
#print axioms OnBytes.Slice.batchLit_whole
#print axioms OnBytes.Slice.accept_whole
#print axioms OnBytes.Slice.refuses_of_whole
