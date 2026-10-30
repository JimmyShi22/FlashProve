-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Lent.lean: through what the functions that give a part its
coins read a run's coins (Honest/Frame.lean: `lend`, `lendPart`, `cutAll`): through the look-up at
the part's own address and through the cuts of the entries that name it as their spender, and
through nothing else; and which chain's look-up sees which owner. No run of a protocol occurs here.

  1  `Cs.cut_some`, `cutAll_some`, `cutAll_cuts`   cuts within the count; two coins with the same
     tuple of cuts have each cut in common
  2  `lend_congr`, `lendPart_congr`   `lend` and `lendPart` at two look-ups
  3  `dueAt_none`, `dueAt_left`, `dueAt_right`   a count looked up in concatenated tables
  4  `findIdx_ge`, `Addr.not_before`   a part whose place is not in an initial segment of the order
     is not before a part whose place is in it
  5  `ProverCoinCounts.keptIn` (the book's ninth test), `placesAt`, `ProverCoinCounts.visible`   an entry's spender is in
     its owner's chain or in the second chain: so its chain's look-up sees the owner's row

Limits.
  * Hypotheses that the prose above does not name: `ProverCoinCounts.word … = none` (every test on the book
    passes): `ProverCoinCounts.keptIn`, `ProverCoinCounts.visible`; `FileDescription.placesOk` (the library's executable test):
    `ProverCoinCounts.visible`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowLens
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi V W X : Type}

/-! ## 1 Cuts -/

theorem Cs.cut_some {d : Due} (c : Cs d) {a n : Due}
    (h : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e) : ∃ y, c.cut a n = some y :=
  ⟨_, dif_pos h⟩

theorem cutAll_some {d : Due} (c : Cs d) : ∀ es : List Ahead,
    (∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e) →
    ∃ y, cutAll c es = some y
  | [], _ => ⟨(), rfl⟩
  | a :: es, h => by
    obtain ⟨x, hx⟩ := Cs.cut_some c (h a (List.mem_cons.2 (Or.inl rfl)))
    obtain ⟨y, hy⟩ := cutAll_some c es fun e he => h e (List.mem_cons_of_mem _ he)
    refine ⟨(x, y), ?_⟩
    show (c.cut a.start a.count).bind (fun x => (cutAll c es).map fun y => (x, y)) = some (x, y)
    rw [hx, hy]
    rfl

/-- Two coins with the same tuple of cuts have each cut in common. -/
theorem cutAll_cuts {d : Due} (c c' : Cs d) : ∀ es : List Ahead,
    (∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e) →
    cutAll c es = cutAll c' es → ∀ e ∈ es, c.cut e.start e.count = c'.cut e.start e.count
  | [], _, _, _, he => by cases he
  | a :: es, hin, h, e, he => by
    have hin' : ∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e :=
      fun e he => hin e (List.mem_cons_of_mem _ he)
    obtain ⟨x, hx⟩ := Cs.cut_some c (hin a (List.mem_cons.2 (Or.inl rfl)))
    obtain ⟨x', hx'⟩ := Cs.cut_some c' (hin a (List.mem_cons.2 (Or.inl rfl)))
    obtain ⟨y, hy⟩ := cutAll_some c es hin'
    obtain ⟨y', hy'⟩ := cutAll_some c' es hin'
    have e1 : cutAll c (a :: es) = some (x, y) := by
      show (c.cut a.start a.count).bind (fun x => (cutAll c es).map fun y => (x, y)) = some (x, y)
      rw [hx, hy]
      rfl
    have e2 : cutAll c' (a :: es) = some (x', y') := by
      show (c'.cut a.start a.count).bind (fun x => (cutAll c' es).map fun y => (x, y)) =
        some (x', y')
      rw [hx', hy']
      rfl
    rw [e1, e2] at h
    have h2 := Option.some.inj h
    have hxx : x = x' :=
      congrArg (fun t : Cs a.count × CsAll (es.map Ahead.named) => t.1) h2
    have hyy : y = y' :=
      congrArg (fun t : Cs a.count × CsAll (es.map Ahead.named) => t.2) h2
    rcases List.mem_cons.1 he with rfl | he
    · rw [hx, hx', hxx]
    · exact cutAll_cuts c c' es hin' (by rw [hy, hy', hyy]) e he

/-! ## 2 `lend` and `lendPart` at two look-ups -/

theorem lend_congr (look look' : Addr → (d : Due) × Cs d) :
    ∀ (ds : List (String × Due)) (es : List Ahead),
    (∀ e ∈ es, (look e.owner).2.cut e.start e.count = (look' e.owner).2.cut e.start e.count) →
    lend look ds es = lend look' ds es
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | (dn, dc) :: ds, a :: l, h => by
    have ih := lend_congr look look' ds l fun e he => h e (List.mem_cons_of_mem _ he)
    have h0 := h a (List.mem_cons.2 (Or.inl rfl))
    simp only [lend]
    by_cases hn : (a.name != dn) = true
    · simp only [if_pos hn]
    · by_cases hc : (a.count != dc) = true
      · simp only [if_neg hn, if_pos hc]
      · have hcd : a.count = dc := by simpa using hc
        subst hcd
        simp only [if_neg hn, if_neg hc]
        rw [h0, ih]

/-- **`lendPart` reads the coins at the part's own address, and through the cuts of the entries that
name it as their spender.** -/
theorem lendPart_congr (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look look' : Addr → (d : Due) × Cs d) (a : Addr) (p : Part V W X) (ha : look a = look' a)
    (he : ∀ e ∈ B.ahead, e.spender = a →
      (look e.owner).2.cut e.start e.count = (look' e.owner).2.cut e.start e.count) :
    lendPart B rows look a p = lendPart B rows look' a p := by
  have h1 : ∀ P : Ahead → Bool, ∀ e ∈ (B.ahead.filter fun e => e.spender == a).filter P,
      (look e.owner).2.cut e.start e.count = (look' e.owner).2.cut e.start e.count := by
    intro P e he'
    have h2 := List.mem_filter.1 (List.mem_filter.1 he').1
    exact he e h2.1 (beq_iff_eq.1 h2.2)
  simp only [lendPart]
  rw [ha, lend_congr look look' p.spends _ (h1 fun e => e.once),
    lend_congr look look' p.carries _ (h1 fun e => !e.once)]

/-! ## 3 A count, in concatenated tables -/

theorem dueAt_none : ∀ (l : List (Addr × Due)) (a : Addr),
    l.any (fun r => r.1 == a) = false → dueAt l a = ⟨0, 0⟩
  | [], _, _ => rfl
  | r :: l, a, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    rw [dueAt_cons, if_neg (beq_eq_false_iff_ne.1 h.1)]
    exact dueAt_none l a h.2

theorem dueAt_left : ∀ (l₁ l₂ : List (Addr × Due)) (a : Addr),
    l₁.any (fun r => r.1 == a) = false → dueAt (l₁ ++ l₂) a = dueAt l₂ a
  | [], _, _, _ => rfl
  | r :: l₁, l₂, a, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    rw [List.cons_append, dueAt_cons, if_neg (beq_eq_false_iff_ne.1 h.1)]
    exact dueAt_left l₁ l₂ a h.2

theorem dueAt_right : ∀ (l₁ l₂ : List (Addr × Due)) (a : Addr),
    l₂.any (fun r => r.1 == a) = false → dueAt (l₁ ++ l₂) a = dueAt l₁ a
  | [], l₂, a, h => dueAt_none l₂ a h
  | r :: l₁, l₂, a, h => by
    rw [List.cons_append, dueAt_cons, dueAt_cons, dueAt_right l₁ l₂ a h]

/-! ## 4 The order -/

section
variable {α : Type} [BEq α] [LawfulBEq α]

/-- What a list does not hold has its first index after the list. -/
theorem findIdx_ge (x : α) (l₂ : List α) : ∀ l₁ : List α, x ∉ l₁ →
    l₁.length ≤ (l₁ ++ l₂).findIdx (· == x)
  | [], _ => Nat.zero_le _
  | y :: l₁, h => by
    have hy : (y == x) = false := beq_eq_false_iff_ne.2 fun e => h (List.mem_cons.2 (Or.inl e.symm))
    have ih := findIdx_ge x l₂ l₁ fun hx => h (List.mem_cons_of_mem _ hx)
    simp only [List.cons_append, List.findIdx_cons, hy, cond_false, List.length_cons]
    omega

end

/-- A part whose place is not in an initial segment of the order is not before one whose place is in
it. -/
theorem Addr.not_before {l₁ l₂ : List Place} {a b : Addr} (ha : a.place ∈ l₁)
    (hb : b.place ∉ l₁) : b.before (l₁ ++ l₂) a = false := by
  unfold Addr.before
  have h1 := findIdx_lt a.place l₂ l₁ ha
  have h2 := findIdx_ge b.place l₂ l₁ hb
  have hne : (b.place == a.place) = false := beq_eq_false_iff_ne.2 fun e => hb (by rw [e]; exact ha)
  rw [hne, Bool.false_and, Bool.or_false, decide_eq_false_iff_not]
  omega

/-! ## 5 Which chain sees which owner -/

/-- The places of the chain number ch, from 0. -/
def placesAt (F : FileDescription Xi) (ch : Nat) : List Place :=
  if ch == 0 then F.first.blocksInOrder.map (·.place)
  else if ch == 1 then F.shared.blocksInOrder.map (·.place) else F.second.blocksInOrder.map (·.place)

section
variable {F : FileDescription Xi} {B : ProverCoinCounts}

/-- The ninth test: a coin of the shared chain is spent inside it alone. -/
theorem ProverCoinCounts.keptIn (h : B.word F = none) : ∀ e ∈ B.ahead, e.once = true →
    e.owner.place ∈ F.shared.blocksInOrder.map (·.place) →
    e.spender.place ∈ F.shared.blocksInOrder.map (·.place) := by
  have t := ProverCoinCounts.tests h
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨-, -, -, -, -, -, -, -, t9, -⟩ := t
  intro e he h1 h2
  have := List.all_eq_true.1 t9 e he
  rw [h1, List.contains_iff_mem.2 h2] at this
  by_contra hn
  have hc : (F.shared.blocksInOrder.map (·.place)).contains e.spender.place = false := by
    cases hh : (F.shared.blocksInOrder.map (·.place)).contains e.spender.place with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.1 hh) hn
  rw [hc] at this
  cases this

/-- **An entry's spender is in its owner's chain or in the second chain.** `t`, `c`: the numbers,
from 0, of chains in which the owner's and the spender's places are. -/
theorem ProverCoinCounts.visible (h : B.word F = none) (hp : F.placesOk = true) {e : Ahead} (he : e ∈ B.ahead)
    {t c : Nat} (ht : t = 0 ∨ t = 1 ∨ t = 2) (hc : c = 0 ∨ c = 1 ∨ c = 2)
    (ho : e.owner.place ∈ placesAt F t) (hs : e.spender.place ∈ placesAt F c) : c = t ∨ c = 2 := by
  have hb := ProverCoinCounts.behind h e he
  have c1 := chain_first hp
  have c2 := chain_shared hp
  have c3 := chain_second hp
  have n1 : ∀ q : Place, q.chain ≠ 1 → q ∉ F.first.blocksInOrder.map (·.place) := fun q hq hm => hq (c1 q hm)
  have n12 : ∀ q : Place, q.chain = 3 →
      q ∉ F.first.blocksInOrder.map (·.place) ++ F.shared.blocksInOrder.map (·.place) := by
    intro q hq hm
    rcases List.mem_append.1 hm with hm | hm
    · have := c1 q hm
      omega
    · have := c2 q hm
      omega
  rcases ht with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd hs (ProverCoinCounts.notUp h e he ho)
  · exact Or.inr rfl
  · -- the owner in the shared chain, the spender in the first
    exfalso
    have hq : e.owner.place ∉ F.first.blocksInOrder.map (·.place) := n1 _ (by rw [c2 _ ho]; decide)
    have hnb : Addr.before (F.first.blocksInOrder.map (·.place) ++
        (F.shared.blocksInOrder.map (·.place) ++ F.second.blocksInOrder.map (·.place))) e.owner e.spender = false :=
      Addr.not_before (a := e.spender) (b := e.owner) hs hq
    unfold orderOf at hb
    rw [List.append_assoc, hnb] at hb
    cases hb
  · exact Or.inl rfl
  · exact Or.inr rfl
  · -- the owner in the second chain, the spender in the first
    exfalso
    have hq := n12 _ (c3 _ ho)
    have hnb : Addr.before (F.first.blocksInOrder.map (·.place) ++ F.shared.blocksInOrder.map (·.place) ++
        F.second.blocksInOrder.map (·.place)) e.owner e.spender = false :=
      Addr.not_before (a := e.spender) (b := e.owner) (List.mem_append.2 (Or.inl hs)) hq
    unfold orderOf at hb
    rw [hnb] at hb
    cases hb
  · -- the owner in the second chain, the spender in the shared
    exfalso
    have hq := n12 _ (c3 _ ho)
    have hnb : Addr.before (F.first.blocksInOrder.map (·.place) ++ F.shared.blocksInOrder.map (·.place) ++
        F.second.blocksInOrder.map (·.place)) e.owner e.spender = false :=
      Addr.not_before (a := e.spender) (b := e.owner) (List.mem_append.2 (Or.inr hs)) hq
    unfold orderOf at hb
    rw [hnb] at hb
    cases hb
  · exact Or.inl rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.Cs.cut_some
#print axioms ProofFile.Honest.cutAll_some
#print axioms ProofFile.Honest.cutAll_cuts
#print axioms ProofFile.Honest.lend_congr
#print axioms ProofFile.Honest.lendPart_congr
#print axioms ProofFile.Honest.dueAt_none
#print axioms ProofFile.Honest.dueAt_left
#print axioms ProofFile.Honest.dueAt_right
#print axioms ProofFile.Honest.findIdx_ge
#print axioms ProofFile.Honest.Addr.not_before
#print axioms ProofFile.Honest.ProverCoinCounts.keptIn
#print axioms ProofFile.Honest.ProverCoinCounts.visible
