-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ItemsFit.lean: WHAT THE LAWS "THE KIND's OWN DECISION SAYS YES" ASK
OF THE TWO ROUNDS' ITEMS, OF THE SECOND ROUND's DRAWS AND OF THE NUMBER OF GROUPS FOLLOWS FROM THE
TEST ON ROUNDS THAT `Block.step` RUNS IN FRONT OF EVERY DECISION (`roundsFit`,
Johnson/Desc/Block.lean) AND FROM HOW IT LAYS THE COLUMNS INTO GROUPS (`regroup`), AT THE KIND's OWN
TWO ROUNDS, AT ANY NUMBERS. Statements with their proofs; no definition. Beside
Returns/DrawFits.lean, which has the like for the first round's draws and says of the items, of
`fits₁` and of `locOk` nothing.

  `filter_cut`      an entry's cut without the roots: its answers, then its elements
  `items_give`      THE STATEMENT: rounds that fit the kind's rounds: `fits₁` · `vals` (the first
                    round shows no item) · the second round's items are p.answers answers · it
                    draws no element, p.positions positions, no matrix entry
  `range_give`      every position that the second round drew lies below 2 ^ p.logN
  `answers_give`    so, cut to k ≤ p.answers items, it holds k answers
  `answers_tied`    `answers`, UNDER ONE TIE: the sending's count of answers is p.answers
  `loc_tied`        `loc`, UNDER THREE TIES: the sending took p.answers items · p.logN is the old
                    main code's · p.positions is not 0
  `groups_give`     `groups`: the columns as `Block.step` lays them into groups, at two
                    challenges, are p.read.length groups

By, the library's: `answers_of_items` (Johnson/Desc/K1/Law/When.lean) · `regroup_len`
(Johnson/Desc/Sound/Gather.lean). Kin: `cut_elems` (Johnson/Desc/First/Tape/TapeFits.lean) has
`filter_cut` at an entry without answers and roots · `fit_facts`, `draw_len`, `answers_len`
(Johnson/Desc/K1/Law/When.lean) have the like of `items_give` and `answers_give` at the sending
kind's own rounds · `allTaken_groups` (Johnson/Top/H0/Tw/K2C/Laws.lean) has `groups` the other way
round, from a yes · `rounds_give` (Returns/DrawFits.lean) has `range_give`'s end among five, under
two ties that this one does not want.

Limits. THE TIES ARE PREMISES: that a plan's numbers meet them at a reached state is not shown here.
Nothing on the columns themselves (`readsOpens`, `noneLeft`). Nothing on who sends the rounds: that
a prover's rounds pass `roundsFit` is the frame's law (`fits_played`,
Johnson/Desc/ProofFile/Honest/Law/Cut.lean), not called here. Nothing on any property.


-/
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Desc.K1.Law.SendP4
import Johnson.Desc.K1.Law.When
import Johnson.Desc.Sound.Gather

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit itemOf regroup groupsOf OpenedColumn)
open VerifiableInference.Desc.First.K2 (P2 rounds par9 locOk behindArgs)

/-- An entry's cut without the roots. -/
theorem filter_cut (e : Fmt.Entry) :
    e.cut.filter (· != .root) = List.replicate e.answers .answer ++
      List.replicate ((e.msg - 24 * e.answers - 32 * e.roots) / 24) .e := by
  unfold Fmt.Entry.cut
  rw [List.filter_append, List.filter_append]
  have a : (List.replicate e.answers Fmt.Item.answer).filter (· != .root) =
      List.replicate e.answers .answer :=
    List.filter_eq_self.2 fun x hx => by
      rw [List.eq_of_mem_replicate hx]
      rfl
  have b : (List.replicate e.roots Fmt.Item.root).filter (· != .root) = [] :=
    List.filter_eq_nil_iff.2 fun x hx => by
      rw [List.eq_of_mem_replicate hx]
      decide
  have c : (List.replicate ((e.msg - 24 * e.answers - 32 * e.roots) / 24) Fmt.Item.e).filter
      (· != .root) = List.replicate ((e.msg - 24 * e.answers - 32 * e.roots) / 24) .e :=
    List.filter_eq_self.2 fun x hx => by
      rw [List.eq_of_mem_replicate hx]
      rfl
  rw [a, b, c, List.append_nil]

/-- **Rounds that fit give what the laws ask of the items and of the second round's draws.** -/
theorem items_give (p : P2) (r₁ r₂ : Fmt.RoundView) (h : roundsFit (rounds p) [r₁, r₂] = true) :
    _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true ∧ r₁.vals = [] ∧
      r₂.vals.map itemOf = List.replicate p.answers .answer ∧
      r₂.drawn.elems = [] ∧ r₂.drawn.poss.length = p.positions ∧ r₂.drawn.trits = [] := by
  simp only [rounds, roundsFit, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨i1, e1⟩, p1⟩, t1⟩, _⟩, _⟩, _⟩, ⟨⟨⟨⟨⟨⟨i2, e2⟩, p2⟩, t2⟩, _⟩, _⟩, _⟩, _⟩ := h
  have j1 := beq_iff_eq.1 i1
  have j2 := beq_iff_eq.1 i2
  unfold Fmt.DeclaredRound.items at j1 j2
  rw [filter_cut] at j1 j2
  refine ⟨?_, ?_, ?_, List.length_eq_zero_iff.1 (beq_iff_eq.1 e2), beq_iff_eq.1 p2,
    List.length_eq_zero_iff.1 (beq_iff_eq.1 t2)⟩
  · show (r₁.drawn.elems.length == p.seeds && r₁.drawn.poss.length == 0 &&
      r₁.drawn.trits.length == 0) = true
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨e1, p1⟩, t1⟩
  · have z : (32 * p.roots - 24 * 0 - 32 * p.roots) / 24 = 0 := by omega
    have j : r₁.vals.map itemOf = List.replicate 0 .answer ++
        List.replicate ((32 * p.roots - 24 * 0 - 32 * p.roots) / 24) .e := j1
    rw [z] at j
    exact List.map_eq_nil_iff.1 j
  · have z : (24 * p.answers - 24 * p.answers - 32 * 0) / 24 = 0 := by omega
    have j : r₂.vals.map itemOf = List.replicate p.answers .answer ++
        List.replicate ((24 * p.answers - 24 * p.answers - 32 * 0) / 24) .e := j2
    rw [z] at j
    exact j.trans (List.append_nil _)

/-- Every position that the second round drew lies below the plan's range. -/
theorem range_give (p : P2) (r₁ r₂ : Fmt.RoundView) (h : roundsFit (rounds p) [r₁, r₂] = true) :
    ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN := by
  simp only [rounds, roundsFit, Bool.and_eq_true] at h
  obtain ⟨_, ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, q2⟩, _⟩, _⟩, _⟩ := h
  exact fun q hq => of_decide_eq_true (List.all_eq_true.1 q2 q hq)

/-- Cut to k ≤ n items, a round of n answers holds k answers. -/
theorem answers_give (r₂ : Fmt.RoundView) (n k : Nat)
    (h : r₂.vals.map itemOf = List.replicate n .answer) (hk : k ≤ n) :
    (K1.answersIn { r₂ with vals := r₂.vals.take k }).length = k := by
  refine K1.answers_of_items (r₂.vals.take k) k ?_
  rw [List.map_take, h, List.take_replicate, Nat.min_eq_left hk]

/-- **`answers`, under one tie.** -/
theorem answers_tied (p : P2) (Q : K1.Par) (r₁ r₂ : Fmt.RoundView) (ht : Q.answers = p.answers)
    (h : roundsFit (rounds p) [r₁, r₂] = true) :
    (K1.answersIn (K1.cutTo Q r₂)).length = Q.answers :=
  answers_give r₂ p.answers Q.answers (items_give p r₁ r₂ h).2.2.1 (Nat.le_of_eq ht)

/-- **`loc`, under three ties.** -/
theorem loc_tied (p : P2) (x : _root_.Tw.K2.Front) (y : _root_.Tw.K2.Sent) (r₁ r₂ : Fmt.RoundView)
    (cols : List _root_.Tw.K2.Col) (logN : Nat) (ht : y.took = p.answers) (hl : p.logN = logN)
    (hp : 0 < p.positions) (h : roundsFit (rounds p) [r₁, r₂] = true) :
    locOk (behindArgs (par9 p) x y r₂ cols) logN = true := by
  obtain ⟨_, _, i2, e2, p2, t2⟩ := items_give p r₁ r₂ h
  have hv : r₂.vals.length = p.answers := by
    have := congrArg List.length i2
    rwa [List.length_map, List.length_replicate] at this
  show (!("LOC" != "LOC") && !((0 : Nat) != 0) && ((0 : Nat) == 0) &&
    !(r₂.vals.length - y.took != 0) &&
    (r₂.drawn.elems.length == 0 && r₂.drawn.poss.length == p.positions &&
      r₂.drawn.trits.length == 0) &&
    (p.logN == logN && decide (0 < p.positions)) && r₂.drawn.elems.isEmpty) = true
  rw [hv, ht, e2, p2, t2, hl]
  simp [hp]

/-- **`groups`**: the columns as `Block.step` lays them into groups. -/
theorem groups_give (p : P2) (ft : Nat) (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn) :
    (regroup ((groupsOf ft (rounds p) [d₁, d₂]).map (·.length)) cols).length = p.read.length := by
  rw [VerifiableInference.Desc.Sound.regroup_len, List.length_map]
  simp [rounds, groupsOf]

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.filter_cut
#print axioms VerifiableInference.Desc.K2.Honest.Returns.items_give
#print axioms VerifiableInference.Desc.K2.Honest.Returns.range_give
#print axioms VerifiableInference.Desc.K2.Honest.Returns.answers_give
#print axioms VerifiableInference.Desc.K2.Honest.Returns.answers_tied
#print axioms VerifiableInference.Desc.K2.Honest.Returns.loc_tied
#print axioms VerifiableInference.Desc.K2.Honest.Returns.groups_give
