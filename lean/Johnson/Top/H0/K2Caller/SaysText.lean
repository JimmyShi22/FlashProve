-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SaysText.lean: FROM WHAT A ROW SAYS OF WORDS (`OnBytes.Means.Says`,
Johnson/Desc/Means/Says.lean: the sum over both tables of all messages of a statement) TO WHAT IT
SAYS OF THE TYPED ENTRIES OF A SENDING (`TextHolds`, Johnson/Top/H0/K2Hands/AfterText.lean), and
back. Why: the table of joints' item on a class of rows is worded by `Says`; the law of the code
switch asks `TextHolds` of each row that the switch has laid.

Main names:
  `tabPart`, `tabAll`: the places (message's number, table, index) of a statement's tables, as a
    finite set; `mem_tabPart`, `mem_tabAll`, `sum_tabPart`.
  `value_eq`: what a row is applied to words is one sum over `tabAll`.
  `says_iff_textHolds`: `Says rdE st r m` just if `TextHolds cs l ids r` at the words' values at the
    typed entries' names: `textHolds_iff` (Johnson/Top/H0/K2Hands/TextSum.lean) at `tabAll st`.
    Premises: ids is one to one · `OnlyAt`: inside the tables the row has no coefficient but at a
    typed entry's name · every typed entry's name lies in the tables · outside `inside` the words
    are 0.
Limits. The four are premises. Tools: they would stay proved if the protocol were another. Nothing
on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Hands.TextSum
import Johnson.Desc.Means.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H
open OnBytes.Means (Words tableSize onTable value Says)
open VerifiableInference.Desc.First.K2Hands (TextHolds OnlyAt nameOf textHolds_iff)

/-- The places of one table of every message of a statement: number, table, index. -/
def tabPart (st : Statement) (part : Part) : Finset (ℕ × Part × ℕ) :=
  ((Finset.range st.oracles.size).sigma fun o => Finset.range (tableSize st o part)).image
    fun x => (x.1, part, x.2)

/-- The places of both tables of every message. -/
def tabAll (st : Statement) : Finset (ℕ × Part × ℕ) := tabPart st .main ∪ tabPart st .mask

theorem mem_tabPart (st : Statement) (part : Part) (x : ℕ × Part × ℕ) :
    x ∈ tabPart st part ↔
      x.1 < st.oracles.size ∧ x.2.1 = part ∧ x.2.2 < tableSize st x.1 part := by
  unfold tabPart
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨h1, h2⟩ := Finset.mem_sigma.1 hy
    exact ⟨Finset.mem_range.1 h1, rfl, Finset.mem_range.1 h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine Finset.mem_image.2 ⟨⟨x.1, x.2.2⟩,
      Finset.mem_sigma.2 ⟨Finset.mem_range.2 h1, Finset.mem_range.2 h3⟩, ?_⟩
    exact Prod.ext rfl (Prod.ext h2.symm rfl)

theorem mem_tabAll (st : Statement) (x : ℕ × Part × ℕ) :
    x ∈ tabAll st ↔ x.1 < st.oracles.size ∧ x.2.2 < tableSize st x.1 x.2.1 := by
  unfold tabAll
  rw [Finset.mem_union, mem_tabPart, mem_tabPart]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> exact ⟨h1, h2 ▸ h3⟩
  · rintro ⟨h1, h3⟩
    cases hp : x.2.1 with
    | main => exact Or.inl ⟨h1, rfl, hp ▸ h3⟩
    | mask => exact Or.inr ⟨h1, rfl, hp ▸ h3⟩

theorem sum_tabPart (st : Statement) (part : Part) (f : ℕ × Part × ℕ → GE) :
    ∑ x ∈ tabPart st part, f x =
      ∑ o ∈ Finset.range st.oracles.size, ∑ i ∈ Finset.range (tableSize st o part),
        f (o, part, i) := by
  unfold tabPart
  rw [Finset.sum_image, Finset.sum_sigma']
  intro a _ b _ h
  have h1 : a.1 = b.1 := congrArg Prod.fst h
  have h2 : a.2 = b.2 := congrArg (fun y : ℕ × Part × ℕ => y.2.2) h
  exact Sigma.ext h1 (heq_of_eq h2)

/-- **What a row is applied to words, as one sum over the places of the tables.** -/
theorem value_eq (st : Statement) (r : Row) (m : Words GE) :
    value rdE st r m = ∑ x ∈ tabAll st, coefAt r x.1 x.2.1 x.2.2 * m x.1 x.2.1 x.2.2 := by
  have hd : Disjoint (tabPart st .main) (tabPart st .mask) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have a := ((mem_tabPart st .main x).1 h1).2.1
    have b := ((mem_tabPart st .mask x).1 h2).2.1
    rw [a] at b
    cases b
  unfold tabAll value
  rw [Finset.sum_union hd, sum_tabPart, sum_tabPart, Finset.sum_add_distrib]
  rfl

/-- **FROM WHAT A ROW SAYS OF WORDS TO WHAT IT SAYS OF THE NEW SENDING's TYPED ENTRIES**, and back.
st: the statement behind the switch; m: words. By `textHolds_iff`
(Johnson/Top/H0/K2Hands/TextSum.lean). -/
theorem says_iff_textHolds (cs : Codes) (l : List (OracleShape × ℕ)) (ids : ℕ → ℕ)
    (hids : Function.Injective ids) {inside : ℕ → Part → ℕ → Prop} {r : Row}
    (h : OnlyAt cs l ids inside r) (st : Statement) (m : Words GE)
    (hF : ∀ n, nameOf cs l ids n ∈ tabAll st)
    (h0 : ∀ x ∈ tabAll st, ¬ inside x.1 x.2.1 x.2.2 → m x.1 x.2.1 x.2.2 = 0) :
    Says rdE st r m ↔ TextHolds cs l ids r
      (fun n => m (ids (entAt cs l n).1) (entAt cs l n).2.1 (entAt cs l n).2.2) := by
  rw [textHolds_iff cs l ids hids h m (tabAll st) hF h0, ← value_eq]
  rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.value_eq
#print axioms VerifiableInference.Desc.First.K2Caller.says_iff_textHolds
