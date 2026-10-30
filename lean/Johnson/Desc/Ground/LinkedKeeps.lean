-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/LinkedKeeps.lean: every plain function of the ground, but for the beginning of a
proximity test, keeps "Linked" and "Frozen" (Johnson/Desc/Ground/Linked.lean). Theorems. joinP and
addRowP keep Frozen BY THEIR OWN CLAUSE "no test has begun", which the proofs read out of the
function's yes; joinP keeps Linked because it writes both sides, at the group that it has itself
looked up.

  clause_of_ok            a clause of a list that passes holds.
  groundKeeps_linked      KeepsLinked meets GroundKeeps.
  groundKeeps_frozen      Frozen meets GroundKeeps.
  groundKeeps_four        Grows, NoNewMark, KeepsLinked and Frozen together meet it.
What is not claimed. beginRunP is left out, as in GroundKeeps: it lays the mark. Nothing on a step
that writes the statement by another road than these functions. The four together do not exclude a
message that is made a member before it is sampled (see Johnson/Desc/Ground/Linked.lean's head).

-/
import Johnson.Desc.Ground.Linked

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- A clause of a list that passes holds. -/
theorem clause_of_ok (l : Clauses) (h : ok l = true) (c : String × Bool) (hc : c ∈ l) :
    c.2 = true := by
  unfold ok at h
  exact List.all_eq_true.1 h c hc

/-- joinP's yes: the group, if it stood there, bore no mark. -/
theorem join_unmarked (S : Statement) (g o : Nat) (kept : Bool) (h : ok (joinL S g o kept) = true)
    (G : Group) (hG : S.groups[g]? = some G) : G.inRun = false := by
  have := clause_of_ok _ h ("join: no test has begun", has S.groups[g]? (!·.inRun))
    (by simp [joinL])
  simpa [has, hG] using this

/-- addRowP's yes: the group, if it stood there, bore no mark. -/
theorem row_unmarked (S : Statement) (g : Nat) (row : OnBytes.Row) (h : ok (rowL S g row) = true)
    (G : Group) (hG : S.groups[g]? = some G) : G.inRun = false := by
  have := clause_of_ok _ h ("addRow: no test has begun", has S.groups[g]? (!·.inRun))
    (by simp [rowL])
  simpa [has, hG] using this

/-- "Linked stays" is such a relation. -/
theorem groundKeeps_linked : GroundKeeps KeepsLinked where
  refl := KeepsLinked.refl
  trans := KeepsLinked.trans
  newGroup := by
    intro L d d' code maskCode n h
    unfold newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact linked_withGroup d.st code maskCode
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold recvP at h
    split at h
    · cases hl : Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact linked_stSent d.st sent
    · cases h
  admit := by
    intro L d d' o rows h
    unfold admitP at h
    split at h
    · cases hx : d.st.oracles[o]? with
      | none => simp [hx] at h
      | some x =>
        cases hp : Own.padMade d.st.codes x.shape with
        | none => simp [hx, hp] at h
        | some places =>
          simp only [hx, hp, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          exact linked_modOracle d.st o _ fun _ => rfl
    · cases h
  join := by
    intro L d d' g o kept h
    unfold joinP at h
    split at h
    · cases hg : d.st.groups[g]? with
      | none => simp [hg] at h
      | some G =>
        simp only [hg, Option.map_some, Option.some.injEq] at h
        subst h
        exact linked_joined d.st g o kept G hg
    · cases h
  addRow := by
    intro L d d' g row h
    unfold addRowP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact linked_modGroup d.st g (fun G => { G with rows := G.rows.push row }) fun _ _ k => k
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold takeMaskP at h
    split at h
    · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
      | none => simp [hl] at h
      | some l =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact linked_modOracle d.st o _ fun _ => rfl
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold closeLedgerP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact linked_closeLedgers [o] d.st
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold spendAsMaskP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact linked_modOracle d.st o _ fun _ => rfl
    · cases h
  adopt := by
    intro L d d' sent given ids h
    unfold adoptP at h
    split at h
    · cases hl : Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact linked_stSent d.st sent
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold elsewhereP at h
    split at h
    · cases hy : other.oracles[theirs]? with
      | none => simp [hy] at h
      | some y =>
        simp only [hy, Option.map_some, Option.some.injEq] at h
        subst h
        exact linked_modOracle d.st mine _ fun _ => rfl
    · cases h

/-- "A marked group keeps its mark, its members and its open rows" is such a relation. -/
theorem groundKeeps_frozen : GroundKeeps Frozen where
  refl := Frozen.refl
  trans := Frozen.trans
  newGroup := by
    intro L d d' code maskCode n h
    unfold newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact frozen_withGroup d.st code maskCode
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold recvP at h
    split at h
    · cases hl : Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact frozen_oracles d.st _
    · cases h
  admit := by
    intro L d d' o rows h
    unfold admitP at h
    split at h
    · cases hx : d.st.oracles[o]? with
      | none => simp [hx] at h
      | some x =>
        cases hp : Own.padMade d.st.codes x.shape with
        | none => simp [hx, hp] at h
        | some places =>
          simp only [hx, hp, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
          subst h
          exact frozen_oracles d.st _
    · cases h
  join := by
    intro L d d' g o kept h
    unfold joinP at h
    split at h
    · rename_i hok
      cases hg : d.st.groups[g]? with
      | none => simp [hg] at h
      | some G =>
        simp only [hg, Option.map_some, Option.some.injEq] at h
        subst h
        exact (frozen_modGroup d.st g _ fun A hA => join_unmarked d.st g o kept hok A hA).trans
          (frozen_oracles _ _)
    · cases h
  addRow := by
    intro L d d' g row h
    unfold addRowP at h
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h
      subst h
      exact frozen_modGroup d.st g _ fun A hA => row_unmarked d.st g row hok A hA
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold takeMaskP at h
    split at h
    · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
      | none => simp [hl] at h
      | some l =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact frozen_oracles d.st _
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold closeLedgerP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact frozen_closeLedgers [o] d.st
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold spendAsMaskP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact frozen_oracles d.st _
    · cases h
  adopt := by
    intro L d d' sent given ids h
    unfold adoptP at h
    split at h
    · cases hl : Own.treesMade d.st.codes sent with
      | none => simp [hl] at h
      | some lay =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact frozen_oracles d.st _
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold elsewhereP at h
    split at h
    · cases hy : other.oracles[theirs]? with
      | none => simp [hy] at h
      | some y =>
        simp only [hy, Option.map_some, Option.some.injEq] at h
        subst h
        exact frozen_oracles d.st _
    · cases h

/-- All four together. -/
theorem groundKeeps_four : GroundKeeps fun a b =>
    (Grows a b ∧ NoNewMark a b) ∧ (KeepsLinked a b ∧ Frozen a b) :=
  (groundKeeps_grows.and groundKeeps_noNew).and (groundKeeps_linked.and groundKeeps_frozen)

end VerifiableInference.Desc.Ground
