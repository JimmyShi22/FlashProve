-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/StepAt.lean: the i-th dealt group stands at the list of the i-th declared
opening, from Block.step's test "the columns".

Statements and proofs, for the proximity test (the kind K12) and for any rounds without a stored
table.
Main names:
  `opensWith`: the declared openings of rounds, in turn, each with the positions that its own round
    drew.
  `groupsOf_opens`: where no round reads a stored table, the groups' positions are, opening by
    opening, Fmt.listOf (poss.map (· % 2 ^ a)).
  `layOpens_stored`, `roundsOfNums_stored`: no declared round of a proximity test reads a stored
    table (by the definitions of H2U.layOpens and H2U.roundsOfNums).
  `group_at`: under the step's test on the columns the i-th group of regroup has the positions of
    the i-th declared opening; and there is a group for each opening and no other.
  `group_at_k12`: the same of the block proximityTestKind X p, from its test on the plan and the step's first two
    lines.
Limits: No soundness is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.StepGroups

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

/-- The declared openings, in turn, each with the positions that its round drew. -/
def opensWith : List Fmt.DeclaredRound → List Fmt.Drawn → List ((Fmt.Shape × Fmt.TreeSource) × List ℕ)
  | d :: ds, R :: Rs => d.opens.map (fun o => (o, R.poss)) ++ opensWith ds Rs
  | _, _ => []

theorem groupsOf_opens (F : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = []) →
    (groupsOf F ds Rs).map (·.map (·.2.1)) =
      (opensWith ds Rs).map fun y => Fmt.listOf (y.2.map (· % 2 ^ y.1.1.a))
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | d :: ds, R :: Rs, h => by
    rw [groupsOf_cons, List.map_append, groupsOf_opens F ds Rs fun x hx => h x (List.mem_cons_of_mem
        _ hx)]
    show _ = List.map _ (d.opens.map (fun o => (o, R.poss)) ++ opensWith ds Rs)
    rw [List.map_append]
    congr 1
    unfold grp1
    rw [h d List.mem_cons_self]
    simp [Function.comp_def]

theorem layOpens_stored (own : Bool) : ∀ (rs : List Fmt.Round) (seen : Bool)
    (l : List (List (Fmt.Shape × Fmt.TreeSource))) (out : List Fmt.DeclaredRound),
    H2U.layOpens own seen rs l = some out → ∀ d ∈ out, d.stored = []
  | [], _, [], out, h => by
    cases h
    intro d hd
    cases hd
  | [], _, _ :: _, _, h => by cases h
  | r :: rs, seen, l, out, h => by
    unfold H2U.layOpens at h
    dsimp only at h
    split at h
    · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · rfl
      · exact layOpens_stored own rs _ _ o' h1 d hd
    · split at h
      · split at h
        · cases h
        · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          intro d hd
          rcases List.mem_cons.1 hd with rfl | hd
          · rfl
          · exact layOpens_stored own rs _ _ o' h1 d hd
      · cases h

theorem roundsOfNums_stored (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some rds) : ∀ d ∈ rds, d.stored = [] := by
  unfold H2U.roundsOfNums at h
  split at h
  · exact layOpens_stored _ _ _ _ _ h
  · cases h

/-- The i-th dealt group has the positions of the i-th declared opening. -/
theorem group_at (F : ℕ) (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn)
    (got : List VerifiableInference.Desc.OpenedColumn) (hst : ∀ d ∈ ds, d.stored = [])
    (hcols : got.map kpw = (groupsOf F ds Rs).flatMap id) :
    (regroup ((groupsOf F ds Rs).map (·.length)) got).length = (opensWith ds Rs).length ∧
    ∀ (i : ℕ) (grp : List (ℕ × List UInt64)),
      (regroup ((groupsOf F ds Rs).map (·.length)) got)[i]? = some grp →
      ∃ (o : Fmt.Shape × Fmt.TreeSource) (poss : List ℕ), (opensWith ds Rs)[i]? = some (o, poss) ∧
        grp.map (·.1) = Fmt.listOf (poss.map (· % 2 ^ o.1.a)) := by
  have h := (regroup_pos _ _ hcols).trans (groupsOf_opens F ds Rs hst)
  refine ⟨by simpa using congrArg List.length h, fun i grp hi => ?_⟩
  have h1 := congrArg (·[i]?) h
  simp only [List.getElem?_map, hi, Option.map_some] at h1
  cases ho : (opensWith ds Rs)[i]? with
  | none =>
    rw [ho] at h1
    cases h1
  | some y =>
    rw [ho] at h1
    exact ⟨y.1, y.2, rfl, Option.some.inj h1⟩

/-- The same of the block, from its test on the plan and Block.step's first two lines. -/
theorem group_at_k12 {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (F : ℕ) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn)
    (hcols : ((cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
        (rs.map (·.drawn))).flatMap id).length).map (fun c => (c.1, c.2.1, c.2.2.length)) ==
      (groupsOf F (proximityTestKind X p : Block T Cl).rounds (rs.map (·.drawn))).flatMap id) = true)
    (i : ℕ) (grp : List (ℕ × List UInt64))
    (hi : (regroup ((groupsOf F (proximityTestKind X p : Block T Cl).rounds (rs.map (·.drawn))).map (·.length))
      (cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
        (rs.map (·.drawn))).flatMap id).length))[i]? = some grp) :
    ∃ (o : Fmt.Shape × Fmt.TreeSource) (poss : List ℕ),
      (opensWith ((laidOf p).map (·.1)) (rs.map (·.drawn)))[i]? = some (o, poss) ∧
        grp.map (·.1) = Fmt.listOf (poss.map (· % 2 ^ o.1.a)) := by
  rw [k12_rounds X p hp] at hcols hi
  refine (group_at F _ _ _ (fun d hd => ?_) (beq_iff_eq.1 hcols)).2 i grp hi
  unfold laidOf at hd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
  cases hr : H2U.roundsOfNums p.nums with
  | none =>
    rw [hr] at hx
    simp at hx
  | some rds =>
    rw [hr] at hx
    exact roundsOfNums_stored _ rds hr _ (List.of_mem_zip hx).1

end H2K.Sw
