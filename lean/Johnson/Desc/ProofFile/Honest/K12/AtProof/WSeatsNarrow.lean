-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/WSeatsNarrow.lean: the members, seats and shapes of the last
chain's test's three members, at a record that agrees with the closed narrow shape narrowW: what
sameCore_at_seat (K12/AtFile/WFrontAtSeat.lean) gives at the state on entry at every stand.

  narrow_lit       on the closed shape: the group's members, places, trees' numbers; a kernel line
  members_of_narrow, tree_of_narrow, seats_of_narrow, shape_of_narrow   at a record that agrees
  first_tree_of_laid   behind the block the last chain's first tree is 84

Limits.
- seats_of_narrow stands at the number 84 for the last chain's first tree: first_tree_of_laid has it.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WNarrowAtW
import Johnson.Desc.Sound.WordsAt
import Johnson.Desc.Third.Law.LaidDef

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.Ground.Sh (coreSh grpSh treeSh orcSh map_get)
open VerifiableInference.Desc.Sound (seatBy noLast seatBy_some)
open ProofFile.Honest.K12.AtFile (SameCore narrowW strip stripT)
open OnBytes (Group)

/-- **On the closed shape.** An evaluation in Lean's kernel. -/
theorem narrow_lit :
    (narrowW.st.groups[0]?).map (·.members) = some [4, 197, 199] ∧
    narrowW.book.place[4]? = some (1, 0) ∧ narrowW.book.place[197]? = some (82, 0) ∧
    narrowW.book.place[199]? = some (83, 0) ∧
    (narrowW.book.trees[1]?).map (·.number) = some 1 ∧
    (narrowW.book.trees[82]?).map (·.number) = some 82 ∧
    (narrowW.book.trees[83]?).map (·.number) = some 1 := by
  decide +kernel

variable {T : VerifiableInference.Desc.Ground.Core} {g : Nat}

local notation "A₄" => ([4, 197, 198, 199] : List Nat)

/-- **At a record that agrees with the closed shape the own group's members are the three.** -/
theorem members_of_narrow (hc : SameCore A₄ g 0 (coreSh T) narrowW) {G : Group}
    (hG : T.st.groups[g]? = some G) : G.members = #[4, 197, 199] := by
  have e : (coreSh T).st.groups[g]? = some (grpSh G) := by
    show (T.st.groups.toList.map grpSh)[g]? = _
    rw [map_get, hG]
    rfl
  have e₂ := hc.group.trans e
  have e₃ : (narrowW.st.groups[0]?).map (·.members) = some G.members.toList := by
    rw [e₂]
    rfl
  exact Array.toList_inj.1 (Option.some.inj (e₃.symm.trans narrow_lit.1))

theorem place_of_narrow (hc : SameCore A₄ g 0 (coreSh T) narrowW) (o : Nat) (ho : o ∈ A₄) :
    T.book.place[o]? = narrowW.book.place[o]? := by
  have e := hc.place o ho
  rw [e]
  show _ = T.book.place.toList[o]?
  rw [Array.getElem?_toList]

/-- The shape of a member at such a record. -/
theorem shape_of_narrow (hc : SameCore A₄ g 0 (coreSh T) narrowW) (o : Nat) (ho : o ∈ A₄) :
    (T.st.oracles[o]?).map (·.shape) = (narrowW.st.oracles[o]?).map (·.shape) := by
  have e := congrArg (Option.map (·.shape)) (hc.msg o ho)
  rw [Option.map_map, Option.map_map] at e
  have e' : ((coreSh T).st.oracles[o]?).map (·.shape) = (T.st.oracles[o]?).map (·.shape) := by
    show ((T.st.oracles.toList.map orcSh)[o]?).map (·.shape) = _
    rw [map_get, Option.map_map]
    rfl
  exact e'.symm.trans e.symm

theorem tree_of_narrow (hc : SameCore A₄ g 0 (coreSh T) narrowW) (o : Nat) (ho : o ∈ A₄) (q : Nat × Nat)
    (hq : T.book.place[o]? = some q) (n : Nat)
    (h : (narrowW.book.trees[q.1]?).map (·.number) = some n) :
    ∃ t : OnBytes.Tree, T.book.trees[q.1]? = some t ∧ t.number = n := by
  have hq' : (coreSh T).book.place[o]? = some q := by
    show T.book.place.toList[o]? = _
    rw [Array.getElem?_toList]
    exact hq
  have e := congrArg (Option.map (·.number)) (hc.tree o ho q hq')
  rw [Option.map_map, Option.map_map] at e
  have e₁ : ((narrowW.book.trees[q.1]?).map (·.number)) =
      ((coreSh T).book.trees[q.1]?).map (·.number) := e
  rw [h] at e₁
  have e₂ : ((T.book.trees.toList.map treeSh)[q.1]?).map (·.number) = some n := e₁.symm
  rw [map_get] at e₂
  cases hq₁ : T.book.trees[q.1]? with
  | none =>
    rw [hq₁] at e₂
    cases e₂
  | some t =>
    rw [hq₁] at e₂
    exact ⟨t, rfl, Option.some.inj e₂⟩

/-- **At such a record the three members' seats.** -/
theorem seats_of_narrow (hc : SameCore A₄ g 0 (coreSh T) narrowW) (t₁ t₂ : Nat) :
    seatBy (noLast t₁ t₂ 84) T.book 4 = some (1, 0) ∧
    seatBy (noLast t₁ t₂ 84) T.book 197 = some (82, 0) ∧
    seatBy (noLast t₁ t₂ 84) T.book 199 = some (t₁ + 1, 0) := by
  obtain ⟨-, p4, p197, p199, n1, n82, n83⟩ := narrow_lit
  have q4 := (place_of_narrow hc 4 (by decide)).trans p4
  have q197 := (place_of_narrow hc 197 (by decide)).trans p197
  have q199 := (place_of_narrow hc 199 (by decide)).trans p199
  obtain ⟨a, ha, ea⟩ := tree_of_narrow hc 4 (by decide) _ q4 1 n1
  obtain ⟨b, hb, eb⟩ := tree_of_narrow hc 197 (by decide) _ q197 82 n82
  obtain ⟨c, hcc, ec⟩ := tree_of_narrow hc 199 (by decide) _ q199 1 n83
  refine ⟨?_, ?_, ?_⟩
  · rw [seatBy_some _ _ 4 _ a q4 ha]
    simp [noLast, ea]
  · rw [seatBy_some _ _ 197 _ b q197 hb]
    simp [noLast, eb]
  · rw [seatBy_some _ _ 199 _ c q199 hcc]
    simp [noLast, ec]

/-- The closed shape has 200 messages. An evaluation in Lean's kernel. -/
theorem narrow_length : narrowW.st.oracles.length = 200 := by
  decide +kernel

/-- **Behind the block the last chain's first tree is 84.** L: what the block has laid; hfirst: in front
of it the first own tree counts one tree more than the book holds. -/
theorem first_tree_of_laid {S : OnBytes.Params.LinShape} {s₀ s : VerifiableInference.Desc.Third.S₃}
    {b : VerifiableInference.Desc.Third.Border} {y : OnBytes.Oracle} {G : Group} {dot : OnBytes.Row}
    (L : VerifiableInference.Desc.Third.Laid S s₀ s b y G dot)
    (hfirst : s₀.book.trees.size + 1 = s₀.loc.firstTree)
    (hc : SameCore A₄ g 0 (coreSh ⟨s.st, s.book, s.roots⟩) narrowW) : s.loc.firstTree = 84 := by
  have hlen : s.st.oracles.size = 200 := by
    have e := hc.length
    rw [narrow_length] at e
    have e' : (s.st.oracles.toList.map orcSh).length = s.st.oracles.size := by simp
    exact (e.trans e').symm
  have h₀ : s₀.st.oracles.size = 199 := by
    have e := L.size
    omega
  have hp := L.place
  rw [h₀] at hp
  have q : s.book.place[199]? = some (83, 0) :=
    (place_of_narrow (T := ⟨s.st, s.book, s.roots⟩) hc 199 (by decide)).trans narrow_lit.2.2.2.1
  have ht : s₀.book.trees.size = 83 := by
    have e := q.symm.trans hp
    exact (congrArg Prod.fst (Option.some.inj e)).symm
  have e := congrArg (·.firstTree) L.loc
  have e' : s.loc.firstTree = s₀.loc.firstTree := e
  rw [e', ← hfirst, ht]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.first_tree_of_laid
#print axioms ProofFile.Honest.K12.AtProof.narrow_lit
#print axioms ProofFile.Honest.K12.AtProof.members_of_narrow
#print axioms ProofFile.Honest.K12.AtProof.shape_of_narrow
#print axioms ProofFile.Honest.K12.AtProof.seats_of_narrow
