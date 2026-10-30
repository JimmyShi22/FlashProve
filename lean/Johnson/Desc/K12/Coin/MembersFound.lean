-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/MembersFound.lean: **TWO CLAUSES OF CoreFacts (Johnson/Desc/Sound/SeamFacts.lean) AT THE SHARED CHAIN's TWO PROXIMITY TESTS, FROM THE ONE X**: the group's members are the data's (hmembers) · the layout finds each member at its place (hfind).
Statements and proofs.
  find_two        a layout with two members that differ finds each at its place.
  found_of_ids    general: where the data have two members with the numbers n₀ ≠ n₁ and the group's members are #[n₀, n₁]: both clauses. By K12's files' Made (made_of: the layout's members are the data's, place by place).
  **found_nine | found_ten**   at the record behind the seat's door in, under sharedX … 9 | 10: by sits_nine | sits_ten (MemberSits.lean) and membX.
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Coin.MemberSits
import Johnson.Desc.Sound.NineAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared (Msg2)
open H2K.First (Plain Seat1 made_of)
open _root_.Desc.K14 (St P14 withOmega)
open _root_.Desc.K14.Law.Fence (sharedX sharedX_parts tenantSh numSh membX_nine membX_ten memOf)

/-- A layout with two members that differ finds each at its place. -/
theorem find_two (L : GroupLayout) (n₀ n₁ : ℕ) (hne : n₀ ≠ n₁) (hm : L.members = #[n₀, n₁]) :
    L.find n₀ = some 0 ∧ L.find n₁ = some 1 := by
  unfold GroupLayout.find
  rw [hm]
  have hb : (n₀ == n₁) = false := by simpa using hne
  constructor
  · simp [List.idxOf?, List.findIdx?_cons]
  · simp [List.idxOf?, List.findIdx?_cons, hb]

/-- An array of two, by its size and its two entries. -/
theorem array_two (A : Array ℕ) (n₀ n₁ : ℕ) (hs : A.size = 2) (h0 : A[0]? = some n₀)
    (h1 : A[1]? = some n₁) : A = #[n₀, n₁] := by
  apply Array.ext'
  rcases A with ⟨l⟩
  match l, hs, h0, h1 with
  | [x, y], _, h0, h1 =>
    simp at h0 h1
    simp [h0, h1]

/-- **Both clauses, from the two numbers.** -/
theorem found_of_ids (π : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group)
    (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) (n₀ n₁ : ℕ) (hne : n₀ ≠ n₁)
    (h2 : D.mems.length = 2)
    (hq : ∀ q : Fin D.mems.length, (q.val = 0 ∧ (D.mems.get q).id = n₀) ∨
      (q.val = 1 ∧ (D.mems.get q).id = n₁))
    (hG : G0.members = #[n₀, n₁]) :
    (∀ j : Fin D.mems.length, D.L.find (D.mems.get j).id = some j.val) ∧
      ∀ o ∈ G0.members.toList, ∃ j : Fin D.mems.length, (D.mems.get j).id = o := by
  have hm := made_of π _ a Ly D (hf.2.2.2 default)
  have id0 : (D.mems.get ⟨0, by omega⟩).id = n₀ := by
    rcases hq ⟨0, by omega⟩ with ⟨_, e⟩ | ⟨e, _⟩
    · exact e
    · exact absurd e Nat.zero_ne_one
  have id1 : (D.mems.get ⟨1, by omega⟩).id = n₁ := by
    rcases hq ⟨1, by omega⟩ with ⟨e, _⟩ | ⟨_, e⟩
    · exact absurd e Nat.one_ne_zero
    · exact e
  have hL : Ly.members = #[n₀, n₁] := array_two _ _ _ (by rw [hm.size, h2])
    (by rw [← id0]; exact (hm.mem ⟨0, by omega⟩).1) (by rw [← id1]; exact (hm.mem ⟨1, by omega⟩).1)
  obtain ⟨f0, f1⟩ := find_two Ly n₀ n₁ hne hL
  refine ⟨fun j => ?_, fun o ho => ?_⟩
  · rw [hm.lay]
    rcases hq j with ⟨e, hid⟩ | ⟨e, hid⟩
    · rw [hid, e]; exact f0
    · rw [hid, e]; exact f1
  · rw [hG] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact ⟨⟨0, by omega⟩, id0⟩
    · exact ⟨⟨1, by omega⟩, id1⟩

/-- **AT THE TEST ON G_u.** -/
theorem found_nine (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hU : 0 < sentU.size) (hO : 1 < (withOmega P.S).size)
    (hX : sharedX P sentU layU layO 9 d = true) (π : P12) (t : T12)
    (ht : Seat.enter (·.gU) (·.firstMask) d = .ok t) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) :
    (∀ j : Fin D.mems.length, D.L.find (D.mems.get j).id = some j.val) ∧
      ∀ o ∈ G0.members.toList, ∃ j : Fin D.mems.length, (D.mems.get j).id = o := by
  obtain ⟨h2, hq⟩ := sits_nine P sentU layU layO 0 0 d hU hO hX π t ht a rest G0 Ly D hf
  have hmem := (membX_nine _ _ ((sharedX_parts P sentU layU layO 9 d).1 hX).2.2.1).1
  cases ht
  unfold memOf at hmem
  obtain ⟨G', hG', hmm⟩ := Option.map_eq_some_iff.1 hmem
  obtain rfl : G' = G0 := Option.some.inj (hG'.symm.trans hf.2.1)
  exact found_of_ids π _ a rest G' Ly D hf 0 (sentU.size + 1) (by omega) h2
    (fun q => (hq q).imp (fun h => ⟨h.1, h.2.1⟩) fun h => ⟨h.1, h.2.1⟩) hmm

/-- **AT THE TEST ON G_omega.** -/
theorem found_ten (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hO : 1 < (withOmega P.S).size) (hX : sharedX P sentU layU layO 10 d = true) (π : P12) (t : T12)
    (ht : Seat.enter (·.gOmega) (fun _ => none) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    (∀ j : Fin D.mems.length, D.L.find (D.mems.get j).id = some j.val) ∧
      ∀ o ∈ G0.members.toList, ∃ j : Fin D.mems.length, (D.mems.get j).id = o := by
  obtain ⟨h2, hq⟩ := sits_ten P sentU layU layO 0 0 d hO hX π t ht a rest G0 Ly D hf
  have hmem := membX_ten _ _ ((sharedX_parts P sentU layU layO 10 d).1 hX).2.2.1
  cases ht
  unfold memOf at hmem
  obtain ⟨G', hG', hmm⟩ := Option.map_eq_some_iff.1 hmem
  obtain rfl : G' = G0 := Option.some.inj (hG'.symm.trans hf.2.1)
  exact found_of_ids π _ a rest G' Ly D hf sentU.size (sentU.size + 1) (by omega) h2
    (fun q => (hq q).imp (fun h => ⟨h.1, h.2.1⟩) fun h => ⟨h.1, h.2.1⟩) hmm

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.found_nine
#print axioms VerifiableInference.Desc.K12.Coin.found_ten
#print axioms VerifiableInference.Desc.K12.Coin.find_two
#print axioms VerifiableInference.Desc.K12.Coin.found_of_ids
