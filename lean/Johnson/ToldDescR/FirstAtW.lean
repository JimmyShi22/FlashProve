-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/FirstAtW.lean: no soundness is claimed.
The premises «first» and «seated» of firstOpens_at_last (Johnson/Desc/K12/Coin/FirstOpensAtLast.lean) at the place that onlineDescription seats on the last chain: every member of π.nums.first, π := proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W, is of a tree that is taken over: by make: the planner's road fills that list with the head of secondOpens (so the text of Johnson/Desc/K12/Plan/PlaceOfPlan.lean: placesLater: «let fW ← get … (secondOpens S A.input t0 t1 t2).head?» · «W := mkPlace … (fW, t0.length + 1) …»; placesOfMade: «W := X.W»), whose members are all laid by takenAt (secondOpens_head_taken, Johnson/G/SecondOpensTaken.lean).
  later_W            placesLater A = .ok X → every member of X.W.nums.first is taken over (it is the head of a secondOpens)
  places_W           placesOfMade m = .ok N → ∃ A X, placesLater A = .ok X ∧ N.W = X.W
  p12At_first        a member of (proximityTestParametersAt pl x).nums.first is one of x.nums.first
  **first_at_W**     placesOfMade m = .ok N → ∀ o ∈ (proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.first, ∃ c n, o.2 = .taken c n
  **seated_at**      the premise «seated»: every round of proximityTestKind guardedProximityTestParts π is a round of (fileDescBy o mk Z A (P2Third.secondSeatOf Z N) …).roundsDeclaredByBlocks.2.2 (last_blocks_in)
Does not show. ownMask = false and «two stages at least» at that place (values of the plan). Nothing on soundness.
-/
import Johnson.ToldDescR.LastBlocks
import Johnson.G.SecondOpensTaken

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open Johnson.G.OfPlan (Made secondOpens secondOpens_head_taken)
open VerifiableInference.Desc (Place KindName)

theorem later_W {A : H2U.LaterArgs} {X : H2U.Later3} (h : H2U.placesLater A = .ok X) :
    ∀ o ∈ X.W.nums.first, ∃ c n, o.2 = .taken c n := by
  unfold H2U.placesLater at h
  try dsimp only at h
  obtain ⟨t0, -, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  obtain ⟨t1, -, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  obtain ⟨t2, -, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  obtain ⟨fU, -, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  obtain ⟨fW, hw, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  obtain ⟨tU, -, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  obtain ⟨tW, -, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  have e := Except.ok.inj h
  subst e
  intro o ho
  have ho' : o ∈ fW := ho
  split at hw
  · rename_i a ha
    have e' := Except.ok.inj hw
    subst e'
    obtain ⟨c, n, hc, -⟩ := secondOpens_head_taken _ _ _ _ _ _ ha o ho'
    exact ⟨c, n, hc⟩
  · exact nomatch hw

theorem places_W {m : Made} {N : H2U.Places4} (h : H2U.placesOfMade m = .ok N) :
    ∃ A X, H2U.placesLater A = .ok X ∧ N.W = X.W := by
  unfold H2U.placesOfMade at h
  try dsimp only at h
  obtain ⟨Fs, -, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  obtain ⟨tL, -, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  obtain ⟨X, hX, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  obtain ⟨rows, -, h⟩ := ok_of_bind_ok h
  try dsimp only at h
  have e := Except.ok.inj h
  subst e
  exact ⟨_, X, hX, rfl⟩

theorem p12At_first (pl : Place) (x : H2U.PlaceNums) :
    ∀ o ∈ (H2U.proximityTestParametersAt pl x).nums.first, o ∈ x.nums.first := by
  unfold H2U.proximityTestParametersAt
  split
  · intro o ho
    exact nomatch ho
  · split
    · exact fun o ho => ho
    · intro o ho
      exact nomatch ho

/-- **The premise «first», at the place that the description seats on the last chain.** -/
theorem first_at_W {m : Made} {N : H2U.Places4} (h : H2U.placesOfMade m = .ok N) :
    ∀ o ∈ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.first, ∃ c n, o.2 = .taken c n := by
  obtain ⟨A, X, hX, e⟩ := places_W h
  intro o ho
  have h1 := p12At_first _ _ o ho
  rw [e] at h1
  exact later_W hX o h1

/-- **The premise «seated»**: the proximity test's rounds are rounds of the description's last chain. -/
theorem seated_at (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (A : ProofFile.SharedSeat)
    (N : H2U.Places4)
    (c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl) :
    ∀ r ∈ (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
        (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) :
        VerifiableInference.Desc.Block VerifiableInference.Desc.K12.T12 Unit).rounds,
      r ∈ (ProofFile.fileDescBy o mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c).roundsDeclaredByBlocks.2.2 := by
  intro r hr
  show r ∈ ((ProofFile.fileDescBy o mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c).second.blocksInOrder).flatMap
    (·.rounds)
  rw [last_blocks_in]
  exact List.mem_flatMap.2 ⟨(ownAt N).retype,
    List.mem_map.2 ⟨ownAt N, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl⟩, hr⟩

end ToldDesc

#print axioms ToldDesc.seated_at
#print axioms ToldDesc.later_W
#print axioms ToldDesc.places_W
#print axioms ToldDesc.p12At_first
#print axioms ToldDesc.first_at_W
