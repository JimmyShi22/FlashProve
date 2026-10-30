-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: what the filling lays at the request's own test and at the test on G_u.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/FoundOwnAndShared.lean: in the prover that onlineProverFromPublicFiles returns at
the unread filling onlineProverPartsInUse: the search at placeW in the last list finds the job's two parts
behind the guard; the search at placeU in the shared list finds the job's two parts, bare. So the
premise hg of five_at_own_test (Sim2/OwnTestEntry.lean), and its like at G_u, are paid there. No
property of the protocol is claimed.

  own_test_found_of_laid      from secondW ≠ [], LastTestMade: the places, the chain, the job, its
                              place, its word on the fresh table, its door, and the search
  six_not_at_test             no side of the six stands at the test on G_u
  shared_test_found_of_laid   from halfU ≠ [], TestOnUMade, and the six made: the job and the
                              search

Limits. Conditional on onlineProverFromPublicFiles's return. At that filling alone (K1/Law/WSideAtFill.lean's head). That a
half plays is not said. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.K14.NoStray

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open ProofFile.Honest
open ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light (ManyJob doorW)
open OnBytes (TableKey)

variable {W₀ : Type}

/-- **The search at the request's own test, from LastTestMade.** -/
theorem own_test_found_of_laid {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A)
    (hL : (secondW I o S O A.Z A.G :
      List (Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit)) ≠ []) :
    ∃ (N : H2U.Places4) (c : Chain P5J.TS ProofFile.Cl) (M : ManyJob (Local W₀ IndexCommitterCoins Inst Cells) Unit),
      H2U.placesOfMade A.Z.made = .ok N ∧ ProofFile.onlineFirstChainAt A.Z = .ok c ∧
      jobRealW S (P5J.F0T o A.Z N c) enterOwn O.pile (K1.lotNo o A.Z)
        (fun w => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩) (fun w => I.weights A.Z w.w₀)
        (fun P w => randAt P w.rc) A.Z A.G = some M ∧
      M.p = (fourOf N).W ∧ (∃ f, M.fresh = some f) ∧
      M.rec₀ = doorW (P5J.F0T o A.Z N c) (·.x) enterOwn placeW idleT12 ∧
      A.H.second.find? (fun g => g.place == placeW) =
        some ((proverSideOfProximityTest M.toRun.toTest :
          Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).needsField) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hA
  have hs' : A.H.second = secondW I o S O A.Z A.G := hs
  cases h1 : nowSharedBy (I.weights A.Z) A.Z with
  | error e => exact absurd (secondW_error I o S O A.G h1) hL
  | ok six =>
    cases h2 : H2U.placesOfMade A.Z.made with
    | error e => exact absurd (secondW_error_places I o S O A.G h2) hL
    | ok N =>
      cases h3 : ProofFile.onlineFirstChainAt A.Z with
      | error e => exact absurd (secondW_error_chain I o S O A.G h3) hL
      | ok c =>
        have e := secondW_ok (X := Unit) I o S O A.G h1 h2 h3
        cases hM : jobRealW S (P5J.F0T o A.Z N c) enterOwn O.pile (K1.lotNo o A.Z)
            (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩)
            (fun w => I.weights A.Z w.w₀) (fun P w => randAt P w.rc) A.Z A.G with
        | none =>
          refine absurd (e.trans ?_) hL
          unfold halfW realW
          rw [hM]
          rfl
        | some M =>
          have eh : (halfW S (P5J.F0T o A.Z N c) enterOwn O.pile (K1.lotNo o A.Z)
              (fun w => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩) (fun w => I.weights A.Z w.w₀)
              (fun P w => randAt P w.rc) A.Z A.G :
              List (Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit)) =
              [(proverSideOfProximityTest M.toRun.toTest :
                Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).needsField] := by
            unfold halfW realW
            rw [hM]
            rfl
          have hM' := hM
          unfold jobRealW at hM'
          obtain ⟨F, hF, hM'⟩ := Option.bind_eq_some_iff.1 hM'
          obtain ⟨Ap, -, hM'⟩ := Option.bind_eq_some_iff.1 hM'
          obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM'
          have hFN : F = fourOf N := by
            unfold four at hF
            rw [h2] at hF
            exact (Option.some.inj hF).symm
          subst hFN
          refine ⟨N, c, _, rfl, rfl, hM, rfl, ⟨_, rfl⟩, rfl, ?_⟩
          rw [hs', e, eh]
          refine List.find?_cons_of_pos ?_
          show ((fourOf N).W.place == placeW) = true
          have hp : (fourOf N).W.place = placeW := p12At_place _ _
          rw [hp]
          exact beq_self_eq_true _

/-- No side of the six stands at the test on G_u. -/
theorem six_not_at_test {Z : Pub} (wt : W₀ → Weights)
    {six : List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)}
    (h : nowSharedBy wt Z = .ok six) : ∀ g ∈ six, g.place ≠ placeU := by
  unfold nowSharedBy at h
  obtain ⟨P, -, h⟩ := exBind_ok h
  cases hd : due? "the shared chain's place in the description" (onlineSharedChain Z) with
  | error e =>
    rw [hd] at h
    cases h
  | ok s =>
    rw [hd] at h
    change K14.sixOf P s.chain.blocksInOrder wt _ = .ok six at h
    unfold K14.sixOf at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i d _
        obtain rfl := Except.ok.inj h
        intro g hg e
        have hp := K14.six_places d _ wt _ g hg
        rw [e] at hp
        exact absurd hp (by decide)

/-- **The search at the test on G_u, from TestOnUMade and the six made.** -/
theorem shared_test_found_of_laid {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A)
    {six : List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)}
    (h1 : nowSharedBy (I.weights A.Z) A.Z = .ok six)
    (hU : halfU (I.weights A.Z) (fun w => Bind.ForProver.encW A.Z (I.weights A.Z w)) A.Z ≠ []) :
    ∃ M : ManyJob (Common W₀ IndexCommitterCoins TableKey) Unit,
      jobRealU (I.weights A.Z) (fun w => Bind.ForProver.encW A.Z (I.weights A.Z w)) A.Z = some M ∧
      A.H.shared.find? (fun g => g.place == placeU) = some (proverSideOfProximityTest M.toRun.toTest) := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hA
  have hs' : A.H.shared = sharedWithUO I A.Z := hs
  have e0 : sharedWithUO I A.Z =
      six ++ halfU (I.weights A.Z) (fun w => Bind.ForProver.encW A.Z (I.weights A.Z w)) A.Z ++
        halfO (I.weights A.Z) A.Z := by
    show (match nowSharedBy (I.weights A.Z) A.Z with
      | .ok six =>
        six ++ halfU (I.weights A.Z) (fun w => Bind.ForProver.encW A.Z (I.weights A.Z w)) A.Z ++
          halfO (I.weights A.Z) A.Z
      | .error _ => []) = _
    rw [h1]
  cases hM : jobRealU (I.weights A.Z) (fun w => Bind.ForProver.encW A.Z (I.weights A.Z w)) A.Z with
  | none =>
    refine absurd ?_ hU
    unfold halfU realU
    rw [hM]
    rfl
  | some M =>
    have eh : halfU (I.weights A.Z) (fun w => Bind.ForProver.encW A.Z (I.weights A.Z w)) A.Z =
        [proverSideOfProximityTest M.toRun.toTest] := by
      unfold halfU realU
      rw [hM]
      rfl
    have hM' := hM
    unfold jobRealU at hM'
    obtain ⟨F, hF, hM'⟩ := Option.bind_eq_some_iff.1 hM'
    obtain ⟨Ap, -, hM'⟩ := Option.bind_eq_some_iff.1 hM'
    obtain ⟨bs, -, hMb⟩ := Option.map_eq_some_iff.1 hM'
    have hpM : M.p = F.U := by
      rw [← hMb]
      rfl
    have hpl : F.U.place = placeU := by
      unfold four at hF
      split at hF
      · obtain rfl := Option.some.inj hF
        exact p12At_place _ _
      · cases hF
    refine ⟨M, rfl, ?_⟩
    have hn : six.find? (fun g => g.place == placeU) = none := by
      refine List.find?_eq_none.2 fun g hg hb => ?_
      exact six_not_at_test _ h1 g hg (beq_iff_eq.1 hb)
    have hc : List.find? (fun g : Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit => g.place == placeU)
        [proverSideOfProximityTest M.toRun.toTest] = some (proverSideOfProximityTest M.toRun.toTest) := by
      refine List.find?_cons_of_pos ?_
      show (M.p.place == placeU) = true
      rw [hpM, hpl]
      exact beq_self_eq_true _
    rw [hs', e0, eh, List.find?_append, List.find?_append, hn, hc]
    rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.own_test_found_of_laid
#print axioms ProofFile.Honest.K12.Sim2.six_not_at_test
#print axioms ProofFile.Honest.K12.Sim2.shared_test_found_of_laid
