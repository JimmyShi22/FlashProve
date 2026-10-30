-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastSample.lean: THE THREE CONJUNCTS OF `FiveAt` ON THE OOD SAMPLE (the
sendings' invariant at the state in front; the reader smp is the reading off that state; the yes of
`sampleL`) AT THE LAST CHAIN's OWN PROXIMITY TEST, FROM FACTS AT THE TWO EARLIER CHAINS' ENDS: a
join of `three_elder` and `three_copy` (ToldDesc/ThreeAtW.lean).
  `sample_of_ends`: at a member that is an elder message: from `SampleAt` at the first chain's last
    state and "the reader is the reading off that state"; at Omega's copy: from the invariant at
    Omega in the shared chain's end, "the reader is the reading off that end", and `OneTable` at the
    shape. Both under `K1.Tie` at the shape, the book-keeping's yes at border 2, the door's yes and
    `Fixes`.
Limits. The facts at the ends are premises. Nothing on soundness.
-/
import Johnson.LLT25R.LastMembers
import Johnson.ToldDescR.ThreeAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open OnBytes OnBytes.Slice Johnson.Pack H2K.Pin
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Last VerifiableInference.Desc.Third
open VerifiableInference.Desc.K12.Seat (enterOwn)
open H2K.First (Plain)

/-- **The three on the OOD sample, from facts at the ends.** -/
theorem sample_of_ends (p : P₁₄) (R : List Fmt.DeclaredRound) (f : Handed) (e : SharedOut) (s : S₃)
    (t : T12) (π : P12) (st : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group)
    (Ly : GroupLayout) (D : Plain) (hk : shapeAt p R 2 f e s = true) (ht : enterOwn s = .ok t)
    (hf : Fixes π t st rest G0 Ly D) (j : Fin D.mems.length) (sh : OracleShape) (e0 : ℕ)
    (v : Option (portOmZ p.codes sh e0).Smp) (hT : K1.Tie p.codes sh)
    (h : (ToldDesc.SampleAt p.codes sh f.st (D.mems.get j).id ∧
        v = K1.smpAt p.codes sh e0 f.st (D.mems.get j).id) ∨
      ((D.mems.get j).id = s.loc.omega ∧ ToldDesc.OneTable p.codes sh ∧
        (∃ ρ yv, K1.SeedIs p.codes sh e.st e.omega ρ yv) ∧
        v = K1.smpAt p.codes sh e0 e.st e.omega)) :
    ToldDesc.ThreeOf p.codes sh e0 v t D j := by
  rcases h with ⟨hE, hv⟩ | ⟨hj, h1, hE, hv⟩
  · exact ToldDesc.three_elder hk ht hf j hT rfl hE hv
  · exact ToldDesc.three_copy hk ht hf j hT h1 hj hE hv

end LLT25

#print axioms LLT25.sample_of_ends
