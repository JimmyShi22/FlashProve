-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeedTwo.lean: THE SECOND CLAUSE OF `MemberFacts` (Johnson/Desc/Sound/
SeamMembers.lean: the yes of the test with code `sampleL` at a member's message in the test's plain
data), from the sendings' invariant at the record in front of the test and five facts on the plan's
shape. One statement with its proof: two calls.

  `two_at_member`: by `seed_at_member` (Johnson/Desc/Sound/SeedAtKind.lean) and K12's files'
    read-back law `sampleL_of_seed` (Johnson/Desc/K12/Law/SampleOfSeed.lean).
Limits. As the read-back law's: a shape with rows of one kind alone. That a record holds the
invariant is a premise. General in the seat, the arm, the chain and the number of members. No
soundness is claimed.
Words, as this file uses them: «record» is the verifier's state, never
the OOD sample on a committed table; «block»: a sub-protocol; «plan»: the list of rounds; «yes»: an
acceptance; «seed»: a sampled message's OOD seed; «description»: the IOP as written in Lean.

-/
import Johnson.Desc.Sound.SeedAtKind
import Johnson.Desc.K12.Law.SampleOfSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open Cb Cb.Ood OnBytes OnBytes.Params OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (Fixes)
open H2K.First (Seat1 Plain ok)
open H2K.Pin (sampleL sampleL_of_seed)
open H2K.Pin (mainB maskB)

theorem two_at_member {cs : Codes} {s : OracleShape} {π : P12} {t : T12} {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain}
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow) (j : Fin D.mems.length) (hT : K1.Tie cs s)
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE}
    (h : K1.SeedIs cs s t.st (D.mems.get j).id ρ y)
    (hone : ¬ (0 < s.mainRows ∧ 0 < s.maskRows)) (hsome : 0 < s.mainRows ∨ 0 < s.maskRows)
    (hcase : (0 < s.maskRows ∨ s.mainDeg = 3) ∨ (s.maskRows = 0 ∧ s.mainDeg = 1))
    (hpM : s.mainRows = 0 ∨ 2 ^ ceilLog2 (mainB cs s).ell = (mainB cs s).ell)
    (hpZ : s.maskRows = 0 ∨ 2 ^ ceilLog2 (maskB cs s).ell = (maskB cs s).ell) :
    ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
      ok (sampleL cs (D.mems.get j) o) = true := by
  obtain ⟨hs, x, seed, row0, tt, β, hx, h1, hform, hr, hl, hb⟩ := seed_at_member hf row₀ j hT h
  subst hs
  exact ⟨x, hx, sampleL_of_seed cs (D.mems.get j) x seed row0 tt β h1 hform hr hl hb hT.one hone
    hsome hcase hpM hpZ⟩

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.two_at_member
