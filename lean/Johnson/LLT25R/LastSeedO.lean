-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastSeedO.lean: THE SENDINGS' INVARIANT ON THE OOD SAMPLE AT OMEGA, AT THE
SHARED CHAIN's END (the field seedO of `FoldRest₃`, LastOwedCore.lean), FROM WHAT THE LAYER X
SAYS. `XSamples cs S X`: a condition on the letter X: wherever X says yes of a state d of the shared
chain, d's statement holds Omega's message at d.loc.oOmega, with the shape S.omega, and `sampleL`
accepts it. It is, up to the unfolding of `seatY sh o` (by a note on that file: { id := o, sh :=
sh, t := 0, part := 0, tsh := default, num := 0 }), the conclusion of
`Sh.omega_sampled` (Johnson/Desc/K14/Law/SharedConstLast.lean)
at X := `Sh.X A 12`, cs := A.Q.codes, S := A.Q.S
[held by reading that note, not the file].
  `seed_at_end`: **inside the book-keeping's yes at border 2, at e := what `endedX X` returns of d:
    the invariant `K1.SeedIs` at e's Omega**, from `XSamples` and the shape's tie. By `sampleAt_iff`
    and `seedIs_of_sampleAt` (ThreeAtW.lean); that the end's codes are the plan's is the
    start's own test.
Limits. `XSamples` is a premise. Nothing on soundness.
-/
import Johnson.LLT25R.LastRowZeroB
import Johnson.ToldDescR.ThreeAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice Johnson.Pack H2K.Pin
open VerifiableInference.Desc VerifiableInference.Desc.Last VerifiableInference.Desc.Third
open VerifiableInference.Desc.Third.Law
open _root_.Desc.K14 (St)

/-- **What the layer says of Omega's message.** -/
def XSamples (cs : Codes) (S : LinShape) (X : St → Bool) : Prop :=
  ∀ d, X d = true → ∃ x, d.st.oracles[d.loc.oOmega]? = some x ∧ x.shape = S.omega ∧
    ok (sampleL cs ⟨d.loc.oOmega, S.omega, 0, 0, default, 0⟩ x) = true

/-- **The invariant on the OOD sample at Omega, at the shared chain's end.** -/
theorem seed_at_end (p : P₁₄) (R : List Fmt.DeclaredRound) (f : Handed) (e : SharedOut) (s : S₃)
    (hk : shapeAt p R 2 f e s = true) (X : St → Bool) (d : St) (hX : XSamples p.codes p.S X)
    (he : endedX X d = some e) (hT : K1.Tie p.codes p.S.omega) :
    ∃ ρ yv, K1.SeedIs p.codes p.S.omega e.st e.omega ρ yv := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  obtain ⟨f', -, hst'⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨-, c2, -⟩ := start₃_inv _ _ _ _ hst'
  unfold endedX at he
  split at he
  · rename_i hXd
    obtain ⟨en, hen, rfl⟩ := Option.map_eq_some_iff.1 he
    unfold _root_.Desc.K14.ended at hen
    simp only at hen
    split at hen
    · obtain rfl := Option.some.inj hen
      obtain ⟨x, hx, hs, hq⟩ := hX d hXd
      refine ToldDesc.seedIs_of_sampleAt ((ToldDesc.sampleAt_iff _ _ _ _).1 ?_) c2 hT
      show ToldDesc.sampleAtB p.codes p.S.omega d.st d.loc.oOmega = true
      unfold ToldDesc.sampleAtB
      rw [hx]
      simp only [hs, decide_true, Bool.true_and]
      exact hq
    · cases hen
  · cases he

end LLT25

#print axioms LLT25.seed_at_end
