-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeedOfAt.lean: the way back: from the program's letters to the sendings' invariant.
One statement with its proof. No new mathematics.

  `seedIs_of_seedAt`: where the statement's codes are cs, the message number o has the shape sh, and
    its one sample row is `Send.form`'s at a seed (`SeedAt`, Johnson/Desc/Sound/SeedAtSeam.lean): the
    sendings' invariant `K1.SeedIs` holds there, at the seed's and the target's readings.
Why. `SeedAt`'s conjuncts are what `sample_of_L` (Johnson/Desc/K12/Law/SampleLaw.lean)
concludes from the yes of the test with code `sampleL`. So a promise that holds that test's yes, the
message's shape and the codes holds the invariant too: nothing but tests with code need ride.
  `seedIs_of_sampleL`: so: from the yes of `sampleL` at a seat m and the statement's message number
    m.id, that message's shape being m.sh and the codes cs.
Limits. `Tie cs sh` is a premise. No soundness is claimed.
Words, as this file uses them: «record» is the verifier's state, never
the OOD sample on a committed table; «block»: a sub-protocol; «plan»: the list of rounds; «yes»: an
acceptance; «seed»: a sampled message's OOD seed; «description»: the IOP as written in Lean.

-/
import Johnson.Desc.Sound.SeedAtSeam
import Johnson.Desc.K12.Law.SampleLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open Cb Cb.Ood OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc

theorem seedIs_of_seedAt {cs : Codes} {sh : OracleShape} {St : Statement} {o : ℕ}
    (hT : K1.Tie cs sh) (hc : St.codes = cs) (h : SeedAt cs sh St o)
    (hsh : ∀ x, St.oracles[o]? = some x → x.shape = sh) :
    ∃ ρ y, K1.SeedIs cs sh St o ρ y := by
  obtain ⟨x, seed, row0, tt, β, hx, h1, hf, hr, hl, hb⟩ := h
  obtain ⟨z, b⟩ := seed
  have e := K1.form_eq cs sh o z b 0 tt hT.lengths hT.shape hT.fits
  rw [hf] at e
  have hrow := Option.some.inj e
  refine ⟨(readP (bitsZ cs sh) z, β), readE tt, hc, x, z, b, tt, hx, hsh x hx, h1, ?_,
    ⟨hl, fun _ => rfl, hb.symm⟩, rfl⟩
  apply Array.toList_inj.1
  rw [hr]
  exact congrArg (fun r => [r]) hrow

/-- **From the test with code.** -/
theorem seedIs_of_sampleL {cs : Codes} {m : H2K.First.Seat1} {x : OnBytes.Oracle} {St : Statement}
    (hq : H2K.First.ok (H2K.Pin.sampleL cs m x) = true) (hx : St.oracles[m.id]? = some x)
    (hsh : x.shape = m.sh) (hc : St.codes = cs) (hT : K1.Tie cs m.sh) :
    ∃ ρ y, K1.SeedIs cs m.sh St m.id ρ y := by
  obtain ⟨seed, row0, tt, β, hf, hr, hl, hb, _⟩ := H2K.Pin.sample_of_L hq
  have hs : x.sampled = true := by
    simp only [H2K.Pin.sampleL, H2K.First.ok, List.all_cons, Bool.and_eq_true] at hq
    exact hq.1
  refine seedIs_of_seedAt hT hc ⟨x, seed, row0, tt, β, hx, hs, hf, hr, hl, hb⟩ fun x' hx' => ?_
  rw [hx] at hx'
  obtain rfl := Option.some.inj hx'
  exact hsh

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.seedIs_of_seedAt
#print axioms Desc.K14.Law.Fence.seedIs_of_sampleL
