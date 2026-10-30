-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeedAtSeam.lean: two clauses of what the seam at a proximity test asks of one
member (`MemberFacts`, Johnson/Desc/Sound/SeamMembers.lean), from ONE invariant of the record.
Definitions, statements and proofs. No new mathematics: calls of the sendings' lemmas.

The invariant is the sendings' own: `K1.SeedIs cs sh St o ρ y` (Johnson/Desc/K1/Law/SeedIs.lean): the
statement St holds message number o, of the shape sh, marked as sampled, with just one sample row:
the kind's row at a point and a factor that read as the seed ρ, with a target that reads as y. It is
earned behind a yes of a sending (`seedIs_behind`, there) and kept along every step that leaves the
sampled messages (`SeedIs.stays`, Johnson/Desc/K1/Law/SealStays.lean).

  `SeedAt`: the same in the verifier program's letters (`Send.form`), without the seed's reading:
    the text that is wanted at the seam.
  `seed_of_seedIs`: `SeedIs` gives the message, its shape and mark, a seed and `Send.form`'s row at
    it, the one sample row, the seed's length, AND that ρ and y are that seed's and that target's
    readings. By `form_eq` (Johnson/Desc/K1/Law/FormEq.lean).
  `seedAt_of_seedIs`, `SeedAt.stays`.
  `smp_of_seedIs`: the reading of the sample off a statement (`K1.smpAt`) returns, at a shape and a
    radius that are equal to sh and e0, a sample that the library's sample map reads as ρ, with the
    answer y. By `smpAt_of` (Johnson/Desc/K1/Law/GoodSendForms.lean).
  `six_of_seedIs`: THE SIXTH CLAUSE OF `MemberFacts`, whole, at any reading smp that is `K1.smpAt` at
    some statement and number at which the invariant holds too.
Limits. That the invariant holds at a seat is shown nowhere here. `Tie cs sh` (one answer; the codes'
lengths; the shape's and the pad's tests) is a premise. Nothing on the second clause (`sampleL`'s
yes). No soundness is claimed.
Words, as this file uses them: «record» is the verifier's state, never
the OOD sample on a committed table; «block»: a sub-protocol; «plan»: the list of rounds; «yes»: an
acceptance; «seed»: a sampled message's OOD seed; «description»: the IOP as written in Lean.

-/
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.K12.Law.FirstOk
import Johnson.Desc.K1.Law.SealStays
import Johnson.Desc.K1.Law.GoodSendForms
import Johnson.Desc.K1.Law.FormEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open Cb Cb.Ood OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open H2K.First (Seat1 Plain)

/-- **A message's one sample row is the program's row at a seed.** -/
def SeedAt (cs : Codes) (sh : OracleShape) (St : Statement) (o : ℕ) : Prop :=
  ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
    St.oracles[o]? = some x ∧ x.sampled = true ∧ Send.form cs sh o seed 0 = some row0 ∧
    x.sampleRows.toList = [{ row0 with target := tt }] ∧ bitsZ cs sh ≤ seed.z.length ∧
    (β : GE) = readE seed.beta

/-- **The sendings' invariant, in the program's letters, with the seed's reading.** -/
theorem seed_of_seedIs {cs : Codes} {sh : OracleShape} {St : Statement} {o : ℕ}
    {ρ : (Fin (bitsZ cs sh) → GE) × GEˣ} {y : GE} (hT : K1.Tie cs sh)
    (h : K1.SeedIs cs sh St o ρ y) :
    ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E),
      St.oracles[o]? = some x ∧ x.shape = sh ∧ x.sampled = true ∧
      Send.form cs sh o seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧ bitsZ cs sh ≤ seed.z.length ∧
      (ρ.2 : GE) = readE seed.beta ∧ ρ.1 = readP (bitsZ cs sh) seed.z ∧ y = readE tt := by
  obtain ⟨_, x, z, β, t, hx, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨row0, hr, e2⟩ := Option.map_eq_some_iff.1
    (K1.form_eq cs sh o z β 0 t hT.lengths hT.shape hT.fits)
  refine ⟨x, ⟨z, β⟩, row0, t, hx, h1, h2, hr, ?_, h4.long, h4.factor.symm,
    funext fun i => (h4.point i).symm, h5.symm⟩
  rw [h3, e2]

theorem seedAt_of_seedIs {cs : Codes} {sh : OracleShape} {St : Statement} {o : ℕ}
    {ρ : (Fin (bitsZ cs sh) → GE) × GEˣ} {y : GE} (hT : K1.Tie cs sh)
    (h : K1.SeedIs cs sh St o ρ y) : SeedAt cs sh St o := by
  obtain ⟨x, seed, row0, tt, hx, _, hs, hf, hr, hl, hb, _, _⟩ := seed_of_seedIs hT h
  exact ⟨x, seed, row0, tt, ρ.2, hx, hs, hf, hr, hl, hb⟩

/-- It is kept along every step that leaves the sampled messages. -/
theorem SeedAt.stays {cs : Codes} {sh : OracleShape} {A B : Statement} {o : ℕ}
    (h : SeedAt cs sh A o) (hs : K1.SmpStay A B) : SeedAt cs sh B o := by
  obtain ⟨x, seed, row0, tt, β, hx, h1, hf, hr, hl, hb⟩ := h
  obtain ⟨x', hx', _, e2, e3⟩ := hs.2 o x hx h1
  exact ⟨x', seed, row0, tt, β, hx', e2, hf, by rw [e3]; exact hr, hl, hb⟩

/-- **The sample that is read off a statement**, at a shape and a radius equal to sh and e0. -/
theorem smp_of_seedIs (cs : Codes) (sh s' : OracleShape) (e0 e' : ℕ) (hs : s' = sh) (he : e' = e0)
    (St : Statement) (o : ℕ) (ρ : (Fin (bitsZ cs sh) → GE) × GEˣ) (y : GE) (hT : K1.Tie cs sh)
    (h : K1.SeedIs cs sh St o ρ y) :
    ∃ z σ' : (portOmZ cs s' e').Smp, K1.smpAt cs s' e' St o = some z ∧
      HEq ((ρ, fun _ => y) : (portOmZ cs sh e0).Smp) σ' ∧ z.2 = σ'.2 ∧
      (portOmZ cs s' e').Z.val z.1 = (portOmZ cs s' e').Z.val σ'.1 := by
  subst hs he
  obtain ⟨z, h1, h2, h3⟩ := K1.smpAt_of cs s' e' St o ρ y hT h
  exact ⟨z, (ρ, fun _ => y), h1, HEq.rfl, h3, h2⟩

/-- **THE SIXTH CLAUSE OF `MemberFacts`.** St₀, o₀: the statement and the number at which the reading
smp reads the sample. -/
theorem six_of_seedIs (cs : Codes) {A : Type}
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (a0 : A)
    (D : Plain) (j : Fin D.mems.length) (x : Mem) (e0 : ℕ)
    (hx : x.1.l.get x.2 = ((D.mems.get j).sh, e0)) (hT : K1.Tie cs (D.mems.get j).sh)
    (ρ : (Fin (bitsZ cs (D.mems.get j).sh) → GE) × GEˣ) (y : GE)
    (hD : K1.SeedIs cs (D.mems.get j).sh D.st (D.mems.get j).id ρ y) (St₀ : Statement) (o₀ : ℕ)
    (h0 : K1.SeedIs cs (D.mems.get j).sh St₀ o₀ ρ y)
    (hsmp : smp a0 x.1 x.2 = K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 St₀ o₀) :
    ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
      D.st.oracles[(D.mems.get j).id]? = some o ∧
      Send.form cs (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
      o.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ cs (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      ∃ (z σ' : ((sigOf cs x.1.l).om x.2).Smp), smp a0 x.1 x.2 = some z ∧
        HEq (((readP (bitsZ cs (D.mems.get j).sh) seed.z, β), fun _ => readE tt) :
          (portOmZ cs (D.mems.get j).sh e0).Smp) σ' ∧ z.2 = σ'.2 ∧
        ((sigOf cs x.1.l).om x.2).Z.val z.1 = ((sigOf cs x.1.l).om x.2).Z.val σ'.1 := by
  obtain ⟨o, seed, row0, tt, ho, _, _, hf, hr, hl, hb, hp, hy⟩ := seed_of_seedIs hT hD
  obtain ⟨z, σ', h1, h2, h3, h4⟩ := smp_of_seedIs cs (D.mems.get j).sh (x.1.l.get x.2).1 e0
    (x.1.l.get x.2).2 (by rw [hx]) (by rw [hx]) St₀ o₀ ρ y hT h0
  refine ⟨o, seed, row0, tt, ρ.2, ho, hf, hr, hl, hb, z, σ', hsmp.trans h1, ?_, h3, h4⟩
  rw [← hp, ← hy]
  exact h2

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.seed_of_seedIs
#print axioms Desc.K14.Law.Fence.seedAt_of_seedIs
#print axioms Desc.K14.Law.Fence.SeedAt.stays
#print axioms Desc.K14.Law.Fence.smp_of_seedIs
#print axioms Desc.K14.Law.Fence.six_of_seedIs
