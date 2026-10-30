-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeedAtKind.lean: the sendings' invariant `K1.SeedIs` (Johnson/Desc/K1/Law/
SeedIs.lean), carried from the record in front of a proximity test to the test's own plain data, and
what it gives there of one member. Statements and proofs. No new mathematics.

  `seedIs_of_part`: the invariant is kept by every step that leaves the codes and, at the message's
    number, the shape, the mark "sampled" and the sample rows. (That triple is the text of
    `smpPart`, Johnson/Desc/K12/Coin/SamplesThrough.lean: so its `onGu_leaves`, `onGomega_leaves`
    and `KeepsSmp` (SamplesAtK14.lean, beside this file) feed this lemma as they lie.)
  `seedIs_begun`: past the beginning of a test.  `seedIs_made`: into the plain data.
  `seedIs_fixes`: from the kind's record t to whatever the record fixes (`Fixes`,
    Johnson/Desc/K12/Coin/Sheet.lean).
  `member_of_seedIs`: at a member j of the plain data: if the record holds the invariant at the
    member's number at a shape s (the plan's), then THE MEMBER's SHAPE IS s, and the plain data's
    statement holds the invariant there.
  `seed_at_member`: so: the message, `Send.form`'s row at a seed, the one sample row, the seed's
    length and its factor's reading: all that is said of the row, at the member's own shape.
  `six_at_member`: THE SIXTH CLAUSE OF `MemberFacts` (Johnson/Desc/Sound/SeamMembers.lean), where the
    reading smp is `K1.smpAt` at the record's statement and the member's number.
Limits. That a record in front of a test holds the invariant is a premise: it is shown at no seat
here. General in the place, the arm and the chain. No soundness is claimed.
Words, as this file uses them: «record» is the verifier's state, never
the OOD sample on a committed table; «block»: a sub-protocol; «plan»: the list of rounds; «yes»: an
acceptance; «seed»: a sampled message's OOD seed; «description»: the IOP as written in Lean.

-/
import Johnson.Desc.Sound.SeedAtSeam
import Johnson.Desc.K12.Law.TieFront
import Johnson.Desc.K12.Coin.Sheet
import OnBytes.Slice.BlkLinkHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open Cb Cb.Ood OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (Fixes)
open H2K.First (Seat1 Plain Made made_of)

/-- **Kept where the codes and, at the number, the shape, the mark and the sample rows stay.** -/
theorem seedIs_of_part {cs : Codes} {s : OracleShape} {A B : Statement} {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : K1.SeedIs cs s A o ρ y)
    (hc : B.codes = A.codes)
    (hp : (B.oracles[o]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      (A.oracles[o]?).map fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) :
    K1.SeedIs cs s B o ρ y := by
  obtain ⟨h0, x, z, β, t, hx, h1, h2, h3, h4, h5⟩ := h
  rw [hx] at hp
  obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1 hp
  obtain ⟨e1, e23⟩ := Prod.mk.inj e
  obtain ⟨e2, e3⟩ := Prod.mk.inj e23
  exact ⟨hc.trans h0, x', z, β, t, hx', e1.trans h1, e2.trans h2, e3.trans h3, h4, h5⟩

/-- Past the beginning of a test. -/
theorem seedIs_begun {cs : Codes} {s : OracleShape} {S : Statement} {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : K1.SeedIs cs s S o ρ y) (g : ℕ) (G : Group) :
    K1.SeedIs cs s (begun S g G) o ρ y := by
  refine seedIs_of_part h (begun_codes S g G) ?_
  have e : (begun S g G).oracles[o]? = (S.oracles[o]?).map fun x =>
      if o ∈ G.members.toList then shut x else x := closeLedgers_get _ _ _
  rw [e, Option.map_map]
  congr 1
  funext x
  show ((if o ∈ G.members.toList then shut x else x).shape,
    (if o ∈ G.members.toList then shut x else x).sampled,
    (if o ∈ G.members.toList then shut x else x).sampleRows) = _
  split <;> rfl

/-- Into the plain data. -/
theorem seedIs_made {cs : Codes} {s : OracleShape} {p : P12} {t : T12} {a : Fmt.M1.Stage}
    {L : GroupLayout} {D : Plain} (hm : Made p t a L D) {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : K1.SeedIs cs s t.st o ρ y) :
    K1.SeedIs cs s D.st o ρ y := by
  have ho : o < t.st.oracles.size := by
    obtain ⟨_, x, _, _, _, hx, _⟩ := h
    by_contra hn
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at hx
    cases hx
  exact seedIs_of_part h (H2K.Pin.codes_made hm).symm (by rw [H2K.Pin.oracle_made hm o ho])

/-- **From the kind's record to whatever the record fixes.** -/
theorem seedIs_fixes {cs : Codes} {s : OracleShape} {π : P12} {t : T12} {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain}
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow) {o : ℕ}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : K1.SeedIs cs s t.st o ρ y) :
    K1.SeedIs cs s D.st o ρ y :=
  seedIs_made (made_of π _ a Ly D (hf.2.2.2 row₀)) (seedIs_begun h t.g G0)

/-- **The member's shape is the plan's, and the plain data hold the invariant.** -/
theorem member_of_seedIs {cs : Codes} {s : OracleShape} {π : P12} {t : T12} {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain}
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow) (j : Fin D.mems.length)
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE}
    (h : K1.SeedIs cs s t.st (D.mems.get j).id ρ y) :
    (D.mems.get j).sh = s ∧ K1.SeedIs cs s D.st (D.mems.get j).id ρ y := by
  have hD := seedIs_fixes hf row₀ h
  refine ⟨?_, hD⟩
  obtain ⟨x, hx, ex⟩ := ((made_of π _ a Ly D (hf.2.2.2 row₀)).mem j).2.oracle
  obtain ⟨_, x', _, _, _, hx', e', _⟩ := hD
  rw [hx] at hx'
  obtain rfl := Option.some.inj hx'
  exact ex.symm.trans e'

/-- **All that is said of the row, at the member's own shape.** -/
theorem seed_at_member {cs : Codes} {s : OracleShape} {π : P12} {t : T12} {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain}
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow) (j : Fin D.mems.length) (hT : K1.Tie cs s)
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE}
    (h : K1.SeedIs cs s t.st (D.mems.get j).id ρ y) :
    (D.mems.get j).sh = s ∧
    ∃ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
      D.st.oracles[(D.mems.get j).id]? = some x ∧ x.sampled = true ∧
      Send.form cs (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ cs (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta := by
  obtain ⟨hs, hD⟩ := member_of_seedIs hf row₀ j h
  subst hs
  exact ⟨rfl, seedAt_of_seedIs hT hD⟩

/-- **THE SIXTH CLAUSE OF `MemberFacts`, AT THE KIND's RECORD.** -/
theorem six_at_member (cs : Codes) {A : Type}
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (a0 : A)
    {s : OracleShape} {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    {G0 : Group} {Ly : GroupLayout} {D : Plain} (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow)
    (j : Fin D.mems.length) (x : Mem) (e0 : ℕ) (hx : x.1.l.get x.2 = (s, e0)) (hT : K1.Tie cs s)
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE}
    (h : K1.SeedIs cs s t.st (D.mems.get j).id ρ y)
    (hsmp : smp a0 x.1 x.2 =
      K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 t.st (D.mems.get j).id) :
    ∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
      D.st.oracles[(D.mems.get j).id]? = some o ∧
      Send.form cs (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
      o.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ cs (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      ∃ (z σ' : ((sigOf cs x.1.l).om x.2).Smp), smp a0 x.1 x.2 = some z ∧
        HEq (((readP (bitsZ cs (D.mems.get j).sh) seed.z, β), fun _ => readE tt) :
          (portOmZ cs (D.mems.get j).sh e0).Smp) σ' ∧ z.2 = σ'.2 ∧
        ((sigOf cs x.1.l).om x.2).Z.val z.1 = ((sigOf cs x.1.l).om x.2).Z.val σ'.1 := by
  obtain ⟨hs, hD⟩ := member_of_seedIs hf row₀ j h
  subst hs
  exact six_of_seedIs cs smp a0 D j x e0 hx hT ρ y hD t.st (D.mems.get j).id h hsmp

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.seedIs_of_part
#print axioms Desc.K14.Law.Fence.seedIs_fixes
#print axioms Desc.K14.Law.Fence.member_of_seedIs
#print axioms Desc.K14.Law.Fence.seed_at_member
#print axioms Desc.K14.Law.Fence.six_at_member
