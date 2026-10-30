-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeedAtRecord.lean: from what three tests with code say of the record d in front of
a proximity test's seat (the codes are cs · message number o has the plan's shape sh · the test
`sampleL` says yes of it at every seat with that shape and number) to what the seam asks at a member
j of the test's plain data with that number. Statements and proofs. No new mathematics.

  `made_msg`: whatever the kind's record fixes: the plain data's statement holds each message of the
    record with its shape, its mark "sampled" and its sample rows.
  `sampleL_congr`: `sampleL` reads of a message its mark and its sample rows alone.
  `seed_at_record`: (i) the sendings' invariant `K1.SeedIs` at the kind's record.
  `sampleL_at_record`: (ii) THE SECOND CLAUSE OF `MemberFacts`: `sampleL`'s yes at the member's own
    seat and at the plain data's message. No read-back of a seed is spent: so at every shape.
  `at_record`: both.
Limits. The three tests' content is a premise: it is shown at no seat here. `Tie cs sh` is a test on
the plan, asked for (i) alone. General in the seat, the arm, the chain and the number of members. No
soundness is claimed.
Words, as this file uses them: «record» is the verifier's state, never
the OOD sample on a committed table; «block»: a sub-protocol; «plan»: the list of rounds; «yes»: an
acceptance; «seed»: a sampled message's OOD seed; «description»: the IOP as written in Lean.

-/
import Johnson.Desc.Sound.SeedAtKind
import Johnson.Desc.Sound.SeedOfAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open Cb Cb.Ood OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (Fixes)
open H2K.First (Seat1 Plain ok made_of)
open H2K.Pin (sampleL)

/-- **The plain data hold the record's messages**: shape, mark and sample rows. -/
theorem made_msg {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
    {Ly : GroupLayout} {D : Plain} (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow) {o : ℕ}
    {x : OnBytes.Oracle} (hx : t.st.oracles[o]? = some x) :
    ∃ o', D.st.oracles[o]? = some o' ∧ o'.shape = x.shape ∧ o'.sampled = x.sampled ∧
      o'.sampleRows = x.sampleRows := by
  have e : (begun t.st t.g G0).oracles[o]? = (t.st.oracles[o]?).map fun x =>
      if o ∈ G0.members.toList then shut x else x := closeLedgers_get _ _ _
  rw [hx] at e
  have ho : o < (begun t.st t.g G0).oracles.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at e
    cases e
  have hD := H2K.Pin.oracle_made (made_of π _ a Ly D (hf.2.2.2 row₀)) o ho
  refine ⟨_, hD.trans e, ?_, ?_, ?_⟩ <;> split <;> rfl

/-- `sampleL` reads of a message its mark and its sample rows alone. -/
theorem sampleL_congr (K : Codes) (m : Seat1) {x x' : OnBytes.Oracle}
    (h1 : x'.sampled = x.sampled) (h2 : x'.sampleRows = x.sampleRows) :
    sampleL K m x' = sampleL K m x := by
  simp only [sampleL, h1, h2]

section
variable {cs : Codes} {sh : OracleShape} {π : P12} {t : T12} {a : Fmt.M1.Stage}
  {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain} {St₀ : Statement} {o : ℕ}

/-- **(i) The invariant at the kind's record.** St₀: the statement of the record in front of the
seat. -/
theorem seed_at_record (hst : t.st = St₀) (hc : St₀.codes = cs)
    (hm : ∃ x, St₀.oracles[o]? = some x ∧ x.shape = sh ∧
      ∀ m : Seat1, m.sh = sh → m.id = o → ok (sampleL cs m x) = true)
    (hT : K1.Tie cs sh) : ∃ ρ y, K1.SeedIs cs sh t.st o ρ y := by
  obtain ⟨x, hx, hs, hq⟩ := hm
  subst hst
  exact seedIs_of_sampleL (m := ⟨o, sh, 0, 0, default, 0⟩) (hq _ rfl rfl) hx hs hc hT

/-- **(ii) `sampleL`'s yes at the member's own seat, at the plain data's message.** -/
theorem sampleL_at_record (hst : t.st = St₀)
    (hm : ∃ x, St₀.oracles[o]? = some x ∧ x.shape = sh ∧
      ∀ m : Seat1, m.sh = sh → m.id = o → ok (sampleL cs m x) = true)
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow) (j : Fin D.mems.length)
    (hj : (D.mems.get j).id = o) :
    ∃ o', D.st.oracles[(D.mems.get j).id]? = some o' ∧
      ok (sampleL cs (D.mems.get j) o') = true := by
  obtain ⟨x, hx, hs, hq⟩ := hm
  subst hst
  obtain ⟨o', ho', e1, e2, e3⟩ := made_msg hf row₀ hx
  obtain ⟨x₁, hx₁, ex⟩ := ((made_of π _ a Ly D (hf.2.2.2 row₀)).mem j).2.oracle
  rw [hj, ho'] at hx₁
  obtain rfl := Option.some.inj hx₁
  refine ⟨o', by rw [hj]; exact ho', ?_⟩
  rw [sampleL_congr cs _ e2 e3]
  exact hq _ (ex.symm.trans (e1.trans hs)) hj

/-- **Both.** -/
theorem at_record (hst : t.st = St₀) (hc : St₀.codes = cs)
    (hm : ∃ x, St₀.oracles[o]? = some x ∧ x.shape = sh ∧
      ∀ m : Seat1, m.sh = sh → m.id = o → ok (sampleL cs m x) = true)
    (hT : K1.Tie cs sh) (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow)
    (j : Fin D.mems.length) (hj : (D.mems.get j).id = o) :
    (∃ ρ y, K1.SeedIs cs sh t.st o ρ y) ∧
    ∃ o', D.st.oracles[(D.mems.get j).id]? = some o' ∧
      ok (sampleL cs (D.mems.get j) o') = true :=
  ⟨seed_at_record hst hc hm hT, sampleL_at_record hst hm hf row₀ j hj⟩

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.made_msg
#print axioms Desc.K14.Law.Fence.sampleL_congr
#print axioms Desc.K14.Law.Fence.seed_at_record
#print axioms Desc.K14.Law.Fence.sampleL_at_record
#print axioms Desc.K14.Law.Fence.at_record
