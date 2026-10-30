-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SigHeld.lean: THE PROOFS OF TWO OF THE STATEMENTS THAT
Johnson/Desc/K13/Law/OwedSig.lean WRITES AS OWED: the sample that the record holds of a tenant
(`smpSeed`, Johnson/Desc/SmpRows.lean) stays over a step of kind K13's block (M:3) and over a step
of W's commitment (M:4). Statements with their proofs.
Main names:
  `same_at`: what `SameAll` (Johnson/Desc/K13/Law/PinDec.lean) says of one number: no message at
    either statement, or one at each with the same shape, mark and sample rows.
  `smpSeed_same`: **one book, two statements with `SameAll`: one sample at EVERY tenant**, held or
    not.
  `seed3`: the first owed statement: the block leaves the book (`atM3_rec`) and that part of the
    statement (`atM3_same`).
  `smpStay4`: over a step of W's commitment every sampled message stays (`K1.SmpStay`): the sending
    leaves an older message whole (`K1.sendAtS_kept`); the block behind it leaves every message's
    shape, mark and sample rows (`rowsB_same`).
  `seed4`: the second owed statement: by the kind-free `K1.smpHeldStays`
    (Johnson/Desc/K1/Law/SmpHeldStays.lean), called at `smpStay4` and at the book's own equation
    (`atM4_booked`: places are appended).
What is not claimed. Of `OwedSeed4`'s two premises "the book has a place for every message" IS NOT
SPENT: the statement holds without it. Nothing on a tenant whose sample is not held in front of W's
commitment. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.OwedSig
import Johnson.Desc.K1.Law.SmpHeldStays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)

/-- What `SameAll` says of one number. -/
theorem same_at {A B : Statement} (h : SameAll A B) (o : ℕ) :
    (A.oracles[o]? = none ∧ B.oracles[o]? = none) ∨
      ∃ a b : OnBytes.Oracle, A.oracles[o]? = some a ∧ B.oracles[o]? = some b ∧
        b.shape = a.shape ∧ b.sampled = a.sampled ∧ b.sampleRows = a.sampleRows := by
  have e := h.2 o
  unfold sampleOf at e
  cases hA : A.oracles[o]? with
  | none =>
    rw [hA, Option.map_none, Option.map_eq_none_iff] at e
    exact Or.inl ⟨rfl, e⟩
  | some a =>
    rw [hA, Option.map_some] at e
    obtain ⟨b, hb, eb⟩ := Option.map_eq_some_iff.1 e
    simp only [Prod.mk.injEq] at eb
    exact Or.inr ⟨a, b, rfl, hb, eb.1, eb.2.1, eb.2.2.1⟩

/-- **One book, the same part of the statement: one sample at every tenant.** -/
theorem smpSeed_same {A B : Statement} (h : SameAll A B) (bk : TreeBook) (j t : ℕ) :
    smpSeed B bk j t = smpSeed A bk j t := by
  cases ho : oracleNo bk j t with
  | none =>
    unfold smpSeed
    rw [ho]
    rfl
  | some o =>
    rcases same_at h o with ⟨hA, hB⟩ | ⟨a, b, hA, hB, e1, e2, e3⟩
    · unfold smpSeed
      rw [ho]
      show (B.oracles[o]?).bind _ = (A.oracles[o]?).bind _
      rw [hA, hB]
      rfl
    · have hrows : smpRows B bk j t = smpRows A bk j t := by
        unfold smpRows
        rw [ho]
        show (B.oracles[o]?).bind _ = (A.oracles[o]?).bind _
        rw [hA, hB]
        show (if b.sampled && decide (0 < b.shape.answers) &&
            b.sampleRows.size == b.shape.answers then some b.sampleRows else none) =
          (if a.sampled && decide (0 < a.shape.answers) &&
            a.sampleRows.size == a.shape.answers then some a.sampleRows else none)
        rw [e1, e2, e3]
      unfold smpSeed
      rw [hrows, ho]
      show (B.oracles[o]?).bind _ = (A.oracles[o]?).bind _
      rw [hA, hB]
      show ((smpRows A bk j t).bind fun rows => (rows[0]?).bind fun r =>
          (seedOf B.codes b.shape r).map fun sd => (sd, rows.toList.map (·.target))) =
        ((smpRows A bk j t).bind fun rows => (rows[0]?).bind fun r =>
          (seedOf A.codes a.shape r).map fun sd => (sd, rows.toList.map (·.target)))
      rw [h.1, e1]

/-- **The first owed statement.** -/
theorem seed3 : OwedSeed3 := by
  intro Pp Cl P x x' j t h
  obtain ⟨rs, gs, hd⟩ := h.2
  obtain ⟨f, st', o, _, e⟩ := atM3_rec hd
  have hbk : x'.2.book = x.2.book := by rw [e]
  rw [hbk]
  exact smpSeed_same (atM3_same hd) _ j t

/-- **Over a step of W's commitment every sampled message stays.** -/
theorem smpStay4 {Pp Cl : Type} {P : Where} {P' : K1.Par} {x x' : Pp × S}
    (h : StepM4 Cl P P' x x') : K1.SmpStay x.2.st x'.2.st := by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid hd
  have hk := K1.sendAtS_kept P' x.2 s₁ _ g₁ h1
  have hs := rowsB_same h2
  refine ⟨hs.1.trans hk.1, fun i a hi ha => ?_⟩
  have hlt : i < x.2.st.oracles.size := (Array.getElem?_eq_some_iff.1 hi).1
  have h₁ : s₁.st.oracles[i]? = some a := (hk.2.2 i hlt).trans hi
  rcases same_at hs i with ⟨hA, _⟩ | ⟨a', b, hA, hB, e1, e2, e3⟩
  · rw [h₁] at hA
    cases hA
  · obtain rfl : a = a' := Option.some.inj (h₁.symm.trans hA)
    exact ⟨b, hB, e1, e2.trans ha, e3⟩

/-- **The second owed statement.** -/
theorem seed4 : OwedSeed4 := by
  intro Pp Cl P P' x x' j t h _ hh
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  exact (K1.smpHeldStays x.2.st x'.2.st x.2.book x'.2.book _ j t (smpStay4 h)
    (atM4_booked hd).place hh).2.2.1

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.smpSeed_same
#print axioms VerifiableInference.Desc.K13.Law.seed3
#print axioms VerifiableInference.Desc.K13.Law.smpStay4
#print axioms VerifiableInference.Desc.K13.Law.seed4
