-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Written/MadeFacts.lean: eleven closed facts at the joined written term (`writtenMade`,
Johnson/Goal/Written/Made.lean): the two public tests on the plans, and nine conditions that reach
across the files or speak of a plan's form. Each of the nine has a plant that it refuses and the ten
other tests pass.

Definitions.
  `sizedTests Z`: the six tests on the sizes, as a list: `oneTableB`, `oneSizedTableB`, `oneRowsB`,
    `oneKLoB`, `slotsB`, `tauB` (Johnson/Desc/Ok/PlanWritten/Mixed.lean).
  `JoinedFacts`: the closed statement: for every eight strings h, `Desc.madeOk` and `Desc.fitOk` say
    yes at `writtenMade.at h`; the six tests on the sizes say yes at `writtenSized`; `oneSetB`,
    `workTableB`, `formsB` say yes at `writtenMade`.
  `atSizes Z`: `writtenMade` with other sizes. `withEntry E`: with another plan for the entry file.
Statements.
  `made_ok`, `fit_ok`, `sized_yes`, `one_set`, `work_table`, `forms_ok`; `joinedFacts :
    JoinedFacts`.
  Tools for the plants: `fitOk_of`, `workTableB_of`, `formsB_at`, `keyOk_of`, `proofOk_of`: the
    tests, from the plans' own. `plans_over`: over any sizes whose line on slots says 64 and whose
    link has the written table's shape, the four tests that read the plans say yes.
    `made_withEntry`, `fit_withEntry`, `work_withEntry`, `forms_withEntry`, `forms_no_withEntry`:
    the tests at another plan for the entry file follow from that plan's own.
  The plants on the sizes: `table_plant` (the link's table one row variable deeper),
    `sizedTable_plant` (one more in a distance's integer in the proof file's sized table),
    `rows_plant` (one more row in the shape of the key file's test), `kLo_plant`, `slots_plant` (one
    more request in the proof file's sizes): of the six tests on the sizes its own says no and the
    five others yes, and the five tests that read the plans say yes.
  `tau_plant`: with two instances in the setting in all ten places (the sizes', the key file's and
    the proof file's sizes', the seven plans') `tauB` says no, and the ten other tests say yes.
  The plants on the entry file's plan: `set_plant` (the other reading of the closeness bound in its
    setting), `work_plant` (31 bits of work for 32 in the entry of its round on positions),
    `form_plant` (the entry "RECORD" struck): its own test says no, the four others that read the
    plans say yes, and the sizes are untouched.
  `form_plants`: six more plans that `formB` refuses: "RECORD" in the second place; twice; with
    another number; in a plan of the proof file; struck from the key file's first plan; a "SEAL"
    with work.
By evaluations in Lean's kernel (`decide +kernel`): `sized_yes`, `one_set`, the plants' own lines
and premises. The rest is by proof from Johnson/Desc/Ok/NumberPrices/PlansAtWritten.lean.

What of OnBytes/Model/ is used: nothing by name.

Limits. That the term is what the planner configures at any public files is no theorem here; what
follows from the sizes is in Johnson/Goal/Written/MadeOfSized.lean. The sizes are held against the
plans by nothing here: that the stages for which the errors were computed are the shapes' own is not
asked. `oneSetB` compares written words: see the limits of Mixed.lean. What holds a written error:
see the head of Johnson/Desc/Ok/NumberPrices/AtWritten.lean. Nothing on soundness.
-/
import Johnson.Goal.Written.Made
import Johnson.Desc.Ok.NumberPrices.PlansAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten.Joined
open VerifiableInference VerifiableInference.Number.ByRuns VerifiableInference.PlanWritten
open VerifiableInference.PlanWritten.Mixed
open OnBytes OnBytes.Params Johnson.G Johnson.G.Runs Johnson.G.MadeFree Lk6.AtPlan

/-- The six tests on the sizes. -/
def sizedTests (Z : Sized) : List Bool :=
  [oneTableB Z, oneSizedTableB Z, oneRowsB Z, oneKLoB Z, slotsB Z, tauB Z]

/-! ## The eleven facts -/

/-- The public test on the prices says yes, whatever the eight strings. -/
theorem made_ok (h : Hung) : Desc.madeOk (writtenMade.at h) = true :=
  madeOk_join proof_lit_ok proofSizedFull keyFull h

/-- The public test on the format's words says yes, whatever the eight strings. -/
theorem fit_ok (h : Hung) : Desc.fitOk (writtenMade.at h) = true :=
  fitOk_join proofSizedFull keyFull h

/-- The six tests on the sizes say yes. -/
theorem sized_yes : sizedTests writtenSized = [true, true, true, true, true, true] := by
  decide +kernel

/-- All seven plans and the two files' sizes have one setting. -/
theorem one_set : oneSetB writtenMade = true := by decide +kernel

/-- Every round's bits of work are its plan's setting's. -/
theorem work_table : workTableB writtenMade = true := workTable_join proofSizedFull keyFull

/-- The seven plans have the form. -/
theorem forms_ok : formsB writtenMade = true := forms_join proofSizedFull keyFull

/-- The eleven together. -/
def JoinedFacts : Prop :=
  (∀ h : Hung, Desc.madeOk (writtenMade.at h) = true ∧ Desc.fitOk (writtenMade.at h) = true) ∧
    sizedTests writtenSized = [true, true, true, true, true, true] ∧
    oneSetB writtenMade = true ∧ workTableB writtenMade = true ∧ formsB writtenMade = true

/-- **They hold.** -/
theorem joinedFacts : JoinedFacts :=
  ⟨fun h => ⟨made_ok h, fit_ok h⟩, sized_yes, one_set, work_table, forms_ok⟩

/-! ## Tools for the plants -/

/-- The test on the format's words, from the seven plans' own. -/
theorem fitOk_of {c : Configured} {k₁ k₂ k₃ p₁ p₂ p₃ : Planned} (hk : c.key = [k₁, k₂, k₃])
    (hp : c.proof = [p₁, p₂, p₃]) (a₁ : k₁.plan.fit = true) (a₂ : k₂.plan.fit = true)
    (a₃ : k₃.plan.fit = true) (e : c.entry.plan.fit = true) (b₁ : p₁.plan.fit = true)
    (b₂ : p₂.plan.fit = true) (b₃ : p₃.plan.fit = true) : Desc.fitOk c = true := by
  unfold Desc.fitOk Desc.keyFit Desc.entryFit Desc.proofFit
  rw [hk, hp]
  simp [a₁, a₂, a₃, e, b₁, b₂, b₃]

/-- The test on the bits of work, from the seven plans' own. -/
theorem workTableB_of {W : Free} {k₁ k₂ k₃ p₁ p₂ p₃ : Planned} (hk : W.key = [k₁, k₂, k₃])
    (hp : W.proof = [p₁, p₂, p₃]) (a₁ : workB k₁ = true) (a₂ : workB k₂ = true)
    (a₃ : workB k₃ = true) (e : workB W.entry = true) (b₁ : workB p₁ = true)
    (b₂ : workB p₂ = true) (b₃ : workB p₃ = true) : workTableB W = true := by
  unfold workTableB
  rw [hk, hp]
  simp [a₁, a₂, a₃, e, b₁, b₂, b₃]

/-- What the test on the seven plans' form is, at three and three plans. -/
theorem formsB_at {W : Free} {k₁ k₂ k₃ p₁ p₂ p₃ : Planned} (hk : W.key = [k₁, k₂, k₃])
    (hp : W.proof = [p₁, p₂, p₃]) :
    formsB W = (formB W.sized.link.shape.table true k₁ &&
      formB W.sized.link.shape.table false k₂ && formB W.sized.link.shape.table false k₃ &&
      formB W.sized.link.shape.table true W.entry && formB W.sized.link.shape.table false p₁ &&
      formB W.sized.link.shape.table false p₂ && formB W.sized.link.shape.table false p₃) := by
  simp only [formsB, hk, hp]

/-- The joined term with other sizes. -/
def atSizes (Z : Sized) : Free := { writtenMade with sized := Z }

/-- The joined term with another plan for the entry file. -/
def withEntry (E : Planned) : Free := { writtenMade with entry := E }

/-- Over any sizes whose line on slots says 64 and whose link has the written table's shape, the
four tests that read the plans say yes. -/
theorem plans_over (Z : Sized) (hs : Z.lines.slots = Desc.slots)
    (hT : Z.link.shape.table = recordLink.table) (h : Hung) :
    Desc.madeOk ((atSizes Z).at h) = true ∧ Desc.fitOk ((atSizes Z).at h) = true ∧
      workTableB (atSizes Z) = true ∧ formsB (atSizes Z) = true := by
  refine ⟨(Desc.madeOk_iff _).2 ⟨keyOk_of_lit key_lit_ok _ rfl, entry_all,
    proofOk_of_lit proof_lit_ok _ rfl hs⟩,
    fitOk_of rfl rfl key_fit0 key_fit1 key_fit2 entry_fit proof_fit0 proof_fit1 proof_fit2,
    workTableB_of rfl rfl key_work0 key_work1 key_work2 entry_work proof_work0 proof_work1
      proof_work2, ?_⟩
  have hT' : (atSizes Z).sized.link.shape.table = recordLink.table := hT
  rw [formsB_at (W := atSizes Z) rfl rfl, hT']
  exact and7 key_form0 key_form1 key_form2 entry_form proof_form0 proof_form1 proof_form2

theorem made_withEntry (E : Planned) (hE : Desc.chainAll 32 E = true) (h : Hung) :
    Desc.madeOk ((withEntry E).at h) = true :=
  (Desc.madeOk_iff _).2 ⟨keyOk_of_lit key_lit_ok _ rfl, hE,
    proofOk_of_lit proof_lit_ok _ rfl record_slots⟩

theorem fit_withEntry (E : Planned) (hE : E.plan.fit = true) (h : Hung) :
    Desc.fitOk ((withEntry E).at h) = true :=
  fitOk_of rfl rfl key_fit0 key_fit1 key_fit2 hE proof_fit0 proof_fit1 proof_fit2

theorem work_withEntry (E : Planned) (hE : workB E = true) : workTableB (withEntry E) = true :=
  workTableB_of rfl rfl key_work0 key_work1 key_work2 hE proof_work0 proof_work1 proof_work2

theorem forms_withEntry (E : Planned) (hE : formB recordLink.table true E = true) :
    formsB (withEntry E) = true := by
  rw [formsB_at (W := withEntry E) rfl rfl]
  exact and7 key_form0 key_form1 key_form2 hE proof_form0 proof_form1 proof_form2

theorem forms_no_withEntry (E : Planned) (hE : formB recordLink.table true E = false) :
    formsB (withEntry E) = false := by
  have hE' : formB (withEntry E).sized.link.shape.table true (withEntry E).entry = false := hE
  rw [formsB_at (W := withEntry E) rfl rfl, hE']
  simp

/-! ## The plants on the sizes -/

/-- The sizes with the link's table one row variable deeper. -/
def tableBent : Sized :=
  { writtenSized with link := { writtenSized.link with shape := { writtenSized.link.shape with
      table := { writtenSized.link.shape.table with v := writtenSized.link.shape.table.v + 1 } } } }

set_option maxRecDepth 1000000 in
theorem table_forms : formsB (atSizes tableBent) = true := by
  rw [formsB_at (W := atSizes tableBent) rfl rfl]
  exact and7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem table_plant (h : Hung) :
    sizedTests tableBent = [false, true, true, true, true, true] ∧
      oneSetB (atSizes tableBent) = true ∧ Desc.madeOk ((atSizes tableBent).at h) = true ∧
      Desc.fitOk ((atSizes tableBent).at h) = true ∧ workTableB (atSizes tableBent) = true ∧
      formsB (atSizes tableBent) = true :=
  ⟨by decide +kernel, by decide +kernel,
    (Desc.madeOk_iff _).2 ⟨keyOk_of_lit key_lit_ok _ rfl, entry_all,
      proofOk_of_lit proof_lit_ok _ rfl record_slots⟩,
    fitOk_of rfl rfl key_fit0 key_fit1 key_fit2 entry_fit proof_fit0 proof_fit1 proof_fit2,
    workTableB_of rfl rfl key_work0 key_work1 key_work2 entry_work proof_work0 proof_work1
      proof_work2, table_forms⟩

/-- The sizes with one more in a distance's integer in the proof file's sized table. -/
def sizedTableBent : Sized :=
  { writtenSized with proof := { writtenSized.proof with batch := { writtenSized.proof.batch with
      table := { writtenSized.proof.batch.table with distances :=
        { writtenSized.proof.batch.table.distances with
          mLater := writtenSized.proof.batch.table.distances.mLater + 1 } } } } }

theorem sizedTable_plant (h : Hung) :
    sizedTests sizedTableBent = [true, false, true, true, true, true] ∧
      oneSetB (atSizes sizedTableBent) = true ∧
      Desc.madeOk ((atSizes sizedTableBent).at h) = true ∧
      Desc.fitOk ((atSizes sizedTableBent).at h) = true ∧
      workTableB (atSizes sizedTableBent) = true ∧ formsB (atSizes sizedTableBent) = true :=
  ⟨by decide +kernel, by decide +kernel, plans_over sizedTableBent record_slots rfl h⟩

/-- The sizes with one more row in the shape of the key file's test on the table. -/
def rowsBent : Sized :=
  { writtenSized with key := { writtenSized.key with once := { writtenSized.key.once with
      shape := { writtenSized.key.once.shape with
        matrixRows := writtenSized.key.once.shape.matrixRows + 1 } } } }

theorem rows_plant (h : Hung) :
    sizedTests rowsBent = [true, true, false, true, true, true] ∧
      oneSetB (atSizes rowsBent) = true ∧ Desc.madeOk ((atSizes rowsBent).at h) = true ∧
      Desc.fitOk ((atSizes rowsBent).at h) = true ∧ workTableB (atSizes rowsBent) = true ∧
      formsB (atSizes rowsBent) = true :=
  ⟨by decide +kernel, by decide +kernel, plans_over rowsBent record_slots rfl h⟩

/-- The sizes with one more in the key file's number of columns in a row of the table. -/
def kLoBent : Sized :=
  { writtenSized with key := { writtenSized.key with once := { writtenSized.key.once with
      shape := { writtenSized.key.once.shape with
        kLo := writtenSized.key.once.shape.kLo + 1 } } } }

theorem kLo_plant (h : Hung) :
    sizedTests kLoBent = [true, true, true, false, true, true] ∧
      oneSetB (atSizes kLoBent) = true ∧ Desc.madeOk ((atSizes kLoBent).at h) = true ∧
      Desc.fitOk ((atSizes kLoBent).at h) = true ∧ workTableB (atSizes kLoBent) = true ∧
      formsB (atSizes kLoBent) = true :=
  ⟨by decide +kernel, by decide +kernel, plans_over kLoBent record_slots rfl h⟩

/-- The sizes with one more request of a batch in the proof file's sizes. -/
def slotsBent : Sized :=
  { writtenSized with proof := { writtenSized.proof with batch := { writtenSized.proof.batch with
      lines := { writtenSized.proof.batch.lines with
        requests := writtenSized.proof.batch.lines.requests + 1 } } } }

theorem slots_plant (h : Hung) :
    sizedTests slotsBent = [true, true, true, true, false, true] ∧
      oneSetB (atSizes slotsBent) = true ∧ Desc.madeOk ((atSizes slotsBent).at h) = true ∧
      Desc.fitOk ((atSizes slotsBent).at h) = true ∧ workTableB (atSizes slotsBent) = true ∧
      formsB (atSizes slotsBent) = true :=
  ⟨by decide +kernel, by decide +kernel, plans_over slotsBent record_slots rfl h⟩

/-! ## Two instances, in all ten places -/

/-- The written setting with two instances. -/
def twoSet : Setting := { recordSet with instances := 2 }

/-- A written plan under that setting. -/
def twoLit (L : Lit) : Lit := ⟨twoSet, L.recs, L.runs⟩

/-- The joined term with two instances in the setting in all ten places. -/
def tauAll : Free :=
  ⟨{ writtenSized with
      set := twoSet
      proof := { writtenSized.proof with set := twoSet }
      key := { writtenSized.key with set := twoSet } },
    [(twoLit proofThree.A).plan, (twoLit proofThree.B).plan, (twoLit proofThree.C).plan],
    [(twoLit keyThree.A).plan, (twoLit keyThree.B).plan, (twoLit keyThree.C).plan],
    ⟨twoSet, pricedEntryFull.rounds⟩⟩

theorem tau_entry : Desc.chainAll 32 ⟨twoSet, pricedEntryFull.rounds⟩ = true := by decide +kernel

/-- The key file's own public test, from its three plans' own. -/
theorem keyOk_of {c : Configured} {A B C : Planned} (hc : c.key = [A, B, C])
    (a : Desc.chainAll 32 A = true) (b : Desc.chainAll 32 B = true)
    (d : Desc.chainAll 32 C = true) : Desc.keyOk c = true := by
  unfold Desc.keyOk
  rw [hc]
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨a, b⟩, d⟩

/-- The proof file's own public test, from its three plans' own and the line on slots. -/
theorem proofOk_of {c : Configured} {A B C : Planned} (hc : c.proof = [A, B, C])
    (a : Desc.chainAll 20 A = true) (b : Desc.chainAll 28 B = true)
    (d : Desc.chainAll 20 C = true) (hs : c.sized.lines.slots = Desc.slots) :
    Desc.proofOk c = true := by
  unfold Desc.proofOk
  rw [hc]
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨a, b⟩, d⟩,
    decide_eq_true hs⟩

theorem tau_key0 : Desc.chainAll 32 ⟨twoSet, pricedKeyRecsFull0⟩ = true := by decide +kernel
theorem tau_key1 : Desc.chainAll 32 ⟨twoSet, pricedKeyRecsFull1⟩ = true := by decide +kernel
theorem tau_key2 : Desc.chainAll 32 ⟨twoSet, pricedKeyRecsFull2⟩ = true := by decide +kernel
theorem tau_proof0 : Desc.chainAll 20 ⟨twoSet, pricedProofRecsFull0⟩ = true := by decide +kernel
theorem tau_proof1 : Desc.chainAll 28 ⟨twoSet, pricedProofRecsFull1⟩ = true := by decide +kernel
theorem tau_proof2 : Desc.chainAll 20 ⟨twoSet, pricedProofRecsFull2⟩ = true := by decide +kernel

theorem tau_made (h : Hung) : Desc.madeOk (tauAll.at h) = true :=
  (Desc.madeOk_iff _).2
    ⟨keyOk_of (A := (twoLit keyThree.A).plan) (B := (twoLit keyThree.B).plan)
        (C := (twoLit keyThree.C).plan) rfl (chainAll_of_runs pricedKeyRunsFull0 tau_key0)
        (chainAll_of_runs pricedKeyRunsFull1 tau_key1)
        (chainAll_of_runs pricedKeyRunsFull2 tau_key2),
      tau_entry,
      proofOk_of (A := (twoLit proofThree.A).plan) (B := (twoLit proofThree.B).plan)
        (C := (twoLit proofThree.C).plan) rfl (chainAll_of_runs pricedProofRunsFull0 tau_proof0)
        (chainAll_of_runs pricedProofRunsFull1 tau_proof1)
        (chainAll_of_runs pricedProofRunsFull2 tau_proof2)
        record_slots⟩

set_option maxRecDepth 1000000 in
theorem tau_fit (h : Hung) : Desc.fitOk (tauAll.at h) = true :=
  fitOk_of rfl rfl
    (fit_of_lit (twoLit keyThree.A) (by decide +kernel) (by decide +kernel))
    (fit_of_lit (twoLit keyThree.B) (by decide +kernel) (by decide +kernel))
    (fit_of_lit (twoLit keyThree.C) (by decide +kernel) (by decide +kernel))
    (by decide +kernel : (⟨twoSet, pricedEntryFull.rounds⟩ : Planned).plan.fit = true)
    (fit_of_lit (twoLit proofThree.A) (by decide +kernel) (by decide +kernel))
    (fit_of_lit (twoLit proofThree.B) (by decide +kernel) (by decide +kernel))
    (fit_of_lit (twoLit proofThree.C) (by decide +kernel) (by decide +kernel))

theorem tau_work : workTableB tauAll = true :=
  workTableB_of rfl rfl (workB_of_lit (twoLit keyThree.A) (by decide +kernel))
    (workB_of_lit (twoLit keyThree.B) (by decide +kernel))
    (workB_of_lit (twoLit keyThree.C) (by decide +kernel))
    (by decide +kernel : workB ⟨twoSet, pricedEntryFull.rounds⟩ = true)
    (workB_of_lit (twoLit proofThree.A) (by decide +kernel))
    (workB_of_lit (twoLit proofThree.B) (by decide +kernel))
    (workB_of_lit (twoLit proofThree.C) (by decide +kernel))

set_option maxRecDepth 1000000 in
theorem tau_forms : formsB tauAll = true := by
  rw [formsB_at (W := tauAll) rfl rfl]
  exact and7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem tau_plant (h : Hung) :
    sizedTests tauAll.sized = [true, true, true, true, true, false] ∧ oneSetB tauAll = true ∧
      Desc.madeOk (tauAll.at h) = true ∧ Desc.fitOk (tauAll.at h) = true ∧
      workTableB tauAll = true ∧ formsB tauAll = true :=
  ⟨by decide +kernel, by decide +kernel, tau_made h, tau_fit h, tau_work, tau_forms⟩

/-! ## The plants on the entry file's plan -/

/-- The entry file's plan with the other reading of the closeness bound in its setting. -/
def setBent : Planned := ⟨{ pricedEntryFull.set with printed := false }, pricedEntryFull.rounds⟩

theorem set_plant (h : Hung) :
    oneSetB (withEntry setBent) = false ∧ Desc.madeOk ((withEntry setBent).at h) = true ∧
      Desc.fitOk ((withEntry setBent).at h) = true ∧ workTableB (withEntry setBent) = true ∧
      formsB (withEntry setBent) = true ∧ (withEntry setBent).sized = writtenSized :=
  ⟨by decide +kernel, made_withEntry _ (by decide +kernel) h, fit_withEntry _ (by decide +kernel) h,
    work_withEntry _ (by decide +kernel), forms_withEntry _ (by decide +kernel), rfl⟩

/-- The rounds with f at the round i. -/
def turnAt : ℕ → (PlanRound → PlanRound) → List PlanRound → List PlanRound
  | _, _, [] => []
  | 0, f, r :: rs => f r :: rs
  | i + 1, f, r :: rs => r :: turnAt i f rs

/-- The entry file's plan with 31 bits of work for 32 in the entry of its round on positions. -/
def workBent : Planned :=
  ⟨pricedEntryFull.set,
    turnAt 4 (fun r => { r with entry := { r.entry with work := 31 } }) pricedEntryFull.rounds⟩

theorem work_plant (h : Hung) :
    workTableB (withEntry workBent) = false ∧ oneSetB (withEntry workBent) = true ∧
      Desc.madeOk ((withEntry workBent).at h) = true ∧
      Desc.fitOk ((withEntry workBent).at h) = true ∧ formsB (withEntry workBent) = true ∧
      (withEntry workBent).sized = writtenSized := by
  refine ⟨?_, by decide +kernel, made_withEntry _ (by decide +kernel) h,
    fit_withEntry _ (by decide +kernel) h, forms_withEntry _ (by decide +kernel), rfl⟩
  have w : workB workBent = false := by decide +kernel
  have hk : (withEntry workBent).key =
      [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] := rfl
  have he : (withEntry workBent).entry = workBent := rfl
  unfold workTableB
  rw [hk, he]
  simp [w]

/-- The entry file's plan with the entry "RECORD" struck from its head. -/
def formBent : Planned := ⟨pricedEntryFull.set, pricedEntryFull.rounds.drop 1⟩

theorem form_plant (h : Hung) :
    formsB (withEntry formBent) = false ∧ oneSetB (withEntry formBent) = true ∧
      Desc.madeOk ((withEntry formBent).at h) = true ∧
      Desc.fitOk ((withEntry formBent).at h) = true ∧ workTableB (withEntry formBent) = true ∧
      (withEntry formBent).sized = writtenSized :=
  ⟨forms_no_withEntry _ (by decide +kernel), by decide +kernel,
    made_withEntry _ (by decide +kernel) h, fit_withEntry _ (by decide +kernel) h,
    work_withEntry _ (by decide +kernel), rfl⟩

set_option maxRecDepth 1000000 in
/-- Six more plans that the test on a plan's form refuses: "RECORD" in the second place; twice; with
another number; in a plan of the proof file; struck from the key file's first plan; a "SEAL" with
work. -/
theorem form_plants :
    formB recordLink.table true ⟨pricedEntryFull.set,
        (pricedEntryFull.rounds.drop 1).take 1 ++ pricedEntryFull.rounds.take 1 ++
          pricedEntryFull.rounds.drop 2⟩ = false ∧
      formB recordLink.table true ⟨pricedEntryFull.set,
        pricedEntryFull.rounds.take 1 ++ pricedEntryFull.rounds⟩ = false ∧
      formB recordLink.table true ⟨pricedEntryFull.set,
        turnAt 0 (fun r => { r with entry := { r.entry with drawE := r.entry.drawE + 1 } })
          pricedEntryFull.rounds⟩ = false ∧
      formB recordLink.table false ⟨pricedProofSetFull,
        pricedEntryFull.rounds.take 1 ++ proofThree.C.plan.rounds⟩ = false ∧
      formB recordLink.table true ⟨pricedKeySetFull, keyThree.A.plan.rounds.drop 1⟩ = false ∧
      formB recordLink.table false ⟨pricedProofSetFull, proofThree.B.plan.rounds.map fun r =>
        if r.entry.name == "SEAL" then { r with entry := { r.entry with work := 1 } } else r⟩ =
          false := by
  decide +kernel

end VerifiableInference.PlanWritten.Joined

#print axioms VerifiableInference.PlanWritten.Joined.made_ok
#print axioms VerifiableInference.PlanWritten.Joined.fit_ok
#print axioms VerifiableInference.PlanWritten.Joined.sized_yes
#print axioms VerifiableInference.PlanWritten.Joined.one_set
#print axioms VerifiableInference.PlanWritten.Joined.work_table
#print axioms VerifiableInference.PlanWritten.Joined.forms_ok
#print axioms VerifiableInference.PlanWritten.Joined.joinedFacts
#print axioms VerifiableInference.PlanWritten.Joined.fitOk_of
#print axioms VerifiableInference.PlanWritten.Joined.workTableB_of
#print axioms VerifiableInference.PlanWritten.Joined.formsB_at
#print axioms VerifiableInference.PlanWritten.Joined.plans_over
#print axioms VerifiableInference.PlanWritten.Joined.made_withEntry
#print axioms VerifiableInference.PlanWritten.Joined.fit_withEntry
#print axioms VerifiableInference.PlanWritten.Joined.work_withEntry
#print axioms VerifiableInference.PlanWritten.Joined.forms_withEntry
#print axioms VerifiableInference.PlanWritten.Joined.forms_no_withEntry
#print axioms VerifiableInference.PlanWritten.Joined.table_forms
#print axioms VerifiableInference.PlanWritten.Joined.table_plant
#print axioms VerifiableInference.PlanWritten.Joined.sizedTable_plant
#print axioms VerifiableInference.PlanWritten.Joined.rows_plant
#print axioms VerifiableInference.PlanWritten.Joined.kLo_plant
#print axioms VerifiableInference.PlanWritten.Joined.slots_plant
#print axioms VerifiableInference.PlanWritten.Joined.tau_entry
#print axioms VerifiableInference.PlanWritten.Joined.keyOk_of
#print axioms VerifiableInference.PlanWritten.Joined.proofOk_of
#print axioms VerifiableInference.PlanWritten.Joined.tau_key0
#print axioms VerifiableInference.PlanWritten.Joined.tau_key1
#print axioms VerifiableInference.PlanWritten.Joined.tau_key2
#print axioms VerifiableInference.PlanWritten.Joined.tau_proof0
#print axioms VerifiableInference.PlanWritten.Joined.tau_proof1
#print axioms VerifiableInference.PlanWritten.Joined.tau_proof2
#print axioms VerifiableInference.PlanWritten.Joined.tau_made
#print axioms VerifiableInference.PlanWritten.Joined.tau_fit
#print axioms VerifiableInference.PlanWritten.Joined.tau_work
#print axioms VerifiableInference.PlanWritten.Joined.tau_forms
#print axioms VerifiableInference.PlanWritten.Joined.tau_plant
#print axioms VerifiableInference.PlanWritten.Joined.set_plant
#print axioms VerifiableInference.PlanWritten.Joined.work_plant
#print axioms VerifiableInference.PlanWritten.Joined.form_plant
#print axioms VerifiableInference.PlanWritten.Joined.form_plants
