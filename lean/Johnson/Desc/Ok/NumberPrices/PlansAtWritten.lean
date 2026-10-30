-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/PlansAtWritten.lean: three tests on each of the seven written priced
plans of the full size, plan by plan, and so at the joined term: the plan fits the format's words
(`Fmt.Plan.fit`, Fmt/ParamsReadLaws.lean; `Desc.fitOk`, Johnson/Desc/FitOk.lean); every round's bits
of work are those of the plan's setting (`workB`); the plan has the form (`formB`; both in
Johnson/Desc/Ok/PlanWritten/Mixed.lean).

`len_of_lit`, `fit_of_lit`, `workB_of_lit`, `all3`, `all7`, `and7` are tools. The facts plan by plan
are closed facts on written files. `fitOk_join`, `workTable_join`, `forms_join` hold at `joinMade PS
KS proofThree` (MadeAtWritten.lean) for all sizes PS and KS: none of the three tests reads these.

Statements.
  `len_of_lit`: the number of a written plan's entries, counted along the runs. `fit_of_lit`: a
    written plan fits the format's words if its five numbers and that number do and each record's
    entry does. `workB_of_lit`: `workB` at the records gives `workB` at the plan.
  `key_fit0`, `1`, `2`, `entry_fit`, `proof_fit0`, `1`, `2`; `key_work0` and so on; `key_form0` and
    so on: the three tests say yes at each plan. The table's shape in `formB` is that of the written
    link (`recordLink.table`); the key file's first plan and the entry file's plan are held to have
    the entry "RECORD", the five others to have none.
  `fitOk_join`, `workTable_join`, `forms_join`: so at the joined term.
By evaluations in Lean's kernel (`decide +kernel`): the facts plan by plan, or their premises.

What of OnBytes/Model/ is used: nothing by name.

Limits. The proof file's written plans stand on prints of the library's own planner (see the head of
ProofAtWritten.lean). What the three tests are good for is said by no theorem. Nothing on soundness.

-/
import Johnson.Desc.Ok.NumberPrices.MadeAtWritten
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
import Johnson.Desc.Ok.PlanWritten.Mixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number VerifiableInference.PlanWritten.Mixed
open OnBytes OnBytes.Params Johnson.G Johnson.G.Runs Johnson.G.MadeFree

/-! ## Tools -/

/-- The number of a written plan's entries, counted along the runs. -/
theorem len_of_lit (L : Lit) :
    L.plan.plan.entries.length = cntG (fun _ : PlanRound => true) 0 (valRuns L.recs L.runs) := by
  have e : L.plan.plan.entries.length = (unrunG L.recs L.runs).length := by
    show ((unrunG L.recs L.runs).map (·.entry)).length = _
    rw [List.length_map]
  rw [e, ← count_unrunG]
  simp

/-- A written plan fits the format's words if its numbers do and each record's entry does. -/
theorem fit_of_lit (L : Lit)
    (h1 : ([L.set.saltBytes, L.set.nonceBytes, L.set.positionBytes, L.set.samples, 1,
      cntG (fun _ : PlanRound => true) 0 (valRuns L.recs L.runs)].all
        fun n => decide (n < 2 ^ 64)) = true)
    (h2 : (L.recs.map (·.entry)).all Fmt.Entry.fit = true) : L.plan.plan.fit = true := by
  have e : L.plan.plan.entries.all Fmt.Entry.fit = true := by
    rw [entries_of_lit]
    exact all_of_recs L.runs h2
  have h1' : ([L.set.saltBytes, L.set.nonceBytes, L.set.positionBytes, L.set.samples, 1,
      L.plan.plan.entries.length].all fun n => decide (n < 2 ^ 64)) = true := by
    rw [len_of_lit]
    exact h1
  exact Bool.and_eq_true_iff.2 ⟨h1', e⟩

/-- The test on the bits of work at the records gives it at the plan. -/
theorem workB_of_lit (L : Lit) (h : workB ⟨L.set, L.recs⟩ = true) : workB L.plan = true :=
  all_of_recs L.runs h

theorem all3 {α : Type} {f : α → Bool} {a b c : α} (ha : f a = true) (hb : f b = true)
    (hc : f c = true) : [a, b, c].all f = true := by
  simp [ha, hb, hc]

theorem all7 {α : Type} {f : α → Bool} {a b c d e g i : α} (ha : f a = true) (hb : f b = true)
    (hc : f c = true) (hd : f d = true) (he : f e = true) (hg : f g = true) (hi : f i = true) :
    [a, b, c, d, e, g, i].all f = true := by
  simp [ha, hb, hc, hd, he, hg, hi]

theorem and7 {a b c d e g i : Bool} (ha : a = true) (hb : b = true) (hc : c = true)
    (hd : d = true) (he : e = true) (hg : g = true) (hi : i = true) :
    (a && b && c && d && e && g && i) = true := by
  simp [ha, hb, hc, hd, he, hg, hi]

/-! ## The plans fit the format's words -/

set_option maxRecDepth 1000000 in
theorem key_fit0 : keyThree.A.plan.plan.fit = true :=
  fit_of_lit keyThree.A (by decide +kernel) (by decide +kernel)

theorem key_fit1 : keyThree.B.plan.plan.fit = true :=
  fit_of_lit keyThree.B (by decide +kernel) (by decide +kernel)

theorem key_fit2 : keyThree.C.plan.plan.fit = true :=
  fit_of_lit keyThree.C (by decide +kernel) (by decide +kernel)

theorem entry_fit : pricedEntryFull.plan.fit = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem proof_fit0 : proofThree.A.plan.plan.fit = true :=
  fit_of_lit proofThree.A (by decide +kernel) (by decide +kernel)

theorem proof_fit1 : proofThree.B.plan.plan.fit = true :=
  fit_of_lit proofThree.B (by decide +kernel) (by decide +kernel)

theorem proof_fit2 : proofThree.C.plan.plan.fit = true :=
  fit_of_lit proofThree.C (by decide +kernel) (by decide +kernel)

/-! ## Every round's bits of work are the setting's -/

theorem key_work0 : workB keyThree.A.plan = true := workB_of_lit keyThree.A (by decide +kernel)
theorem key_work1 : workB keyThree.B.plan = true := workB_of_lit keyThree.B (by decide +kernel)
theorem key_work2 : workB keyThree.C.plan = true := workB_of_lit keyThree.C (by decide +kernel)
theorem entry_work : workB pricedEntryFull = true := by decide +kernel
theorem proof_work0 : workB proofThree.A.plan = true :=
  workB_of_lit proofThree.A (by decide +kernel)
theorem proof_work1 : workB proofThree.B.plan = true :=
  workB_of_lit proofThree.B (by decide +kernel)
theorem proof_work2 : workB proofThree.C.plan = true :=
  workB_of_lit proofThree.C (by decide +kernel)

/-! ## The plans have the form -/

set_option maxRecDepth 1000000 in
theorem key_form0 : formB recordLink.table true keyThree.A.plan = true := by decide +kernel
theorem key_form1 : formB recordLink.table false keyThree.B.plan = true := by decide +kernel
theorem key_form2 : formB recordLink.table false keyThree.C.plan = true := by decide +kernel
theorem entry_form : formB recordLink.table true pricedEntryFull = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem proof_form0 : formB recordLink.table false proofThree.A.plan = true := by decide +kernel
theorem proof_form1 : formB recordLink.table false proofThree.B.plan = true := by decide +kernel
theorem proof_form2 : formB recordLink.table false proofThree.C.plan = true := by decide +kernel

/-! ## At the joined term -/

/-- The plans of all seven chains fit the format's words, whatever the eight strings. -/
theorem fitOk_join (PS : ProofSized) (KS : Plan.KeySized) (h : Hung) :
    Desc.fitOk ((joinMade PS KS proofThree).at h) = true :=
  Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨all3 (f := fun P : Planned => P.plan.fit) key_fit0 key_fit1 key_fit2, entry_fit⟩,
    all3 (f := fun P : Planned => P.plan.fit) proof_fit0 proof_fit1 proof_fit2⟩

theorem workTable_join (PS : ProofSized) (KS : Plan.KeySized) :
    workTableB (joinMade PS KS proofThree) = true :=
  all7 (f := workB) key_work0 key_work1 key_work2 entry_work proof_work0 proof_work1 proof_work2

theorem forms_join (PS : ProofSized) (KS : Plan.KeySized) :
    formsB (joinMade PS KS proofThree) = true :=
  and7 key_form0 key_form1 key_form2 entry_form proof_form0 proof_form1 proof_form2

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.len_of_lit
#print axioms VerifiableInference.Number.ByRuns.fit_of_lit
#print axioms VerifiableInference.Number.ByRuns.workB_of_lit
#print axioms VerifiableInference.Number.ByRuns.all3
#print axioms VerifiableInference.Number.ByRuns.all7
#print axioms VerifiableInference.Number.ByRuns.and7
#print axioms VerifiableInference.Number.ByRuns.key_fit0
#print axioms VerifiableInference.Number.ByRuns.key_fit1
#print axioms VerifiableInference.Number.ByRuns.key_fit2
#print axioms VerifiableInference.Number.ByRuns.entry_fit
#print axioms VerifiableInference.Number.ByRuns.proof_fit0
#print axioms VerifiableInference.Number.ByRuns.proof_fit1
#print axioms VerifiableInference.Number.ByRuns.proof_fit2
#print axioms VerifiableInference.Number.ByRuns.key_work0
#print axioms VerifiableInference.Number.ByRuns.key_work1
#print axioms VerifiableInference.Number.ByRuns.key_work2
#print axioms VerifiableInference.Number.ByRuns.entry_work
#print axioms VerifiableInference.Number.ByRuns.proof_work0
#print axioms VerifiableInference.Number.ByRuns.proof_work1
#print axioms VerifiableInference.Number.ByRuns.proof_work2
#print axioms VerifiableInference.Number.ByRuns.key_form0
#print axioms VerifiableInference.Number.ByRuns.key_form1
#print axioms VerifiableInference.Number.ByRuns.key_form2
#print axioms VerifiableInference.Number.ByRuns.entry_form
#print axioms VerifiableInference.Number.ByRuns.proof_form0
#print axioms VerifiableInference.Number.ByRuns.proof_form1
#print axioms VerifiableInference.Number.ByRuns.proof_form2
#print axioms VerifiableInference.Number.ByRuns.fitOk_join
#print axioms VerifiableInference.Number.ByRuns.workTable_join
#print axioms VerifiableInference.Number.ByRuns.forms_join
