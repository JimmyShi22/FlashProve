-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/Paid.lean: the premise's form `MSForm`
(Law/ExactFresh/Forms.lean) holds at the test `betaMarked`: one call of the law on the frame's
masked sumcheck's part beside its simulator (`exact_sumPart_field`, Honest/SumLaw/SumExact.lean). A
statement, `k4_msForm`, and its proof.

Limits. The statement is that law with its binders in another order: nothing is added to it, and
what its own head says of it holds here: an equation of two laws over uniform coins, at one member
by itself, all else fixed in front of the coins; the half of the part that spends the runs alone; at
every job, so that it says nothing on whether a job is the protocol's. A job is handed what is shown
in front of the part (`Front.seen`, Honest/Sum.lean): the rounds and, where they are handed, the
opened columns: in the equation these are fixed in front of the coins. Where an item that a job
reads was sent under an entry that is spent here, or a column that it reads is of a table that was
sent under such an entry, that is not so in a run, and the statement says nothing: it is the
caller's to meet (for items the condition stands in the head of Honest/Sum.lean; for columns that
law's head names no file that states it). The form ends in `ExactMember` (Honest/Small/Field.lean:
the text of `Good.exact` without its hypothesis on the opened columns) at every On: so the equation
is stated at every value of `m.opened` too. `k4_msForm` is called by no file that its writers know
of: Law/ExactFresh/Closed.lean, which imports this file, calls the law itself, in its form under
`shapeFair`.

Kin. The statement is `exact_sumPart_field` under this folder's form: see Limits. The attention
segments' files pay their own form of the same short name in the like way: `msForm_paid`
(Honest/K5/Law/GoodPaid.lean, of other writers; its form: `K5.MSForm`,
Honest/K5/Law/GoodForms.lean); neither file lies beneath this one. Sought: by statement, to the
letter and up to the bound letters, and by short name, among the theorems of the library as it lay
with the writer, and by short name among the definitions under Honest/: no hit. The search by
statement does not see a statement that has a binder in front of the colon where ours has it behind,
or the other way round.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.Forms
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open ProofFile.Honest.SumLaw (betaMarked exact_sumPart_field)

/-- **The form holds at `betaMarked`.** -/
theorem k4_msForm : MSForm betaMarked :=
  fun _ _ _ _ _ _ _ _ _ φ σ chain firstTree On bud see wit get set hgs hsg name endName J j rs a hk
      hr hb =>
    exact_sumPart_field φ σ chain firstTree On bud see wit get set hgs hsg name endName J hk rs hr
      hb j a

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_msForm
