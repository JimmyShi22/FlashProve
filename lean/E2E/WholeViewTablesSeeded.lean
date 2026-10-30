-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/WholeViewTablesSeeded.lean: the statement of E2E/WholeViewTables.lean on the index's committed
tables, WITH EACH OOD SEED NAMED BY THE ENVIRONMENT, AND WITH NO CUT OF THE INDEX TYPE: at the
library's own object `F.withProvers F.fixedMessageProvers`, every index of its type.

GIVEN THE INTERFACE's CLAUSES ON READS (`ReadsR`: a premise here): the OOD samples and all opened
columns of all tables that encode the index (the first table and its copies), over any copies, links
and batches within the budget, at OOD seeds that the environment names from what has been shown and
coins of its own, do not depend on the index. That, and no more.

Why it can stand at the uncut object. The library's theorem with named seeds
(`Hiop.Seeded.whole_all_seeds`, Hiop/Seeded/Whole.lean) asks nothing of the index decoder. The
placeholder provers send fixed messages at every index. So nothing fails at an index out of range.

What is shown.
  `own_silent_ext`, `good_silentS`: the library's two premises on provers, at the object's own
    fields, which hold the placeholder provers; error 0; all seeds; every relation.
  `tables_seeded`: for any configuration C and three protocols F with `ReadsR` at b, qT, qpar, qch,
    qon: for every two indices i, i' of C, all bounds B that fit, every first OOD seed s₀ and every
    environment within B that names the further seeds: the law of its output is the same at i and
    i'.

What the statement covers, and what not: as in E2E/WholeViewTables.lean's head. ALL MESSAGES OF THE
THREE PROTOCOLS ARE FIXED at these provers: nothing is said of any message of the protocol, alone or
jointly with the tables. What turns against that file:
- The OOD seed of a table is any value of the configuration's type of OOD seeds (at the full size
  its factor is never 0, by that type) that the environment names, as a function of what has been
  shown so far and of coins of its own, BEFORE the pads and the encoding randomness of that table
  are sampled. So no law of the seeds is assumed. Of a seed that hangs on anything hidden (the
  randomness of its own or of another table, a prover's coins) nothing is said. A seed that is a
  hash value of the table's root does hang on that table's randomness: that the two orders give near
  laws is for the compile step to show.
- ONE OOD SEED A TABLE. One table's randomness is used under one set of public files alone. The same
  rows and pads under other public files would get another seed, and of two OOD samples on one
  table's pads this file says nothing.
- Every index of the type: at the full size every matrix, in range or not. THAT IT HOLDS OUT OF
  RANGE IS ONLY BECAUSE THE PROVERS ARE PLACEHOLDERS: with the protocol's own provers the cut to the
  matrices in range comes back (by an argument outside Lean; no theorem here says so). (Of a cell
  the encoder reads the first coordinate alone: two matrices that differ outside the base field
  alone have one table and one OOD sample, so for such a pair the statement is idle, and it is as
  rich as "any two matrices over the base field". That two different indices never share table and
  OOD sample holds of the matrices in range: E2E/ObjectGuardsMore.lean.)

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.

Terms: for "the protocol's own provers" see E2E/HidingTerms.lean.


-/
import E2E.FixedMessages
import Hiop.Seeded.WholeProof

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop Hiop.Seeded AtPublicFiles.Fixed
open OnBytes.Flat (Files)
open scoped ENNReal

section General
variable {C : ConfigurationWithOutOfDomainSample} (F : Files C)

/-- The object's own three fields hold the encoder's tables. -/
theorem own_silent_ext : (ProversS.own (F.withProvers F.fixedMessageProvers)).Ext :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- The three functions that replay the fixed messages, at every number of a table. -/
def silentSimsS (y₀ : Fin C.n → C.Sg) : SimsS (F.withProvers F.fixedMessageProvers) :=
  ⟨fun _ => (silentSims F y₀).T, fun _ => (silentSims F y₀).Lk, fun _ => (silentSims F y₀).B⟩

/-- They are good simulators of the object's own provers, at all seeds, every relation and all
numbers: the messages are fixed. -/
theorem good_silentS (y₀ : Fin C.n → C.Sg) (Gs : (F.withProvers F.fixedMessageProvers).OutOfDomainSeed → Prop)
    (Ryes : C.I → C.X → Prop) (zT zL zO : ℝ≥0∞) :
    (silentSimsS F y₀).Good (ProversS.own (F.withProvers F.fixedMessageProvers)) Gs Ryes zT zL zO :=
  ⟨fun _ w x hv _ => (silent_good F y₀ Ryes zT zL zO).goodT w x hv,
    fun _ w x hv _ _ => (silent_good F y₀ Ryes zT zL zO).goodL w x hv,
    fun _ w x _ hv J xs hxs => (silent_good F y₀ Ryes zT zL zO).goodB w x hv J xs hxs⟩

/-- **Given `reads`: the OOD samples and all opened columns of all tables that encode the index,
over any copies, links and batches within the budget, at OOD seeds named by the environment, do not
depend on the index.** At the library's own object, every index of its type. Nothing is said of the
protocol's messages: at these provers they are fixed. -/
theorem tables_seeded {b qT qpar qch qon : ℕ}
    (reads : (F.withProvers F.fixedMessageProvers).ReadsR b qT qpar qch qon) (B : BoundsR)
    (fits : B.Fits b qT qpar qch qon) (i i' : C.I) (α : Type) (s₀ : (F.withProvers F.fixedMessageProvers).OutOfDomainSeed)
    (E : (F.withProvers F.fixedMessageProvers).Rec → EnvS (F.withProvers F.fixedMessageProvers) α)
    (adm : ∀ a, (E a).Adm B (fun _ => True) (fun _ => True) 0 UsedR.zero) :
    (realHostS (F.withProvers F.fixedMessageProvers) (ProversS.own (F.withProvers F.fixedMessageProvers)) i).view s₀ E =
      (realHostS (F.withProvers F.fixedMessageProvers) (ProversS.own (F.withProvers F.fixedMessageProvers)) i').view s₀ E := by
  have h := whole_all_seeds _ _ (F.withProvers F.fixedMessageProvers) (fun _ _ => True) b qT qpar qch qon
    0 0 0 reads (ProversS.own (F.withProvers F.fixedMessageProvers)) (own_silent_ext F)
    (silentSimsS F ((F.withProvers F.fixedMessageProvers).encodeIndex i (Classical.arbitrary _)))
    (good_silentS F _ (fun _ => True) (fun _ _ => True) 0 0 0) B fits i
  have e0 : B.err 0 0 0 = 0 := by simp [BoundsR.err]
  rw [e0] at h
  have h1 := tv_eq_zero_iff.1 (le_antisymm (h i α s₀ E trivial adm) (zero_le _))
  have h2 := tv_eq_zero_iff.1 (le_antisymm (h i' α s₀ E trivial adm) (zero_le _))
  exact h1.trans h2.symm

end General

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.own_silent_ext
#print axioms AtPublicFiles.AtFiles.good_silentS
#print axioms AtPublicFiles.AtFiles.tables_seeded
