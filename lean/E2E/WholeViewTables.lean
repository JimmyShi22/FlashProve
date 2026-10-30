-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/WholeViewTables.lean: GIVEN THE INTERFACE's CLAUSES ON READS (`ReadsR`, A PREMISE OF EVERY
THEOREM HERE, PROVED NOWHERE IN THIS FILE): THE OOD SAMPLES AND ALL OPENED COLUMNS OF ALL COMMITTED
TABLES, OVER ANY COPIES, LINKS AND BATCHES WITHIN THE BUDGET, DO NOT DEPEND ON THE INDEX. That, and
no more. The premise holds the statement for ONE table (at every OOD seed the OOD answers together
with any b columns have a law that is the same for all indices) and four counts of columns read;
what is added here is the passage to many tables and runs.

It is the theorem of E2E/WholeView.lean at the library's placeholder provers (`Files.fixedMessageProvers`,
OnBytes/Flat/Silent.lean), which send each round's fixed message whatever the index, the request and
the challenges are. These are the provers that the library lays into the object from which
`VerifierAndGoals.verify` is compiled (E2E/ObjectGuards.lean: `ownProvers_silent`). THEY ARE NOT THE
PROTOCOL's PROVER.

What the statement covers. In the experiment of Hiop/RecWhole.lean, at these provers, what hangs on
the index in what the environment sees is: the OOD sample of every committed table (first table and
copies); the tables' symbols at the columns that the three verifiers read, in every run; and the
single symbols that the environment asks for. All messages of the three protocols are fixed.
What it does NOT cover: ANY MESSAGE OF THE PROTOCOL. Nothing is said of what an honest prover sends:
no oracle of a request, no plain part, no folded row, no reply. It is not a statement on the
protocol's privacy, and it is not to be cited as one.

What is shown.
  `fit_silent`: the placeholder provers meet `ProversFit` at all numbers, 0 among them: so the
    premises of E2E/WholeView.lean can be met together.
  `err_zero`: the library's error at zT = zL = zO = 0 is 0.
  `tables_same_view`: for any three protocols F over the full size's configuration with `ReadsR` at
    numbers b, qT, qpar, qch, qon: for every two matrices i, i' in range, all bounds B that fit and
    every environment within B: the environment's output has THE SAME LAW at i and at i'.
  (At `filesAt Z`, with the numbers 44,040,191 | 62 | 62 | 62 | 64 and without the premise:
  E2E/WholeViewAtFiles.lean.)

Limits.
- `ReadsR` is a premise (E2E/ReadsAtFiles.lean proves it at every Z in scope;
  E2E/WholeViewAtFiles.lean has the form without the premise). All the content is in it: the clause
  `hidE` (at every OOD seed, the law of the OOD answers together with any b columns, over pads and
  encoding randomness, is the same for all indices) and the four counts. What this file adds is the
  library's book-keeping over many tables and runs.
- Where the IOP's own test on the public files rejects, the key file's and the proof file's
  verifiers have no rounds' data and read no column; the link's verifier reads its columns at every
  Z.
- "Committed tables": the tables that encode THE INDEX (the first table and its copies), not the
  oracles that a prover commits to in a run.
- Of the three protocols this is read, and no more: the rounds' shapes (with them the types of
  messages and of the verifier's randomness), the map from the verifier's randomness to the
  positions that it reads, and four counts of these positions. The three decisions, the gates and
  the proof of work are read by nothing; whether a verifier accepts a run that is shown is not said.
- Nothing on the messages of the protocol's own provers, alone or jointly with the tables (they read
  the same pads and encoding randomness).
- ONE OOD SEED A TABLE, sampled by the host uniformly, afresh for each table together with that
  table's pads and encoding randomness: so independently of ALL that is hidden (every table's pads
  and encoding randomness, the provers' coins) and of all that has been shown. In the format the
  seed is a hash value of the table's root, the public files' digest and the shape: it hangs on the
  table; nothing here covers that. (With seeds named by the environment:
  E2E/WholeViewTablesSeeded.lean.) One table's randomness is used under one set of public files
  alone. The same rows and pads under other public files would get another seed, and of two OOD
  samples on one table's pads this file says nothing.
- The budget is a table's whole life; nothing in Lean keeps count of it. Bare columns and OOD
  answers: no root, salt, authentication path or commitment ID. Nothing on any program.
- If the matrices in range had one member the statement would be empty: E2E/ObjectGuards.lean.
- The budget is table by table (E2E/WholeView.lean, Limits). At bounds with no run and no read the
  statement is about the OOD samples alone.
- The relation on requests is "every request": at these provers it is read by nothing.
- Equality of laws of the OUTPUT of every environment, outputs of every type: so of all that it
  sees.

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
import E2E.WholeView
import E2E.FixedMessages

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.Fixed
open OnBytes.Flat (Files)
open scoped ENNReal

/-- The library's error at three zeros. -/
theorem err_zero (B : BoundsR) : B.err 0 0 0 = 0 := by
  simp [BoundsR.err]

section General
variable {X : Type} {pp : Inst.Model.ScalesAndPolicy} {req : X → Inst.Model.Instance Inst.Model.ppref}

/-- The three functions that replay the fixed messages, at the cut object. y₀: any table; nothing
of it is read (`viewWith_any`, E2E/FixedMessages.lean). -/
def silentSimsCut (F : Files (ConfAt pp req)) (y₀ : Fin (ConfAt pp req).n → (ConfAt pp req).Sg) :
    SimsR (cutObj F F.fixedMessageProvers) :=
  simsRe (I := FullSizeMatrix) (X := X) Subtype.val (back inRange) (silentSims F y₀)

/-- They are good simulators there, for every relation and all numbers: the messages are fixed. -/
theorem good_silentCut (F : Files (ConfAt pp req))
    (y₀ : Fin (ConfAt pp req).n → (ConfAt pp req).Sg) (Ryes : Ix → X → Prop) (zT zL zO : ℝ≥0∞) :
    (silentSimsCut F y₀).Good Ryes zT zL zO :=
  good_reIndex (I := FullSizeMatrix) (X := X) Subtype.val (back inRange) (Ryes := fun _ _ => True)
    (fun _ _ _ => trivial) (silent_good F y₀ (fun _ _ => True) zT zL zO)

/-- **The placeholder provers meet `ProversFit`**, for every relation and all numbers. A member that
shows that the premises can be met together, and nothing about the protocol's prover. -/
theorem fit_silent (F : Files (ConfAt pp req)) (y₀ : Fin (ConfAt pp req).n → (ConfAt pp req).Sg)
    (Ryes : Ix → X → Prop) (zT zL zO : ℝ≥0∞) : ProversFit F F.fixedMessageProvers Ryes zT zL zO where
  ext := ext_cutObj_silent F
  hidden :=
    ⟨⟨(silentSimsCut F y₀).T, (good_silentCut F y₀ Ryes zT zL zO).goodT⟩,
      ⟨(silentSimsCut F y₀).Lk, (good_silentCut F y₀ Ryes zT zL zO).goodL⟩,
      ⟨(silentSimsCut F y₀).B, (good_silentCut F y₀ Ryes zT zL zO).goodB⟩⟩

/-- **Given `reads`: the OOD samples and all opened columns of all committed tables, over any
copies, links and batches within the budget, do not depend on the index.** At the placeholder
provers: for every two
matrices in range, all bounds that fit the numbers of `reads`, and every environment within the
bounds, the law of the environment's output is the same. Nothing is said of the protocol's
messages: at these provers they are fixed. -/
theorem tables_same_view (F : Files (ConfAt pp req)) {b qT qpar qch qon : ℕ}
    (reads : (cutObj F F.fixedMessageProvers).ReadsR b qT qpar qch qon) (B : BoundsR)
    (fits : B.Fits b qT qpar qch qon) (i i' : Ix) (α : Type)
    (E : (cutObj F F.fixedMessageProvers).Rec → EnvR (cutObj F F.fixedMessageProvers) α)
    (adm : ∀ a, (E a).Adm B (fun _ => True) 0 UsedR.zero) :
    (realHostR (cutObj F F.fixedMessageProvers) i).view E = (realHostR (cutObj F F.fixedMessageProvers) i').view E := by
  have h := whole_of_good F F.fixedMessageProvers (fun _ _ => True) (ext_cutObj_silent F) reads
    (silentSimsCut F ((F.withProvers F.fixedMessageProvers).encodeIndex i.1 (Classical.arbitrary _)))
    (good_silentCut F _ (fun _ _ => True) 0 0 0) B fits i
  rw [err_zero] at h
  have h1 := tv_eq_zero_iff.1 (le_antisymm (h i α E adm) (zero_le _))
  have h2 := tv_eq_zero_iff.1 (le_antisymm (h i' α E adm) (zero_le _))
  exact h1.trans h2.symm

end General

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.err_zero
#print axioms AtPublicFiles.AtFiles.good_silentCut
#print axioms AtPublicFiles.AtFiles.fit_silent
#print axioms AtPublicFiles.AtFiles.tables_same_view
