-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ObjectGuardsMore.lean: two more guards for the statements on the index's committed tables
(E2E/WholeViewTables.lean, E2E/WholeViewAtFiles.lean). For the forms with named OOD seeds the first
guard's like is in E2E/ObjectGuardsSeeded.lean.

What is shown.
  `demo_adm`, `demo_fits`: THE PREMISES ON THE ENVIRONMENT CAN BE MET BY ONE THAT ASKS FOR
    EVERYTHING: a typed environment that makes a copy, runs the key file's protocol on the first
    table, the link on the copy, a batch on the copy with all its requests shown, reads a single
    symbol of the copy, and STOPS WITH ALL THAT IT WAS SHOWN (`Seen`), so that the statements'
    conclusion says something at it (at an environment that stops with nothing the conclusion is an
    equation of laws on a type with one member, true of any two hosts); it is admissible at bounds
    that fit the numbers 44,040,191 | 62 | 62 | 62 | 64 (the first table is read at no more than 124
    columns, the copy at no more than 127). For every object.
  `index_of_table`, `NeverShare`, `neverShare_cut`, `tables_differ`: THE VIEW IS NOT A CONSTANT FOR
    WANT OF CONTENT: two different matrices in range never have the same committed table with the
    same OOD sample, whatever the pads, the encoding randomness and the OOD seeds: from both
    together the decoder returns the index. So what the statements call equal in law is a law of
    parts of values that, whole, tell the index.

  `NeverShareOn`, `neverShareOn_of_dec`, `tables_differ_uncut`: the same at the object that is not
    cut, of two different matrices in range.

Limits. `tables_differ` is at the object CUT to the matrices in range; `tables_differ_uncut` speaks
of matrices in range alone. At the uncut object (every matrix over the extension field) `NeverShare`
is false BY THE ENCODER's TEXT (Johnson/Flat/CodingCells.lean; no theorem here says so): of a cell
the encoder reads the first coordinate alone, so two matrices that differ outside the base field
alone have one table and one OOD sample. No environment beyond the budget is typed that tells two
indices apart. What would do (an argument; no theorem here says so): by the second guard the whole
table with its OOD sample; by E2E/TableHidesGuard.lean one column more than the budget, at one OOD
seed and two matrices. An environment that reads so much is not written here.

`NeverShare` and `NeverShareOn` name properties of an object: they may be read as goals. They are
not among this library's goals.

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


-/
import E2E.ObjectAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files)

/-! ## 1. An admissible environment with all five requests -/

section Demo
variable {I X : Type} (L : HolographicProtocol I X) (x : X) (p : Fin L.wordLength)

/-- One copy; one run of the key file's protocol, on the first table; on the copy one link, one
batch and one single read; N requests shown. -/
def demoB (N : ℕ) : BoundsR where
  nenc := 1
  tests := fun e => if e = 0 then 1 else 0
  links := fun e => if e = 0 then 0 else 1
  sess := fun e => if e = 0 then 0 else 1
  reads := fun e => if e = 0 then 0 else 1
  shown := N

/-- All that such an environment is shown: the two OOD samples, what is shown of the three runs, and
the symbol. -/
abbrev Seen : Type :=
  L.Rec × L.Rec × Compile.Lifetime.Sess L.offline × Compile.Lifetime.Sess L.link ×
    Compile.BatchLife.BSess L.onlineBatch (Finset.univ : Finset (Fin L.maxBatchSize)) × L.Symbol

/-- Make a copy; run the key file's protocol on the first table; the link on the copy; a batch on
the copy, all its requests being x, and all shown; read the copy's symbol at p; STOP WITH ALL THAT
WAS SHOWN. -/
def demoEnv : L.Rec → EnvR L (Seen L) := fun a₀ =>
  .fresh fun a₁ => .test 0 fun v₁ => .link 1 fun v₂ =>
    .session 1 Finset.univ (fun _ => x) (fun _ => none) fun v₃ => .read 1 p fun y =>
      .stop (a₀, a₁, v₁, v₂, v₃, y)

/-- **Its bounds fit**: 62 + 62 columns of the first table, 62 + 64 + 1 of the copy. -/
theorem demo_fits (N : ℕ) : (demoB N).Fits 44040191 62 62 62 64 := by
  intro e he
  have h : e = 0 ∨ e = 1 := by
    have he' : e ≤ 1 := he
    omega
  rcases h with rfl | rfl <;> simp [demoB, BoundsR.sum, Finset.sum_range_succ]

/-- **It is admissible at these bounds.** -/
theorem demo_adm (a : L.Rec) :
    (demoEnv L x p a).Adm (demoB L.maxBatchSize) (fun _ => True) 0 UsedR.zero := by
  exact ⟨by simp [demoB], fun _ => ⟨Nat.zero_le _, by simp [demoB, UsedR.zero], fun _ =>
    ⟨le_rfl, le_rfl, by simp [demoB, UsedR.zero], fun _ =>
      ⟨le_rfl, by simp [demoB, UsedR.zero], (Finset.card_univ.trans (Fintype.card_fin _)).le,
        fun _ => trivial, fun _ _ _ => trivial, fun _ =>
          ⟨le_rfl, by simp [demoB, UsedR.zero], fun _ => trivial⟩⟩⟩⟩⟩

end Demo

/-! ## 2. Two indices never share a table with its OOD sample -/

/-- Where the decoder returns the index from the honest table and OOD sample, these two together
fix the index. -/
theorem index_of_table {I X : Type} {L : HolographicProtocol I X}
    (h : ∀ i r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i) {i i' : I} {r r' : L.EncodingRandomness}
    {s s' : L.OutOfDomainSeed} (he : L.encodeIndex i r = L.encodeIndex i' r') (hr : L.recOf i r s = L.recOf i' r' s') :
    i = i' := by
  have a := h i r s
  rw [he, hr, h i' r' s'] at a
  exact (Option.some.inj a).symm

/-- Two different indices never have the same committed table with the same OOD sample, whatever the
randomness and the OOD seeds. -/
def NeverShare {I X : Type} (L : HolographicProtocol I X) : Prop :=
  ∀ i i' : I, i ≠ i' → ∀ (r r' : L.EncodingRandomness) (s s' : L.OutOfDomainSeed),
    ¬ (L.encodeIndex i r = L.encodeIndex i' r' ∧ L.recOf i r s = L.recOf i' r' s')

theorem neverShare_of_dec {I X : Type} {L : HolographicProtocol I X}
    (h : ∀ i r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i) : NeverShare L :=
  fun _ _ hne _ _ _ _ e => hne (index_of_table h e.1 e.2)

/-- At a cut object, from the decoder's clause at the indices with p. -/
theorem neverShare_cut {I X : Type} (L : HolographicProtocol I X) (p : I → Prop)
    (h : ∀ i, p i → ∀ r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i) : NeverShare (cut L p) :=
  neverShare_of_dec fun i r s => (dec_cut_eq_some L p _ _ i).2 (h i.1 i.2 r s)

/-- **Two different matrices in range never have the same committed table with the same OOD
sample**, for any three protocols over the full size's configuration and any provers. -/
theorem tables_differ {X : Type} {pp : Inst.Model.ScalesAndPolicy}
    {req : X → Inst.Model.Instance Inst.Model.ppref} (F : Files (ConfAt pp req)) (P : F.Provers) :
    NeverShare (cutObj F P) :=
  neverShare_cut (I := FullSizeMatrix) (X := X) (F.withProvers P) inRange fun M hM r s =>
    OnBytes.Flat.obj_decodes_cells_full pp req F P M hM r s

/-- The same said of the indices with p alone, at an object that is not cut. -/
def NeverShareOn {I X : Type} (L : HolographicProtocol I X) (p : I → Prop) : Prop :=
  ∀ i i' : I, p i → p i' → i ≠ i' → ∀ (r r' : L.EncodingRandomness) (s s' : L.OutOfDomainSeed),
    ¬ (L.encodeIndex i r = L.encodeIndex i' r' ∧ L.recOf i r s = L.recOf i' r' s')

/-- From the decoder's clause at the indices with p. -/
theorem neverShareOn_of_dec {I X : Type} {L : HolographicProtocol I X} {p : I → Prop}
    (h : ∀ i, p i → ∀ r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i) : NeverShareOn L p :=
  fun i i' hi hi' hne r r' s s' e => hne (by
    have a := h i hi r s
    rw [e.1, e.2, h i' hi' r' s'] at a
    exact (Option.some.inj a).symm)

/-- **At the object that is not cut: two different matrices IN RANGE never have the same committed
table with the same OOD sample.** (Of all matrices it is false by the encoder's text: this file's
head.) -/
theorem tables_differ_uncut {X : Type} {pp : Inst.Model.ScalesAndPolicy}
    {req : X → Inst.Model.Instance Inst.Model.ppref} (F : Files (ConfAt pp req)) (P : F.Provers) :
    NeverShareOn (I := FullSizeMatrix) (X := X) (F.withProvers P) inRange :=
  neverShareOn_of_dec fun M hM r s => OnBytes.Flat.obj_decodes_cells_full pp req F P M hM r s

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.demo_fits
#print axioms AtPublicFiles.AtFiles.demo_adm
#print axioms AtPublicFiles.AtFiles.index_of_table
#print axioms AtPublicFiles.AtFiles.neverShare_cut
#print axioms AtPublicFiles.AtFiles.tables_differ
#print axioms AtPublicFiles.AtFiles.neverShareOn_of_dec
#print axioms AtPublicFiles.AtFiles.tables_differ_uncut
