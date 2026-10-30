-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/OneTextAtTrace.lean: AT THE FULL-SIZE TRACE, THE SMALLNESS TEST's CELL OF A
MATRIX, THE CELL OF THE TRACE AND THE CELL THAT THE FIRST SENDINGS PACK ARE ONE CELL. The test reads a
matrix through cellsAtOf at the list matsOwn, at the reader cellsC of the trace theTrace X i x. The sendings
pack that reader's cells (packedCells, Johnson/HonestTrace/Packed.lean; cellsVals,
Johnson/Desc/ProofFile/Honest/K1/FirstData.lean). Statements and proofs, in the goals' scope, at a request
that is served. None of the library's goals.

  cell_at_trace      through matsOwn, at every segment below 25, number, row and column: the test's cell is
                    the trace's entry
  **cell_at_planes**  at the matrix of multiplicities of the segment (number bNo X k: b at a layers'
                    segment, bA at an attention segment, bH at the head's), inside its shape: the test's
                    cell is the entry of plOf
  reader_at_trace    the reader's cell under a matrix's own label is the image of the test's cell
  **cell_is_packed**  what packedCells packs, in a column of the matrix's shape, is the column of the
                    test's cells
  **cellsVals_at_trace**  the same of the value that cellsVals gives an array
  **owner_at_trace**  a matrix that an earlier segment owns: the test's cell at the later segment is the
                    test's cell at the owner's segment, and there the matrix has a number

  **cells_at_input**  the corollary at a return of the maker: at an input that meets ReadyInput, under the
                    named premise ReadyLaws: the test's cell through matsOwn at the return's own public
                    record is the entry of the full-size trace of an index that serves the request
  cells_small_at_input  the same read is small at every place

Q is any table of sizes that agrees with the reference one but for the planes' shapes: the reference
table itself is one (planesAtRef_ref).

Limits. ServesAt, the scope and publicOf's return are premises, and ReadyLaws is a premise of the
corollary. That an array's value is laid in a message
of a run, and that K3's reading of a bit is this cell, are not here. Of what the planes hold nothing is said
beyond plOf. Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.HonestTrace.PlanOwnersInScope
import Johnson.Goal.HonestTrace.FromCellsInScope
import Johnson.HonestTrace.DigitsAtTrace
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedVals
import Johnson.Desc.ProofFile.Honest.K5.Law.SizesOffPlanes
import AtFullSide.K8.LawsAtIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open Inst.Model
open OnBytes
open OnBytes.HonestTrace
open OnBytes.Model.Verify (publicOf)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K1 (labelNo cellsVals)
open ProofFile.Honest.K5 (planesAtRef matAt_planesAtRef cellsVals_pack)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {i : Cm.Idx} {x : Instance ppref}

/-- A segment of a proof with 12 groups has a number below 25. -/
theorem no_lt_25 {σ : Seg} (h : σ.Below 12) : σ.no 12 < 25 := by
  cases σ with
  | ff g =>
    have : g < 12 := h
    show 2 * g < 25
    omega
  | att g =>
    have : g < 12 := h
    show 2 * g + 1 < 25
    omega
  | head =>
    show 2 * 12 < 25
    omega

/-- What the reference table says of a matrix's place. -/
theorem ref_at {k mu : ℕ} {σ : Seg} {μ : MatName} (h : Sz.ref.matAt k mu = some (σ, μ)) :
    σ.Below 12 ∧ σ.no 12 = k ∧ MatName.no? 3 1 1 4 σ μ = some mu := by
  obtain ⟨b1, b2, b3⟩ := (matAt_eq_some_iff Sz.ref k mu σ μ).1 h
  refine ⟨b1, b2, ?_⟩
  unfold Sz.mu at b3
  rw [if_pos b1] at b3
  exact b3

/-- The reference table agrees with itself. -/
theorem planesAtRef_ref : planesAtRef Sz.ref = Sz.ref := rfl

/-- A table that agrees with the reference one but for the planes' shapes places a matrix alike. -/
theorem matAt_ref {Q : Sz} (hq : planesAtRef Q = Sz.ref) (k mu : ℕ) :
    Q.matAt k mu = Sz.ref.matAt k mu := by
  rw [← hq, matAt_planesAtRef]

section
variable (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
  (h : publicOf Z.pol Z.KL lay = .ok X) (S : ServesAt X i x)
include hZ hR h S

/-- **Through matsOwn the test's cell is the trace's entry.** -/
theorem cell_at_trace {k : ℕ} (hk : k < 25) (mu r c : ℕ) :
    cellsAtOf (cellsC X (theTrace X i x)) (matsOwn X k) mu r c = theTrace X i x k mu r c := by
  rw [planOwners_in_scope hZ hR h k hk]
  exact cellsAtOf_matsOf (namesFit_theTrace hZ hR h S) (meetsAll_theTrace hZ hR h S) hk mu r c

/-- **At the matrix of multiplicities, inside its shape, the test's cell is the entry of plOf.** -/
theorem cell_at_planes {k r c : ℕ} (hk : k < 25) (hs : InShape X k (bNo X k) r c) :
    cellsAtOf (cellsC X (theTrace X i x)) (matsOwn X k) (bNo X k) r c = plOf X i x k r c := by
  rw [cell_at_trace hZ hR h S hk]
  exact trFull_planes X (plOf X i x) i x hs

/-- The reader's cell under a matrix's own label is the image of the test's cell. -/
theorem reader_at_trace {k mu : ℕ} (hk : k < 25) {σ : Seg} {μ : MatName}
    (hm : Sz.ref.matAt k mu = some (σ, μ)) (r c : ℕ) :
    (cellsC X (theTrace X i x)).cell k μ.label r c =
      ((cellsAtOf (cellsC X (theTrace X i x)) (matsOwn X k) mu r c : ℤ) : Cb.Gl.F) := by
  rw [cell_at_trace hZ hR h S hk]
  obtain ⟨hb, rfl, hn⟩ := ref_at hm
  exact cellOf_label (namesFit_theTrace hZ hR h S).parts (theTrace X i x) hb hn r c

/-- **What the sendings pack, in a column of the shape, is the column of the test's cells.** -/
theorem cell_is_packed {Q : Sz} (hq : planesAtRef Q = Sz.ref) {k mu c : ℕ} (hk : k < 25) {σ : Seg}
    {μ : MatName} (hm : Q.matAt k mu = some (σ, μ)) (hc : c < (Q.shape σ μ).2) (i' : ℕ) :
    packedCells Q (cellsC X (theTrace X i x)).cell k mu i' c =
      pack3 (Q.shape σ μ).1 (fun r =>
        ((cellsAtOf (cellsC X (theTrace X i x)) (matsOwn X k) mu r c : ℤ) : Cb.Gl.F)) i' := by
  have hr : Sz.ref.matAt k mu = some (σ, μ) := (matAt_ref hq k mu).symm.trans hm
  have e : (fun r => (cellsC X (theTrace X i x)).cell k μ.label r c) =
      fun r => ((cellsAtOf (cellsC X (theTrace X i x)) (matsOwn X k) mu r c : ℤ) : Cb.Gl.F) :=
    funext fun r => reader_at_trace hZ hR h S hk hr r c
  simp only [packedCells, hm, if_pos hc]
  rw [e]

/-- **The same of the value that cellsVals gives the array "M mu".** -/
theorem cellsVals_at_trace {Q : Sz} (hq : planesAtRef Q = Sz.ref) (Rd : Readers)
    (hc' : Rd.cells = cellsC X (theTrace X i x)) (hd : List Fmt.Drawn) {k mu c : ℕ} (hk : k < 25)
    {name : String} (hn : labelNo name = some mu) {σ : Seg} {μ : MatName}
    (hm : Q.matAt k mu = some (σ, μ)) (hc : c < (Q.shape σ μ).2) (i' : ℕ) :
    asE (some ((cellsVals Q).val Rd hd k name i' c)) =
      Alg.pack (2 ^ 20) (fun r : Fin (Q.shape σ μ).1 =>
        algebraMap Cb.Gl.F Cb.Gl.E
          ((cellsAtOf (cellsC X (theTrace X i x)) (matsOwn X k) mu r.val c : ℤ) : Cb.Gl.F)) i' := by
  rw [cellsVals_pack Q Rd hd hn hm hc i', hc']
  have hr : Sz.ref.matAt k mu = some (σ, μ) := (matAt_ref hq k mu).symm.trans hm
  have e : (fun r : Fin (Q.shape σ μ).1 => algebraMap Cb.Gl.F Cb.Gl.E
        ((cellsC X (theTrace X i x)).cell k μ.label r.val c)) =
      fun r : Fin (Q.shape σ μ).1 => algebraMap Cb.Gl.F Cb.Gl.E
        ((cellsAtOf (cellsC X (theTrace X i x)) (matsOwn X k) mu r.val c : ℤ) : Cb.Gl.F) :=
    funext fun r => by rw [reader_at_trace hZ hR h S hk hr r.val c]
  rw [e]

/-- **A matrix that another segment owns**: it has a number at its owner's segment, and the test's cell
at the later segment is the test's cell there. -/
theorem owner_at_trace {Q : Sz} (hq : planesAtRef Q = Sz.ref) {k mu : ℕ} {σ : Seg} {μ : MatName}
    (hk : k < 25) (hσ : Seg.ofNo 12 k = some σ) (hμ : (MatName.all 3 1 1 4 σ)[mu]? = some μ) :
    ∃ a, ((Sz.ref.owner σ μ).1.no 12) < 25 ∧
      Q.matAt ((Sz.ref.owner σ μ).1.no 12) a = some ((Sz.ref.owner σ μ).1, (Sz.ref.owner σ μ).2) ∧
      ∀ r c, cellsAtOf (cellsC X (theTrace X i x)) (matsOwn X k) mu r c =
        cellsAtOf (cellsC X (theTrace X i x)) (matsOwn X ((Sz.ref.owner σ μ).1.no 12)) a r c := by
  obtain ⟨hb, hno⟩ := Seg.of_ofNo hσ
  have N := namesFit_theTrace hZ hR h S
  have M := meetsAll_theTrace hZ hR h S
  obtain ⟨a, ob, on, -⟩ := owner_entries N M hb hμ 0 0
  have hlt := no_lt_25 ob
  refine ⟨a, hlt, ?_, fun r c => ?_⟩
  · rw [matAt_ref hq]
    refine (matAt_eq_some_iff Sz.ref _ a _ _).2 ⟨ob, rfl, ?_⟩
    have ob' : (Sz.ref.owner σ μ).1.Below Sz.ref.nGr := ob
    unfold Sz.mu
    rw [if_pos ob']
    exact on
  · rw [cell_at_trace hZ hR h S hk, cell_at_trace hZ hR h S hlt]
    obtain ⟨a', -, on', oe⟩ := owner_entries N M hb hμ r c
    obtain rfl : a' = a := Option.some.inj (on'.symm.trans on)
    rw [oe, hno]

end

section
variable {W₀ Rc X₀ Y : Type}

/-- **The corollary at a return of the maker.** At an input that meets ReadyInput there are an index and
an instance: the index serves the instance, and the test's cell through matsOwn at the return's public
record is the entry of the full-size trace. -/
theorem cells_at_input {o} {pol lay' KL : ByteArray} {P : OnlineProverParts W₀ Rc Cells X₀ Y}
    {Fd : VerifiableInference.Desc.FileDescription ProofFile.Inst} {A : OnlineProverWithDescription W₀ Rc Cells X₀ Y}
    (hA : onlineProverFromPublicFiles o pol lay' KL P = .ok A) (hL : ReadyLaws Fd A)
    {v : Local W₀ Rc ProofFile.Inst Cells} (hv : ReadyInput Fd A.H v) :
    ∃ (i : Cm.Idx) (x : Instance ppref), ProofFile.instOf v.x = some x ∧ ServesAt A.Z.p.X i x ∧
      v.trace = cellsC A.Z.p.X (theTrace A.Z.p.X i x) ∧
      ∀ l, l < 25 → ∀ mu r c, cellsAtOf (id v.trace) (matsOwn A.G.W l) mu r c =
        theTrace A.Z.p.X i x l mu r c := by
  obtain ⟨i, x, h1, h2, h3, M, -, N, Pf, Mk⟩ := hL v hv
  have hW : A.G.W = A.Z.p.X := ProofFile.Law.blankBy_W (atPure_ok hA).2.1
  refine ⟨i, x, h1, h2, h3, fun l hl mu r c => ?_⟩
  show cellsAtOf v.trace (matsOwn A.G.W l) mu r c = _
  rw [h3, hW, planOwners_of_marks Mk Pf l hl]
  exact cellsAtOf_matsOf N M hl mu r c

/-- That read is small at every place. -/
theorem cells_small_at_input {Fd : VerifiableInference.Desc.FileDescription ProofFile.Inst}
    {A : OnlineProverWithDescription W₀ Rc Cells X₀ Y} (hL : ReadyLaws Fd A)
    {v : Local W₀ Rc ProofFile.Inst Cells} (hv : ReadyInput Fd A.H v)
    (p : VerifiableInference.Desc.First.K8.Par) (l : Nat) :
    VerifiableInference.Desc.First.K8.Honest.cellsSmall p (cellsAtOf (id v.trace) (matsOwn A.G.W l)) =
      true :=
  ready_cells_small hL hv p _

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.no_lt_25
#print axioms ProofFile.Honest.K8.ref_at
#print axioms ProofFile.Honest.K8.matAt_ref
#print axioms ProofFile.Honest.K8.cell_at_trace
#print axioms ProofFile.Honest.K8.cell_at_planes
#print axioms ProofFile.Honest.K8.reader_at_trace
#print axioms ProofFile.Honest.K8.cell_is_packed
#print axioms ProofFile.Honest.K8.cellsVals_at_trace
#print axioms ProofFile.Honest.K8.owner_at_trace
#print axioms ProofFile.Honest.K8.planesAtRef_ref
#print axioms ProofFile.Honest.K8.cells_at_input
#print axioms ProofFile.Honest.K8.cells_small_at_input
