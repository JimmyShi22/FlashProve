-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ReadsNotEmpty.lean: the counts of E2E/ReadsCount.lean are not bounds on nothing: at the
written data of the key file and of the proof file, at EVERY verifier randomness, the verifier reads
at least one column of the committed table. Statements and proofs.

What is shown.
  `dr_poss`: with verifier's messages as hash outputs (`ckP`, Run/PlanPull.lean) a round samples
    exactly as many positions as its entry says, whatever the message: from the library's
    `planPull_view` and `drawRound_poss`.
  `Opens ds`: a test on a chain's data: some round has a stored entry whose part of the round's
    sampled positions is not empty.
  `wants_table`: such a chain asks for a column below 2^a, at every verifier randomness.
  **`whole_reads_some`**: a whole file's verifier whose second chain passes that test reads at least
    one column, at every verifier randomness.
  `opens_written`: the second chains of the written data of both files pass it: by an evaluation in
    Lean's kernel.
  **`key_reads_some`**, **`proof_reads_some`**: so at the written data.

Limits. A lower bound of one column, of the positions that a protocol DECLARES as read. That 62 or
64 different columns are read at some verifier randomness is not shown (equal positions are read
once). The statements are on a whole file's verifier at the written data and free letters; at the
objects of E2E/ReadsAtWritten.lean and E2E/ReadsAtFiles.lean they are in
E2E/ReadsNotEmptyAtObject.lean. Nothing here on the copy's file (E2E/StringsHoldLink.lean). All
limits of E2E/ReadsCount.lean stand. Nothing on hiding.

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
import E2E.ReadsCount
import Run.PlanPull
import Run.CostFmtProofs
import Johnson.Flat.Dec.FitAtWritten

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Reads
open Iop
open OnBytes.Maker
open _root_.Run (ckP)
open _root_.Run.PQ (View)
open Johnson.G (dKeyFull dProofFull writtenKFull writtenPFull)

/-- A round samples exactly as many positions as its entry says. -/
theorem dr_poss (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind)
    (u : (ckP f).Ch e k) : ((ckP f).dr e k u).poss.length = e.poss := by
  rw [(_root_.Run.planPull_view f e k u).2]
  exact _root_.Run.CostP.drawRound_poss f e k _

/-- Some round has a stored entry whose part of the round's sampled positions is not empty. -/
def Opens (ds : List RDT) : Bool :=
  ds.any fun d => d.stored.any fun s => decide (s.lo < d.entry.poss) && decide (0 < s.count)

/-- The part is not empty. -/
theorem partOf_ne_nil (s : _root_.Fmt.Stored) (poss : List ℕ) (h₁ : s.lo < poss.length)
    (h₂ : 0 < s.count) : _root_.Fmt.partOf s poss ≠ [] := by
  intro h
  have hl : (_root_.Fmt.partOf s poss).length = 0 := by rw [h]; rfl
  unfold _root_.Fmt.partOf at hl
  rw [List.length_take, List.length_drop] at hl
  omega

/-- So its entry asks for a column below 2^a. -/
theorem tableWants_some (a : ℕ) (s : _root_.Fmt.Stored) (poss : List ℕ) (h₁ : s.lo < poss.length)
    (h₂ : 0 < s.count) : ∃ x, x < 2 ^ a ∧ Want.table s.item x ∈ tableWants a poss s := by
  obtain ⟨y, l, hy⟩ := List.exists_cons_of_ne_nil (partOf_ne_nil s poss h₁ h₂)
  refine ⟨y % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a), ?_⟩
  unfold tableWants
  refine List.mem_map.2 ⟨y % 2 ^ a, (_root_.Fmt.listOf_mem _ _).2 ?_, rfl⟩
  rw [hy]
  exact List.mem_map.2 ⟨y, List.mem_cons_self, rfl⟩

/-- **A chain that passes the test asks for a column, at every verifier randomness.** -/
theorem wants_table (f : _root_.Fmt.Fld) (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (ds : List RDT) (ρ : Rho (uLT (ckP f) ds)), Opens ds = true →
      ∃ item x, x < 2 ^ a ∧ Want.table item x ∈ wantsOf a dep ds (drawnT (ckP f) ds ρ)
  | [], _, h => by cases h
  | d :: ds, (c, ρ), h => by
      have e : drawnT (ckP f) (d :: ds) (c, ρ) =
          (ckP f).dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: drawnT (ckP f) ds ρ := rfl
      rw [e, wantsOf_round]
      rcases Bool.or_eq_true _ _ ▸ (show ((d.stored.any fun s =>
          decide (s.lo < d.entry.poss) && decide (0 < s.count)) || Opens ds) = true from h)
        with h | h
      · obtain ⟨s, hs, hc⟩ := List.any_eq_true.1 h
        have hc' := Bool.and_eq_true_iff.1 hc
        have c₁ : s.lo < d.entry.poss := of_decide_eq_true hc'.1
        have c₂ : 0 < s.count := of_decide_eq_true hc'.2
        obtain ⟨x, hx, hm⟩ := tableWants_some a s
          ((ckP f).dr d.entry d.kind (GChal.old (b := d.entry.work) c)).poss
          (by rw [dr_poss]; exact c₁) c₂
        exact ⟨s.item, x, hx, List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.2 ⟨s, hs, hm⟩))⟩
      · obtain ⟨item, x, hx, hm⟩ := wants_table f a dep ds ρ h
        exact ⟨item, x, hx, List.mem_append_right _ hm⟩

section
variable (f : _root_.Fmt.Fld) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **A whole file's verifier whose second chain passes the test reads at least one column, at every
verifier randomness.** -/
theorem whole_reads_some (h : Opens D.ds₂ = true) (ρ : Rho (chainsOf (ckP f) D tF tJ t3).sh) :
    ((reductionOfWholeFile (ckP f) D tF tJ t3 silent run).extReads ρ).Nonempty := by
  obtain ⟨item, x, hx, hm⟩ := wants_table f D.a D.depth D.ds₂
    ((chainsOf (ckP f) D tF tJ t3).rho₂ ρ) h
  refine ⟨⟨x, hx⟩, List.mem_toFinset.2 (List.mem_filterMap.2 ⟨Want.table item x, ?_, ?_⟩)⟩
  · exact List.mem_append_right _ (List.mem_append_left _ hm)
  · show (if h : x < 2 ^ D.a then some (⟨x, h⟩ : Fin (2 ^ D.a)) else none) = some ⟨x, hx⟩
    rw [dif_pos hx]

end

set_option maxRecDepth 1000000 in
/-- The second chains of the two files' written data pass the test. -/
theorem opens_written : Opens dKeyFull.ds₂ = true ∧ Opens dProofFull.ds₂ = true := by
  decide +kernel

section
variable {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {Xi : Type}
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **At the key file's written data every run reads a column.** -/
theorem key_reads_some (ρ : Rho (chainsOf (ckP .two) writtenKFull tF tJ t3).sh) :
    ((reductionOfWholeFile (ckP .two) writtenKFull tF tJ t3 silent run).extReads ρ).Nonempty :=
  whole_reads_some .two writtenKFull tF tJ t3 silent run
    (by rw [Johnson.G.writtenKFull_eq]; exact opens_written.1) ρ

/-- **At the proof file's written data every run reads a column.** -/
theorem proof_reads_some (ρ : Rho (chainsOf (ckP .two) writtenPFull tF tJ t3).sh) :
    ((reductionOfWholeFile (ckP .two) writtenPFull tF tJ t3 silent run).extReads ρ).Nonempty :=
  whole_reads_some .two writtenPFull tF tJ t3 silent run
    (by rw [Johnson.G.writtenPFull_eq]; exact opens_written.2) ρ

end

end AtPublicFiles.Reads

#print axioms AtPublicFiles.Reads.dr_poss
#print axioms AtPublicFiles.Reads.wants_table
#print axioms AtPublicFiles.Reads.whole_reads_some
#print axioms AtPublicFiles.Reads.opens_written
#print axioms AtPublicFiles.Reads.key_reads_some
#print axioms AtPublicFiles.Reads.proof_reads_some
