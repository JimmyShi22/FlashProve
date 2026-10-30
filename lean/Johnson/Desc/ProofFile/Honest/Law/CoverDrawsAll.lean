-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverDrawsAll.lean: `drawNZ ≤ drawE` (no declared round draws more
non-zero elements than elements) at every declared round of the proof file's three chains, the
sealing round too. Honest/Law/CoverDraws.lean proves it of the first chain's gated rounds and of the
other two chains' rounds. `due_typed` (Honest/Law/Due.lean) and the lemmas of
Honest/Law/DueData.lean take it as one hypothesis on the three lists of declared rounds in a row.
Here it is proved in that form, from the two fields of the library's `P5J.AtMg` that it needs: that
the public files are in scope, and `LaidAt`.

  1  `seal_draws`   where `FileDescription.data` returns data: the first chain has a last declared round,
     and it draws no element; general in the description
  2  `data_laid`   in scope, under `LaidAt`, the file's data are `writtenPFull`
  3  `draws_decl`   the statement on the three lists in a row

Limits.
  * That the public files are in scope, and `LaidAt`, are hypotheses.
  * `seal_draws` follows the last step of the proof of `kinds_of_data` (Honest/Law/DataKinds.lean),
    which keeps another clause of the same test.
  * `data_laid` and `draws_decl` are at the library's full-size parameter set alone.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverDraws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes OnBytes.Maker
open P5J (TS)

variable {Xi : Type}

/-- Where `FileDescription.data` returns data, the first chain has a last declared round, and it draws no
element (`drawNZ = 0`, `drawE = 0`). -/
theorem seal_draws {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D) :
    ∃ d, F.roundsDeclaredByBlocks.1.getLast? = some d ∧ d.entry.drawNZ = 0 ∧ d.entry.drawE = 0 := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, -, -⟩ := writtenOf_ok hR
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hk).fits
  obtain ⟨r, hr, -, -, -, q7, q8, -, -⟩ := seal_of_fits hf
  obtain ⟨d, hd, y, hy, rfl⟩ := forall₂_last w₁ r hr
  have e := (round_ok hy).1
  have q7' : y.entry.drawE = 0 := q7
  have q8' : y.entry.drawNZ = 0 := q8
  rw [e] at q7' q8'
  exact ⟨d, hd, q8', q7'⟩

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- In scope, under `LaidAt`, the file's data are the written data. -/
theorem data_laid (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) : D = Johnson.G.writtenPFull :=
  Except.ok.inj (L.data.symm.trans
    (VerifiableInference.PlanWritten.seat_in_scope _ _ Z hZ (LPFD.asks_written L.asks)).2.2)

/-- At every declared round of the three chains: `drawNZ ≤ drawE`. -/
theorem draws_decl (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∀ d ∈ (P5J.F0T o Zp Np cF).roundsDeclaredByBlocks.1 ++ (P5J.F0T o Zp Np cF).roundsDeclaredByBlocks.2.1 ++
      (P5J.F0T o Zp Np cF).roundsDeclaredByBlocks.2.2, d.entry.drawNZ ≤ d.entry.drawE := by
  have k := kinds_of_data L.data
  have hD : (∀ d ∈ D.ds₁, d.entry.drawNZ ≤ d.entry.drawE) ∧
      (∀ d ∈ D.ds₂, d.entry.drawNZ ≤ d.entry.drawE) ∧
      ∀ d ∈ D.ds₃, d.entry.drawNZ ≤ d.entry.drawE := by
    rw [data_laid hZ L, Johnson.G.writtenPFull_eq]
    exact ⟨fun d hd => of_decide_eq_true (List.all_eq_true.1 draws_written_yes.1 d hd),
      fun d hd => of_decide_eq_true (List.all_eq_true.1 draws_written_yes.2.1 d hd),
      fun d hd => of_decide_eq_true (List.all_eq_true.1 draws_written_yes.2.2 d hd)⟩
  obtain ⟨d₀, hl, q1, q2⟩ := seal_draws L.data
  intro d hd
  rcases List.mem_append.1 hd with hd | hd
  · rcases List.mem_append.1 hd with hd | hd
    · rw [← List.dropLast_append_getLast? d₀ hl] at hd
      rcases List.mem_append.1 hd with hd | hd
      · exact entries_of_kinds (p := fun e => e.drawNZ ≤ e.drawE) k.1 hD.1 d hd
      · rw [List.mem_singleton.1 hd, q1]
        exact Nat.zero_le _
    · exact entries_of_kinds (p := fun e => e.drawNZ ≤ e.drawE) k.2.1 hD.2.1 d hd
  · exact entries_of_kinds (p := fun e => e.drawNZ ≤ e.drawE) k.2.2.1 hD.2.2 d hd

end ProofFile.Honest

#print axioms ProofFile.Honest.seal_draws
#print axioms ProofFile.Honest.data_laid
#print axioms ProofFile.Honest.draws_decl
