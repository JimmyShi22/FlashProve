-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/Honest.lean: the head segment's honest trace, at the final normalisation of the
quantization scales (`Scl.nf`, Inst/Model/Scl.lean), for requests under the acceptance policy.

Every cell that the cell rule writes from a run of the integer program within the acceptance policy
has absolute value at most 128 (under `HonIn` and `[Lawful]`). That these cells satisfy the part of
the field relation that belongs to the head is not said here. `hon_rfz`
(Policy/Rel/LedgerHeadHonest.lean) says it, under `N.HonIn` and as congruences (`RFz p`), of the
head's relation in the form of Policy/Rel/LedgerHead.lean, and of no other form.
  `HonIn`                    what is assumed: NORM does not halt at any position; |H| ≤ 2^12; every
                             checked token is below V; the policy is met by the stream's logits; C,
                             θ < 2^40, cap < 2^16
  `honCells_N`, `HonIn.toN`  `honCells` is `N.honCells Scl.nf` (by definition); at valid scales
                             `HonIn` gives `N.HonIn Scl.nf`
  `honIn_program`            at the reference scales (`Scl.ref`): `HonIn` for the last state of the
                             residual stream, if the program runs on well-formed weights, the policy
                             holds of its logits, `y.OK`, C, θ < 2^40 and cap < 2^16;
                             `honIn_program_last`: at `Req.last y`, from `ModelIs`, for well-formed
                             weights
The proofs are in Inst/Model/Head/HonestN.lean, for every valid final normalisation; this file has
the case `Scl.nf`, under `[Lawful]` (Inst/Model/Head/NoWrap.lean).
The cell rule is used in the widened form of Inst/Model/Widened.lean; the header of HonestN.lean
says which cells follow a protocol text of the implementation (not in this repository).
Notation:
  `Lawful` (Inst/Model/Head/NoWrap.lean): a class, of type `Prop`: the quantization scales are valid
    for the head: their final normalisation is in the range of NORM (`NormPar.OK`).
  `y : Req` (Inst/Model/Head/Index.lean): what the head reads of a request and of the policy: `y.r`,
    `y.e`: the two numbers that bound the covered positions; `y.win i`: the token that is checked at
    position i; `y.pol`: the three numbers of the acceptance policy.
  `y.OK` (`Req.OK`, Inst/Model/Head/Index.lean): a `Prop`: every checked token is below V.
  `AcceptancePolicy` (Inst/Model/ProgramR.lean): the three numbers of the acceptance policy: the clip (C), the
    bound on the mean cost (θ), the limit on the number of positions above the clip (cap).
  `PolOK` (Inst/Model/ProgramR.lean): a `Prop`: the policy's three clauses (a), (b), (c) of the
    comment at the top of that file.
Limits: what the head of Inst/Model/Head/HonestN.lean lists as not said is not said here either.
That is: nothing is said on the protocol; all is at the step table and at sh = 8 only (`EX`,
Inst/Model/Tables.lean; `costOf`, Inst/Model/ProgramR.lean); outside `HonIn` and `[Lawful]` the
cells are still defined, and mean nothing.
(Words of this library: lean/GLOSSARY.md.)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Head.HonestN
import Inst.Model.Head.NoWrap

set_option autoImplicit false

namespace Inst.Model.Head

open Finset

export N (bX b256_congr R_congr cs_congr idn_congr)

/-- the logits of the residual stream x at position i -/
def lgv [scl : Scl] (x : ℕ → Vec) (H : Mat) (i v : ℕ) : ℤ := N.lgv Scl.nf x H i v

/-- The honest cells. -/
def honCells [scl : Scl] (x : ℕ → Vec) (H : Mat) (y : Req) : Cells ℤ := N.honCells Scl.nf x H y

/-- What is assumed of the run of the program and of the policy. -/
structure HonIn [scl : Scl] (x : ℕ → Vec) (H : Mat) (y : Req) : Prop where
  ok : ∀ i < nT, NORM.OK Scl.nf nD (x i)
  hH : ∀ j v, |H j v| ≤ 2 ^ 12
  win : y.OK
  pol : PolOK (lgv x H) y.pol y.inst
  C : y.pol.C < 2 ^ 40
  theta : y.pol.theta < 2 ^ 40
  cap : y.pol.cap < 2 ^ 16

variable {x : ℕ → Vec} {H : Mat} {y : Req}

/-- The honest cells are those of Inst/Model/Head/HonestN.lean at `Scl.nf`. -/
theorem honCells_N [scl : Scl] (x : ℕ → Vec) (H : Mat) (y : Req) :
    N.honCells Scl.nf x H y = honCells x H y := rfl

theorem HonIn.toN [scl : Scl] [law : Lawful] (h : HonIn x H y) : N.HonIn Scl.nf x H y :=
  ⟨law.nf, h.ok, h.hH, h.win, h.pol, h.C, h.theta, h.cap⟩

/-- under `HonIn` and `[Lawful]`: every cell of the honest trace of the head, and of the borrowed x,
has absolute value at most 128 -/
theorem hon_cells_le [scl : Scl] [law : Lawful] (h : HonIn x H y) {i : ℕ} (hi : i < nT) :
    (∀ φ < nFeat .hf, |(honCells x H y).hf φ i| ≤ 128) ∧
    (∀ φ < nFeat .hd, |(honCells x H y).hd φ i| ≤ 128) ∧
    (∀ φ < nFeat .hr, |(honCells x H y).hr φ i| ≤ 128) ∧
    ∀ φ < nFeat .x, |(honCells x H y).x φ i| ≤ 128 :=
  N.hon_cells_le h.toN hi

/-! ## With the definitions of Inst/Model/Program.lean -/

/-- If the program runs on (idx, prompt), with well-formed weights idx, and the policy holds of its
logits, with `y.OK`, C, θ < 2^40 and cap < 2^16, then `HonIn`, at the reference scales (`Scl.ref`),
holds for the last state of its residual stream, H and y. -/
theorem honIn_program (tb : Tables) (idx : Weights) (hWF : idx.WF ppref)
    (prompt : Fin ppref.T → Fin ppref.V) {y : Req} (hrun : Runs ppref tb idx prompt) (hw : y.OK)
    (hp : PolOK (Inst.Model.lg ppref tb idx prompt) y.pol y.inst) (hC : y.pol.C < 2 ^ 40)
    (hθ : y.pol.theta < 2 ^ 40) (hcap : y.pol.cap < 2 ^ 16) :
    HonIn (X ppref tb idx prompt (2 * ppref.layers)) idx.H y where
  ok := fun i hi => hrun.2 i hi
  hH := fun j v => by
    have := hWF.2.2 j v
    rw [abs_le]
    split_ifs at this
    · constructor <;> omega
    · rw [this]; norm_num
  win := hw
  pol := hp
  C := hC
  theta := hθ
  cap := hcap

/-- At the request for the next token after 1,024 tokens: `HonIn`, at the reference scales
(`Scl.ref`), from `ModelIs`, for well-formed weights idx. No position is counted, so of the policy
only (c) applies (`PolOK.c`, Inst/Model/ProgramR.lean). -/
theorem honIn_program_last (tb : Tables) (idx : Weights) (hWF : idx.WF ppref)
    (prompt : Fin ppref.T → Fin ppref.V) {y : ℕ} (hm : ModelIs ppref tb idx prompt y) :
    HonIn (X ppref tb idx prompt (2 * ppref.layers)) idx.H (Req.last y) := by
  have hy : y < 202048 := hm.2.1
  have hc : (Req.last y).inst.cnt = ∅ := Finset.eq_empty_of_forall_notMem fun i hi => by
    have := (Req.last y).mem_inst_cnt.1 hi
    simp only [Req.last] at this
    omega
  have hN : (Req.last y).inst.NB = 0 := by rw [← (Req.last y).inst.card_cnt, hc]; rfl
  refine honIn_program tb idx hWF prompt hm.1 (fun _ => hm.2.1) ⟨?_, ?_, fun _ _ => ?_⟩
    (by norm_num [Req.last]) (by norm_num [Req.last]) (by norm_num [Req.last])
  · rw [hc, hN]; simp
  · rw [hc]; simp
  · have e : (Req.last y).inst.y.val = y := by
      show min y 202047 = y
      omega
    rw [e]
    exact (gapOf_eq_zero_iff ppref.V _ hm.2.1).2 ⟨hm.2.2.1, hm.2.2.2⟩

end Inst.Model.Head
