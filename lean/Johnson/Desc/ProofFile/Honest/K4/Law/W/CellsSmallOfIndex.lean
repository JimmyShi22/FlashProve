-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CellsSmallOfIndex.lean: CONDITIONAL.

What is here. THE CELLS THAT K4's ROW READS ARE SMALL (`K4CellsSmall`), AT AN INDEX THAT IS A LETTER:
wherever the filling's trace is the trace of an index of the library. At `fullIn` the index is the
input's own.

  `k4CellsSmall_of_index`   **the cells are small**, from hV (each valid input is one that `ready`
      takes) and hTrace (what the filling's trace returns, `fullIn.trace` returns at some index)

Limits. CONDITIONAL on h, hA, hV and hTrace. `fullIn.trace` is spent once, at the index that hTrace
gives. The full size alone; the format's second hash function alone.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsSmallFullIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (HTailF2 Reading)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.HonestTrace (planesOf_01 meetsAll_in_scope)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.First.Look (szOf)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, hA, hTrace and hV. **THE TRACE's CELLS ARE SMALL**, at a filling whose trace is
that of an index of the library. F: any description; it stands in `ReadyInput` alone. At a request
that is not served the prover has no trace: `ReadyInput` holds of no input there, and this statement
is idle. -/
theorem k4CellsSmall_of_index (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {W₀ Rc X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (toIndex : W₀ → Option Cm.Idx)
    (hTrace : ∀ Zq w₀ ξ tr, P.trace Zq w₀ ξ = some tr →
      ∃ i, toIndex w₀ = some i ∧ fullIn.trace Zq i ξ = some tr)
    (F : FileDescription ProofFile.Inst) (Vd : Local W₀ Rc ProofFile.Inst Cells → Prop)
    (hV : ∀ v, Vd v → ReadyInput F A.H v) (tl : HTailF2) (Qp : K4Pub) (weights : W₀ → Weights)
    (tokens : ProofFile.Inst → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    K4CellsSmall Vd tl Qp id weights tokens look := by
  intro v hv i c _ _
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X :=
    Op.W ▸ Op.public
  have ht := (hV v hv).2.2
  rw [atPure_trace hA] at ht
  obtain ⟨ix, -, ht'⟩ := hTrace _ _ _ _ ht
  obtain ⟨x, -, Sv, eC⟩ := fullIn_trace_some ht'
  rw [(atPure_at_laid_ground h.laid Op.blank hA).1] at Sv eC
  have M := meetsAll_in_scope h.scope h.reads hpub (pl := OnBytes.HonestTrace.plOf Zp.p.X ix x)
    (fun k a b => planesOf_01 _ _ _ _ k a b) Sv
  have H : ∀ a : Fin (tl.mats.getD i {}).m, ∃ z : ℤ, |z| < 129 ∧
      OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X ix x)
        (k4Owner Qp i).1 (k4Owner Qp i).2.1 a.val ((k4Owner Qp i).2.2 + c) = ((z : ℤ) : Cb.Gl.F) :=
    fun a => cellOf_int M.small _ _ _ _
  choose col hcol using H
  have eB : (((szOf tl).beta : ℕ) : ℤ) = 2 ^ 17 := by
    show ((2 ^ 17 : ℕ) : ℤ) = 2 ^ 17
    norm_num
  refine ⟨col, fun a => ?_, fun a => ?_⟩
  · rw [eB]
    exact lt_trans (hcol a).1 (by norm_num)
  · show _ = Reading.gl.val (OnBytes.ofF (OnBytes.Slice.ofF
      ((id v.trace).cell (k4Owner Qp i).1 (k4Owner Qp i).2.1 a.val ((k4Owner Qp i).2.2 + c))))
    rw [gl_slice]
    show _ = algebraMap Cb.Gl.F Cb.Gl.E
      (v.trace.cell (k4Owner Qp i).1 (k4Owner Qp i).2.1 a.val ((k4Owner Qp i).2.2 + c))
    rw [eC]
    show _ = algebraMap Cb.Gl.F Cb.Gl.E
      (OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X ix x)
        (k4Owner Qp i).1 (k4Owner Qp i).2.1 a.val ((k4Owner Qp i).2.2 + c))
    rw [(hcol a).2, map_intCast]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4CellsSmall_of_index
