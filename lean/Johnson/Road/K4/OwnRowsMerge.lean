-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnRowsMerge.lean: THE MERGE's OWN ROW AGAINST THE LEDGER's FORM, AT THE WORDS THAT
THE CHAIN's DATA READ OFF THE TAPE. K4's run "back" makes the merge's row as `ownClaim o.wo.p
o.wo.fvp {}` (OnBytes/Desc/First/K4/Plain.lean: `formsBack`): the form `wo.p.rowForm wo.fvp {}`.
Where `flatForkEnd` returns from a ledger with arrays of the right sizes, that form is worth 0
exactly if `mergeU` (Cb/Pv/Lay/End/RowForm.lean: the one member of `mergeLed`,
Cb/Pv/Lay/End/MergeShare.lean) is worth 0 at the typed output `sumOut` of the tape's words. One
statement and its proof.

`hear_tie` (Johnson/Top/H0/MergeLaw/Said.lean) says the like against `UHolds`,
at lists under "there are" and at the word v that was sent. Here the lists are `pscT`'s and the word
is the record's `fvp`.

  `merge_row_tape`: for every `MergeL` L with L.k = lay.lk and every state st: for every world W and
    entries m, w with (D1) and (D2): `(wo.p.rowForm wo.fvp {}).value ρ W = 0 ↔ Blocks.Form.val
    (Sum.elim m w) (mergeU L (sumOut ρ L.toSum (the pick `pick`) st wo.p.target (pscT 0 L.k (t.drop
    1)).mu wo.p.eps … fun _ => ρ.val ((pscT 0 L.k (t.drop 1)).v.getD 0 zeroE))) = 0`.

NO NEW ARGUMENT: `merge_recAt` (MergeRec.lean), `merge_shown` (MergeShown.lean),
`sum_said`, `merge_fits` (OnBytes/Tie/Pv/Lay/MergeTie.lean), `MergeL.pick_ok`; `row_uForm`
(OnBytes/Desc/First/P1/RowForms.lean).

Limits. PREMISES: `Sized F`; hβ; (D1), (D2). (D3), (D4) are paid. That `ownClaim` returns this form
is `pscRow_spec`. One direction of use: from a return. Nothing on the pending row (OwnPending.lean).
Nothing on soundness.
-/
import Johnson.Road.K4.MergeShown
import OnBytes.Desc.First.P1.RowForms
import OnBytes.Tie.Pv.Lay.MergeTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.K.Kc Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv.Lay.Eng (SumSaid sum_said sumOut merge_fits)
open Cb.Pv.Lay.End.Gated (mergeU)
open OnBytes.Psc (Weight)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.P1 (pscT row_uForm)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {J₂ : Type} [Fintype J₂]

/-- **The merge's row against the ledger's form, at the tape's words.** -/
theorem merge_row_tape (L : MergeL K) {lay : WsLay} (hk : L.k = lay.lk) {cl : Array WsClaim}
    {sv : Array Nat} {F G : Fork} {t u : Tape} {wo : WsForkOut} (hF : Sized F)
    (h : flatForkEnd lay cl sv F t = some (wo, G, u))
    (hβ : ρ.val (pscT 0 L.k (t.drop 1)).beta ≠ 0) (st : L.St) (Ex : ExtSpec) (y : Ex.Str)
    (W : World K) (m : L.J → K) (w : J₂ → K)
    (D1 : L.toSum.T.par.W st m =
      OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st) wo.p.first)
    (D2 : L.toSum.T.par.inc st m = ρ.val wo.p.target - wo.p.start.value ρ W) :
    (wo.p.rowForm wo.fvp {}).value ρ W = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (mergeU (J₂ := J₂) L
          (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st wo.p.target
            (pscT 0 L.k (t.drop 1)).mu wo.p.eps (pscT 0 L.k (t.drop 1)).rs
            (pscT 0 L.k (t.drop 1)).sentY (pscT 0 L.k (t.drop 1)).beta hβ
            fun _ => ρ.val ((pscT 0 L.k (t.drop 1)).v.getD 0 zeroE))) = 0 := by
  have r := (merge_recAt h).1
  have hv := merge_shown hF h
  rw [← hk] at r hv
  obtain ⟨C, τ, first, a⟩ := r.psc
  have hl : (pscT 0 L.k (t.drop 1)).rs.map (·.1.length) = List.ofFn L.toSum.M.n := by
    rw [r.lens]
    exact (List.ofFn_const L.k 2).symm
  have s := sum_said ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st a hβ
    (fun _ => ρ.val ((pscT 0 L.k (t.drop 1)).v.getD 0 zeroE)) (merge_fits ρ L st) hl r.sentY
  rw [hv]
  exact row_uForm ρ s L.pick_ok Ex y W _ {} m D1 D2
    (by
      rw [Aff.value_empty]
      exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim)
    (by
      show ([(1 : K) * [ρ.val ((pscT 0 L.k (t.drop 1)).v.getD 0 zeroE)].prod]).sum = _
      simp)
    (fun _ b => Empty.elim b) (fun _ _ b _ => Empty.elim b) w

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.merge_row_tape
