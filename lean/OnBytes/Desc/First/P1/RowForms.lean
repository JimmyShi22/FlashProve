-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/RowForms.lean: A SUMCHECK'S OWN ROW, AS THE TEXT HOLDS IT AND AS THE LIBRARY'S
LEDGER WRITES IT. The text holds the row form of the sumcheck's record (`Psc.rowForm`). The
library's ledger of the verifier's claims writes the first output claim as a form on early and late
entries (`uForm`, `prodU`, Cb/Pv/Lay/End/RowForm.lean). Three statements and their proofs.

  `row_uForm`: for every `SumSaid` (OnBytes/Tie/Pv/Lay/SumSaid.lean), under a lawful pick, (D1) to
    (D4) of `SumSaid.row`, and kept maps that are linear in the entries by rowB: the record's row
    form is worth 0 in the world exactly if `uForm` at the typed output is worth 0 at the early
    entries m, whatever the late entries are.
  `row_upFormU`: the same against `upForm (Cb.Sub.formU …)` (Cb/Pv/Lay/End/NormsRows.lean,
    Cb/Sub/SeatPsc.lean), as the ledger writes the batched sumcheck's first output claim.
  `level_row_prodU`: where `Fl.levelIn` returns (the binders of `level_tie_flat`,
    LevelTieFlat.lean): the layer's row is worth 0 exactly if `prodU` at the typed output is, for
    every world and all entries with (D1) and (D2).

NO NEW ARGUMENT: `SumSaid.row`, `level_tie_flat`; `uForm_iff`, `prodU_iff`, `val_upForm`,
`formU_holds` (in the three files below Cb/ that are named above).

Limits. (D1) to (D4) ARE PREMISES, as in `SumSaid.row`: (D1): the typed hiding coefficients are the
world's values under the sumcheck's own slots; (D2): the typed incoming form is the target's reading
less the start form's worth. Those of LevelTieFlat.lean. Nothing on soundness.
-/
import OnBytes.Desc.First.P1.LevelTieFlat
import Cb.Pv.Lay.End.RowForm
import Cb.Pv.Lay.End.NormsRows
import Cb.Sub.SeatPsc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.K.Kc Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv.Att OnBytes.Tie.Pv.Lay.Eng
open Cb.Pv.Lay.End.Gated (uForm uForm_iff prodU prodU_iff)
open OnBytes.Psc (Weight)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {J₂ : Type} [Fintype J₂]

/-- **The record's row form against the ledger's form of the first output claim.** -/
theorem row_uForm {L : SumL K} {F : ∀ st, HFixs (L.T.par.vars st)} {st : L.St}
    {p : OnBytes.Model.Psc} {ws : List Weight} {mu : E} {rs : List (List E × E)} {sentY : List E}
    {beta : E} {hβ : ρ.val beta ≠ 0} {vals : L.S.A → K}
    (s : SumSaid ρ L F st p ws mu rs sentY beta hβ vals) (hF : ∀ st, HFixs.OK _ (F st))
    (Ex : ExtSpec) (y : Ex.Str) (W : World K) (S0 : E) (kept : Aff) (m : L.J → K)
    (D1 : L.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.T.par.vars st) p.first)
    (D2 : L.T.par.inc st m = ρ.val p.target - p.start.value ρ W)
    (D3 : ∑ b, L.Q.polB st
          (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals)) vals b *
        L.Q.Fb st m b
          (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals)) =
      kept.value ρ W)
    (D4 : L.S.pol st (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals))
        vals = ρ.val S0)
    (rowB : (st : L.T.par.St) → L.T.par.B → HPt (L.T.par.vars st) → L.T.par.J → K)
    (hB : L.T.par.LinB rowB) (u : J₂ → K) :
    (p.rowForm S0 kept).value ρ W = 0 ↔
      Blocks.Form.val (Sum.elim m u)
        (uForm (J₂ := J₂) L.T.par rowB
          (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals)) = 0 :=
  (s.row ρ hF Ex y W S0 kept m D1 D2 D3 D4).trans (uForm_iff L.T.par rowB hB _ m u).symm

/-- The same against the other way in which the ledger writes that claim (the batched sumcheck's:
`stackCl`, Cb/Pv/Lay/End/StackA.lean). -/
theorem row_upFormU {L : SumL K} {F : ∀ st, HFixs (L.T.par.vars st)} {st : L.St}
    {p : OnBytes.Model.Psc} {ws : List Weight} {mu : E} {rs : List (List E × E)} {sentY : List E}
    {beta : E} {hβ : ρ.val beta ≠ 0} {vals : L.S.A → K}
    (s : SumSaid ρ L F st p ws mu rs sentY beta hβ vals) (hF : ∀ st, HFixs.OK _ (F st))
    (Ex : ExtSpec) (y : Ex.Str) (W : World K) (S0 : E) (kept : Aff) (m : L.J → K)
    (D1 : L.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.T.par.vars st) p.first)
    (D2 : L.T.par.inc st m = ρ.val p.target - p.start.value ρ W)
    (D3 : ∑ b, L.Q.polB st
          (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals)) vals b *
        L.Q.Fb st m b
          (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals)) =
      kept.value ρ W)
    (D4 : L.S.pol st (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals))
        vals = ρ.val S0)
    (rowB : (st : L.T.par.St) → L.T.par.B → HPt (L.T.par.vars st) → L.T.par.J → K)
    (hB : L.T.par.LinB rowB) (u : J₂ → K) :
    (p.rowForm S0 kept).value ρ W = 0 ↔
      Blocks.Form.val (Sum.elim m u)
        (Cb.Pv.Lay.End.upForm (J₂ := J₂) (Cb.Sub.formU L.T.par rowB
          (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals))) = 0 := by
  rw [Cb.Pv.Lay.End.val_upForm]
  exact (s.row ρ hF Ex y W S0 kept m D1 D2 D3 D4).trans
    (Cb.Sub.formU_holds L.T.par rowB hB _ m).symm

/-- **A product layer's row against the ledger's form.** -/
theorem level_row_prodU (L : ProdL K) {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {o : Level} (h : Fl.levelIn L.k rho C order F t = some (o, G, u))
    (hs : OnBytes.Model.Road.Sized F) (hβ : ρ.val (levelY L.k t).2.2 ≠ 0) (st : L.St)
    (hp : ∀ j : Fin L.k, L.pnt st (L.e j) =
      ρ.val (rho.getD (L.k - 1 - order.getD j.1 0) zeroE)) :
    ∃ (v : Array E) (F1 : Fork), v.size = 2 ∧
      ({ F with next := F.next + 1 + 2 * L.k + 2 + 2 } : Fork).hideRun o.sL v
        (levelY L.k t).2.2 = some F1 ∧
      ∀ (Ex : ExtSpec) (_ : Ex.Str) (W : World K) (m : L.J → K) (w : J₂ → K),
        L.toSum.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st)
          (levelRec L.k rho C order F t).first →
        L.toSum.T.par.inc st m = ρ.val (levelRec L.k rho C order F t).target -
          (levelRec L.k rho C order F t).start.value ρ W →
        (o.row.value ρ W = 0 ↔
          Blocks.Form.val (Sum.elim m w)
            (prodU (J₂ := J₂) L
              (sumOut ρ L.toSum (F₀ L.toSum.T.par) st (levelRec L.k rho C order F t).target
                (tapeMu t) (levelRec L.k rho C order F t).eps (levelRs L.k rho order t)
                (levelY L.k t).2.1 (levelY L.k t).2.2 hβ
                fun b => ρ.val (v.toList.getD (lvNum b) zeroE))) = 0) := by
  obtain ⟨v, F1, h1, h2, _, hrow, _⟩ := level_tie_flat ρ L h hs hβ st hp
  exact ⟨v, F1, h1, h2, fun Ex y W m w D1 D2 =>
    (hrow Ex y W m D1 D2).trans (prodU_iff L _ m w).symm⟩

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.row_uForm
#print axioms OnBytes.Desc.First.P1.row_upFormU
#print axioms OnBytes.Desc.First.P1.level_row_prodU
