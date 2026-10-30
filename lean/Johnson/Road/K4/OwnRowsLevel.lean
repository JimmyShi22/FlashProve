-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnRowsLevel.lean: A PRODUCT LAYER's OWN ROW AGAINST THE LEDGER's FORM, AT THE WORDS
THAT THE CHAIN's DATA READ OFF THE TAPE. Where `Fl.levelIn` returns, the row that the text holds
(`Level.row`) is worth 0 exactly if `prodU` (Cb/Pv/Lay/End/RowForm.lean) is worth 0 at the typed
output `sumOut` OF THE TAPE's WORDS `pscT 0 L.k t` (OnBytes/Desc/First/P1/TailTape.lean), end values
included. One lemma and two statements, with proofs.

`level_row_prodU` (OnBytes/Desc/First/P1/RowForms.lean) says the like at end values v under "there
are", tied to the tape nowhere. Here (D3) and (D4) of `SumSaid.row` are paid; (D1) and (D2) stay.

  `level_mid_shown`: the ledger between the layer's two runs of hidden values holds, under the two
  end values' slots, what the values' round sent.
  `level_row_tape`: for every `ProdL` L, state st and point tie hp (as in `level_tie_flat`): for
  every world W and entries m, w with (D1) and (D2): `o.row.value ρ W = 0 ↔ Blocks.Form.val
    (Sum.elim m w) (prodU L (sumOut ρ L.toSum (F₀ …) st ‹the record's target› (pscT 0 L.k t).mu ‹the
    record's eps› (pscT 0 L.k t).rs (pscT 0 L.k t).sentY (pscT 0 L.k t).beta hβ fun b => ρ.val
    ((pscT 0 L.k t).v.getD (lvNum b) zeroE))) = 0`.

  `level_row_tapeUp`: the same against `upForm (Cb.Sub.formU L.toSum.T.par (fun _ b _ _ =>
  Empty.elim b) …)`: the form in which Cb/Pv/Lay/End/NormsRows.lean:57 writes the squares' own
    claim.

NO NEW ARGUMENT: `level_pscT` (OnBytes/Desc/First/P1/HeardPsc.lean), `level_recAt` (OwnRecs.lean),
`sum_said`, `level_fits`, `level_shown`, `hideRun_ok`, `Fo.hideRun_later`; `row_uForm`.

Limits. PREMISES: `Sized F`; hβ; hp; (D1), (D2) (OwnD1.lean, OwnD2.lean). One direction of use: from
a return. That a stage of a value IS `L.toSum` under the pick F₀ with the numbering `lvNum` is for
whoever holds the value. Nothing on soundness.
-/
import Johnson.Road.K4.OwnRows
import OnBytes.Desc.First.P1.LevelTieFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.K.Kc Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv.Att OnBytes.Tie.Pv.Lay.Eng
open Cb.Pv.Lay.End.Gated (prodU)
open OnBytes.Psc (Weight)
open OnBytes.PscRun (Sized hideRun_ok)
open OnBytes.Desc.First.P1 (pscT levelRec levelWs levelY levelVals levelIn_heard level_shown
  level_pscT row_uForm row_upFormU)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {J₂ : Type} [Fintype J₂]

/-- Between the layer's two runs of hidden values. -/
theorem level_mid_shown {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G F1 : Fork}
    {t u : Tape} {o : Level} {v : Array E} (hF : Sized F)
    (h : Fl.levelIn mu rho C order F t = some (o, G, u)) (hv : v.size = 2)
    (h1 : ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork).hideRun o.sL v (levelY mu t).2.2 =
      some F1)
    (h2 : F1.hideRun (levelRec mu rho C order F t).first
      (Array.replicate (levelRec mu rho C order F t).walk.1.length zeroE) (subE zeroE oneE) =
      some G) (e : ℕ) (he : e < 2) :
    F1.vp.getD (o.sL + e) zeroE = (pscT 0 mu t).v.getD e zeroE := by
  have hF' : Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) := hF
  obtain ⟨_, hS1, hin, _⟩ := hideRun_ok _ F1 o.sL v _ hF' h1
  have k := hin e (by omega)
  have g := (Fo.hideRun_later hS1 h2).keep (o.sL + e) k.2.2.1
  rw [← g.2.1]
  exact level_shown hF h G (Fo.Later.refl G) e he

/-- **A product layer's row against the ledger's form, at the tape's words.** -/
theorem level_row_tape (L : ProdL K) {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {o : Level} (h : Fl.levelIn L.k rho C order F t = some (o, G, u))
    (hs : Sized F) (hβ : ρ.val (pscT 0 L.k t).beta ≠ 0) (st : L.St)
    (hp : ∀ j : Fin L.k, L.pnt st (L.e j) =
      ρ.val (rho.getD (L.k - 1 - order.getD j.1 0) zeroE))
    (Ex : ExtSpec) (y : Ex.Str) (W : World K) (m : L.J → K) (w : J₂ → K)
    (D1 : L.toSum.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st)
      (levelRec L.k rho C order F t).first)
    (D2 : L.toSum.T.par.inc st m = ρ.val (levelRec L.k rho C order F t).target -
      (levelRec L.k rho C order F t).start.value ρ W) :
    o.row.value ρ W = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (prodU (J₂ := J₂) L
          (sumOut ρ L.toSum (F₀ L.toSum.T.par) st (levelRec L.k rho C order F t).target
            (pscT 0 L.k t).mu (levelRec L.k rho C order F t).eps (pscT 0 L.k t).rs
            (pscT 0 L.k t).sentY (pscT 0 L.k t).beta hβ
            fun b => ρ.val ((pscT 0 L.k t).v.getD (lvNum b) zeroE))) = 0 := by
  obtain ⟨ho, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, v, F1, hv2, hF1, hrow, hG⟩ :=
    levelIn_heard h
  have r := level_recAt h
  have hl : (pscT 0 L.k t).rs.map (·.1.length) = List.ofFn L.toSum.M.n := by
    rw [r.lens]
    exact (List.ofFn_const L.k 2).symm
  have s := sum_said ρ L.toSum (F₀ L.toSum.T.par) st (level_pscT h) hβ
    (fun b => ρ.val ((pscT 0 L.k t).v.getD (lvNum b) zeroE))
    (level_fits ρ L st rho order ho hp) hl r.sentY
  have hh0 := level_mid_shown hs h hv2 hF1 hG 0 (by omega)
  have hh1 := level_mid_shown hs h hv2 hF1 hG 1 (by omega)
  rw [Nat.add_zero] at hh0
  have hD4 : ∀ z, L.toSum.S.pol st z (fun b => ρ.val ((pscT 0 L.k t).v.getD (lvNum b) zeroE)) =
      ρ.val (mulE ((pscT 0 L.k t).v.getD 0 zeroE) ((pscT 0 L.k t).v.getD 1 zeroE)) := by
    intro z
    rw [ρ.mul]
    show ([(1 : K) * [ρ.val ((pscT 0 L.k t).v.getD (lvNum false) zeroE),
      ρ.val ((pscT 0 L.k t).v.getD (lvNum true) zeroE)].prod]).sum = _
    simp [lvNum]
  rw [hrow, hh0, hh1]
  exact row_uForm ρ s (F₀_ok _ (L.eq0 : Eq0 L.toSum.T.par)) Ex y W _ {} m D1 D2
    (by
      rw [Aff.value_empty]
      exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim) (hD4 _)
    (fun _ b => Empty.elim b) (fun _ _ b _ => Empty.elim b) w

/-- The same against the other way in which the ledger writes that claim (the squares' head:
`Cb/Pv/Lay/End/NormsRows.lean`). -/
theorem level_row_tapeUp (L : ProdL K) {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {o : Level} (h : Fl.levelIn L.k rho C order F t = some (o, G, u))
    (hs : Sized F) (hβ : ρ.val (pscT 0 L.k t).beta ≠ 0) (st : L.St)
    (hp : ∀ j : Fin L.k, L.pnt st (L.e j) =
      ρ.val (rho.getD (L.k - 1 - order.getD j.1 0) zeroE))
    (Ex : ExtSpec) (y : Ex.Str) (W : World K) (m : L.J → K) (w : J₂ → K)
    (D1 : L.toSum.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st)
      (levelRec L.k rho C order F t).first)
    (D2 : L.toSum.T.par.inc st m = ρ.val (levelRec L.k rho C order F t).target -
      (levelRec L.k rho C order F t).start.value ρ W) :
    o.row.value ρ W = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (Cb.Pv.Lay.End.upForm (J₂ := J₂) (Cb.Sub.formU L.toSum.T.par (fun _ b _ _ => Empty.elim b)
          (sumOut ρ L.toSum (F₀ L.toSum.T.par) st (levelRec L.k rho C order F t).target
            (pscT 0 L.k t).mu (levelRec L.k rho C order F t).eps (pscT 0 L.k t).rs
            (pscT 0 L.k t).sentY (pscT 0 L.k t).beta hβ
            fun b => ρ.val ((pscT 0 L.k t).v.getD (lvNum b) zeroE)))) = 0 := by
  obtain ⟨ho, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, v, F1, hv2, hF1, hrow, hG⟩ :=
    levelIn_heard h
  have r := level_recAt h
  have hl : (pscT 0 L.k t).rs.map (·.1.length) = List.ofFn L.toSum.M.n := by
    rw [r.lens]
    exact (List.ofFn_const L.k 2).symm
  have s := sum_said ρ L.toSum (F₀ L.toSum.T.par) st (level_pscT h) hβ
    (fun b => ρ.val ((pscT 0 L.k t).v.getD (lvNum b) zeroE))
    (level_fits ρ L st rho order ho hp) hl r.sentY
  have hh0 := level_mid_shown hs h hv2 hF1 hG 0 (by omega)
  have hh1 := level_mid_shown hs h hv2 hF1 hG 1 (by omega)
  rw [Nat.add_zero] at hh0
  have hD4 : ∀ z, L.toSum.S.pol st z (fun b => ρ.val ((pscT 0 L.k t).v.getD (lvNum b) zeroE)) =
      ρ.val (mulE ((pscT 0 L.k t).v.getD 0 zeroE) ((pscT 0 L.k t).v.getD 1 zeroE)) := by
    intro z
    rw [ρ.mul]
    show ([(1 : K) * [ρ.val ((pscT 0 L.k t).v.getD (lvNum false) zeroE),
      ρ.val ((pscT 0 L.k t).v.getD (lvNum true) zeroE)].prod]).sum = _
    simp [lvNum]
  rw [hrow, hh0, hh1]
  exact row_upFormU ρ s (F₀_ok _ (L.eq0 : Eq0 L.toSum.T.par)) Ex y W _ {} m D1 D2
    (by
      rw [Aff.value_empty]
      exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim) (hD4 _)
    (fun _ b _ _ => Empty.elim b) (fun _ _ b _ => Empty.elim b) w

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.level_mid_shown
#print axioms OnBytes.Road.K4.level_row_tape
#print axioms OnBytes.Road.K4.level_row_tapeUp
