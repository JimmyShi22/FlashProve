-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnRowsStage.lean: A PRODUCT LAYER's AND THE MERGE's OWN ROW AGAINST THE LEDGER's
FORM, AT A STAGE OF THE CHAIN. OwnRowsLevel.lean and OwnRowsMerge.lean say this of the library's
records `ProdL` and `MergeL`, under their own picks. Here it is said of any stage S of a chain
(`Stg`, Cb/Pv/Lay/Own.lean) THAT KEEPS NOTHING, at its data read off the tape (`stgT`,
OnBytes/Desc/First/P1/TailTape.lean), under `StgFits`: at `tailT`'s own states and targets that is
the typed output which stands in the chain's last statement. Statements and proofs.

  `level_row_stg`, `level_row_stgUp`: where `Fl.levelIn` returns (o, G, u) from a ledger with arrays
    of the right sizes: if the stage has no further scalar, its weights fit, no kept term counts
    (D3) and its summand at end values is the product of the two that are numbered 0 and 1 (D4):
    under (D1) and (D2): `o.row.value gl W = 0` exactly if the ledger's form of the stage's first
    output claim (`uForm`; Up: `upForm (Cb.Sub.formU …)`) is worth 0 at `(stgT num k t hβ st
    tg).out`.
  `merge_row_stg`: the same where `flatForkEnd` returns, for the form `wo.p.rowForm wo.fvp {}`, if
    the summand at end values is the one that is numbered 0.

NO NEW ARGUMENT: `stgT_row`, `stgT_rowUp` (OwnRows.lean); `level_recAt` (OwnRecs.lean),
`level_mid_shown` (OwnRowsLevel.lean), `merge_recAt` (MergeRec.lean), `merge_shown`
(MergeShown.lean).

Limits. PREMISES: `Sized F`; hβ; `StgFits`; the lawful pick; `LinB`; (D1), (D2); (D3) and (D4) IN
THE FORM OF FACTS ON THE STAGE's LETTERS (at the library's `ProdL` and `MergeL` they hold by
unfolding: OwnRowsLevel.lean, OwnRowsMerge.lean); the two numbers. One world: no draw. Nothing on
soundness.
-/
import Johnson.Road.K4.OwnRowsLevel
import Johnson.Road.K4.MergeShown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers
open OnBytes OnBytes.K.Kc OnBytes.Slice
open OnBytes.Model (Psc Aff World Fork Level WsLay WsClaim WsForkOut)
open OnBytes.Tie.Pv.Lay (RecAt StgFits)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.P1 (gl pscT stgT levelRec levelWs plainWs levelIn_heard)
open Cb.Pv.Lay.End.Gated (uForm)

variable {M X : Type} {J₂ : Type} [Fintype J₂]

/-- **A product layer's row at a stage.** -/
theorem level_row_stg {S : Stg GE M X} (num : S.L.S.A → ℕ) {k : ℕ} {rho : Array E} {C : Aff}
    {order : List Nat} {F G : Fork} {t u : Tape} {o : Level}
    (h : Fl.levelIn k rho C order F t = some (o, G, u)) (hs : Sized F)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) (hn : S.n = 0)
    (ht : tg = (levelRec k rho C order F t).target)
    (f : StgFits gl S st (levelWs k rho order) k 2) (hF : ∀ st, HFixs.OK _ (S.F st))
    (Ex : ExtSpec) (y : Ex.Str) (W : World GE) (m : S.L.J → GE)
    (D1 : S.L.T.par.W st m = OnBytes.Road.Hd.place W.slot (S.L.T.par.vars st)
      (levelRec k rho C order F t).first)
    (D2 : S.L.T.par.inc st m = gl.val (levelRec k rho C order F t).target -
      (levelRec k rho C order F t).start.value gl W)
    (D3 : ∀ z vals, ∑ b, S.L.Q.polB st z vals b * S.L.Q.Fb st m b z = 0)
    (a0 a1 : S.L.S.A) (h0 : num a0 = 0) (h1 : num a1 = 1)
    (D4 : ∀ z vals, S.L.S.pol st z vals = vals a0 * vals a1)
    (rowB : (st : S.L.T.par.St) → S.L.T.par.B → HPt (S.L.T.par.vars st) → S.L.T.par.J → GE)
    (hB : S.L.T.par.LinB rowB) (w : J₂ → GE) :
    o.row.value gl W = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (uForm (J₂ := J₂) S.L.T.par rowB (stgT num k t hβ st tg).out) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, v, F1, hv2, hF1, hrow, hG⟩ :=
    levelIn_heard h
  have hh0 := level_mid_shown hs h hv2 hF1 hG 0 (by omega)
  have hh1 := level_mid_shown hs h hv2 hF1 hG 1 (by omega)
  rw [Nat.add_zero] at hh0
  rw [hrow, hh0, hh1]
  refine stgT_row num k t hβ st tg hn (level_recAt h) ht f hF Ex y W _ {} m D1 D2 ?_ ?_ rowB hB w
  · rw [Aff.value_empty]
    exact D3 _ _
  · rw [D4, gl.mul]
    show gl.val ((pscT S.n k t).v.getD (num a0) _) * gl.val ((pscT S.n k t).v.getD (num a1) _) = _
    rw [h0, h1]
    rfl

/-- The same against the other way of writing that claim. -/
theorem level_row_stgUp {S : Stg GE M X} (num : S.L.S.A → ℕ) {k : ℕ} {rho : Array E} {C : Aff}
    {order : List Nat} {F G : Fork} {t u : Tape} {o : Level}
    (h : Fl.levelIn k rho C order F t = some (o, G, u)) (hs : Sized F)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) (hn : S.n = 0)
    (ht : tg = (levelRec k rho C order F t).target)
    (f : StgFits gl S st (levelWs k rho order) k 2) (hF : ∀ st, HFixs.OK _ (S.F st))
    (Ex : ExtSpec) (y : Ex.Str) (W : World GE) (m : S.L.J → GE)
    (D1 : S.L.T.par.W st m = OnBytes.Road.Hd.place W.slot (S.L.T.par.vars st)
      (levelRec k rho C order F t).first)
    (D2 : S.L.T.par.inc st m = gl.val (levelRec k rho C order F t).target -
      (levelRec k rho C order F t).start.value gl W)
    (D3 : ∀ z vals, ∑ b, S.L.Q.polB st z vals b * S.L.Q.Fb st m b z = 0)
    (a0 a1 : S.L.S.A) (h0 : num a0 = 0) (h1 : num a1 = 1)
    (D4 : ∀ z vals, S.L.S.pol st z vals = vals a0 * vals a1)
    (rowB : (st : S.L.T.par.St) → S.L.T.par.B → HPt (S.L.T.par.vars st) → S.L.T.par.J → GE)
    (hB : S.L.T.par.LinB rowB) (w : J₂ → GE) :
    o.row.value gl W = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (Cb.Pv.Lay.End.upForm (J₂ := J₂)
          (Cb.Sub.formU S.L.T.par rowB (stgT num k t hβ st tg).out)) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, v, F1, hv2, hF1, hrow, hG⟩ :=
    levelIn_heard h
  have hh0 := level_mid_shown hs h hv2 hF1 hG 0 (by omega)
  have hh1 := level_mid_shown hs h hv2 hF1 hG 1 (by omega)
  rw [Nat.add_zero] at hh0
  rw [hrow, hh0, hh1]
  refine stgT_rowUp num k t hβ st tg hn (level_recAt h) ht f hF Ex y W _ {} m D1 D2 ?_ ?_ rowB hB w
  · rw [Aff.value_empty]
    exact D3 _ _
  · rw [D4, gl.mul]
    show gl.val ((pscT S.n k t).v.getD (num a0) _) * gl.val ((pscT S.n k t).v.getD (num a1) _) = _
    rw [h0, h1]
    rfl

/-- **The merge's row at a stage.** -/
theorem merge_row_stg {S : Stg GE M X} (num : S.L.S.A → ℕ) {lay : WsLay} {cl : Array WsClaim}
    {sv : Array Nat} {F G : Fork} {t u : Tape} {wo : WsForkOut}
    (h : flatForkEnd lay cl sv F t = some (wo, G, u)) (hs : Sized F)
    (hβ : gl.val (pscT S.n lay.lk (t.drop 1)).beta ≠ 0) (st : S.L.St) (tg : E) (hn : S.n = 0)
    (ht : tg = wo.p.target) (f : StgFits gl S st (plainWs lay.lk) lay.lk 1)
    (hF : ∀ st, HFixs.OK _ (S.F st)) (Ex : ExtSpec) (y : Ex.Str) (W : World GE) (m : S.L.J → GE)
    (D1 : S.L.T.par.W st m = OnBytes.Road.Hd.place W.slot (S.L.T.par.vars st) wo.p.first)
    (D2 : S.L.T.par.inc st m = gl.val wo.p.target - wo.p.start.value gl W)
    (D3 : ∀ z vals, ∑ b, S.L.Q.polB st z vals b * S.L.Q.Fb st m b z = 0)
    (a0 : S.L.S.A) (h0 : num a0 = 0) (D4 : ∀ z vals, S.L.S.pol st z vals = vals a0)
    (rowB : (st : S.L.T.par.St) → S.L.T.par.B → HPt (S.L.T.par.vars st) → S.L.T.par.J → GE)
    (hB : S.L.T.par.LinB rowB) (w : J₂ → GE) :
    (wo.p.rowForm wo.fvp {}).value gl W = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (uForm (J₂ := J₂) S.L.T.par rowB (stgT num lay.lk (t.drop 1) hβ st tg).out) = 0 := by
  refine stgT_row num lay.lk (t.drop 1) hβ st tg hn (merge_recAt h).1 ht f hF Ex y W _ {} m D1 D2
    ?_ ?_ rowB hB w
  · rw [Aff.value_empty]
    exact D3 _ _
  · rw [D4, merge_shown hs h]
    show gl.val ((pscT S.n lay.lk (t.drop 1)).v.getD (num a0) _) = _
    rw [h0]
    rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.level_row_stg
#print axioms OnBytes.Road.K4.level_row_stgUp
#print axioms OnBytes.Road.K4.merge_row_stg
