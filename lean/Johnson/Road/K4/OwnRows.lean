-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnRows.lean: A SUMCHECK'S OWN ROW AT THE CHAIN's DATA READ OFF A TAPE: the row form
of the text's record is worth 0 exactly if the form in which the library's ledger writes the stage's
first output claim is worth 0 AT THE STAGE's OWN TYPED OUTPUT `StgH.out` (the output that stands in
the chain's last statement: OnBytes/Desc/First/P1/TailParts.lean). Two statements and their proofs,
for every stage.

  `stgT_said`: for the data `stgT num k t hβ st tg` (OnBytes/Desc/First/P1/TailTape.lean) of a stage
    S, a record p with `RecAt` at `pscT`, tg = p.target and `StgFits`: the stage's output is
    `sumOut` at the record's target and eps, and `SumSaid` holds of it.
  `stgT_row`: under a lawful pick, (D1) to (D4) of `SumSaid.row` said at `StgH.out`, and kept maps
    linear by rowB: `(p.rowForm S0 kept).value gl W = 0 ↔ Blocks.Form.val (Sum.elim m u) (uForm
    S.L.T.par rowB D.out) = 0`. `prodU L o` and `mergeU L o` (Cb/Pv/Lay/End/RowForm.lean) are
    `uForm` at no kept map, by definition.
  `stgT_rowUp`: the same against `upForm (Cb.Sub.formU S.L.T.par rowB D.out)`.

NO NEW ARGUMENT: `rec_out` (OnBytes/Tie/Pv/Lay/HearTieAll.lean); `row_uForm`,
`row_upFormU` (OnBytes/Desc/First/P1/RowForms.lean).

Limits. (D1) to (D4), `StgFits`, the lawful pick and `LinB` ARE PREMISES. Which S0 and which kept
form the text hands to its row is said where the text is read (LevelTieFlat.lean, StackTieFlat.lean,
HearCalls.lean; Johnson/Top/H0/MergeLaw/Said.lean). Nothing on soundness.
-/
import Johnson.Road.K4.OwnJoint
import OnBytes.Desc.First.P1.RowForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers
open OnBytes OnBytes.K.Kc OnBytes.Slice
open OnBytes.Model (Psc Aff World)
open OnBytes.Tie.Pv.Lay (RecAt StgFits rec_out)
open OnBytes.Tie.Pv.Lay.Eng (StgH SumSaid sumOut)
open OnBytes.Desc.First.P1 (gl pscT stgT sentOf row_uForm row_upFormU)
open Cb.Pv.Lay.End.Gated (uForm)

variable {M X : Type} {J₂ : Type} [Fintype J₂]

/-- The stage's output, and what is said of it. -/
theorem stgT_said {S : Stg GE M X} (num : S.L.S.A → ℕ) (k : ℕ) (t : Tape)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) {n : ℕ} (hn : S.n = n)
    {ws : List OnBytes.Psc.Weight} {dY nv : ℕ} {p : Psc} (r : RecAt (pscT n k t) ws k dY nv p)
    (ht : tg = p.target) (f : StgFits gl S st ws k dY) :
    (stgT num k t hβ st tg).out =
        sumOut gl S.L S.F st p.target (pscT S.n k t).mu p.eps (pscT S.n k t).rs
          (pscT S.n k t).sentY (pscT S.n k t).beta hβ (stgT num k t hβ st tg).v ∧
      SumSaid gl S.L S.F st p (ws ++ [OnBytes.Psc.Weight.atZero (S.L.M.DY + 1)]) (pscT S.n k t).mu
        (pscT S.n k t).rs (pscT S.n k t).sentY (pscT S.n k t).beta hβ
        (stgT num k t hβ st tg).v := by
  subst hn
  obtain ⟨rfl, rfl, h2, h3⟩ := f
  obtain ⟨C, τ, first, a⟩ := r.psc
  refine ⟨?_, (rec_out gl (stgT num S.L.S.k t hβ st tg) (riders := sentOf t) ⟨rfl, rfl, ht⟩ r h2
    h3).2⟩
  show sumOut gl S.L S.F st tg (pscT S.n S.L.S.k t).mu (pscT S.n S.L.S.k t).eps _ _ _ hβ _ = _
  rw [ht, a.eps]
  rfl

/-- **The record's row form against the ledger's form, at the stage's own output.** -/
theorem stgT_row {S : Stg GE M X} (num : S.L.S.A → ℕ) (k : ℕ) (t : Tape)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) {n : ℕ} (hn : S.n = n)
    {ws : List OnBytes.Psc.Weight} {dY nv : ℕ} {p : Psc} (r : RecAt (pscT n k t) ws k dY nv p)
    (ht : tg = p.target) (f : StgFits gl S st ws k dY) (hF : ∀ st, HFixs.OK _ (S.F st))
    (Ex : ExtSpec) (y : Ex.Str) (W : World GE) (S0 : E) (kept : Aff) (m : S.L.J → GE)
    (D1 : S.L.T.par.W st m = OnBytes.Road.Hd.place W.slot (S.L.T.par.vars st) p.first)
    (D2 : S.L.T.par.inc st m = gl.val p.target - p.start.value gl W)
    (D3 : ∑ b, S.L.Q.polB st (S.L.Q.outPt S.L.M (stgT num k t hβ st tg).out)
          (stgT num k t hβ st tg).v b *
        S.L.Q.Fb st m b (S.L.Q.outPt S.L.M (stgT num k t hβ st tg).out) = kept.value gl W)
    (D4 : S.L.S.pol st (S.L.Q.outPt S.L.M (stgT num k t hβ st tg).out) (stgT num k t hβ st tg).v =
      gl.val S0)
    (rowB : (st : S.L.T.par.St) → S.L.T.par.B → HPt (S.L.T.par.vars st) → S.L.T.par.J → GE)
    (hB : S.L.T.par.LinB rowB) (u : J₂ → GE) :
    (p.rowForm S0 kept).value gl W = 0 ↔
      Blocks.Form.val (Sum.elim m u)
        (uForm (J₂ := J₂) S.L.T.par rowB (stgT num k t hβ st tg).out) = 0 := by
  obtain ⟨e, s⟩ := stgT_said num k t hβ st tg hn r ht f
  rw [e] at D3 D4 ⊢
  exact row_uForm gl s hF Ex y W S0 kept m D1 D2 D3 D4 rowB hB u

/-- The same against the other way of writing that claim. -/
theorem stgT_rowUp {S : Stg GE M X} (num : S.L.S.A → ℕ) (k : ℕ) (t : Tape)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) {n : ℕ} (hn : S.n = n)
    {ws : List OnBytes.Psc.Weight} {dY nv : ℕ} {p : Psc} (r : RecAt (pscT n k t) ws k dY nv p)
    (ht : tg = p.target) (f : StgFits gl S st ws k dY) (hF : ∀ st, HFixs.OK _ (S.F st))
    (Ex : ExtSpec) (y : Ex.Str) (W : World GE) (S0 : E) (kept : Aff) (m : S.L.J → GE)
    (D1 : S.L.T.par.W st m = OnBytes.Road.Hd.place W.slot (S.L.T.par.vars st) p.first)
    (D2 : S.L.T.par.inc st m = gl.val p.target - p.start.value gl W)
    (D3 : ∑ b, S.L.Q.polB st (S.L.Q.outPt S.L.M (stgT num k t hβ st tg).out)
          (stgT num k t hβ st tg).v b *
        S.L.Q.Fb st m b (S.L.Q.outPt S.L.M (stgT num k t hβ st tg).out) = kept.value gl W)
    (D4 : S.L.S.pol st (S.L.Q.outPt S.L.M (stgT num k t hβ st tg).out) (stgT num k t hβ st tg).v =
      gl.val S0)
    (rowB : (st : S.L.T.par.St) → S.L.T.par.B → HPt (S.L.T.par.vars st) → S.L.T.par.J → GE)
    (hB : S.L.T.par.LinB rowB) (u : J₂ → GE) :
    (p.rowForm S0 kept).value gl W = 0 ↔
      Blocks.Form.val (Sum.elim m u)
        (Cb.Pv.Lay.End.upForm (J₂ := J₂)
          (Cb.Sub.formU S.L.T.par rowB (stgT num k t hβ st tg).out)) = 0 := by
  obtain ⟨e, s⟩ := stgT_said num k t hβ st tg hn r ht f
  rw [e] at D3 D4 ⊢
  exact row_upFormU gl s hF Ex y W S0 kept m D1 D2 D3 D4 rowB hB u

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.stgT_said
#print axioms OnBytes.Road.K4.stgT_row
#print axioms OnBytes.Road.K4.stgT_rowUp
