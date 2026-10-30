-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/RowTie.lean: the port's row of a plain sumcheck is worth 0 exactly if the typed
block's row claim holds of the output on the transcript that is made from what the port has heard.

OnBytes/Tie/Pv/Psc/PscTie.lean proves that equivalence for every sumcheck of the library
(`row_iff_UHolds`), under premises on the port's record, on the weights, on the transcript and on
four equations. This file applies it to the parameters of Cb/Pv/Att/Plain.lean and the transcript of
OnBytes/Tie/Pv/Att/Tr.lean: the premises on the weights and on the transcript are discharged; the
equation on the maps that are not shown is empty.

Main names:
  `outS_shortV`: the output that OnBytes/Tie/Pv/Psc/PscTie.lean writes out is `TWhole.shortV`.
  `zip_ne`: weights that fit and rounds that are read as a transcript of at least one variable are
    not empty.
  `plain_row`: the equivalence at a plain sumcheck, under: every degree is at least 1 and the choice
    of the coefficients that are left out is lawful; the record is as `PscAt` asks; the port's
    rounds are read as the transcript (`ReadsAs`; `plain_reads` of OnBytes/Tie/Pv/Att/Tr.lean gives
    that from the rounds' lengths); (D1) the coefficients of the hiding polynomial are the world's
    values under the slots from the record's first slot on, in the port's order; (D2) the incoming
    form is worth the target less the start; (D4) the typed summand at the output's point and values
    is the reading of the port's summand.

Limits: (D1) and (D2) are premises on the choice of the places of the mask entries and of the
incoming form. The reading of beta is other than 0 by premise. An element of the external data's
type is asked for and occurs in the proof alone.
-/
import OnBytes.Tie.Pv.Att.Tr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

theorem outS_shortV (Y : PscPar K) (F : ∀ st, HFixs (Y.vars st))
    (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (Ex : ExtSpec) (y : Ex.Str) (x : K × Y.St)
    (τ : Tr (shapeS Y)) : outS Y x (F x.2) Ex τ = shortV Y F x τ :=
  Option.some.inj ((out_carry Y Ex x (F x.2) (hF x.2) y τ).symm.trans (short_out Y F Ex hF x y τ))

omit [Fintype K] in
theorem zip_ne : ∀ (ws : List OnBytes.Psc.Weight) (rs : List (List E × E)) (l : List (PFmt K))
    (d : PDats l) (F : HFixs (pVars l d)) (t : Shape) (τ : Tr (sRounds l ++ t)), l ≠ [] →
    Fits ρ ws l d F → ReadsAs ρ rs l t τ → ws.zip (rs.map (·.2)) ≠ []
  | _ :: _, _ :: _, _ :: _, _, _, _, _, _, _, _ => by simp
  | _, _, [], _, _, _, _, h, _, _ => absurd rfl h
  | [], _, _ :: _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, [], _ :: _, _, _, _, _, _, _, h => h.elim

theorem plain_row (T : PlainSc K) (h1 : ∀ i, 1 ≤ T.deg i) (hF : ∀ st, HFixs.OK _ (T.fix st))
    (Ex : ExtSpec) (y : Ex.Str) (W : World K) (p : OnBytes.Model.Psc) (rs : List (List E × E))
    (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0) (vals : T.A → K) (mu S0 : E) (st : T.St)
    (m : T.J → K)
    (hp : PscAt p (plainWs (List.ofFn T.deg) T.DY) (rs ++ [(sentY, beta)]) mu)
    (hread : ReadsAs ρ (rs ++ [(sentY, beta)]) T.our.par.fmt [pRoundV K T.our.par.A]
      (plainTr ρ T rs sentY beta hβ vals))
    (D1 : T.our.par.W st m = OnBytes.Road.Hd.place W.slot (T.our.par.vars st) p.first)
    (D2 : T.our.par.inc st m = ρ.val p.target - p.start.value ρ W)
    (D4 : T.S st
        (ldPartIni T.nv T.deg (pDummy K T.DY)
          (plainOut ρ T st p.target mu p.eps rs sentY beta hβ vals).pt)
        (plainOut ρ T st p.target mu p.eps rs sentY beta hβ vals).vals = ρ.val S0) :
    (p.rowForm S0 {}).value ρ W = 0 ↔
      T.our.par.UHolds (plainOut ρ T st p.target mu p.eps rs sentY beta hβ vals) m := by
  have hfit := plain_fits ρ T h1 st
  have e : outS T.our.par (ρ.val p.target, st) (T.fix st) Ex
      (((), ρ.val mu), ρ.val p.eps, plainTr ρ T rs sentY beta hβ vals) =
      plainOut ρ T st p.target mu p.eps rs sentY beta hβ vals :=
    outS_shortV T.our.par T.fix hF Ex y (ρ.val p.target, st) _
  have hne : T.our.par.fmt ≠ [] := by
    show ldPartFmt K T.nv T.deg ++ [pDummy K T.DY] ≠ []
    simp
  have key := row_iff_UHolds ρ T.our.par Ex W p _ _ mu S0 {} st (T.fix st)
    (plainTr ρ T rs sentY beta hβ vals) m hp hfit hread
    (zip_ne ρ _ _ _ _ _ _ _ hne hfit hread) D1 D2
    (by
      rw [Aff.value_empty]
      exact Finset.sum_eq_zero fun b _ => (show Empty from b).elim)
    (by
      rw [e]
      exact (congrArg (fun q => T.S st q
        (plainOut ρ T st p.target mu p.eps rs sentY beta hβ vals).vals)
        (ldPartVars_ini K T.nv T.deg T.dat (pDummy K T.DY) (pDummyD K T.DY)
          (plainOut ρ T st p.target mu p.eps rs sentY beta hβ vals).pt)).trans D4)
  rw [e] at key
  exact key

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.outS_shortV
#print axioms OnBytes.Tie.Pv.Att.plain_row
