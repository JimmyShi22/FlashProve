-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/SumTie.lean: for every masked sumcheck of the layers' sub-proof: the typed
block's output on the transcript that is made from what the port has heard, and what its claims say
of the port's record, row and slots.

In the chain of the layers' own rounds every sumcheck is a stage with parameters `SumL`
(Cb/Pv/Lay/Sum.lean): k cube variables, each in the equality form at a point or in the plain form,
one further variable, revealed maps and kept maps. This file does for `SumL`, and for any pick F of
the coefficients that are left out, what OnBytes/Tie/Pv/Att/Tr.lean, RowTie.lean, TiesFull.lean and
EndSlots.lean do for attention's plain sumchecks. That the port's weights fit the variables' data
under the pick (`Fits`, OnBytes/Tie/Pv/Psc/PscTie.lean) is a premise here; it hangs on the engine.

Main names:
  `sumTr`: the rounds behind the first round, made from the lists that were heard, read.
  `sumOut`: the short sumcheck's output on that transcript (`TWhole.shortV` at the pick F).
  `sum_reads`: the port's rounds are read as that transcript, if each round has as many scalars as
    its degree says.
  `sum_st`, `sum_eps`, `sum_vals`, `sum_ini`, `sum_last`: the output's state, eps, end values, point
    and last coordinate are those given, read.
  `sum_fin`: under `Fits`, the output's last value is the reading of the port's running claim behind
    the rounds.
  `sum_block_out`: the chain's verifier at the stage (`rideNR`, Cb/Pv/Att/Ride.lean), with n further
    scalars in the first message, puts out the statement, these scalars and `sumOut`.
  `sum_row`: the port's row form is worth 0 exactly if the typed row claim holds of `sumOut`, under:
    the pick is lawful; the record is as `PscAt` asks; `Fits`; the rounds' lengths; (D1) the
    coefficients of the hiding polynomial are the world's values under the slots from the record's
    first slot on; (D2) the incoming form is worth the target less the start; (D3) the kept maps'
    part at the output's point and values is what the kept form is worth; (D4) the revealed maps'
    part is the reading of the port's summand.
  `sum_end`, `sum_end_world`: the typed claim on end value a holds exactly if the map a at the
    output's point is the end value less its mask entry times the reading of beta; so exactly if it
    is what the slot sEnd + num a is worth in the world of a state in which the end values lie under
    the slots from sEnd on with the factor beta.

Limits: `Fits`, (D1) to (D4), that the reading of beta is not 0, and that the entries' places are
the slots' mask entries are premises. No routine of the port occurs here.
-/
import OnBytes.Tie.Pv.Att.EndSlots
import OnBytes.Tie.Pv.Att.RowTie
import Cb.Pv.Lay.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay.Eng
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open Cb.Pv.Lay OnBytes.Tie.Pv.Att

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- The rounds of a sumcheck behind its first round. -/
noncomputable def sumTr (L : SumL K) (rs : List (List E × E)) (sentY : List E) (beta : E)
    (hβ : ρ.val beta ≠ 0) (vals : L.S.A → K) :
    Tr (sRounds L.T.par.fmt ++ [pRoundV K L.T.par.A]) :=
  cubeTr ρ (pDummy K L.M.DY) [pRoundV K L.S.A] L.S.k L.M.n rs
    (lastTr ρ L.M.DY L.S.A sentY beta hβ vals)

theorem sum_reads (L : SumL K) (rs : List (List E × E)) (sentY : List E) (beta : E)
    (hβ : ρ.val beta ≠ 0) (vals : L.S.A → K) (hl : rs.map (·.1.length) = List.ofFn L.M.n)
    (hY : sentY.length = L.M.DY) :
    ReadsAs ρ (rs ++ [(sentY, beta)]) L.T.par.fmt [pRoundV K L.T.par.A]
      (sumTr ρ L rs sentY beta hβ vals) :=
  cubeTr_reads ρ _ _ (sentY, beta) _ ⟨hY, rfl, rfl, trivial⟩ L.S.k L.M.n rs hl

section Out
variable (L : SumL K) (F : ∀ st, HFixs (L.T.par.vars st)) (st : L.St) (target mu eps : E)
  (rs : List (List E × E)) (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0) (vals : L.S.A → K)

/-- The short sumcheck's output on the transcript that is made from what the port has heard. -/
noncomputable def sumOut : L.T.par.Out :=
  shortV L.T.par F (ρ.val target, st) (((), ρ.val mu), ρ.val eps, sumTr ρ L rs sentY beta hβ vals)

theorem sum_st : (sumOut ρ L F st target mu eps rs sentY beta hβ vals).st = st := rfl

theorem sum_eps : (sumOut ρ L F st target mu eps rs sentY beta hβ vals).eps = ρ.val eps := rfl

theorem sum_vals : (sumOut ρ L F st target mu eps rs sentY beta hβ vals).vals = vals :=
  congrArg (fun τ : Tr [pRoundV K L.S.A] => τ.1.2)
    (cubeTr_tail ρ (pDummy K L.M.DY) [pRoundV K L.S.A]
      (lastTr ρ L.M.DY L.S.A sentY beta hβ vals) L.S.k L.M.n (L.T.par.dat st) (F st) _ rs)

theorem sum_ini (i : Fin L.S.k) :
    L.Q.outPt L.M (sumOut ρ L F st target mu eps rs sentY beta hβ vals) i =
      ρ.val (rs.getD i.1 ([], zeroE)).2 :=
  cubeTr_ini ρ (pDummy K L.M.DY) [pRoundV K L.S.A] (lastTr ρ L.M.DY L.S.A sentY beta hβ vals)
    L.S.k L.M.n (L.T.par.dat st) (F st) _ rs i

theorem sum_last :
    L.Q.outB L.M (sumOut ρ L F st target mu eps rs sentY beta hβ vals) = ρ.val beta :=
  cubeTr_last ρ (pDummy K L.M.DY) [pRoundV K L.S.A] (lastTr ρ L.M.DY L.S.A sentY beta hβ vals)
    L.S.k L.M.n (L.T.par.dat st) (F st) _ rs

theorem sum_fin (ws : List OnBytes.Psc.Weight)
    (hfit : Fits ρ ws L.T.par.fmt (L.T.par.dat st) (F st))
    (hl : rs.map (·.1.length) = List.ofFn L.M.n) (hY : sentY.length = L.M.DY) :
    (sumOut ρ L F st target mu eps rs sentY beta hβ vals).fin =
      ρ.val (OnBytes.Psc.claimAfter ws (rs ++ [(sentY, beta)]) (addE mu (mulE eps target))) := by
  rw [claimAfter_hFin ρ _ _ L.T.par.fmt (L.T.par.dat st) (F st) [pRoundV K L.T.par.A]
    (sumTr ρ L rs sentY beta hβ vals) _ hfit (sum_reads ρ L rs sentY beta hβ vals hl hY),
    vFinT_fin, ρ.add, ρ.mul]
  rfl

theorem sum_block_out (hF : ∀ st, HFixs.OK _ (F st)) (n : ℕ) {X : Type}
    (cl : X → (Fin n → K) → K × L.St) (Ex : ExtSpec) (x : X) (y : Ex.Str) (r : Fin n → K)
    (hcl : cl x r = (ρ.val target, st)) :
    (rideNR L.T.par n F cl Ex).out x y
        (((), (r, ρ.val mu)), ρ.val eps, sumTr ρ L rs sentY beta hβ vals) =
      some ((x, r), sumOut ρ L F st target mu eps rs sentY beta hβ vals) := by
  show ((shortR L.T.par F Ex).out (cl x r) y _).map _ = _
  rw [short_out L.T.par F Ex hF, hcl]
  rfl

theorem sum_row (hF : ∀ st, HFixs.OK _ (F st)) (Ex : ExtSpec) (y : Ex.Str) (W : World K)
    (p : OnBytes.Model.Psc) (ws : List OnBytes.Psc.Weight) (S0 : E) (kept : Aff) (m : L.J → K)
    (hp : PscAt p ws (rs ++ [(sentY, beta)]) mu)
    (hfit : Fits ρ ws L.T.par.fmt (L.T.par.dat st) (F st))
    (hl : rs.map (·.1.length) = List.ofFn L.M.n) (hY : sentY.length = L.M.DY)
    (D1 : L.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.T.par.vars st) p.first)
    (D2 : L.T.par.inc st m = ρ.val p.target - p.start.value ρ W)
    (D3 : ∑ b, L.Q.polB st
          (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals))
          (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).vals b *
        L.Q.Fb st m b
          (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals)) =
      kept.value ρ W)
    (D4 : L.S.pol st (L.Q.outPt L.M (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals))
        (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).vals = ρ.val S0) :
    (p.rowForm S0 kept).value ρ W = 0 ↔
      L.T.par.UHolds (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals) m := by
  have hread := sum_reads ρ L rs sentY beta hβ vals hl hY
  have e : outS L.T.par (ρ.val p.target, st) (F st) Ex
      (((), ρ.val mu), ρ.val p.eps, sumTr ρ L rs sentY beta hβ vals) =
      sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals :=
    outS_shortV L.T.par F hF Ex y (ρ.val p.target, st) _
  have hne : L.T.par.fmt ≠ [] := by
    show ldPartFmt K L.S.k L.M.n ++ [pDummy K L.M.DY] ≠ []
    simp
  have hi := ldPartVars_ini K L.S.k L.M.n (ldPartDat K L.S.k L.M.n (L.S.w st)) (pDummy K L.M.DY)
    (pDummyD K L.M.DY)
    (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).pt
  have key := row_iff_UHolds ρ L.T.par Ex W p _ _ mu S0 kept st (F st)
    (sumTr ρ L rs sentY beta hβ vals) m hp hfit hread
    (zip_ne ρ _ _ _ _ _ _ _ hne hfit hread) D1 D2
    (by
      rw [e]
      exact (congrArg (fun q => ∑ b, L.Q.polB st q
        (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).vals b * L.Q.Fb st m b q)
        hi).trans D3)
    (by
      rw [e]
      exact (congrArg (fun q => L.S.pol st q
        (sumOut ρ L F st p.target mu p.eps rs sentY beta hβ vals).vals) hi).trans D4)
  rw [e] at key
  exact key

theorem sum_end (m : L.J → K) (a : L.S.A) :
    L.T.par.EHolds (sumOut ρ L F st target mu eps rs sentY beta hβ vals) m a ↔
      L.S.F st m a (L.Q.outPt L.M (sumOut ρ L F st target mu eps rs sentY beta hβ vals)) =
        vals a - m (L.M.cAt a) * ρ.val beta := by
  rw [L.Q.val_iff L.M (sumOut ρ L F st target mu eps rs sentY beta hβ vals) m a, sum_last,
    sum_vals]
  exact eq_sub_iff_add_eq.symm

theorem sum_end_world (v : List E) (num : L.S.A → ℕ) (hnum : ∀ a, num a < v.length)
    (F0 F2 : Fork) (sEnd : ℕ) (hFl : Filled F0 F2 sEnd v beta) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) (m : L.J → K) (hm : ∀ a, m (L.M.cAt a) = mask (sEnd + num a))
    (a : L.S.A) :
    L.T.par.EHolds
        (sumOut ρ L F st target mu eps rs sentY beta hβ fun a => ρ.val (v.getD (num a) zeroE))
        m a ↔
      L.S.F st m a (L.Q.outPt L.M
          (sumOut ρ L F st target mu eps rs sentY beta hβ
            fun a => ρ.val (v.getD (num a) zeroE))) =
        (F2.worldOf ρ mask entry).slot (sEnd + num a) := by
  rw [sum_end, hFl.world ρ mask entry (num a) (hnum a), hm a, mul_comm]

end Out

end OnBytes.Tie.Pv.Lay.Eng

#print axioms OnBytes.Tie.Pv.Lay.Eng.sum_fin
#print axioms OnBytes.Tie.Pv.Lay.Eng.sum_block_out
#print axioms OnBytes.Tie.Pv.Lay.Eng.sum_row
#print axioms OnBytes.Tie.Pv.Lay.Eng.sum_end_world
