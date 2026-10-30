-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/PlainFits.lean: the port's weights of a plain sumcheck fit the library's
variables at the programs' choice of the coefficients that are left out.

A sumcheck of Cb/Pv/Att/Plain.lean has nv plain cube variables with a degree each and the further
variable. The port sums a round's polynomial by a weight (OnBytes/Iop/Psc.lean): Weight.plain (d +
1) in a round of degree d, Weight.atZero (DY + 1) in the round of the further variable. That a
weight fits a variable (`Fit1`, OnBytes/Tie/Pv/Psc/PscRead.lean) says: the port's completion of a
round's message, read in the field, is the library's. `Fits` (OnBytes/Tie/Pv/Psc/PscTie.lean) says
it of a list.

Main names:
  `plainWs degs DY`: the port's weights.
  `fit_plain_at`: Weight.plain (n + 1) fits the plain cube variable of degree n, for 1 ≤ n, the
    linear coefficient left out.
  `fits_cube`, `fits_snoc`: `Fits` along the library's list of cube variables, and with one more
    variable at the end.
  `plain_fits`: `Fits` at the parameters of a plain sumcheck and `PlainSc.fix`.
  `sc3_fitsW`, `scd_fitsW`: the two kinds of attention: nv times Weight.plain 4, then Weight.atZero
    3; Weight.plain (d + 1) for each d of the list of degrees, then Weight.atZero (lt + 2).

Limits: on the weights alone. Nothing on a run of the port's routines.
-/
import OnBytes.Tie.Pv.Psc.PscTie
import Cb.Pv.Att.Sc3
import Cb.Pv.Att.ScdProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- The port's weights of a plain sumcheck. -/
def plainWs (degs : List Nat) (DY : Nat) : List OnBytes.Psc.Weight :=
  degs.map (fun d => OnBytes.Psc.Weight.plain (d + 1)) ++ [OnBytes.Psc.Weight.atZero (DY + 1)]

theorem fit_plain_at (n : ℕ) (h : 1 ≤ n) :
    Fit1 ρ (OnBytes.Psc.Weight.plain (n + 1)) ((pfCube K n).var (pdPlain K n))
      ((1 : Fin (n + 1)), (1 : K)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact fit_plain ρ m

theorem fits_cube : ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, 1 ≤ n i) →
    Fits ρ ((List.ofFn n).map fun d => OnBytes.Psc.Weight.plain (d + 1)) (ldPartFmt K k n)
      (ldPartDat K k n fun _ => none) (fixPlain k n)
  | 0, _, _ => by
    rw [List.ofFn_zero]
    trivial
  | k + 1, n, h => by
    rw [List.ofFn_succ, List.map_cons]
    exact ⟨fit_plain_at ρ (n 0) (h 0), fits_cube k (fun i => n i.succ) fun i => h i.succ⟩

omit [Fintype K] in
theorem fits_snoc : ∀ (ws : List OnBytes.Psc.Weight) (l : List (PFmt K)) (d : PDats l)
    (G : HFixs (pVars l d)) (w : OnBytes.Psc.Weight) (f : PFmt K) (e : PDat K f)
    (p : Fin (f.n + 1) × K), Fits ρ ws l d G → Fit1 ρ w (f.var e) p →
    Fits ρ (ws ++ [w]) (l ++ [f]) (PDats.snoc l d f e) (fixSnoc l d f e G p)
  | [], [], _, _, _, _, _, _, _, h => ⟨h, trivial⟩
  | _ :: ws, _ :: l, d, G, w, f, e, p, hF, h => ⟨hF.1, fits_snoc ws l d.2 G.2 w f e p hF.2 h⟩
  | [], _ :: _, _, _, _, _, _, _, hF, _ => hF.elim
  | _ :: _, [], _, _, _, _, _, _, hF, _ => hF.elim

theorem plain_fits (T : PlainSc K) (h : ∀ i, 1 ≤ T.deg i) (st : T.St) :
    Fits ρ (plainWs (List.ofFn T.deg) T.DY) T.our.par.fmt (T.our.par.dat st) (T.fix st) :=
  fits_snoc ρ _ _ _ _ _ _ _ _ (fits_cube ρ T.nv T.deg h) (fit_y ρ T.DY)

theorem sc3_fitsW (T : Sc3 K) (st : T.St) :
    Fits ρ (List.replicate T.nv (OnBytes.Psc.Weight.plain 4) ++ [OnBytes.Psc.Weight.atZero 3])
      T.plain.our.par.fmt (T.plain.our.par.dat st) (T.plain.fix st) := by
  have h := plain_fits ρ T.plain (sc3_ok T).one st
  have e : plainWs (List.ofFn T.plain.deg) T.plain.DY =
      List.replicate T.nv (OnBytes.Psc.Weight.plain 4) ++ [OnBytes.Psc.Weight.atZero 3] := by
    show (List.ofFn fun _ : Fin T.nv => 3).map _ ++ _ = _
    rw [List.ofFn_const, List.map_replicate]
    rfl
  rw [e] at h
  exact h

theorem scd_fitsW {s : ScdSize} (T : Scd K s) (st : T.St) :
    Fits ρ
      ((List.replicate s.lt 2 ++ List.replicate s.lgk (s.lt + 2) ++
          List.replicate s.lt (s.lt + 1)).map (fun d => OnBytes.Psc.Weight.plain (d + 1)) ++
        [OnBytes.Psc.Weight.atZero (s.lt + 2)])
      T.plain.our.par.fmt (T.plain.our.par.dat st) (T.plain.fix st) := by
  have h := plain_fits ρ T.plain (scd_ok T).one st
  have e : List.ofFn T.plain.deg = _ := s.ofFn_deg
  unfold plainWs at h
  rw [e] at h
  exact h

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.plain_fits
#print axioms OnBytes.Tie.Pv.Att.sc3_fitsW
#print axioms OnBytes.Tie.Pv.Att.scd_fitsW
