-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/CloseLaid.lean: at the short sumcheck `SK₀` the verifiers of the join point, the
closing, the zero point and the test of the bits reject nothing; what they put out is written out;
the points in the rows are made of the transcript's challenges.

It imports CloseShort.lean, ClosePoint.lean and Cb/Pv/KeyLookup/ShortPt.lean (`chS`, `ppGet_vFinT`:
the short sumcheck with the round of end values); no file of the port.

  `Clo.chC l τ j`, `Clo.ppGet_vFin`   the value of the challenge drawn in round j, for the short
                  sumcheck without end values.
  `en_eq0`, `bt_eq0`   at both sumchecks every variable's weights sum to 1 (`TWhole.Eq0`,
                  Cb/G6/Pick.lean).
  `join_out`, `zero_out`   out = some (joinNx x ϱ), some (zeroNx x ζ), with ϱ, ζ the point drawn.
  `close_out`     (A.closeK P SK₀).R.out x y τ = some (A.closeOut P (A.zzOf P x τ)) for all x, y, τ;
                  `zzOf` is a total function of x and τ.
  `close_st`, `close_eps`, `close_gam`, `close_pt`   of that value: its state is x; its ε is the
                  draw of τ's first round; `gamE` at i is the challenge of round i after it (i from
                  0); `ptE` at the variable t is the challenge of round k − 1 − t, which bound t.
  `bits_out`, `bits_st`, `bits_gam`, `bits_pt`, `bits_beta`   the same for the test of the bits,
                  with `oOf` for `zzOf`; β is the challenge of the further variable's round.
  `join_total_short`, `close_total_short`, `zero_total_short`, `bits_total_short`   for all x, y, τ
                  the verifier puts out some state.
No condition is asked anywhere in this file.

-/
import Cb.Pv.KeyLookup.CloseShort
import Cb.Pv.KeyLookup.ClosePoint
import Cb.Pv.KeyLookup.ShortPt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Johnson.L5.Layers

namespace Clo
variable {E : Type} [Field E]

/-- the value of the challenge drawn in round j of a transcript of the short rounds of l -/
def chC : (l : List (PFmt E)) → Tr (sRounds l) → ℕ → E
  | [], _, _ => 0
  | f :: _, (_, c, _), 0 => f.val c
  | _ :: l, (_, _, τ), j + 1 => chC l τ j

theorem ppGet_vFin : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E)
    (τ : Tr (sRounds l)) (j : ℕ), ppGet l (TWhole.vFin l d F σ τ).2 j = chC l τ j
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, _, _, (_, _, _), 0 => rfl
  | f :: l, d, F, σ, (m, c, τ), j + 1 =>
    ppGet_vFin l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) τ j

end Clo

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A) (Ex : ExtSpec)

theorem en_eq0 : TWhole.Eq0 (A.En P).par := fun st v hv => by
  rw [show (A.En P).par.vars st = _ from A.en_vars_at P st] at hv
  simp only [List.mem_ofFn] at hv
  obtain ⟨j, rfl⟩ := hv
  exact TWhole.mon0_eq _ _

theorem bt_eq0 : TWhole.Eq0 (A.BT P).par :=
  TWhole.our_eq0 (A.BT P) fun st v hv => by
    rw [show (A.BT P).vars st = _ from ZeroCubeP.vars_at E (A.Bt P).zc st] at hv
    simp only [List.mem_ofFn] at hv
    obtain ⟨j, rfl⟩ := hv
    exact TWhole.mon0_eq 2 _

theorem join_out (x : A.XS) (y : Ex.Str) (τ : Tr (A.joinK Ex).R.shape) :
    (A.joinK Ex).R.out x y τ = some (A.joinNx x (IOR.drawn τ)) := rfl

theorem zero_out (x : A.XS) (y : Ex.Str) (τ : Tr (A.zeroK Ex).R.shape) :
    (A.zeroK Ex).R.out x y τ = some (A.zeroNx x (IOR.drawn τ)) := rfl

/-! ### the closing -/

/-- what the closing's sumcheck ends with, as a total function of the state and the transcript -/
noncomputable def zzOf (x : A.XS) (τ : Tr (TWhole.shapeSC (A.En P).par)) : (A.En P).par.Mid :=
  TWhole.shortVC (A.En P).par (TWhole.F₀ (A.En P).par) (A.closeIn x) τ

theorem close_out (x : A.XS) (y : Ex.Str) (τ : Tr (TWhole.shapeSC (A.En P).par)) :
    (A.closeK P (SK₀ E Ex)).R.out x y τ = some (A.closeOut P (A.zzOf P x τ)) := by
  show (((SK₀ E Ex).core (A.En P).par).R.out (A.closeIn x) ((ExtMap.id Ex).map y) τ).bind
    (fun zz => some (A.closeOut P zz)) = _
  rw [SK₀_outC Ex (A.En P).par (A.en_eq0 P)]
  rfl

theorem close_st (x : A.XS) (τ : Tr (TWhole.shapeSC (A.En P).par)) : (A.zzOf P x τ).st = x := rfl
theorem close_eps (x : A.XS) (τ : Tr (TWhole.shapeSC (A.En P).par)) :
    (A.zzOf P x τ).eps = τ.2.1 := rfl

theorem close_gam (x : A.XS) (τ : Tr (TWhole.shapeSC (A.En P).par)) (i : Fin (A.mu + A.d)) :
    A.gamE P (A.zzOf P x τ) i = Clo.chC (A.En P).par.fmt τ.2.2 i :=
  Clo.ppGet_vFin _ _ _ _ _ _

theorem close_pt (x : A.XS) (τ : Tr (TWhole.shapeSC (A.En P).par)) (t : Fin (A.mu + A.d)) :
    A.ptE P (A.zzOf P x τ) t = Clo.chC (A.En P).par.fmt τ.2.2 t.rev :=
  A.close_gam P x τ t.rev

/-! ### the bits' test -/

noncomputable def oOf (x : A.XS) (τ : Tr (shapeS (A.BT P).par)) : (A.BT P).par.Out :=
  TWhole.shortV (A.BT P).par (TWhole.F₀ (A.BT P).par) (A.bitsIn P x) τ

theorem bits_out (x : A.XS) (y : Ex.Str) (τ : Tr (shapeS (A.BT P).par)) :
    (A.bitsK P (SK₀ E Ex)).R.out x y τ = some (A.bitsOut P (A.oOf P x τ)) := by
  show (((SK₀ E Ex).full (A.BT P).par).R.out (A.bitsIn P x) ((ExtMap.id Ex).map y) τ).bind
    (fun o => some (A.bitsOut P o)) = _
  rw [SK₀_out Ex (A.BT P).par (A.bt_eq0 P)]
  rfl

theorem bits_st (x : A.XS) (τ : Tr (shapeS (A.BT P).par)) : (A.oOf P x τ).st.1 = x := rfl

theorem bits_gam (x : A.XS) (τ : Tr (shapeS (A.BT P).par)) (j : ℕ) :
    A.gamB P (A.oOf P x τ) j = chS (A.BT P).par.fmt [pRoundV E (A.BT P).par.A] τ.2.2 j :=
  ppGet_vFinT _ _ _ _ _ _ j

theorem bits_pt (x : A.XS) (τ : Tr (shapeS (A.BT P).par)) (t : Fin (A.mu + A.d)) :
    A.ptB P (A.oOf P x τ) t = chS (A.BT P).par.fmt [pRoundV E (A.BT P).par.A] τ.2.2 t.rev :=
  A.bits_gam P x τ t.rev

theorem bits_beta (x : A.XS) (τ : Tr (shapeS (A.BT P).par)) :
    A.betaB P (A.oOf P x τ) =
      chS (A.BT P).par.fmt [pRoundV E (A.BT P).par.A] τ.2.2 (A.mu + A.d) :=
  (A.betaB_get P _).trans (A.bits_gam P x τ _)

/-! ### the verifiers put out `some`, at all inputs -/

theorem join_total_short (x : A.XS) (y : Ex.Str) (τ : Tr (A.joinK Ex).R.shape) :
    ∃ x', (A.joinK Ex).R.out x y τ = some x' := ⟨_, A.join_out Ex x y τ⟩

theorem close_total_short (x : A.XS) (y : Ex.Str) (τ : Tr (A.closeK P (SK₀ E Ex)).R.shape) :
    ∃ x', (A.closeK P (SK₀ E Ex)).R.out x y τ = some x' := ⟨_, A.close_out P Ex x y τ⟩

theorem zero_total_short (x : A.XS) (y : Ex.Str) (τ : Tr (A.zeroK Ex).R.shape) :
    ∃ x', (A.zeroK Ex).R.out x y τ = some x' := ⟨_, A.zero_out Ex x y τ⟩

theorem bits_total_short (x : A.XS) (y : Ex.Str) (τ : Tr (A.bitsK P (SK₀ E Ex)).R.shape) :
    ∃ x', (A.bitsK P (SK₀ E Ex)).R.out x y τ = some x' := ⟨_, A.bits_out P Ex x y τ⟩

end Dat
end Lk6

#print axioms Lk6.Dat.join_total_short
#print axioms Lk6.Dat.close_total_short
#print axioms Lk6.Dat.zero_total_short
#print axioms Lk6.Dat.bits_total_short
#print axioms Lk6.Dat.en_eq0
#print axioms Lk6.Dat.bt_eq0
#print axioms Lk6.Dat.close_out
#print axioms Lk6.Dat.close_gam
#print axioms Lk6.Dat.close_pt
#print axioms Lk6.Dat.bits_out
#print axioms Lk6.Dat.bits_gam
#print axioms Lk6.Dat.bits_pt
#print axioms Lk6.Dat.bits_beta
