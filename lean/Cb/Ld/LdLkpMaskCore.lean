-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskCore.lean: a sumcheck where no map is revealed (`PscPar.core`, Cb/Ld/LdPsc.lean),
as a link of a chain of masked blocks (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean).
This file is about the sumcheck protocol for a polynomial summand, without the round after the
rounds of the variables (`PscPar.ends`, Cb/Ld/LdPsc.lean), as one step of a chain of reductions.

Definitions, statements (in `Cb.Spec`) and proofs. Glue: the item "masked messages" (`Honest.MM`,
Ior/Masked.lean) for `Y.core` alone (round 0 and the rounds of the variables) is stated in
Cb/Ld/LdPscZk.lean and proved in Cb/Ld/LdPscZkProofs.lean (`psc_core_mm`), under its hypotheses;
here it is put into the `MJ` record of Cb/Ld/LdLkpMaskChain.lean.
The block: `Y.core Ex` (Cb/Ld/LdPsc.lean): round 0 and the rounds of the variables; no further
variable, no last round, no inner mask. Its own masks: the coefficients of the hiding polynomial, at
the places `Y.wAt`.

Main names:
  `Y.nxtC Ex x pl ρ`: what the verifier outputs if it accepts, from the explicit part, the plain
    parts and its own messages: state, coefficient, point, last value.
  `Y.mjC Ex Rd`: the `MJ` record: own masks, claim (the sum claim), closed-form messages and
    simulator are those of `Y.maskDataC`.
  `Spec.mjCore_link`: under `Y.VarsOK`, `Y.DegOK`, `Y.OwnW Rd`: it is a link, started with any claim
    C that gives its sum claim and does not read its own masks, if there is at least one variable.
    Its messages read Rd' (any set for which the conditions `Y.OwnW` hold); the reading of a
    witness: the entries in Rd, all others forgotten.
  `Spec.mjCore_out`: under `Y.VarsOK`, `Y.DegOK`, and if there is at least one variable: at what the
    honest messages fix, the end claim holds of the entries, whether or not the claim held; the
    state is handed on.

Limits: no chain is assembled here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskOur
import Cb.Ld.LdLkpMaskPscProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Prob Hiop

noncomputable section

namespace PscPar
variable {E : Type} [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec)

/-- What the verifier outputs if it accepts. -/
def nxtC (x : E × Y.St) (pl : Plains (Y.core Ex).shape) (ρ : Rho (Y.core Ex).shape) : Y.Mid :=
  ⟨x.2, ρ.1, pG Y.fmt ρ.2,
    hFin (Y.vars x.2) (pl.1 + ρ.1 * x.1) (pQ Y.fmt (Y.dat x.2) pl.2) (Y.hp x.2 (pG Y.fmt ρ.2))⟩

/-- The `MJ` record of the block. -/
def mjC (Rd : Y.J → Prop) : MJ E Y.J (Y.core Ex) where
  Mk  := (Y.maskDataC Ex (Wt := Y.J → E) (fun m => m) Rd).Mk
  finMk := (Y.maskDataC Ex (Wt := Y.J → E) (fun m => m) Rd).finMk
  neMk := (Y.maskDataC Ex (Wt := Y.J → E) (fun m => m) Rd).neMk
  put := (Y.maskDataC Ex (Wt := Y.J → E) (fun m => m) Rd).put
  Cl  := (Y.maskDataC Ex (Wt := Y.J → E) (fun m => m) Rd).Cl
  msg := (Y.maskDataC Ex (Wt := Y.J → E) (fun m => m) Rd).msg
  nxt := Y.nxtC Ex
  sim := (Y.maskDataC Ex (Wt := Y.J → E) (fun m => m) Rd).sim

end PscPar

namespace Spec
variable (E : Type) [Field E] [Fintype E]

/-- States: under the hypotheses below, the block is a link. -/
def mjCore_link : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (Rd Rd' : Y.J → Prop), Y.VarsOK →
    Y.DegOK → Y.OwnW Rd → Y.OwnW Rd' → Y.fmt ≠ [] →
    ∀ C : E × Y.St → (Y.J → E) → Prop, (∀ x k, C x k → Y.SumHolds x k) →
      MjStab C (fun j => ∃ i, j = Y.wAt i) →
      (Y.mjC Ex Rd).Link (Y.honC Ex msg) (fun w => mjCut Rd (msg w)) (fun w => mjCut Rd (msg w)) Rd'
        (fun j => ∃ i, j = Y.wAt i) C

/-- States: under the hypotheses below, at what the honest messages fix, the end claim holds. -/
def mjCore_out : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Rd : Y.J → Prop), Y.VarsOK → Y.DegOK → Y.fmt ≠ [] →
    ∀ (k : Y.J → E) (x : E × Y.St) (ρ : Rho (Y.core Ex).shape),
      Y.MidHolds ((Y.mjC Ex Rd).nxt x ((Y.mjC Ex Rd).msg k x ρ) ρ) k ∧
      ((Y.mjC Ex Rd).nxt x ((Y.mjC Ex Rd).msg k x ρ) ρ).st = x.2

end Spec
end

section
variable (E : Type) [Field E] [Fintype E]

theorem PscPar.nxtC_sent (Y : PscPar E) (Ex : ExtSpec) (hV : Y.VarsOK) (hD : Y.DegOK)
    (hne : Y.fmt ≠ []) (x : E × Y.St) (m : Y.J → E) (ρ : Rho (Y.core Ex).shape) :
    Y.nxtC Ex x
        (Y.packC Ex x.2 (hMu (Y.vars x.2) (Y.W x.2 m), Y.honQ x.2 m ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2))))
        ρ =
      Y.honMid x.2 m ρ.1 (pG Y.fmt ρ.2) := by
  have h := (hRounds_cons _ _ _ _ (Y.whole_rounds hV hD x.2 m ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2)))).2
  show (⟨x.2, ρ.1, pG Y.fmt ρ.2,
      hFin (Y.vars x.2) _
        (pQ Y.fmt (Y.dat x.2) (pPl Y.fmt (Y.dat x.2) (Y.honQ x.2 m ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2)))))
        (Y.hp x.2 (pG Y.fmt ρ.2))⟩ : Y.Mid) = _
  rw [pQ_pPl, hFin_ne Y.fmt (Y.dat x.2) _ (hSumAll (Y.vars x.2) (Y.whole x.2 m ρ.1)) _ _ hne, h]
  rfl

omit [Fintype E] in
/-- What the block reads of the entries, under the conditions `hO`. -/
theorem PscPar.core_congr {Y : PscPar E} {Rd : Y.J → Prop} (hO : Y.OwnW Rd) (st : Y.St)
    {k k' : Y.J → E} (h : ∀ j, Rd j → k j = k' j) :
    Y.W st k = Y.W st k' ∧ Y.inc st k = Y.inc st k' ∧ Y.sum st k = Y.sum st k' :=
  ⟨funext fun i => h _ (hO.own _),
    PscPar.inc_congr fun j hj => h j (by by_contra hn; exact hj (hO.rdS st j hn)),
    PscPar.sum_congr (hO.rdG st _ _ h) (hO.rdGb st _ _ h)⟩

theorem mjCore_link : Spec.mjCore_link E := by
  intro Y Ex Wt msg Rd Rd' hV hD hO hO' hne C hC hs
  have hw : (Y.mjC Ex Rd).Writes fun j => ∃ i, j = Y.wAt i := fun M k j hj =>
    Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact hj ⟨i, rfl⟩)
  have hcut : ∀ w : Wt, ∀ j, Rd j → mjCut Rd (msg w) j = msg w j := fun w j hj =>
    mjCut_of (msg w) hj
  have hfit : (Y.mjC Ex Rd).Fits (Y.honC Ex msg) (fun w => mjCut Rd (msg w)) fun w =>
      mjCut Rd (msg w) := by
    refine ⟨psc_core_mm E Y Ex Wt msg Rd hV hD hO, fun w x c ρ => ?_, fun w x c ρ => ?_⟩
    · rw [show ((Y.honC Ex msg).strat w x c).run ρ = ((Y.honC Ex msg).strat w x ()).run ρ from rfl,
        (psc_run E Y Ex Wt msg w x ρ).2.2.2]
    · rw [show ((Y.honC Ex msg).strat w x c).run ρ = ((Y.honC Ex msg).strat w x ()).run ρ from rfl,
        (psc_run E Y Ex Wt msg w x ρ).2.2.2]
      obtain ⟨c1, c2, c3⟩ := PscPar.core_congr E hO x.2 (hcut w)
      refine Eq.trans ?_ (Y.nxtC_sent E Ex hV hD hne x (mjCut Rd (msg w)) ρ).symm
      show Y.honMid x.2 (msg w) ρ.1 (pG Y.fmt ρ.2) =
        Y.honMid x.2 (mjCut Rd (msg w)) ρ.1 (pG Y.fmt ρ.2)
      unfold PscPar.honMid
      rw [PscPar.whole_congr c1 c2 c3]
  refine ⟨mj_narrow E Y.J _ _ _ _ _ _ _ _ (Y.mjC Ex Rd) _ _ C hfit hC fun x k M hk =>
      hs x k _ (fun j hj => (hw M k j hj).symm) hk,
    fun k k' x ρ h => ?_,
    hw⟩
  obtain ⟨c1, c2, c3⟩ := PscPar.core_congr E hO' x.2 h
  show Y.packC Ex x.2 (hMu (Y.vars x.2) (Y.W x.2 k), Y.honQ x.2 k ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2))) =
    Y.packC Ex x.2 (hMu (Y.vars x.2) (Y.W x.2 k'), Y.honQ x.2 k' ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2)))
  rw [c1, PscPar.honQ_congr c1 c2 c3]

theorem mjCore_out : Spec.mjCore_out E := by
  intro Y Ex Rd hV hD hne k x ρ
  have e : (Y.mjC Ex Rd).nxt x ((Y.mjC Ex Rd).msg k x ρ) ρ = Y.honMid x.2 k ρ.1 (pG Y.fmt ρ.2) :=
    Y.nxtC_sent E Ex hV hD hne x k ρ
  rw [e]
  exact ⟨rfl, rfl⟩

end
end Cb
