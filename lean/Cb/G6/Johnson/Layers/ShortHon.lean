-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Johnson/Layers/ShortHon.lean: the short sumcheck (Cb/G6/Johnson/Layers/Short.lean) loses no
accepted run.

Definitions, statements and proofs.

Main names:
  `dShort`, `dropS`: a long transcript without the coefficients that are left out.
  `cShort_dShort`, `short_onto`: under `HFixs.OK`, every long transcript that the library's verifier
    accepts is the completion of its own short form.
  `short_honest`: if the sum claim is true of m, then for all draws there is a short transcript with
    these draws whose completion the library's verifier accepts with an output that is true of m:
    the short form of the run of the library's honest prover. So the goal of `short_doomed`
    ("whatever is put out is false of m") is not met by every run: it fails on the honest run of a
    true claim.

Premises: `HFixs.OK`; for `short_honest` also `Y.VarsOK`, `Y.DegOK` (the library's completeness,
`psc_acc_base`).
Limits: nothing is said on the programs' prover.

-/
import Iop.ShapeKit
import Cb.G6.Johnson.Layers.Short

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.L5.Layers
open Iop Prob Cb

variable {E : Type} [Field E]

/-- Long rounds without the coefficient that is left out. -/
def dShort : (l : List (PFmt E)) → (d : PDats l) → HFixs (pVars l d) → (t : Shape) →
    Tr (pRounds l ++ t) → Tr (sRounds l ++ t)
  | [], _, _, _, τ => τ
  | _ :: l, d, F, t, (m, c, τ) =>
    (((), fun i => m.2 (F.1.1.succAbove i)), c, dShort l d.2 F.2 t τ)

/-- A consistent long transcript is the completion of its short form. -/
theorem cShort_dShort : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)),
    HFixs.OK (pVars l d) F → ∀ (σ : E) (t : Shape) (τ : Tr (pRounds l ++ t)),
    HCons (pVars l d) σ (pQ l d (Tr.fst τ).plains) (pH l d (pG l (Tr.fst τ).rho)) →
    (cShort l d F σ t).tr (dShort l d F t τ) = τ
  | [], _, _, _, _, t, τ, _ => Carry.tr_refl t τ
  | f :: l, d, F, hF, σ, t, (m, c, τ), hc => by
    have e1 : hFill (f.var d.1) F.1 σ (fun i => m.2 (F.1.1.succAbove i)) = m.2 := by
      have e := fill_drop (f.var d.1) F.1 hF.1 m.2
      have e2 : (f.var d.1).phi m.2 = σ := hc.1
      rw [e2] at e
      exact e
    show (((), hFill (f.var d.1) F.1 σ (fun i => m.2 (F.1.1.succAbove i))), c,
      (cShort l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ fun i => m.2 (F.1.1.succAbove i)) (f.val c))
        t).tr (dShort l d.2 F.2 t τ)) = (m, c, τ)
    rw [e1, cShort_dShort l d.2 F.2 hF.2 (hev m.2 (f.val c)) t τ hc.2]

variable [Fintype E] (Y : PscPar E)

/-- The short form of a long transcript. -/
def dropS (x : E × Y.St) (F : HFixs (Y.vars x.2)) (Ex : ExtSpec) (τ : Tr (Y.psc Ex).shape) :
    Tr (shapeS Y) :=
  (τ.1, τ.2.1, dShort Y.fmt (Y.dat x.2) F [pRoundV E Y.A] τ.2.2)

/-- A long transcript that the library's verifier accepts is the completion of its short form. -/
theorem short_onto (Ex : ExtSpec) (x : E × Y.St) (F : HFixs (Y.vars x.2))
    (hF : HFixs.OK (Y.vars x.2) F) (y : Ex.Str) (τ : Tr (Y.psc Ex).shape) (o : Y.Out)
    (h : (Y.psc Ex).out x y τ = some o) : (carryS Y x F Ex).tr (dropS Y x F Ex τ) = τ := by
  have hc : HCons (Y.vars x.2)
      (Y.mu (Tr.fst (s := Y.shapeC) τ) + Y.eps (Tr.fst (s := Y.shapeC) τ) * x.1)
      (Y.qs x.2 (Tr.fst (s := Y.shapeC) τ)) (Y.hp x.2 (Y.pt (Tr.fst (s := Y.shapeC) τ))) := by
    by_contra hn
    have e : Y.outC x (Tr.fst (s := Y.shapeC) τ) = none := by
      unfold PscPar.outC
      rw [if_neg hn]
    have h' : ((Y.outC x (Tr.fst (s := Y.shapeC) τ)).bind fun x₂ =>
        (Y.ends Ex).out x₂ y (Tr.snd (s := Y.shapeC) τ)) = some o := h
    rw [e] at h'
    simp at h'
  obtain ⟨m, ε, τ'⟩ := τ
  show (m, ε, (cShort Y.fmt (Y.dat x.2) F (m.2 + ε * x.1) [pRoundV E Y.A]).tr
    (dShort Y.fmt (Y.dat x.2) F [pRoundV E Y.A] τ')) = (m, ε, τ')
  rw [cShort_dShort Y.fmt (Y.dat x.2) F hF (m.2 + ε * x.1) [pRoundV E Y.A] τ' hc]
  rfl

/-- A true claim has, for all draws, a short run that ends in a true output. -/
theorem short_honest (Ex : ExtSpec) (hV : Y.VarsOK) (hD : Y.DegOK) (x : E × Y.St)
    (F : HFixs (Y.vars x.2)) (hF : HFixs.OK (Y.vars x.2) F) (y : Ex.Str) (m : Y.J → E)
    (h : Y.SumHolds x m) (ρ : Rho (Y.psc Ex).shape) :
    ∃ (t : Tr (shapeS Y)) (o : Y.Out), ((carryS Y x F Ex).tr t).rho = ρ ∧
      (Y.psc Ex).out x y ((carryS Y x F Ex).tr t) = some o ∧ Y.OutHolds o m := by
  have hA := psc_acc_base E Y Ex Unit Unit
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ (fun _ => m) hV hD
  have hρ : ρ ∉ (Y.hon Ex fun _ : Unit => m).withheld () x := by
    rintro ((hb | hb) | (hb | ⟨_, _, hb⟩)) <;> exact hb
  obtain ⟨h1, h2⟩ := hA x y () ((), ()) ρ ⟨trivial, h⟩ hρ
  refine ⟨dropS Y x F Ex (((Y.hon Ex fun _ : Unit => m).strat () x ((), ())).run ρ).1, _, ?_, ?_,
    h2.2⟩
  · rw [short_onto Y Ex x F hF y _ _ h1]
    exact Strat.rho_run _ ρ
  · rw [short_onto Y Ex x F hF y _ _ h1]
    exact h1

end Johnson.L5.Layers
