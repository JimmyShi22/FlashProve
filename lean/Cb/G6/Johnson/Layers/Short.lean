-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Johnson/Layers/Short.lean: for every sumcheck block of the library (`PscPar`,
Cb/Ld/LdPsc.lean), the same sumcheck with short messages: in each variable's round the prover sends
n, not n + 1, coefficients, and the one that is left out is set by the round's equation.

Definitions, statements and proofs.

Main names:
  `sRound`, `sRounds`, `shapeS Y`: the rounds: round 0 (a scalar, then the draw ε), a short round
    for each variable with the library's own draws, the round of values.
  `cShort`, `carryS`: the carrying (Cb/G6/Johnson/Layers/Carry.lean) of short messages to long ones,
    by the library's completion `hFill` (Cb/Ld/LdHideShort.lean). Each round knows the running
    claim, that is, what went before.
  `short_doomed`: for each fixed tuple of entries m: if the sum claim is false of m, the prover of
    the short sumcheck is lost (`Doomed`, Iop/Rbr.lean), with the library's numbers, towards:
    whatever the library's verifier puts out on the completed transcript is false of m.
  `short_accepts`: if each left-out power has the inverse of its "sum" (`HFixs.OK`), the library's
    verifier rejects no completed transcript: no check is left. So the goal of `short_doomed` is not
    empty.

Premises: `Y.VarsOK`, `Y.DegOK`, `Y.ValInj` (the library's, for `psc_sound_at`); `HFixs.OK` for
`short_accepts` alone.
Limits: the file does not say which power the programs leave out, nor that the programs' routine
computes this output, nor anything on scalars that ride in a round's message beside the sumcheck's
own. Nothing on zero knowledge.

-/
import Cb.Ld.LdPscProofsIor
import Cb.Ld.LdHideShort
import Cb.G6.Johnson.Layers.Step

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.L5.Layers
open Iop Prob Cb

variable {E : Type} [Field E]

/-- A short round: n coefficients in the clear, the library's draw. -/
@[reducible] def sRound (f : PFmt E) : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim,
    Plain := Fin f.n → E, Chal := f.Ch, dOrc := (), dPlain := 0 }
/-- One short round for each variable. -/
abbrev sRounds (l : List (PFmt E)) : Shape := l.map sRound

/-- Short rounds carried to long ones, from the running claim σ on. The rounds of t behind them are
left as they are. -/
def cShort : (l : List (PFmt E)) → (d : PDats l) → HFixs (pVars l d) → E → (t : Shape) →
    Carry (sRounds l ++ t) (pRounds l ++ t)
  | [], _, _, _, t => Carry.refl t
  | f :: l, d, F, σ, t =>
    (fun m => ((), hFill (f.var d.1) F.1 σ m.2), id,
      fun m c => cShort l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t)

theorem cShort_inj : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E)
    (t : Shape), (cShort l d F σ t).Inj
  | [], _, _, _, t => Carry.inj_refl t
  | _ :: l, d, F, _, t => ⟨Function.injective_id, fun _ _ => cShort_inj l d.2 F.2 _ t⟩

/-- What is completed is consistent. -/
theorem cShort_cons : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)),
    HFixs.OK (pVars l d) F → ∀ (σ : E) (t : Shape) (τ : Tr (sRounds l ++ t)),
    HCons (pVars l d) σ (pQ l d (Tr.fst ((cShort l d F σ t).tr τ)).plains)
      (pH l d (pG l (Tr.fst ((cShort l d F σ t).tr τ)).rho))
  | [], _, _, _, _, _, _ => trivial
  | f :: l, d, F, hF, σ, t, (m, c, τ) =>
    ⟨phi_fill (f.var d.1) F.1 hF.1 σ m.2,
      cShort_cons l d.2 F.2 hF.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ⟩

variable [Fintype E] (Y : PscPar E)

/-- The rounds of the short sumcheck. -/
abbrev shapeS : Shape := pRound0 E :: (sRounds Y.fmt ++ [pRoundV E Y.A])

/-- The carrying, at the claim x. -/
def carryS (x : E × Y.St) (F : HFixs (Y.vars x.2)) (Ex : ExtSpec) :
    Carry (shapeS Y) (Y.psc Ex).shape :=
  (id, id, fun m ε => cShort Y.fmt (Y.dat x.2) F (m.2 + ε * x.1) [pRoundV E Y.A])

theorem carryS_inj (x : E × Y.St) (F : HFixs (Y.vars x.2)) (Ex : ExtSpec) :
    (carryS Y x F Ex).Inj :=
  ⟨Function.injective_id, fun _ _ => cShort_inj _ _ _ _ _⟩

/-- For each fixed tuple of entries: a false sum claim is lost in the short sumcheck too. -/
theorem short_doomed (Ex : ExtSpec) (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj)
    (x : E × Y.St) (F : HFixs (Y.vars x.2)) (y : Ex.Str) (m : Y.J → E) (h : ¬ Y.SumHolds x m) :
    Doomed (shapeS Y) (errTo (shapeS Y) (Y.psc Ex).shape (Y.err Ex)) fun τ =>
      ∀ o, (Y.psc Ex).out x y ((carryS Y x F Ex).tr τ) = some o → ¬ Y.OutHolds o m :=
  Doomed.carry (carryS Y x F Ex) (Y.err Ex) _ _ (carryS_inj Y x F Ex) (fun _ hτ => hτ)
    (psc_sound_at E Y Ex hV hD hI x y m h)

/-- No check is left. -/
theorem short_accepts (Ex : ExtSpec) (x : E × Y.St) (F : HFixs (Y.vars x.2))
    (hF : HFixs.OK (Y.vars x.2) F) (y : Ex.Str) (τ : Tr (shapeS Y)) :
    ∃ o, (Y.psc Ex).out x y ((carryS Y x F Ex).tr τ) = some o := by
  obtain ⟨m, ε, τ⟩ := τ
  have hc := cShort_cons Y.fmt (Y.dat x.2) F hF (m.2 + ε * x.1) [pRoundV E Y.A] τ
  have h1 : Y.outC x (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))) ≠ none := by
    have hc' : HCons (Y.vars x.2)
        (Y.mu (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))) +
          Y.eps (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))) * x.1)
        (Y.qs x.2 (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))))
        (Y.hp x.2 (Y.pt (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))))) := hc
    unfold PscPar.outC
    rw [if_pos hc']
    exact Option.some_ne_none _
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 h1
  refine ⟨⟨z.st, z.eps, z.pt, z.fin,
    (Tr.snd (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ))).plains.1⟩, ?_⟩
  show ((Y.outC x (Tr.fst (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ)))).bind fun x₂ =>
    (Y.ends Ex).out x₂ y (Tr.snd (s := Y.shapeC) ((carryS Y x F Ex).tr (m, ε, τ)))) = _
  rw [hz]
  rfl

end Johnson.L5.Layers
