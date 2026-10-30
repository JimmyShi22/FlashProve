-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Johnson/Door/Ride.lean: small facts on the short rounds of Cb/G6/Johnson/Layers/Short.lean
that a block on these rounds needs.

Definitions, statements and proofs. No protocol occurs here.

Main names:
  `sStrat`, `rhoL`, `sStrat_run`: a strategy of the long rounds made short, the draws read as the
    long rounds', and its run.
  `NoOrc`, `tr_ext`, `noOrc_s`: rounds without oracles; a transcript of such rounds is its draws and
    its plain parts; short rounds are such rounds.
  `sRound_point`, `sRounds_point`: short rounds are rounds of point queries.

Limits: nothing is assumed.

-/
import Cb.Ld.LdPscSig
import Cb.G6.Johnson.Layers.ShortHon

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.L5.Door
open Iop Prob Cb Johnson.L5.Layers

section Foot
variable {E : Type} [Field E]

/-- A strategy of the long rounds, each message without the coefficient that is left out. -/
def sStrat {β : Type} : (l : List (PFmt E)) → (d : PDats l) → HFixs (pVars l d) → (t : Shape) →
    Strat (pRounds l ++ t) β → Strat (sRounds l ++ t) β
  | [], _, _, _, σ => σ
  | _ :: l, d, F, t, (m, k) =>
    (((), fun i => m.2 (F.1.1.succAbove i)), fun c => sStrat l d.2 F.2 t (k c))

/-- The draws of the short rounds are those of the long ones. -/
def rhoL : (l : List (PFmt E)) → (t : Shape) → Rho (sRounds l ++ t) → Rho (pRounds l ++ t)
  | [], _, ρ => ρ
  | _ :: l, t, (c, ρ) => (c, rhoL l t ρ)

/-- The run of the short strategy is the short form of the long strategy's run. -/
theorem sStrat_run {β : Type} : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d))
    (t : Shape) (σ : Strat (pRounds l ++ t) β) (ρ : Rho (sRounds l ++ t)),
    (sStrat l d F t σ).run ρ =
      (dShort l d F t (σ.run (rhoL l t ρ)).1, (σ.run (rhoL l t ρ)).2)
  | [], _, _, _, _, _ => rfl
  | f :: l, d, F, t, (m, k), (c, ρ) => by
    show ((((), fun i => m.2 (F.1.1.succAbove i)), c, ((sStrat l d.2 F.2 t (k c)).run ρ).1),
      ((sStrat l d.2 F.2 t (k c)).run ρ).2) = _
    rw [sStrat_run l d.2 F.2 t (k c) ρ]
    rfl

/-- Rounds without oracles. -/
def NoOrc : Shape → Prop
  | [] => True
  | r :: s => Subsingleton r.Orc ∧ NoOrc s

/-- A transcript of rounds without oracles is its draws and its plain parts. -/
theorem tr_ext : ∀ {s : Shape}, NoOrc s → ∀ τ τ' : Tr s, τ.rho = τ'.rho → τ.plains = τ'.plains →
    τ = τ'
  | [], _, _, _, _, _ => rfl
  | _ :: _, h, (m, c, a), (m', c', a'), h1, h2 => by
    have e1 : c = c' := congrArg Prod.fst h1
    have e2 : a.rho = a'.rho := congrArg Prod.snd h1
    have e3 : m.2 = m'.2 := congrArg Prod.fst h2
    have e4 : a.plains = a'.plains := congrArg Prod.snd h2
    have e5 : m = m' := Prod.ext (h.1.elim _ _) e3
    rw [e1, e5, tr_ext h.2 a a' e2 e4]

/-- Short rounds have no oracles. -/
theorem noOrc_s : ∀ (l : List (PFmt E)) (t : Shape), NoOrc t → NoOrc (sRounds l ++ t)
  | [], _, h => h
  | _ :: l, t, h => ⟨inferInstanceAs (Subsingleton Unit), noOrc_s l t h⟩

/-- A short round is a round of point queries. -/
def sRound_point (f : PFmt E) : (sRound f).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

/-- So are short rounds in a row. -/
def sRounds_point : (l : List (PFmt E)) → (t : Shape) → Shape.IsPoint t →
    Shape.IsPoint (sRounds l ++ t)
  | [], _, h => h
  | f :: l, t, h => (sRound_point f, sRounds_point l t h)

end Foot

end Johnson.L5.Door
