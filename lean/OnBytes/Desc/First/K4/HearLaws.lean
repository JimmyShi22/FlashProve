-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/HearLaws.lean: what the second token sumcheck of the layers' own rounds
leaves, as a theorem on a run of K4's own text.

The second token sumcheck has no claim of its own: `hearTerms` (OnBytes/Desc/First/K4/Hear.lean)
asks for the equation that its rounds leave without the summand, and sets KT to that form times -1 /
eps. Johnson/Road/Rows/LayerEnds34.lean takes this line as a hypothesis (hKT of its record Pub34),
"by reading: no theorem of this library concludes it from a run". Here it is concluded from a run of
K4's text over the plain engine.

  `andThen_some`, `pscRow_some`: a run of two steps that returns; a sumcheck's own claim.
  `hearTerms_KT`: where `hearTerms engFl P H` returns H', there is the sumcheck's record tT with
      H'.tT = some tT, H'.KT = (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps)), and the drawn
      eps is not 0.

Limits. An identity on data: nothing on what KT is worth, on a draw, on soundness. If the plain
functions' text (OnBytes/K/Kc/Flat.lean) turns, this law is owed anew.
-/
import OnBytes.Desc.First.K4.Plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc

theorem andThen_some {α β : Type} {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape}
    {r : β × Fork × Tape} (h : Fl.andThen x f F t = some r) :
    ∃ a G u, x F t = some (a, G, u) ∧ f a G u = some r := by
  unfold Fl.andThen at h
  cases hx : x F t with
  | none => rw [hx] at h; cases h
  | some y =>
    obtain ⟨a, G, u⟩ := y
    rw [hx] at h
    exact ⟨a, G, u, rfl, h⟩

theorem must_some {b : Bool} {F G : Fork} {t u : Tape} {a : Unit}
    (h : Fl.must b F t = some (a, G, u)) : b = true ∧ G = F ∧ u = t := by
  unfold Fl.must at h
  cases b with
  | false => simp at h
  | true =>
    simp only [if_true, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨rfl, h.2.1.symm, h.2.2.symm⟩

theorem pscRow_some {p p' : Psc} {S0 : E} {kept row : Aff} {F G : Fork} {t u : Tape}
    (h : Fl.pscRow p S0 kept F t = some ((row, p'), G, u)) :
    row = p.rowForm S0 kept ∧ p' = { p with rowMade := true } := by
  have h' : Fl.andThen
      (Fl.must (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size))
      (fun _ => Fl.andThen
        (Fl.change (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE)))
        (fun _ => Fl.ret (p.rowForm S0 kept, { p with rowMade := true }))) F t =
      some ((row, p'), G, u) := h
  obtain ⟨_, _, _, _, h1⟩ := andThen_some h'
  obtain ⟨_, _, _, _, h2⟩ := andThen_some h1
  unfold Fl.ret at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact ⟨h2.1.1.symm, h2.1.2.symm⟩

theorem hearTerms_KT {P : Pub} {H H' : Heard} {F F' : Fork} {t t' : Tape}
    (h : hearTerms engFl P H F t = some (H', F', t')) :
    ∃ tT, H'.tT = some tT ∧
      H'.KT = (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps)) ∧
      (!isZeroE tT.p.eps) = true := by
  have h' : Fl.andThen (Fl.tscIn H.ztF P.y.h.lt (nEndT P.y) 1) (fun tT =>
      Fl.andThen (Fl.must (!isZeroE tT.p.eps)) (fun _ =>
        Fl.andThen (Fl.pscRow tT.p zeroE {}) (fun x =>
          Fl.ret ({ H with tT := some { tT with p := x.2 },
                           KT := x.1.scale (negE (invE tT.p.eps)) } : Heard)))) F t =
      some (H', F', t') := h
  obtain ⟨tT, _, _, _, h1⟩ := andThen_some h'
  obtain ⟨_, _, _, hm, h2⟩ := andThen_some h1
  obtain ⟨⟨row, p'⟩, _, _, hp, h3⟩ := andThen_some h2
  obtain ⟨e1, e2⟩ := pscRow_some hp
  unfold Fl.ret at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨hH, _, _⟩ := h3
  subst hH
  subst e1
  subst e2
  exact ⟨{ tT with p := { tT.p with rowMade := true } }, rfl, rfl, (must_some hm).1⟩

#print axioms hearTerms_KT

end OnBytes.Desc.First.K4
