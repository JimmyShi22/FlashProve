-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/PlanesGLetter.lean: the three claims on the planes in the flat
text `planesG` (Johnson/Desc/First/Look/K3LookupGeneral.lean) are those of `planesV`
(Johnson/Desc/First/Look/Via/Rounds.lean), to the letter, where `hearV` has returned. For every
face. Stronger than Honest/K3/Law/PlanesG.lean, which compares the first claim's lead as worth:
every variable of the leaves' sumcheck is summed at a point, and for such a sumcheck the library has
the part's own row and the program's as one form (`MaskedSum.pscRow_mk`,
Johnson/Top/H/P1Tie/FlatMk.lean). Theorems.

Terms. Honest/K3/GLOSSARY.md ("claim", "count, bits, planes", "hearing", "ledger").

What is shown.
  `leafVars_point`: every variable of the leaves' sumcheck is summed at a point.
  `pscRow_letter`: where the part's own row returns, at a structure heard without ends whose
    variables are all summed at points, the flat text of the late claim returns the same form, the
    same ledger, the tape untouched.
  `planesG_letter`: where `hearV` and then `planesV` have returned, `planesG` returns the same list
    of claims.
  `general_then_planes`: with the library's own theorem on the two hearings (`hearV_flRun`,
    Johnson/Top/H/K3Via/Bridge.lean): where `hearV` returns, the general flat hearing returns on the
    strict tape of the same rounds, with the structure `toHeardG g` and the same ledger; and from
    that very structure `planesG` makes the claims of `planesV`.

Hypotheses that remain. The returns of `hearV` and `planesV` (`hh`, `hv`); the first ledger's arrays
have their size (`hS`). `general_then_planes` bears the library's own public hypothesis (`hst`): the
strict reading's tests on the hearing's entries (`(esMsg f).all staticT`: a function of the face).
In `pscRow_letter`: `h0`: the structure was heard without ends; `hpt`: its variables are all summed
at points; `hr`: the part's own row returns.

Users. This file is imported by Honest/K3/Parts/KeyLeft.lean.

Limits. One way: from the return of `planesV` to that of `planesG` (the way back, as worth:
PlanesG.lean). How a sub-protocol of the key file's description calls the two texts is not walked
here. Nothing is said on what the claims are worth.
Instances: Honest/K3/Law/PlanesGGuards.lean [not in this library] (by evaluation); for the strict
tape no instance is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.PlanesG
import Johnson.Top.H.K3Via.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Aff)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var)
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV planesV planesG messagesG toHeardG toPsc
  leafVars
  toPsc_eq esMsg hearV_flRun staticT)
open VerifiableInference.Desc.First.Tape (flRun)

/-- Every variable of the leaves' sumcheck is summed at a point. -/
theorem leafVars_point (f : LFace) (z : Array E) : ∀ v ∈ leafVars f z, v.isPoint = true := by
  intro v hv
  unfold leafVars at hv
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hv
  rfl

/-- **The flat text of the late claim returns the part's own row, to the letter.** Conditional on
the return of the part's `hear`, at a call without ends whose variables are all summed at points,
and of its `row`. -/
theorem pscRow_letter {C : Aff} {vs : List Var} {F₀ G₀ F' G' : Fork} {rs₀ : List Fmt.RoundView}
    {hd : MaskedSum.Heard} {S0 : E} {kept y : Aff} (t : Tape)
    (h0 : MaskedSum.hear C { lead := 0, vs := vs, ends := none } F₀ rs₀ = some (hd, G₀))
    (hpt : ∀ v ∈ vs, v.isPoint = true) (hr : MaskedSum.row hd S0 kept F' = some (y, G')) :
    Fl.pscRow (toPsc hd) S0 kept F' t = some ((y, { toPsc hd with rowMade := true }), G', t) := by
  obtain ⟨hs, T, R, _, hR, he, _⟩ := MaskedSum.hear_spec h0
  have hlen : R.rounds.length = vs.length := MaskedSum.readAll_none_len hR
  have hne : vs.isEmpty = false := by
    simp only [MaskedSum.shapeOk, Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2
  have hv : hd.vars = vs := by rw [he]; rfl
  have hrl : hd.r.length = hd.vars.length := by rw [hv, he]; simp [hlen]
  have hne' : hd.vars ≠ [] := by
    rw [hv]
    intro e
    rw [e] at hne
    exact nomatch hne
  obtain ⟨r1, r2⟩ := MaskedSum.row_some hr
  subst r1
  rw [toPsc_eq]
  exact MaskedSum.pscRow_mk hd (by rw [hv]; exact hpt) hne' hrl false S0 kept F' G' t r2

/-- **Where `hearV` and then `planesV` have returned, `planesG` returns the same three claims, to
the letter**, the same ledger, the tape untouched. Conditional on these two returns and on the first
ledger's arrays having their size. Instances: Honest/K3/Law/PlanesGGuards.lean [not in this library]
(by evaluation). -/
theorem planesG_letter (f : LFace) {F G F' G' : Fork} {x : List Fmt.RoundView} {g : HeardV}
    {cl : List PlaneClaim} (hS : Sized F) (hh : hearV f F x = some (g, G)) (t : Tape)
    (hv : planesV f g F' = some (cl, G')) : planesG f (toHeardG g) F' t = some (cl, G', t) := by
  obtain ⟨C, z, F₀, G₀, rs₀, h0, _, _⟩ := leaves_heard f hS (hearV_messages hh).2
  unfold planesV at hv
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hv
  obtain ⟨y1, G1⟩ := y
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hp := pscRow_letter t h0 (leafVars_point f z) hy
  unfold planesG
  dsimp only
  rw [fl_bind_some (show Fl.pscRow (toHeardG g).leaves oneE {} F' t = _ from hp)]
  rfl

/-- **The general flat hearing, then the flat claims on the planes.** Conditional on the return of
`hearV`, on that of `planesV`, on the first ledger's arrays having their size, and on the library's
public hypothesis on the hearing's entries. For the strict tape no instance of these hypotheses is
exhibited in this file. -/
theorem general_then_planes (f : LFace) {F G F' G' : Fork} {x : List Fmt.RoundView} {g : HeardV}
    {cl : List PlaneClaim} (hst : (esMsg f).all staticT = true) (hS : Sized F)
    (hh : hearV f F x = some (g, G)) (t : Tape) (hv : planesV f g F' = some (cl, G')) :
    flRun {} (messagesG f) (esMsg f) F x = some (toHeardG g, G) ∧
      planesG f (toHeardG g) F' t = some (cl, G', t) :=
  ⟨hearV_flRun hst hh, planesG_letter f hS hh t hv⟩

#print axioms ProofFile.Honest.K3.Law.leafVars_point
#print axioms ProofFile.Honest.K3.Law.pscRow_letter
#print axioms ProofFile.Honest.K3.Law.planesG_letter
#print axioms ProofFile.Honest.K3.Law.general_then_planes

end ProofFile.Honest.K3.Law
