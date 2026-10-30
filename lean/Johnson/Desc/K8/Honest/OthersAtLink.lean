-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/OthersAtLink.lean: THE SMALLNESS TEST: AT A PLAIN SEGMENT, FROM SENTENCES ON
THE OTHER RUNS OF CLAIMS, EACH AT THE STATE AT WHICH THE RUN IS CALLED, TO A SENTENCE ON THE CLAIMS
GATHERED IN FRONT OF THE KIND's OWN LIST AND ON THOSE BEHIND IT: along the cut of the whole list by
the runs themselves (`Walk`, Johnson/Desc/K8/Honest/GathersPlain.lean). The kind's own list is left
out: so the sentence may be one that a claim of that list does not meet. A FRAME: the two invariants
and the claims' property are letters. None of the library's goals.

  **`others_of_walk`**   Walk · each run in front keeps Inv and makes claims with Q alone · a yes of
                   the kind's list leads from Inv to Inv₂ · each run behind keeps Inv₂ and makes
                   claims with Q alone · Inv at the state behind the draw ⊢ every claim in front has
                   Q, and every claim behind
  **`othersOff_of_walk`**   the same at Q := "names no entry and no run of virtual row r₀ of array
                   t₀" (`NamesNotAt`, Johnson/Desc/K8/Honest/NamesOff.lean) ⊢ OthersOff fr bk t₀ r₀
                   i at every column i (Johnson/Desc/K8/Honest/PlanesOff.lean)
ITS PROOF IS THE MIDDLE OF ANOTHER FILE's: `off_at_link` (Johnson/Desc/K8/Honest/OffOfRuns.lean),
whose end speaks of the whole list and so asks Q of the kind's own first four claims too; the walk
with an invariant is that file's `runAll_all`.
Limits. Nothing on any run's text. WHICH INVARIANTS SERVE ALL RUNS OF A SEGMENT AT ONCE IS NOT SAID:
the three premises on the runs are paid by nobody here.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.OffOfRuns
import Johnson.Desc.K8.Honest.PlanesOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

section
variable {L : Link S Claim} {pre post : List (Nat × String)} {t e : S}
  {cls fr k8 bk : List Claim} {e₁ e₂ : S} {F F₂ : Fork} {tl tl' : HTailF2} {funs : Array HFun}

/-- **Along the runs' own cut: the claims in front of the kind's list, and those behind it.** -/
theorem others_of_walk (W : Walk L pre post t e cls fr k8 bk e₁ e₂ F F₂ tl tl' funs)
    (Inv Inv₂ : S → Prop) (Q : Claim → Prop)
    (hpre : ∀ o ∈ pre, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv u → run m u = .ok (c, u') → (∀ cl ∈ c, Q cl) ∧ Inv u')
    (hk8 : ∀ (u : S) (tl tl' : HTailF2) (F F₂ : Fork) (funs : Array HFun) (k8 : List Claim)
      (n : Nat), Inv u → u.fork? = some F → u.tl? = some tl → u.funs? = some funs →
      equations n tl funs F = .ok (tl', F₂, k8) → Inv₂ ((u.putTl tl').putFork F₂))
    (hpost : ∀ o ∈ post, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv₂ u → run m u = .ok (c, u') → (∀ cl ∈ c, Q cl) ∧ Inv₂ u')
    (ht : Inv t) : (∀ cl ∈ fr, Q cl) ∧ ∀ cl ∈ bk, Q cl := by
  obtain ⟨c, c1, c2, c3⟩ := runAll_all L Inv Q pre hpre _ _ W.a1 ht
  have hfr : fr = c := by simpa using c1
  have k2 := hk8 e₁ tl tl' F F₂ funs k8 _ c3 W.a2 W.a3 W.a4 W.a5
  obtain ⟨b, b1, b2, -⟩ := runAll_all L Inv₂ Q post hpost _ _ W.a7 (by rw [W.a6]; exact k2)
  have hbk : bk = b := List.append_cancel_left (W.a8.symm.trans b1)
  exact ⟨by rw [hfr]; exact c2, by rw [hbk]; exact b2⟩

/-- **The same at "names nothing of the virtual row": the other runs' claims lay 0 on each of its
columns.** -/
theorem othersOff_of_walk (W : Walk L pre post t e cls fr k8 bk e₁ e₂ F F₂ tl tl' funs)
    (Inv Inv₂ : S → Prop) (t₀ r₀ : Nat)
    (hpre : ∀ o ∈ pre, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv u → run m u = .ok (c, u') → (∀ cl ∈ c, NamesNotAt t₀ r₀ cl) ∧ Inv u')
    (hk8 : ∀ (u : S) (tl tl' : HTailF2) (F F₂ : Fork) (funs : Array HFun) (k8 : List Claim)
      (n : Nat), Inv u → u.fork? = some F → u.tl? = some tl → u.funs? = some funs →
      equations n tl funs F = .ok (tl', F₂, k8) → Inv₂ ((u.putTl tl').putFork F₂))
    (hpost : ∀ o ∈ post, ∀ run, LinkJoin.At L o run → ∀ (m : Nat) (u u' : S) (c : List Claim),
      Inv₂ u → run m u = .ok (c, u') → (∀ cl ∈ c, NamesNotAt t₀ r₀ cl) ∧ Inv₂ u')
    (ht : Inv t) (i : Nat) : OthersOff fr bk t₀ r₀ i := by
  obtain ⟨h1, h2⟩ := others_of_walk W Inv Inv₂ (NamesNotAt t₀ r₀) hpre hk8 hpost ht
  exact ⟨fun cl hcl => coefOn_off (h1 cl hcl) i, fun cl hcl => coefOn_off (h2 cl hcl) i⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.others_of_walk
#print axioms VerifiableInference.Desc.First.K8.Honest.othersOff_of_walk
