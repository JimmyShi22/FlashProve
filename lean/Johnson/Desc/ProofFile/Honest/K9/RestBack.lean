-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RestBack.lean: FOR THE ITEM "totalB": WHAT `TermsBack` (Honest/K9/TotalFront.lean)
SAYS OF THE SINGLE EQUATIONS' TERMS `tmRest`, AT A STATE, FROM THE TABLE's SENTENCE "forms" AT THE ENTRY
"K8.equations". A statement and its proof over the sealed library's laws; no goal is stated.
  **`rest_back`**   where K9's lens reads the part b at s, and the sentence `Sound.formsQ` of the link's readers (with
      the approximate range proof's reader laid: `K9.readersOfLink (K9.withSmall H) L`) holds at an entry o named
      "K8.equations", at the tables rd: every coefficient of `tmRest π (fixed9 φ s) (dataQ own b rd)` is 0; φ and π
      any letters with π (φ s) = (the smallness test's state blanked, the tables)
  `rest_back_ahead`   the like from `Sound.formsQA`, under "nothing is ahead" (the premise hn of the library's
      `formsQA_iff`)
HOW. The library's `item_small` (Johnson/Desc/First/Link/Law/HitemsSmall.lean) goes the other way (from the terms to
the forms' worths) through AN EQUATION OF LISTS: the terms' coefficients ARE the worths of the single equations'
forms. That equation is typed here anew with the same calls (`small_there`, `named_of_formsIn`, `rowsAff_blank`,
`rowsAff_values`, `value_own`), and read from the forms to the terms. No member; called by no line but that the second
calls the first.
WHAT IS NOT CLAIMED. The sentence "forms" at any state. "Nothing is ahead" at any state. Nothing of the four terms in
front (`tmFour`). Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.Desc.First.Link.Law.HitemsSmall
import Johnson.Desc.Sound.FormsAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (small_there named_of_formsIn rowsAff_blank value_own)
open VerifiableInference.Desc.First.TailClaims (rowsAff)
open VerifiableInference.Desc.First.TailClaims.Law (ownWorld rowsAff_values)

variable {α : Type}

/-- **The single equations' terms, from the sentence "forms".** -/
theorem rest_back (H : Desc.K9.LinkHoles) (L : Link S Claim) (φ : S → α) (own : List (ℕ × ℕ)) (o : ℕ × String)
    (hn : o.2 = "K8.equations") (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (TailClaims.Law.blank u), s.funs?)) (s : S) (b : Desc.K9.Part)
    (hb : atS.get? s = some b)
    (rd : ℕ × ℕ → MsgQ)
    (hQ : formsQ (Desc.K9.readersOfLink (Desc.K9.withSmall H) L) own o.1 o.2 s rd) :
    ∀ c ∈ tmRest π (fixed9 φ s) (dataQ own b rd), c.2 = 0 := by
  have hin := formsQ_in _ own o.1 o.2 s rd hQ
  obtain ⟨a, R, ha, hR, -, hf⟩ := hQ
  obtain rfl : b = a := Option.some.inj ((Desc.K9.segAt_of_atS s b hb).symm.trans ha)
  have hR' : Desc.K9.smallReader s = some R := by
    rw [← hR, hn]
    exact (Desc.K9.forms_small H L o.1 s).symm
  obtain ⟨tl, funs, htl, hfu, rfl⟩ := small_there s R hR'
  have he := named_of_formsIn _ own o.1 o.2 s b _ hb hR hin
  have hq : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  have hp : π (fixed9 φ s).1 = (some (TailClaims.Law.blank u tl), some funs) := by
    show π (φ s) = _
    rw [hπ, htl, hfu]
    rfl
  have e : (tmRest π (fixed9 φ s) (dataQ own b rd)).map (·.2) =
      (rowsAff tl funs).map fun g => g.value Reading.gl
        (ownWorld (cellsA b.L.arrayOf (dataQ own b rd)) (worldOwn b [] (dataQ own b rd)).slot) := by
    simp only [tmRest, hp, hq]
    rw [List.map_map, ← rowsAff_blank u tl funs,
      rowsAff_values Reading.gl _ _ (TailClaims.Law.blank u tl) funs (pubOf b).F.planClaimsF]
    rfl
  intro c hc
  have hm : c.2 ∈ (tmRest π (fixed9 φ s) (dataQ own b rd)).map (·.2) := List.mem_map.2 ⟨c, hc, rfl⟩
  rw [e] at hm
  obtain ⟨g, hg, eg⟩ := List.mem_map.1 hm
  rw [← eg, ← value_own b [] _ g (he g hg)]
  exact (hf g hg).2

/-- The like from the sentence that looks ahead, where nothing is ahead. -/
theorem rest_back_ahead (H : Desc.K9.LinkHoles) (L : Link S Claim) (φ : S → α) (sent : ℕ → List (ℕ × ℕ))
    (own : List (ℕ × ℕ)) (o : ℕ × String) (hn : o.2 = "K8.equations") (u : HTailF2)
    (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (TailClaims.Law.blank u), s.funs?)) (s : S)
    (b : Desc.K9.Part) (hb : atS.get? s = some b) (rd : ℕ × ℕ → MsgQ)
    (hno : ∀ a, Desc.K9.segAt? s = some a → ∀ x, Desc.K9.aheadIn sent own a x = none)
    (hQ : formsQA sent own (Desc.K9.readersOfLink (Desc.K9.withSmall H) L) o.1 o.2 s rd) :
    ∀ c ∈ tmRest π (fixed9 φ s) (dataQ own b rd), c.2 = 0 :=
  rest_back H L φ own o hn u π hπ s b hb rd ((formsQA_iff sent own _ o.1 o.2 s rd hno).1 hQ)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.rest_back
#print axioms ProofFile.Honest.K9.rest_back_ahead
