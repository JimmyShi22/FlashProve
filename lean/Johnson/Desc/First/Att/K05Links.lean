-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05Links.lean: kind K5: WHERE THE ATTENTION LINKS STAND in the list that
Stages.listLinksH makes: a link of kind 1 stands at an odd number 2 g + 1, g below the number of
groups, in a proof that covers attention; its group is g and its name "A‹g›".

Main name: `links_kind1`. It is listLinksH_with and listLinksH_without
(OnBytes/Tie/Pv/Keeps/LinksOrder.lean) read backwards: these say what stands at each number; here:
at which numbers a link of kind 1 can stand.
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Keeps.LinksOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH SubPlanH listLinksH)
open OnBytes.L5.LinksOrder (listLinksH_with listLinksH_without linkG linkA linkHd)

/-- **A link of kind 1 is the attention link of a group, at its odd number.** -/
theorem links_kind1 {NGr : Nat} {p4 : Bool} {Gs As : Array SubPlanH} {Hh : SubPlanH}
    {l₀ : Array LinkH} (h₀ : listLinksH NGr p4 Gs As Hh = .ok l₀) {l : Nat} {Y : LinkH}
    (hY : l₀[l]? = some Y) (hk : Y.kind = 1) :
    p4 = true ∧ ∃ g, g < NGr ∧ l = 2 * g + 1 ∧ Y.g = g ∧ Y.name = "A" ++ toString g := by
  have hlt : l < l₀.size := (Array.getElem?_eq_some_iff.1 hY).1
  cases p4 with
  | false =>
    exfalso
    obtain ⟨gs, zs, pg, eh⟩ := listLinksH_without _ _ _ _ _ h₀
    by_cases hl : l = NGr
    · subst hl
      have e : Y = linkHd _ Hh := Option.some.inj (hY.symm.trans eh)
      rw [e] at hk
      cases hk
    · have hg : l < Gs.size := by omega
      have e : Y = linkG Gs[l] l :=
        Option.some.inj (hY.symm.trans (pg l _ (Array.getElem?_eq_getElem hg)))
      rw [e] at hk
      cases hk
  | true =>
    refine ⟨rfl, ?_⟩
    obtain ⟨gs, as, zs, pg, eh⟩ := listLinksH_with _ _ _ _ _ h₀
    by_cases hl : l = 2 * NGr
    · exfalso
      subst hl
      have e : Y = linkHd _ Hh := Option.some.inj (hY.symm.trans eh)
      rw [e] at hk
      cases hk
    · have hg : l / 2 < NGr := by omega
      obtain ⟨q0, q1⟩ := pg (l / 2) _ _ (Array.getElem?_eq_getElem (by omega : l / 2 < Gs.size))
        (Array.getElem?_eq_getElem (by omega : l / 2 < As.size))
      rcases Nat.mod_two_eq_zero_or_one l with hm | hm
      · exfalso
        have el : 2 * (l / 2) = l := by omega
        rw [el] at q0
        have e := Option.some.inj (hY.symm.trans q0)
        rw [e] at hk
        cases hk
      · have el : 2 * (l / 2) + 1 = l := by omega
        rw [el] at q1
        have e := Option.some.inj (hY.symm.trans q1)
        exact ⟨l / 2, hg, el.symm, by rw [e]; rfl, by rw [e]; rfl⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.links_kind1
