-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/PlanNames.lean: three things that Johnson/Goal/Meaning/PlanShapes.lean leaves:
that the public part has a layers' plan for every group; the links' names, identifiers and the flag
fv; and links_get without its premise on the number of layers' plans.

  plans_size        wherever publicOf returns X: X.G.size = X.NGr (by the text of Layer.plansG,
                    through more_of_public, Johnson/Goal/Meaning/Pub34Scope.lean).
  scope_plans24     so in the goals' scope all 24 plans are there: for g < 12, X.G[g]? and X.A[g]?
                    are some plan.
  IsNamed, links_named   at any sub-plans, along the list that is run: the link at 2 g has the name
                    "G" ++ toString g, the identifier 1 + g and fv = true; at 2 g + 1: "A" ++
                    toString g, 14 + g, false; at 24: "H", 13, true.
  links_get'        links_get with no premise on X.G's size.

What is not claimed: as in Johnson/Goal/Meaning/PlanShapes.lean. No description is named.
-/
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Goal.Meaning.Pub34Scope

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model
open OnBytes OnBytes.Road OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH LinksH SubPlanH listLinksH buildLinksH)
open OnBytes.L5.LinksOrder (zipped ok_bind)

/-- plansFrom returns as many plans as it is asked for. -/
theorem plansFrom_length (P : Layer.Pub) : ∀ (n g : ℕ) (O : Option Layer.HPlan2)
    (l : List Layer.HPlan2), Layer.plansFrom P n g O = .ok l → l.length = n
  | 0, _, _, l, h => by
    obtain rfl : [] = l := Except.ok.inj h
    rfl
  | n + 1, g, O, l, h => by
    unfold Layer.plansFrom at h
    obtain ⟨p, _, h⟩ := ok_bind h
    obtain ⟨l', h2, h⟩ := ok_bind h
    obtain rfl : p :: l' = l := Except.ok.inj h
    rw [List.length_cons, plansFrom_length P n (g + 1) (some p) l' h2]

/-- **The public part has a layers' plan for every group.** -/
theorem plans_size {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : publicOf pol KL lay = .ok X) : X.G.size = X.NGr := by
  obtain ⟨-, -, -, -, hG⟩ := P34.more_of_public h
  unfold Layer.plansG at hG
  obtain ⟨l, h1, hG⟩ := ok_bind hG
  have e : l.toArray = X.G := Except.ok.inj hG
  rw [← e, List.size_toArray, plansFrom_length _ _ _ _ _ h1]
  rfl

/-- **In scope all 24 plans are there.** -/
theorem scope_plans24 {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    ∀ g < 12, (∃ hp, X.G[g]? = some hp) ∧ ∃ a, X.A[g]? = some a ∧ a.S = Hd.shapeA X g := by
  obtain ⟨-, hN, -, hA⟩ := scope_plans hZ hR h
  have hG : X.G.size = 12 := (plans_size h).trans hN
  exact fun g hg => ⟨⟨_, Array.getElem?_eq_getElem (by omega)⟩, hA g hg⟩

/-- A link's name, identifier and flag. -/
structure IsNamed (l : LinkH) (name : String) (gid : ℕ) (fv : Bool) : Prop where
  name : l.name = name
  gid : l.gid = gid
  fv : l.fv = fv

/-- **The links' names**, at twelve groups with attention, whatever the sub-plans. -/
theorem links_named {G₀ A₀ G₁ A₁ : Array SubPlanH} {H₀ H₁ : SubPlanH} {l₀ ls : Array LinkH}
    {ws : WsLay} {first : Params.First} {B : LinksH}
    (h₀ : listLinksH 12 true G₀ A₀ H₀ = .ok l₀) (hB : buildLinksH l₀ 12 true ws first = .ok B)
    (hl : listLinksH 12 true G₁ A₁ H₁ = .ok ls) :
    (∀ g < 12, ∃ l l', (zipped B ls)[2 * g]? = some l ∧ IsNamed l ("G" ++ toString g) (1 + g) true ∧
        (zipped B ls)[2 * g + 1]? = some l' ∧ IsNamed l' ("A" ++ toString g) (2 + 12 + g) false) ∧
      ∃ l, (zipped B ls)[24]? = some l ∧ IsNamed l "H" (1 + 12) true := by
  obtain ⟨g0, a0, -, p0, e0⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨g1, a1, -, p1, e1⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  refine ⟨fun g hg => ?_, ?_⟩
  · have s0 : G₀[g]? = some G₀[g] := Array.getElem?_eq_getElem (by omega)
    have t0 : A₀[g]? = some A₀[g] := Array.getElem?_eq_getElem (by omega)
    have s1 : G₁[g]? = some G₁[g] := Array.getElem?_eq_getElem (by omega)
    have t1 : A₁[g]? = some A₁[g] := Array.getElem?_eq_getElem (by omega)
    obtain ⟨q0, q0'⟩ := p0 g _ _ s0 t0
    obtain ⟨q1, q1'⟩ := p1 g _ _ s1 t1
    obtain ⟨ar, e⟩ := zipped_place hB q0 q1
    obtain ⟨ar', e'⟩ := zipped_place hB q0' q1'
    exact ⟨_, _, e, ⟨rfl, rfl, rfl⟩, e', ⟨rfl, rfl, rfl⟩⟩
  · obtain ⟨ar, e⟩ := zipped_place hB e0 e1
    exact ⟨_, e, ⟨rfl, rfl, rfl⟩⟩

/-- **links_get with no premise on the number of layers' plans.** -/
theorem links_get' {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X)
    {G₀ A₀ G₁ A₁ : Array SubPlanH} {H₀ H₁ : SubPlanH} {l₀ ls : Array LinkH} {ws : WsLay}
    {first : Params.First} {B : LinksH} (h₀ : listLinksH X.NGr X.p4 G₀ A₀ H₀ = .ok l₀)
    (hB : buildLinksH l₀ X.NGr X.p4 ws first = .ok B)
    (hl : listLinksH X.NGr X.p4 G₁ A₁ H₁ = .ok ls) :
    (zipped B ls).size = 25 ∧
      ∀ k < 25, ((zipped B ls)[k]?).bind (getsAt X) = getsOf X k ∧ (getsOf X k).isSome = true :=
  links_get hZ hR h ((plans_size h).trans (scope_plans hZ hR h).2.1) h₀ hB hl

end Meaning

#print axioms Meaning.plans_size
#print axioms Meaning.scope_plans24
#print axioms Meaning.links_named
#print axioms Meaning.links_get'
