-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/PadsTurn.lean: WHAT THE TABLE's EXTRACTOR DOES TO A WITNESS AT A CODE SWITCH:
it turns the pads of the kept copies' tenants and nothing else. One definition, three theorems. A
law
file: no sub-protocol imports it.

Why. The tie for the claims that stay open across a code switch asks each of them at the extractor's
value. The switch's row in the table of joints (Johnson/Desc/First/Borders.lean) lays the pads of
the tenants that the group in front has kept, and no message, no token, no cell. So whoever fills a
sentence owes one fact: it does not turn with these pads.

What is said.
  `PadsTurn L w w'`: the two witnesses share every component (Johnson/Desc/Sound/BordersSides.lean:
    `sameQ`) but the pads of the tenants in L.
  `PadsTurn.mono`: a longer list does no harm. `padsTurn_refl`: a witness with itself.
  `laysOf_switch`: at a place of the kind K2 the table's list of laid components is just these pads.
  `padsTurn_extQAt`: so the table's extractor at such a place gives `PadsTurn (laysPads N links p)`.

Limits. Rules over parameters: the numbers, the list of places and the extractor's parameters are
free. Nothing is said of any sentence here. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (Place Wit FileDescription KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Numbers Comp laysOf laysSeats laysPads laysTok rowOf)

/-- The two witnesses share every component but the pads of the tenants in L. -/
def PadsTurn {Cells Tok : Type} (L : List (ℕ × ℕ)) (w w' : Wit Cells Tok MsgT) : Prop :=
  ∀ c : Comp, (∀ x ∈ L, c ≠ .pad x.1 x.2) → sameQ c w w'

/-- A longer list does no harm. -/
theorem PadsTurn.mono {Cells Tok : Type} {L L' : List (ℕ × ℕ)} {w w' : Wit Cells Tok MsgT}
    (h : PadsTurn L w w') (hL : ∀ x ∈ L, x ∈ L') : PadsTurn L' w w' :=
  fun c hc => h c fun x hx => hc x (hL x hx)

/-- A witness with itself. -/
theorem padsTurn_refl {Cells Tok : Type} (L : List (ℕ × ℕ)) (w : Wit Cells Tok MsgT) :
    PadsTurn L w w := fun c _ => by cases c <;> rfl

/-- At a place of the kind K2 the table's list of laid components is the kept tenants' pads. -/
theorem laysOf_switch (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart) (p : Place)
    (hk : p.kind = KindName.K2) :
    laysOf arr N links p = (laysPads N links p).map fun x => Comp.pad x.1 x.2 := by
  have h1 : laysSeats N links p = [] := by
    unfold laysSeats
    rw [hk]
    split <;> rfl
  have h2 : laysTok links p = false := by
    unfold laysTok
    rw [hk]
    cases (rowOf links p).lays <;> rfl
  unfold laysOf
  rw [h1, h2]
  simp

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × First.S → Tok)

/-- **The table's extractor at a code switch turns the kept tenants' pads alone.** -/
theorem padsTurn_extQAt {A : Type} {Fr : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (p : Place) (hp : ps[k]? = some p)
    (hk : p.kind = KindName.K2) (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    PadsTurn (laysPads N links p) w
      (extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w) := by
  intro c hc
  refine extQAt_keeps cs G arr smp ms decT c₀ tokOf N links ps get k a b w c ?_
  unfold laysAtQ
  rw [hp]
  show c ∉ laysOf arr N links p
  rw [laysOf_switch arr N links p hk]
  intro hm
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
  exact hc x hx rfl

end

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.PadsTurn.mono
#print axioms VerifiableInference.Desc.First.K2Ties.padsTurn_refl
#print axioms VerifiableInference.Desc.First.K2Ties.laysOf_switch
#print axioms VerifiableInference.Desc.First.K2Ties.padsTurn_extQAt
