-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/OnZeroAt.lean: THE PROMISE GOES FORWARD FROM THE FIRST CHAIN's LAST BORDER TO THE SHARED CHAIN's FIRST, AT ONE STATEMENT. One theorem.
WHY. onZeroOfEnd (Johnson/Desc/Sound/TieEnd.lean) asks its two premises AT EVERY b inside the first chain's last promise. The second ("the shared table's book-keeping at border 0 accepts the state that start₂ makes": at the meant filling: THE KEY FITS the committed table's shape) is not payable from what it has in hand at a seat whose public part holds EVERY key: nothing in the first table's promise reads whether the key fits. There onZeroOfEnd is TO BE COUNTED EMPTY (that its premise is FALSE there is not shown: no b inside the promise with an ill-fitting key has been exhibited): nothing false is proved by it, and it counts nothing.
  onZeroAt: the same end AT ONE b, from the two premises AT THAT b ALONE; and with one fact R b.1 on what is handed laid beside the first chain's last promise (the later tables' own condition: fun p y => ocEnd … p y ∧ R p).
"The key fits" reads what is handed alone: so it may stand in R and ride for nothing.

Limits. hSh at b is a premise: who pays it at a seat is the statement's scope. NO MEMBER IS SHOWN.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TieEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start openSets pubSets onAt)

/-- **THE PROMISE GOES FORWARD, AT ONE STATEMENT**, with a fact on what is handed beside it. -/
theorem onZeroAt (C : CK) (D : WholeD) (all : List LeftT) (Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type)
    (start₂ : P → S₂')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
    (get : P × S₁' → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart)
    (ps : List Place) (R₀ : (P × S₁') × (EAll D all).Str → W → Prop) (Ns : NumbersS)
    (Pm : PromMeaning S₂') (split : Bool) (R : P × S₁' → Prop)
    (hlen : 1 + T.l₁.length = ps.length) (b : (P × S₁') × (EAll D all).Str)
    (h : (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).on₁ (1 + T.l₁.length) b)
    (hTP : Mg₁.decodes (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      Pm.tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))))
    (hSh : Pm.shape 0 (start₂ b.1.1) = true) (hR : R b.1) :
    onQ₂ (tiedNumbers N₁ Ns) Pm (fun p y => ocEnd get N₁ Mg₁ links ps p y ∧ R p) split T.p₂ T.l₂ 0
      ((b.1, start₂ b.1.1), b.2) := by
  have hnone : ps[1 + T.l₁.length]? = none := by
    rw [hlen]
    exact List.getElem?_eq_none (Nat.le_refl _)
  have h' : onAt N₁ Mg₁ links ps[1 + T.l₁.length]?
      ((openSets links ps (start links))[1 + T.l₁.length]?.getD [])
      ((pubSets Mg₁.more links ps)[1 + T.l₁.length]?.getD []) (get b.1)
      (strsOf (frameAt D all D.key₁ T.ft₁) b.2) := h
  rw [hnone, hlen] at h'
  have ho : ocEnd get N₁ Mg₁ links ps b.1 (strsOf (frameAt D all D.key₂ T.ft₂) b.2) := h'
  refine ⟨fun c hc => ?_, ho, hR⟩
  rw [promsAt_zero'] at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact hTP ho.1
  · obtain rfl := List.mem_singleton.1 hc
    exact hSh

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.onZeroAt
