-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/OwnOfFacts.lean: `ownSitsB V` AT THE FIRST CHAIN'S REACHED LAST STATE, INSIDE THE FIRST
TABLE'S LAST PROMISE, IN THE LETTERS OF A PREMISE THAT ANOTHER FILE NAMES hOwn, FROM THE FACTS ALONG THE
FOLD: the leaner sibling of `hOwn_of_promise` (Johnson/Desc/Last/IndexAtOwn.lean): its hCount and hTwo are
struck (`ownSitsB_at_promise_facts`, Johnson/Desc/Last/EndAtPromise.lean). Three theorems.

  `handsBack_and`: a family that hands back still does with a condition on the public part beside it.
  **`hOwn_of_facts_at`**: with a letter Pp on the public part: ∀ q y, (ocEnd g N₁ Mg₁ links ps q y ∧ Pp q.1) →
    EndAt₁ (ProofFile.seatedAt OnBytes.secondHashFunction Z Np c) q → q.2.failed = none → ownSitsB V q.2 = true, at every Np:
    hRc (each reached state is read off a member of the facts' own family) IS ASKED UNDER Pp z ALONE: so facts
    that are stated of a narrower "reached" (the public part is a typed instance's) can pay it.
  `hOwn_of_facts`: the case Pp := always.

What stays a premise. The scope: hS, hR, O : `IM.Open`. hI, hII. hsp. `PlanSits d.L d.M V idx nW`.
hNum : N₁.msgsAt none = nW + wMsgs Z. `First.FoldFacts` of a family from which the reached states are read
(FF, hRc). ONE idx STANDS IN hII AND `PlanSits`; ONE nW IN `PlanSits` AND hNum; ONE PAIR d.L, d.M IN
`PlanSits` AND `FoldFacts`: that each can be met at one value is shown nowhere here.
Limits. Letters throughout. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.EndAtPromise
import Johnson.Desc.Last.ShapeDoorFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Last
open OnBytes
open VerifiableInference.Desc.First (Item Pub ModelPart Numbers Meaning openSets FoldData FoldFacts)
open VerifiableInference.Desc.Sound (ocEnd)
open ToldDesc (HandsBack PlanSits)
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- A family that hands back still does with a condition on the public part beside it. -/
theorem handsBack_and {T Cl Pp : Type} {bs : List (Block T Cl)} {Rc : ℕ → Pp × T → Prop}
    (hb : HandsBack bs Rc) (Q : Pp → Prop) : HandsBack bs (fun k q => Q q.1 ∧ Rc k q) := by
  intro n z s h
  obtain ⟨s₀, b, ft, rs, cols, m, r0, hb0, y0⟩ := hb n z s h.2
  exact ⟨s₀, b, ft, rs, cols, m, ⟨h.1, r0⟩, hb0, y0⟩

/-- **In the letters of the premise hOwn, from the facts along the fold, under a condition on the
public part.** -/
theorem hOwn_of_facts_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {P₀ W X : Type} (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart) (ps : List Place) {V : OwnSeats}
    {idx nW : ℕ} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × First.S} {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32} {lk : List ModelPart} {pl : List Place}
    (FF : FoldFacts Rch at_ d reqW lk pl) (Pp : ProofFile.InstPub → Prop)
    (hRc : ∀ k z s, Pp z → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (z, s) →
      ∃ a, Rch k a ∧ at_ a = (z, s))
    (hI : Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD [])
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC idx x.2)
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) (T : PlanSits d.L d.M V idx nW)
    (hNum : N₁.msgsAt none = nW + wMsgs Z) (Np : H2U.Places4) :
    ∀ q y, (ocEnd g N₁ Mg₁ links ps q y ∧ Pp q.1) →
      EndAt₁ (ProofFile.seatedAt OnBytes.secondHashFunction Z Np c) q → q.2.failed = none →
      ownSitsB V q.2 = true := by
  rintro ⟨z, s⟩ y ⟨hoc, hP⟩ he hm
  have he' : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length (z, s) := he
  rw [flat_358 hS hR O] at he'
  have h := ownSitsB_at_promise_facts hS hR O
    (handsBack_and (ToldDesc.handsBack_below 0 c.blocksInOrder (ProofFile.startS Z)) Pp) g hg
    N₁ Mg₁ links ps FF (fun k z s h => hRc k z s h.1 h.2) hI hII hsp T hNum (z, s) y hoc ⟨hP, he'⟩
    (by rw [hg]; exact hm)
  rw [hg] at h
  exact h

/-- **The case without a condition.** -/
theorem hOwn_of_facts (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {P₀ W X : Type} (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart) (ps : List Place) {V : OwnSeats}
    {idx nW : ℕ} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × First.S} {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32} {lk : List ModelPart} {pl : List Place}
    (FF : FoldFacts Rch at_ d reqW lk pl)
    (hRc : ∀ k z s, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (z, s) →
      ∃ a, Rch k a ∧ at_ a = (z, s))
    (hI : Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD [])
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC idx x.2)
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) (T : PlanSits d.L d.M V idx nW)
    (hNum : N₁.msgsAt none = nW + wMsgs Z) (Np : H2U.Places4) :
    ∀ q y, ocEnd g N₁ Mg₁ links ps q y → EndAt₁ (ProofFile.seatedAt OnBytes.secondHashFunction Z Np c) q →
      q.2.failed = none → ownSitsB V q.2 = true :=
  fun q y hoc he hm =>
    hOwn_of_facts_at hS hR O g hg N₁ Mg₁ links ps FF (fun _ => True)
      (fun k z s _ h => hRc k z s h) hI hII hsp T hNum Np q y ⟨hoc, trivial⟩ he hm

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.handsBack_and
#print axioms VerifiableInference.Desc.Last.hOwn_of_facts_at
#print axioms VerifiableInference.Desc.Last.hOwn_of_facts
