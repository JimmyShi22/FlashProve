-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/EndAtPromise.lean: WHAT THE TEST `ownSitsB V` AT THE FIRST CHAIN'S LAST STATE STILL ASKED OF
THAT STATE, PAID INSIDE THE FIRST TABLE's LAST PROMISE: two tests from the facts along the fold
(Johnson/Desc/Last/TwoTestsAtEnd.lean), two counts from the promise's own clause on the book
(Johnson/Desc/Last/CountAtEnd.lean). Statements with their proofs: joinings by calls.

Main names (namespace `VerifiableInference.Desc.Last`).
  `wMsgs_pos`: in scope, where a family that hands back has a state at border 358: W's sending has a message.
  **`hEnd_of_promise`**: at a state q at border 358, inside the promise (`Sound.ocEnd`), without a mark:
      seatsCarriedB L s.book = true ∧ msgShapesB M s.st = true ∧ nW < s.st.oracles.size ∧
      s.book.place.size = s.st.oracles.size, s := (g q).2:
    the first two from hTests (asked at border 358 alone); the last two from `book_of_ocEnd` and
    hNum : N₁.msgsAt none = nW + wMsgs Z.
  **`ownSitsB_at_promise_facts`**, **`ownSitsB_at_end_facts`**: `ownSitsB_at_promise_count` | `_at_end_count` WITH
    hTwo STRUCK: in its place `First.FoldFacts` of a family from which the reached states are read (FF · hR), at
    L := d.L and M := d.M.

What stays a premise. hsp · `PlanSits d.L d.M V idx nW` · hI · hII · hNum · FF (with hR).
ONE PAIR OF LISTS d.L | d.M STANDS IN `PlanSits` AND IN `FoldFacts`: that the lists at which the tests on the plan
accept are the facts' own lists is shown nowhere here: where they part, the premises cannot be met together.
ONE NUMBER nW STANDS IN `PlanSits` AND IN hNum: the like.
What is not claimed. `FoldFacts` itself. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.CountAtEnd
import Johnson.Desc.Last.TwoTestsAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Last
open OnBytes
open VerifiableInference.Desc.First (Item Pub ModelPart Numbers Meaning openSets FoldData FoldFacts)
open VerifiableInference.Desc.Sound (ocEnd)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open ToldDesc (HandsBack PlanSits)
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope, where a family that hands back has a state at border 358: W's sending has a message. -/
theorem wMsgs_pos (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc) {z : Pp} {s : First.S}
    (h : Rc 358 (z, s)) : 0 < wMsgs Z := by
  obtain ⟨s₂, b₂, f2, R2, c2, m2, r2, hb2, y2⟩ := hb 357 z s h
  obtain ⟨s₁, b₁, f1, R1, c1, m1, r1, hb1, y1⟩ := hb 356 z s₂ r2
  exact (size_back_356 hS hR O hb1 y1).2

/-- **The four clauses at the last state, inside the first table's last promise.** -/
theorem hEnd_of_promise (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp P₀ W : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc)
    (g : Pp × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁) (N₁ : Numbers)
    (Mg₁ : Meaning P₀ W) (links : List ModelPart) (ps : List Place) {L : Laid} {M : List OracleShape}
    {nW : ℕ} (hNum : N₁.msgsAt none = nW + wMsgs Z)
    (hTests : ∀ z s, Rc 358 (z, s) → s.failed = none → seatsCarriedB L s.book = true ∧
      msgShapesB M s.st = true) :
    ∀ q y, ocEnd g N₁ Mg₁ links ps q y → Rc 358 q → (g q).2.failed = none →
      seatsCarriedB L (g q).2.book = true ∧ msgShapesB M (g q).2.st = true ∧
        nW < (g q).2.st.oracles.size ∧ (g q).2.book.place.size = (g q).2.st.oracles.size := by
  rintro ⟨z, s⟩ y hoc hr hm
  have hk := book_of_ocEnd g N₁ Mg₁ links ps (z, s) y hoc hm
  have hp := wMsgs_pos hS hR O hb hr
  rw [hg] at hk hm ⊢
  obtain ⟨t1, t2⟩ := hTests z s hr hm
  exact ⟨t1, t2, by omega, hk.1⟩

/-- **`ownSitsB` inside the first table's last promise, from the facts along the fold.** -/
theorem ownSitsB_at_promise_facts (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp P₀ W X : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc)
    (g : Pp × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁) (N₁ : Numbers)
    (Mg₁ : Meaning P₀ W) (links : List ModelPart) (ps : List Place) {V : OwnSeats} {idx nW : ℕ}
    {Rch : ℕ → X → Prop} {at_ : X → Pp × First.S} {d : FoldData} {reqW : Pp → Array UInt32}
    {lk : List ModelPart} {pl : List Place} (FF : FoldFacts Rch at_ d reqW lk pl)
    (hRc : ∀ k z s, Rc k (z, s) → ∃ a, Rch k a ∧ at_ a = (z, s))
    (hI : Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD [])
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC idx x.2)
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) (T : PlanSits d.L d.M V idx nW)
    (hNum : N₁.msgsAt none = nW + wMsgs Z) :
    ∀ q y, ocEnd g N₁ Mg₁ links ps q y → Rc 358 q → (g q).2.failed = none →
      ownSitsB V (g q).2 = true :=
  ownSitsB_at_promise_count hS hR O hb g hg N₁ Mg₁ links ps hI hII hsp T hNum
    fun z s₂ => two_tests_of_facts FF hRc 357 z s₂

/-- **The same at "the first chain's last state is reached"**, of the IOP as the opening spells it. -/
theorem ownSitsB_at_end_facts (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
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
    (hNum : N₁.msgsAt none = nW + wMsgs Z) :
    ∀ q y, ocEnd g N₁ Mg₁ links ps q y →
      EndAt₁ (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        q →
      (g q).2.failed = none → ownSitsB V (g q).2 = true :=
  ownSitsB_at_end_count hS hR O g hg N₁ Mg₁ links ps hI hII hsp T hNum
    fun z s₂ => two_tests_of_facts FF hRc 357 z s₂

end

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.wMsgs_pos
#print axioms VerifiableInference.Desc.Last.hEnd_of_promise
#print axioms VerifiableInference.Desc.Last.ownSitsB_at_promise_facts
#print axioms VerifiableInference.Desc.Last.ownSitsB_at_end_facts
