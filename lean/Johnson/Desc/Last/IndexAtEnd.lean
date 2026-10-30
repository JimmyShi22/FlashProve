-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/IndexAtEnd.lean: THE NUMBER OF THE INDEX MASKS' MESSAGE AT THE FIRST CHAIN'S LAST
THREE BORDERS: taken from the first table's promise at its last border, and carried back over the
last two sub-protocols. Statements with their proofs.

Why. The test `ownSitsB V` at the first chain's last state (`ToldDesc.ownSitsB_last_bools`,
Johnson/ToldDescR/OwnSitsBools.lean) asks, at border 356, one row on the table whose mask entries are
all of the message idx (its premise hRow: `K13.Law.OnLedger idx r`). What is proved elsewhere gives
that row at the state's OWN number (`OnLedger s.out.indexMasks r`). So "s.out.indexMasks = idx at
border 356" was wanted.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`index_of_ocEnd`**: the first table's promise at its last border (`Sound.ocEnd`), no mark, the
    item pinI open there, and a filling whose public item indexIs is `K13.indexIsC idx`: then the
    state's number is idx. (The promise ties indexIs to pinI: `First.pubOfItems`.)
  `WithIdx idx Rc`: a family of reached states, cut at border 358, with "the number is idx" beside
    it from border 356 on.
  `flat_358`: in the goals' scope the first chain's flat list has 358 sub-protocols.
  `out_back_356`: an accepting step of sub-protocol 356 (W's sending) leaves "out".
  **`handsBack_withIdx`**: in scope: where Rc hands back (`ToldDesc.HandsBack`), so does
    `WithIdx idx Rc`: the number goes BACK over the seal (the same state) and over W's sending.
  **`row_at_356`**: in scope, at every state at border 356 of a family that hands back: no mark; one
    row, on the state's own number, with a mask entry (`IM.at_355`, `K13.Law.rowMasks`).
  `noMark_357`: the like at border 357: no mark (`IM.at_356`).
  **`ownSitsB_last_idx`**: `ownSitsB_last_bools` WITH hRow STRUCK: in its place
    "s.out.indexMasks = idx" at the LAST state alone; hCount and hTwo are asked at states without a
    mark alone.
  **`ownSitsB_at_promise`**: the same with that equation had from `index_of_ocEnd`.
  **`ownSitsB_at_end`**: the same at "the first chain's last state is reached"
    (`Johnson.Desc.First.Walk.Tied.EndAt₁`) of the description as `IM.Open.desc` spells it.

What stays a premise. hsp, `PlanSits`, hCount (border 356), hTwo (border 357): as in
OwnSitsBools.lean. hI: a closed test on the table. hII: what the filling's item indexIs tests. ONE
LETTER idx STANDS IN hII AND IN `PlanSits`: that the filling's number passes the tests on the plan is
shown nowhere here: where it does not, the premises cannot be met together.
What is not claimed. "The number is idx" at EVERY state reached at border 356 with no promise in
hand: that wants a walk by position from the sub-protocol that writes the number. Nothing on
soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.ToldDescR.OwnSitsBools
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.K13.Law.RowMasks
import Johnson.Desc.K13.PubK13
import Johnson.IMR.PlacesScope
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Last
open OnBytes
open VerifiableInference.Desc.First (Item Pub ModelPart Numbers Meaning openSets pubOfItems)
open VerifiableInference.Desc.Sound (ocEnd)
open VerifiableInference.Desc.K13.Law (OnLedger)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open ToldDesc (HandsBack PlanSits)
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)

/-- **From the first table's last promise: the number of the index masks' message.** -/
theorem index_of_ocEnd {A P₀ W : Type} (get : A → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W)
    (links : List ModelPart) (ps : List Place) (idx : ℕ)
    (hI : Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD [])
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC idx x.2)
    (p : A) (y : Strs) (h : ocEnd get N₁ Mg₁ links ps p y) (hm : (get p).2.failed = none) :
    (get p).2.out.indexMasks = idx := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have hb := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h'.1).1).2
    have hq : Pub.indexIs ∈
        pubOfItems ((openSets links ps (First.start links))[ps.length]?.getD []) :=
      List.mem_flatMap.2 ⟨_, hI, List.Mem.head _⟩
    have h1 : Mg₁.pub .indexIs (get p) = true :=
      List.all_eq_true.1 hb .indexIs (List.mem_append_right _ hq)
    rw [hII] at h1
    have h2 : ((get p).2.out.indexMasks == idx) = true := h1
    exact beq_iff_eq.1 h2

/-- A family of reached states, cut at border 358, with "the number is idx" from border 356 on. -/
def WithIdx {Pp : Type} (idx : ℕ) (Rc : ℕ → Pp × First.S → Prop) : ℕ → Pp × First.S → Prop :=
  fun k q => Rc k q ∧ k ≤ 358 ∧ (356 ≤ k → q.2.out.indexMasks = idx)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In the goals' scope the first chain's flat list has 358 sub-protocols. -/
theorem flat_358 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    c.blocksInOrder.length = 358 := by
  rw [← List.length_map (f := (·.place)), IM.places_scope hS hR O, IM.places_len]

/-- An accepting step of sub-protocol 356 leaves "out". -/
theorem out_back_356 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {b : Block First.S ProofFile.Cl} (hb : c.blocksInOrder[356]? = some b) {ft : ℕ} {s s' : First.S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ} (hy : b.step ft s rs cols = .ok (s', n)) :
    s'.out = s.out := by
  obtain ⟨w, hw, ⟨rs', gs, hd⟩, -, -⟩ := IM.at_356 hS hR O hb hy
  obtain ⟨msg, -, rfl⟩ := (K13.Law.wAt_is _ _ _ w).1 hw
  obtain ⟨q₁, q₂, hd2⟩ := ToldDesc.atM4_two hd
  exact (K13.Law.atM4_rec hd2).2.2.2.1

/-- **The number goes back**: over the seal and over W's sending. -/
theorem handsBack_withIdx (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc) (idx : ℕ) :
    HandsBack c.blocksInOrder (WithIdx idx Rc) := by
  intro n z s h
  obtain ⟨h0, hk, hi⟩ := h
  obtain ⟨s₀, b, ft, rs, cols, m, r0, hb0, y0⟩ := hb n z s h0
  refine ⟨s₀, b, ft, rs, cols, m, ⟨r0, by omega, fun h6 => ?_⟩, hb0, y0⟩
  have hi' : s.out.indexMasks = idx := hi (by omega)
  show s₀.out.indexMasks = idx
  obtain rfl | rfl : n = 356 ∨ n = 357 := by omega
  · rw [← out_back_356 hS hR O hb0 y0]
    exact hi'
  · rw [← IM.at_357 hS hR O hb0 y0]
    exact hi'

/-- **At border 356**: no mark; one row, on the state's own number, with a mask entry. -/
theorem row_at_356 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc) {z : Pp} {s₁ : First.S}
    (h : Rc 356 (z, s₁)) :
    s₁.failed = none ∧ ∃ r, s₁.rows = [r] ∧ OnLedger s₁.out.indexMasks r ∧ r.masks ≠ [] := by
  obtain ⟨s₀, b, ft, rs, cols, m, -, hb0, y0⟩ := hb 355 z s₁ h
  obtain ⟨⟨rs', gs, hd⟩, hf, -⟩ := IM.at_355 hS hR O hb0 y0
  exact ⟨hf, K13.Law.rowMasks _ _ _ _ _ hd⟩

/-- At border 357: no mark. -/
theorem noMark_357 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc) {z : Pp} {s₂ : First.S}
    (h : Rc 357 (z, s₂)) : s₂.failed = none := by
  obtain ⟨s₀, b, ft, rs, cols, m, -, hb0, y0⟩ := hb 356 z s₂ h
  obtain ⟨w, -, -, hf, -⟩ := IM.at_356 hS hR O hb0 y0
  exact hf

/-- **`ownSitsB` at the first chain's last reached state, with the premise on the row struck**: in
its place the number at the last state alone. -/
theorem ownSitsB_last_idx (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc) {z : Pp} {s : First.S}
    (h : Rc 358 (z, s)) (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) {L : Laid}
    {M : List OracleShape} {V : OwnSeats} {idx nW : ℕ} (T : PlanSits L M V idx nW)
    (hi : s.out.indexMasks = idx)
    (hCount : ∀ s₁, Rc 356 (z, s₁) → s₁.failed = none → s₁.st.oracles.size = nW)
    (hTwo : ∀ s₂, Rc 357 (z, s₂) → s₂.failed = none → seatsCarriedB L s₂.book = true ∧
      msgShapesB M s₂.st = true ∧ nW < s₂.st.oracles.size ∧
      s₂.book.place.size = s₂.st.oracles.size) :
    ownSitsB V s = true := by
  refine ToldDesc.ownSitsB_last_bools hS hR O (handsBack_withIdx hS hR O hb idx) (z := z) (s := s)
    ⟨h, Nat.le_refl _, fun _ => hi⟩ hsp T (fun s₁ h1 => ?_)
    (fun s₁ h1 => hCount s₁ h1.1 (row_at_356 hS hR O hb h1.1).1)
    (fun s₂ h2 => hTwo s₂ h2.1 (noMark_357 hS hR O hb h2.1))
  obtain ⟨-, r, e1, e2, e3⟩ := row_at_356 hS hR O hb h1.1
  have e : s₁.out.indexMasks = idx := h1.2.2 (Nat.le_refl _)
  rw [e] at e2
  exact ⟨r, e1, e2, e3⟩

/-- **The same inside the first table's last promise.** -/
theorem ownSitsB_at_promise (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp P₀ W : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc)
    (g : Pp × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁) (N₁ : Numbers)
    (Mg₁ : Meaning P₀ W) (links : List ModelPart) (ps : List Place) {L : Laid} {M : List OracleShape}
    {V : OwnSeats} {idx nW : ℕ}
    (hI : Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD [])
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC idx x.2)
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) (T : PlanSits L M V idx nW)
    (hCount : ∀ z s₁, Rc 356 (z, s₁) → s₁.failed = none → s₁.st.oracles.size = nW)
    (hTwo : ∀ z s₂, Rc 357 (z, s₂) → s₂.failed = none → seatsCarriedB L s₂.book = true ∧
      msgShapesB M s₂.st = true ∧ nW < s₂.st.oracles.size ∧
      s₂.book.place.size = s₂.st.oracles.size) :
    ∀ q y, ocEnd g N₁ Mg₁ links ps q y → Rc 358 q → (g q).2.failed = none →
      ownSitsB V (g q).2 = true := by
  rintro ⟨z, s⟩ y hoc hr hm
  have hi := index_of_ocEnd g N₁ Mg₁ links ps idx hI hII (z, s) y hoc hm
  rw [hg] at hi ⊢
  exact ownSitsB_last_idx hS hR O hb hr hsp T hi (hCount z) (hTwo z)

/-- **The same at "the first chain's last state is reached"**, of the description as the opening
spells it; the family is the one that a run makes (the sub-protocols with the test "every word is
below the prime" in front). -/
theorem ownSitsB_at_end (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {P₀ W : Type} (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart) (ps : List Place) {L : Laid}
    {M : List OracleShape} {V : OwnSeats} {idx nW : ℕ}
    (hI : Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD [])
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC idx x.2)
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) (T : PlanSits L M V idx nW)
    (hCount : ∀ z s₁, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 356 (z, s₁) →
      s₁.failed = none → s₁.st.oracles.size = nW)
    (hTwo : ∀ z s₂, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 357 (z, s₂) →
      s₂.failed = none → seatsCarriedB L s₂.book = true ∧ msgShapesB M s₂.st = true ∧
      nW < s₂.st.oracles.size ∧ s₂.book.place.size = s₂.st.oracles.size) :
    ∀ q y, ocEnd g N₁ Mg₁ links ps q y →
      EndAt₁ (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        q →
      (g q).2.failed = none → ownSitsB V (g q).2 = true := by
  intro q y hoc he hm
  have he' : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length q := he
  rw [flat_358 hS hR O] at he'
  exact ownSitsB_at_promise hS hR O (ToldDesc.handsBack_below 0 c.blocksInOrder (ProofFile.startS Z)) g hg N₁ Mg₁
    links ps hI hII hsp T hCount hTwo q y hoc he' hm

end

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.index_of_ocEnd
#print axioms VerifiableInference.Desc.Last.flat_358
#print axioms VerifiableInference.Desc.Last.out_back_356
#print axioms VerifiableInference.Desc.Last.handsBack_withIdx
#print axioms VerifiableInference.Desc.Last.row_at_356
#print axioms VerifiableInference.Desc.Last.noMark_357
#print axioms VerifiableInference.Desc.Last.ownSitsB_last_idx
#print axioms VerifiableInference.Desc.Last.ownSitsB_at_promise
#print axioms VerifiableInference.Desc.Last.ownSitsB_at_end
