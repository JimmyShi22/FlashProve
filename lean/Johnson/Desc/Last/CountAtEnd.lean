-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/CountAtEnd.lean: THE NUMBER OF ORACLE MESSAGES IN THE VERIFIER's STATE AT THE FIRST CHAIN'S
LAST THREE BORDERS: taken from the first table's promise at its last border, and carried back over the last
two sub-protocols. Statements with their proofs. The sibling of Johnson/Desc/Last/IndexAtEnd.lean, whose
pattern it follows.

Why. The test `ownSitsB V` at the first chain's last state (`ownSitsB_at_promise`, `ownSitsB_at_end`,
IndexAtEnd.lean) still asks, at every state reached at border 356, that the statement holds nW messages
(hCount), and, at border 357, two counts beside two tests (hTwo: nW < the statement's messages; the book has
as many places as the statement has messages). The first table's promise says the counts itself, at the last
border: its clause `First.bookAt`.

Main names (namespace `VerifiableInference.Desc.Last`).
  `wMsgs Z`: how many messages W's sending has, off the public parameters (a number with code).
  `linMessageW_pos`: where the shape has that sending, it has a message.
  **`book_of_ocEnd`**: the first table's promise at its last border (`Sound.ocEnd`), no mark: the book has as
    many places as the statement has messages, and these are `N₁.msgsAt none`.
  `size_back_356`: an accepting step of sub-protocol 356 (W's sending) adds `wMsgs Z` messages.
  `WithCount n d Rc`: a family of reached states, cut at border 358, with the two counts beside it at
    borders 357 and 358 and "the messages and d are n" at border 356.
  **`handsBack_withCount`**: in scope: where Rc hands back (`ToldDesc.HandsBack`), so does
    `WithCount n (wMsgs Z) Rc`.
  **`ownSitsB_last_count`**: `ownSitsB_last_idx` WITH hCount STRUCK AND hTwo CUT TO ITS TWO TESTS: in their
    place two equations at the LAST state alone.
  **`ownSitsB_at_promise_count`**, **`ownSitsB_at_end_count`**: the same with these two had from
    `book_of_ocEnd`: what is left of the counts is ONE CLOSED EQUATION ON NUMBERS:
    hNum : N₁.msgsAt none = nW + wMsgs Z.

What stays a premise. hsp, `PlanSits`, hI, hII: as in IndexAtEnd.lean. hTwo: `seatsCarriedB` and `msgShapesB`
at border 357. hNum: the filling's number of messages at the last border against the plan's number of W's
message: where it fails, the premises cannot be met together.
What is not claimed. The count at EVERY state reached at border 356 with no promise in hand: that wants a walk
along the fold. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.IndexAtEnd
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Last
open OnBytes
open VerifiableInference.Desc.First (Item Pub ModelPart Numbers Meaning openSets pubOfItems)
open VerifiableInference.Desc.Sound (ocEnd)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open ToldDesc (HandsBack PlanSits)
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)

/-- How many messages W's sending has; 0 where the shape has no such sending. -/
def wMsgs (Z : ProofFile.Pub) : ℕ := ((linMessageW Z.first.lin).map (·.size)).getD 0

/-- Where the shape has W's sending, it has a message. -/
theorem linMessageW_pos {S : Params.LinShape} {msg : Array OracleNotice}
    (h : linMessageW S = some msg) : 0 < msg.size := by
  unfold linMessageW at h
  by_cases hm : S.masksAhead = true <;> by_cases ho : S.ownSplitNeeded = true <;>
    simp [hm, ho] at h
  all_goals first
    | (subst h; simp)
    | (obtain ⟨a, -, e⟩ := Option.bind_eq_some_iff.1 h
       obtain rfl := Option.some.inj e
       simp)

/-- **From the first table's last promise: the two counts.** -/
theorem book_of_ocEnd {A P₀ W : Type} (get : A → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W)
    (links : List ModelPart) (ps : List Place) (p : A) (y : Strs) (h : ocEnd get N₁ Mg₁ links ps p y)
    (hm : (get p).2.failed = none) :
    (get p).2.book.place.size = (get p).2.st.oracles.size ∧
      (get p).2.st.oracles.size = N₁.msgsAt none := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have hb : First.bookAt N₁ none (get p).2 = true := (Bool.and_eq_true_iff.1 h'.1).2
    unfold First.bookAt at hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact ⟨hb.1.2, hb.2⟩

/-- A family of reached states, cut at border 358, with the counts beside it from border 356 on. -/
def WithCount {Pp : Type} (n d : ℕ) (Rc : ℕ → Pp × First.S → Prop) : ℕ → Pp × First.S → Prop :=
  fun k q => Rc k q ∧ k ≤ 358 ∧
    (357 ≤ k → q.2.book.place.size = n ∧ q.2.st.oracles.size = n) ∧
    (k = 356 → q.2.st.oracles.size + d = n)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- An accepting step of sub-protocol 356 adds the messages of W's sending; and there is one. -/
theorem size_back_356 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {b : Block First.S ProofFile.Cl} (hb : c.blocksInOrder[356]? = some b) {ft : ℕ} {s s' : First.S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ} (hy : b.step ft s rs cols = .ok (s', n)) :
    s'.st.oracles.size = s.st.oracles.size + wMsgs Z ∧ 0 < wMsgs Z := by
  obtain ⟨w, hw, ⟨rs', gs, hd⟩, -, -⟩ := IM.at_356 hS hR O hb hy
  obtain ⟨msg, hm, rfl⟩ := (K13.Law.wAt_is _ _ _ w).1 hw
  obtain ⟨q₁, q₂, hd2⟩ := ToldDesc.atM4_two hd
  have e := (K13.Law.atM4_booked hd2).msgs
  have e2 : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (piece : ℕ)
      (m : Array OracleNotice), (K1.parW q gp piece m).sent.size = m.size := by
    intro q gp piece m
    simp [K1.Par.sent, K1.parW]
  have e3 : wMsgs Z = msg.size := by
    unfold wMsgs
    rw [hm]
    rfl
  rw [e2] at e
  rw [e3]
  exact ⟨e, linMessageW_pos hm⟩

/-- **The counts go back**: over the seal and over W's sending. -/
theorem handsBack_withCount (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc) (n : ℕ) :
    HandsBack c.blocksInOrder (WithCount n (wMsgs Z) Rc) := by
  intro k z s h
  obtain ⟨h0, hk, h7, -⟩ := h
  obtain ⟨s₀, b, ft, rs, cols, m, r0, hb0, y0⟩ := hb k z s h0
  refine ⟨s₀, b, ft, rs, cols, m, ⟨r0, by omega, fun h6 => ?_, fun h6 => ?_⟩, hb0, y0⟩
  · obtain rfl : k = 357 := by omega
    show s₀.book.place.size = n ∧ s₀.st.oracles.size = n
    rw [← IM.at_357 hS hR O hb0 y0]
    exact h7 (by omega)
  · subst h6
    show s₀.st.oracles.size + wMsgs Z = n
    have e := (size_back_356 hS hR O hb0 y0).1
    have e' : s.st.oracles.size = n := (h7 (by omega)).2
    omega

/-- **`ownSitsB` at the first chain's last reached state, with the premise on the count struck and the
premise at border 357 cut to its two tests**: in their place two equations at the last state alone. -/
theorem ownSitsB_last_count (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc) {z : Pp} {s : First.S}
    (h : Rc 358 (z, s)) (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) {L : Laid}
    {M : List OracleShape} {V : OwnSeats} {idx nW : ℕ} (T : PlanSits L M V idx nW)
    (hi : s.out.indexMasks = idx) (hbk : s.book.place.size = s.st.oracles.size)
    (hn : s.st.oracles.size = nW + wMsgs Z)
    (hTwo : ∀ s₂, Rc 357 (z, s₂) → s₂.failed = none → seatsCarriedB L s₂.book = true ∧
      msgShapesB M s₂.st = true) :
    ownSitsB V s = true := by
  have hpos : 0 < wMsgs Z := by
    obtain ⟨s₂, b₂, f2, R2, c2, m2, r2, hb2, y2⟩ := hb 357 z s h
    obtain ⟨s₁, b₁, f1, R1, c1, m1, r1, hb1, y1⟩ := hb 356 z s₂ r2
    exact (size_back_356 hS hR O hb1 y1).2
  refine ownSitsB_last_idx hS hR O (handsBack_withCount hS hR O hb (nW + wMsgs Z)) (z := z) (s := s)
    ⟨h, Nat.le_refl _, fun _ => ⟨hbk.trans hn, hn⟩, fun h6 => absurd h6 (by decide)⟩ hsp T hi
    (fun s₁ h1 _ => ?_) (fun s₂ h2 hm => ?_)
  · have e : s₁.st.oracles.size + wMsgs Z = nW + wMsgs Z := h1.2.2.2 rfl
    omega
  · obtain ⟨a, b⟩ : s₂.book.place.size = nW + wMsgs Z ∧ s₂.st.oracles.size = nW + wMsgs Z :=
      h2.2.2.1 (Nat.le_refl _)
    exact ⟨(hTwo s₂ h2.1 hm).1, (hTwo s₂ h2.1 hm).2, by omega, by omega⟩

/-- **The same inside the first table's last promise**: of the counts one closed equation is left. -/
theorem ownSitsB_at_promise_count (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp P₀ W : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc)
    (g : Pp × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁) (N₁ : Numbers)
    (Mg₁ : Meaning P₀ W) (links : List ModelPart) (ps : List Place) {L : Laid} {M : List OracleShape}
    {V : OwnSeats} {idx nW : ℕ}
    (hI : Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD [])
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC idx x.2)
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) (T : PlanSits L M V idx nW)
    (hNum : N₁.msgsAt none = nW + wMsgs Z)
    (hTwo : ∀ z s₂, Rc 357 (z, s₂) → s₂.failed = none → seatsCarriedB L s₂.book = true ∧
      msgShapesB M s₂.st = true) :
    ∀ q y, ocEnd g N₁ Mg₁ links ps q y → Rc 358 q → (g q).2.failed = none →
      ownSitsB V (g q).2 = true := by
  rintro ⟨z, s⟩ y hoc hr hm
  have hi := index_of_ocEnd g N₁ Mg₁ links ps idx hI hII (z, s) y hoc hm
  have hk := book_of_ocEnd g N₁ Mg₁ links ps (z, s) y hoc hm
  rw [hg] at hi hk ⊢
  exact ownSitsB_last_count hS hR O hb hr hsp T hi hk.1 (hk.2.trans hNum) (hTwo z)

/-- **The same at "the first chain's last state is reached"**, of the IOP as the opening spells it. -/
theorem ownSitsB_at_end_count (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {P₀ W : Type} (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart) (ps : List Place) {L : Laid}
    {M : List OracleShape} {V : OwnSeats} {idx nW : ℕ}
    (hI : Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD [])
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC idx x.2)
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) (T : PlanSits L M V idx nW)
    (hNum : N₁.msgsAt none = nW + wMsgs Z)
    (hTwo : ∀ z s₂, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 357 (z, s₂) →
      s₂.failed = none → seatsCarriedB L s₂.book = true ∧ msgShapesB M s₂.st = true) :
    ∀ q y, ocEnd g N₁ Mg₁ links ps q y →
      EndAt₁ (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        q →
      (g q).2.failed = none → ownSitsB V (g q).2 = true := by
  intro q y hoc he hm
  have he' : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length q := he
  rw [flat_358 hS hR O] at he'
  exact ownSitsB_at_promise_count hS hR O (ToldDesc.handsBack_below 0 c.blocksInOrder (ProofFile.startS Z)) g hg N₁
    Mg₁ links ps hI hII hsp T hNum hTwo q y hoc he' hm

end

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.linMessageW_pos
#print axioms VerifiableInference.Desc.Last.book_of_ocEnd
#print axioms VerifiableInference.Desc.Last.size_back_356
#print axioms VerifiableInference.Desc.Last.handsBack_withCount
#print axioms VerifiableInference.Desc.Last.ownSitsB_last_count
#print axioms VerifiableInference.Desc.Last.ownSitsB_at_promise_count
#print axioms VerifiableInference.Desc.Last.ownSitsB_at_end_count
