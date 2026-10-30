-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean: THE SMALLNESS TEST: THE KIND's WHOLE DEBT
UNDER "THE EXCHANGE" AT THE FIRST CHAIN's THREAD AT THE HEAD, IN THE FORM IN WHICH THE GATHER OVER
THAT CHAIN ASKS IT OF A KIND: at every number b whose place in the library's written list is of the
kind K8, at every item that the row owes, but for one that is open in front and is a pin, pinI, pinW
or a constr at one of `P5J.parts4`: `ExchangeAtS`. FROM FOUR PREMISES, BY NAME: `K8Seated` · tie ·
zz (`K8TwoAt`) · `BehindS`; WITH hOk (what is said gives `SaidOk`) AND TWO ON PUBLIC DATA: hG (the
ground is the one that the description's links make) and, in hSeat, that segment l is built there.
One structure; ten theorems, five of them closed tests on written lists; none of the library's
goals.

tie AND zz NAME THE HIDDEN INPUT (the input's trace's cells) AND THE THREAD's WITNESS: EACH IS AN
EQUATION ON THE SCRIPT IN ALL BUT NAME. THEY ARE PREMISES HERE: NOTHING HERE PAYS THEM.

  `K8TwoAt T Said b blk cells P A`   the two fields tie and zz of the record `K8ItemsAt`
                   (Johnson/Desc/ProofFile/Honest/K8/SeatedItemsAt.lean), sign for sign, as a record
                   of their own
  `k8_place_at`   a place of the kind K8 in `P5J.At.ps` stands at a number 14 * l + (if l = 24 then
                   5 else 4) + 2 with l < 25: A CALL of the library's `P1K8T.k8_places_full`
                   (Johnson/P1K8R/Tied.lean) · `k8_places_all`: at each of these 25 numbers the
                   place is of the kind: so the top speaks of 25 numbers
  `k8_owes_full`, `k8_owes_at`   the forward row there owes four items: forms l (5 + shift (subAt
                   l)) "small" · constr l lookDigits · pin l 0 · pin l 1 · `k8_owes_no`: a control:
                   one number on, no row owes these
  `k8_pins_full`, `k8_pins_fwd`   the two pins are open in front: so they are of those that the
                   gather exempts · `k8_asked_no`: the two others are open in front at no segment:
                   so they are asked
  `itemsAt_of_two`   at the head: K8Seated at the description's own parameters, K8TwoAt and hOk give
                   the whole record at the true items: its four other fields by
                   `small_field_at_head`, `digits_field_at_head`, `fine_field_at_head`,
                   `some_field_at_head`
  **`k8_exchange_by_kind`**   THE TOP
THE FIVE CLOSED TESTS ARE EVALUATED BY LEAN's KERNEL (`decide +kernel`) ON THE LIBRARY's WRITTEN
LISTS OF THE FULL SIZE. THE TOP's PROOF SPENDS TWO OF THEM (`k8_owes_full`, `k8_pins_full`); the
three others are called by no line: they are there to show that the sentence speaks of 25 numbers,
that the test on a row can say no, and that the two items are asked. ONE OPTION IS RAISED AT EACH
(maxRecDepth); ONE INSTANCE IS TAKEN AWAY (attribute [-instance] Inst.Model.Scl.ref), as in the
files beneath. TACTICS THAT SEARCH: `simp only` with a written list, on one line. KIN, NOT CALLED:
the library's `P1K8T.k8_row_full` and `P1K8T.k8_pins_open` (Johnson/P1K8R/TableAtK8.lean) say the
like of the TABLE's own row and open sets; the tests here stand at the thread's FORWARD row and open
set (Johnson/Desc/ProofFile/Honest/Thread/FirstRows.lean), the very terms of the top's statement.
Limits. AN IMPLICATION. tie and zz are paid nowhere here; K8Seated and BehindS are premises. ONE
FACT, TWO FORMS: the premise tie ends in `TieBy`, at the integers a by name; the item `tie l`, which
this kind's row takes in hand in front, says the library's `TieOf`
(Johnson/Desc/First/K8/LawItems.lean): there are small integers of which the same two clauses hold.
ONE WAY IS TYPED: `tieOf_of_tieBy` (Johnson/Desc/ProofFile/Honest/K8/SmallLawProofs.lean): `TieBy`
at integers below twice the shift gives `TieOf`. That law asks smallness of a; the top's hypotheses
do not supply it: whoever spends this law and a law on that item in one gather names the premise
that a is small. A SECOND SUCH PAIR, NEAR BUT NOT ALIKE: in `K8Seated` the field half equates what
the thread's list yields for the block's place, place and parts together, with `smallHalf cells P`.
In another author's premise, `RowsPinned` (Johnson/FrontRoad/SessionStopsPinned.lean), of what that
list yields the field parts alone is equated (`[quietStop (smallStop cells P) (windowShare P.1)]`),
beside `smallFits P` and the block's one round. `small_parts`
(Johnson/Desc/ProofFile/Honest/K8/QuietForm.lean) goes from the first equation to the second, under
`smallFits`; NO LEMMA TAKES `K8Seated` TO THAT PREMISE's CLAUSE: one is wanted where a gather takes
both. THAT THE THREAD STANDS AT ANY OF THESE BORDERS, AT ANY PROVER, IS NOT SAID HERE: where it
stands at none, all is idle. The prover H is a letter: no filling is named. Behind a yes at which
the second stop is silent: NOT IN FRONT OF A LAW OVER COINS. THE FULL SIZE ALONE.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SmallFieldAtHead
import Johnson.Desc.ProofFile.Honest.K8.FineFieldAtHead
import Johnson.Desc.ProofFile.Honest.K8.DigitsFieldAtHead
import Johnson.P1K8R.Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S Item shift start)
open VerifiableInference.Desc.First.K8 (Par cellsAhead)
open VerifiableInference.Desc.First.K8.Honest
open IM (subAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

/-- **The two premises that name the hidden input**: the fields tie and zz of `K8ItemsAt`, sign for
sign. a := the input's trace's cells. Behind a yes at which the second stop is silent.
NOT IN FRONT OF A LAW OVER COINS. -/
structure K8TwoAt {W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat) (blk : Block S Claim)
    (cells : Tr → Cells) (P : Par × List (Nat × String × Nat))
    (A : T.P × S → T.Wt → TableE) : Prop where
  tie : ∀ k s m E ds y cols s' tl' e z, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
    T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2 → s'.tl? = some tl' →
    TieBy tl' (A (z, s') (T.wit k m.st.input (m.st.heard ++ e)))
      (cellsAtOf (cells m.st.input.trace) P.2)
  zz : ∀ k s m E ds y cols s' tl' (d : Fmt.Drawn) e z, ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Form (b + 1) k s' y.2 → s'.tl? = some tl' → tl'.cfF = d.trits.toArray →
    ZzBy tl' (A (z, s') (T.wit k m.st.input (m.st.heard ++ d :: e)))
      (cellsAtOf (cells m.st.input.trace) P.2)

/-! ## 1 Closed tests on the written lists -/

set_option maxRecDepth 1000000 in
/-- At each of the 25 numbers the place is of the kind K8. -/
theorem k8_places_all : ((List.range 25).all fun l =>
    (P5J.At.ps[14 * l + (if l = 24 then 5 else 4) + 2]?).any fun p =>
      decide (p.kind = KindName.K8)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The forward row at each of the 25 numbers owes these four items, in this order. -/
theorem k8_owes_full : ((List.range 25).all fun l =>
    decide ((FirstRows.rows P5J.At.links P5J.At.ps (14 * l + (if l = 24 then 5 else 4) + 2)).owes =
      [Item.forms l (5 + shift (subAt l)) "small", Item.constr l .lookDigits, Item.pin l 0,
        Item.pin l 1])) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: one number on, no row owes these four. -/
theorem k8_owes_no : ((List.range 25).any fun l =>
    decide ((FirstRows.rows P5J.At.links P5J.At.ps (14 * l + (if l = 24 then 5 else 4) + 3)).owes =
      [Item.forms l (5 + shift (subAt l)) "small", Item.constr l .lookDigits, Item.pin l 0,
        Item.pin l 1])) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The two pins are open in front of each of the 25 numbers. -/
theorem k8_pins_full : ((List.range 25).all fun l =>
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (14 * l + (if l = 24 then 5 else 4) + 2)).contains (Item.pin l 0) &&
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (14 * l + (if l = 24 then 5 else 4) + 2)).contains (Item.pin l 1)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The two other items are open in front at no segment: the row opens them. -/
theorem k8_asked_no : ((List.range 25).any fun l =>
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (14 * l + (if l = 24 then 5 else 4) + 2)).contains
        (Item.forms l (5 + shift (subAt l)) "small") ||
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (14 * l + (if l = 24 then 5 else 4) + 2)).contains
        (Item.constr l .lookDigits)) = false := by
  decide +kernel

/-- A place of the kind K8 stands at one of the 25 numbers: the library's `P1K8T.k8_places_full`, at
the number written out. -/
theorem k8_place_at {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K8) :
    ∃ l, l < 25 ∧ b = 14 * l + (if l = 24 then 5 else 4) + 2 := by
  obtain ⟨l, hl, rfl⟩ := P1K8T.k8_places_full b p hp hk
  refine ⟨l, Nat.lt_succ_of_le hl, ?_⟩
  unfold P1K8T.ixOf
  split
  · subst_vars
    rfl
  · rfl

/-- What the forward row owes at a draw's number. -/
theorem k8_owes_at {l : Nat} (hl : l < 25) :
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + (if l = 24 then 5 else 4) + 2)).owes =
      [Item.forms l (5 + shift (subAt l)) "small", Item.constr l .lookDigits, Item.pin l 0,
        Item.pin l 1] :=
  of_decide_eq_true (List.all_eq_true.1 k8_owes_full l (List.mem_range.2 hl))

/-- The two pins are open in front of a draw's number. -/
theorem k8_pins_fwd {l : Nat} (hl : l < 25) :
    Item.pin l 0 ∈ (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (14 * l + (if l = 24 then 5 else 4) + 2)) ∧
    Item.pin l 1 ∈ (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (14 * l + (if l = 24 then 5 else 4) + 2)) := by
  have hb : ((fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (14 * l + (if l = 24 then 5 else 4) + 2)).contains (Item.pin l 0) &&
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (14 * l + (if l = 24 then 5 else 4) + 2)).contains (Item.pin l 1)) = true :=
    List.all_eq_true.1 k8_pins_full l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at hb
  exact ⟨List.contains_iff_mem.1 hb.1, List.contains_iff_mem.1 hb.2⟩

/-! ## 2 At the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE WHOLE RECORD AT THE TRUE ITEMS, FROM THE SEAT AND THE TWO.** Behind a yes at which the
second stop is silent. NOT IN FRONT OF A LAW OVER COINS. -/
theorem itemsAt_of_two {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    {blk : Block S ProofFile.Cl} {cells : Tr → Cells} {mats : List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats))
    (h2 : K8TwoAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats)
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a)) :
    K8ItemsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats)
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a)
      (Item.forms l (5 + shift (subAt l)) "small") (Item.constr l .lookDigits) :=
  { small := small_field_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl hK
    digits := digits_field_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk hl hG e3 hK
    tie := h2.tie
    zz := h2.zz
    fine := fine_field_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl hK
    some := some_field_at_head h hl hG e3 }

/-- **K8's WHOLE DEBT UNDER "THE EXCHANGE", BY KIND.** Behind a yes at which the second stop is
silent. NOT IN FRONT OF A LAW OVER COINS. mats is the payer's; nothing ties it to
matsOf (`matsOf`: Johnson/HonestTrace/DigitsAtTrace.lean): it stands under "there is" in hSeat. What
does speak of it: `K8Seated` sets the thread's half at the place equal to the kind's half at it
(half) and its length equal to the number of the place's matrices (named); tie and zz read the cells
through it. -/
theorem k8_exchange_by_kind {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells)
    (hSeat : ∀ l, l < 25 → ∃ (Xl : LinkH) (blk : Block S ProofFile.Cl)
      (mats : List (Nat × String × Nat)), G.built[l]? = some Xl ∧
      K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats) ∧
      K8TwoAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp G Xl l, mats)
        (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a))
    (hB : ∀ l, l < 25 → BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2)) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K8 →
      ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b j := by
  intro b p hp hk j hj hex
  obtain ⟨l, hl, rfl⟩ := k8_place_at hp hk
  obtain ⟨Xl, blk, mats, e3, hK, h2⟩ := hSeat l hl
  have hI := itemsAt_of_two h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk hl hG e3 hK h2
  have hFb := formBehind_of_behindS hK (hB l hl)
  have hj' : j ∈ [Item.forms l (5 + shift (subAt l)) "small", Item.constr l .lookDigits,
      Item.pin l 0, Item.pin l 1] := (k8_owes_at hl) ▸ hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
  rcases hj' with rfl | rfl | rfl | rfl
  · exact smallS_share_at hK hI hFb
  · exact digitsS_share_at hK hI hFb
  · exact absurd rfl ((hex (k8_pins_fwd hl).1).1 l 0)
  · exact absurd rfl ((hex (k8_pins_fwd hl).2).1 l 1)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.K8TwoAt
#print axioms ProofFile.Honest.K8.k8_places_all
#print axioms ProofFile.Honest.K8.k8_owes_full
#print axioms ProofFile.Honest.K8.k8_owes_no
#print axioms ProofFile.Honest.K8.k8_pins_full
#print axioms ProofFile.Honest.K8.k8_asked_no
#print axioms ProofFile.Honest.K8.k8_place_at
#print axioms ProofFile.Honest.K8.k8_owes_at
#print axioms ProofFile.Honest.K8.k8_pins_fwd
#print axioms ProofFile.Honest.K8.itemsAt_of_two
#print axioms ProofFile.Honest.K8.k8_exchange_by_kind
