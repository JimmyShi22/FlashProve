-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/ByKind.lean: the numbers of the first chain's places of the kind K10 (the closing
of a segment), at the full size: on the library's list of the chain's places, `P5J.At.ps` (Johnson/P5J/LettersAt.lean: a
closed term that is evaluated, not a list written out; it has 358 places by our count, which no theorem named here
states and on which nothing here rests), a place of that kind stands at the numbers 14 l + `IM.nAt l` + 5 with l < 25
and nowhere else. With it the two statements on `ExchangeAtS` (Honest/Thread/SharesS.lean) at a closing's items
(Xch/PinKept.lean, Xch/CarryTop.lean), which are stated by number, are restated by the place's kind. No definition;
three local notations.

  `k10_numbers_all`   one walk along the list: at each number, the place there is not of the kind K10, or the
      number is 14 l + `IM.nAt l` + 5 for some l < 25. By `decide +kernel`
  `k10_places_all`   at each of these 25 numbers the list has a place of the kind K10. By `decide +kernel`
  **`k10_number_of_kind`**   hp: the list has p at number b. hk: p is of the kind K10. Then b is
      14 l + `IM.nAt l` + 5 for some l < 25
  `k10_kind_of_number`   the converse, at each l < 25
  `exchange_pinKept_of_kind`   at the head's thread, at every value of carryX and every Said: at a number b that has a
      place of the kind K10, b is the closing's number of some l < 25 and `ExchangeAtS` holds at b at `pinKept l`. By
      `exchange_pinKept_at_head`. The head is the only premise beyond hp and hk
  **`exchange_owes_of_kind`**   at the head's thread at the exact carry: from `CarryOwed` (Xch/CarryTop.lean) at all
      25 closings: at each number that has a place of the kind K10, `ExchangeAtS` at every item that the row there
      owes, stated with the unused extra hypothesis of `exchange_of_two` (Xch/RowAt.lean). By `exchange_owes_top`

What `decide +kernel` is: the head of Xch/RowAt.lean says it. No compiled code is trusted and the tactic adds no axiom.
The notations 𝕋, 𝕏 and 𝕋X, and the option in front of them: the head of Xch/CarryTop.lean says what they are.

What may be said here on hiding, and no more (a rule of use for whoever builds on this file; no theorem), on
`exchange_pinKept_of_kind` and `exchange_owes_of_kind`: NOT IN FRONT OF A LAW OVER COINS; "both end
behind a step". This file does not explain its terms. On hiding this file says nothing of its own.

Limits. The first four speak of the list alone: of no thread, prover or run. `exchange_owes_of_kind` is
`exchange_owes_top` in other words and says no more: it is an implication from the nine premises of `CarryOwed`, none of
which is shown of a run, a prover, a script or a state, and it is not shown that the nine can be met together; it stands
at the exact carry alone. The Limits of Xch/CarryTop.lean and Xch/PinKept.lean hold of the two restatements whole: among
them, where one premise fails at one `StepAt` of one closing, `exchange_owes_of_kind` says nothing at any number, and a
lemma that gathers a chain at another carryX cannot spend it. At l = 24 the item `pinKept 24` holds at every state
(`means_pinKept_last`, Xch/PinKept.lean): there the `ExchangeAtS` in `exchange_pinKept_of_kind`, and the part of
`exchange_owes_of_kind` on that item, say nothing. Both are idle at a border at which the invariant holds at no state
and at a step that is not accepted. `ExchangeAtS` is a definition, meant as a hypothesis of a lemma that gathers a whole
chain; it is none of the library's goals. Whether the head can be had at any files is not shown here. The full size and
the older hash alone. No property of the protocol is claimed: beside the quoted ruling nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.CarryTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## On the list of places -/

/-- Along the list: the place at a number is not of the kind K10, or the number is a closing's. -/
theorem k10_numbers_all :
    ((List.range P5J.At.ps.length).all fun b =>
      (P5J.At.ps[b]?).all fun p =>
        p.kind != KindName.K10 || (List.range 25).any fun l => b == 14 * l + IM.nAt l + 5) = true := by
  decide +kernel

/-- At each of the 25 closings' numbers the list has a place of the kind K10. -/
theorem k10_places_all : ∀ l ∈ List.range 25,
    (P5J.At.ps[14 * l + IM.nAt l + 5]?).map (·.kind) = some KindName.K10 := by
  decide +kernel

/-- **A number at which the list has a place of the kind K10 is the closing's number of some l < 25.** -/
theorem k10_number_of_kind {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K10) :
    ∃ l, l < 25 ∧ b = 14 * l + IM.nAt l + 5 := by
  have hb : b < P5J.At.ps.length := (List.getElem?_eq_some_iff.1 hp).1
  have h0 : ((P5J.At.ps[b]?).all fun p =>
      p.kind != KindName.K10 || (List.range 25).any fun l => b == 14 * l + IM.nAt l + 5) = true :=
    List.all_eq_true.1 k10_numbers_all b (List.mem_range.2 hb)
  rw [hp] at h0
  have h1 : (p.kind != KindName.K10 || (List.range 25).any fun l => b == 14 * l + IM.nAt l + 5) = true := h0
  rw [hk] at h1
  rcases Eq.mp (Bool.or_eq_true _ _) h1 with h2 | h2
  · exact absurd h2 (by decide)
  · obtain ⟨l, hl, e⟩ := List.any_eq_true.1 h2
    exact ⟨l, List.mem_range.1 hl, beq_iff_eq.1 e⟩

/-- At the closing's number of each l < 25 the list has a place of the kind K10. -/
theorem k10_kind_of_number (l : Nat) (hl : l < 25) :
    ∃ p, P5J.At.ps[14 * l + IM.nAt l + 5]? = some p ∧ p.kind = KindName.K10 := by
  have h0 := k10_places_all l (List.mem_range.2 hl)
  obtain ⟨p, hp, hk⟩ := Option.map_eq_some_iff.1 h0
  exact ⟨p, hp, hk⟩

/-! ## At the head's thread -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)

section
variable (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. Why the option stands here: the head of Xch/CarryTop.lean.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- At a number that has a place of the kind K10: it is the closing's number of some l < 25, and `ExchangeAtS` holds
there at `pinKept l`, at every Said and every value of carryX. On the use of this theorem the head says:
NOT IN FRONT OF A LAW OVER COINS. -/
theorem exchange_pinKept_of_kind (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K10) :
    ∃ l, l < 25 ∧ b = 14 * l + IM.nAt l + 5 ∧ ExchangeAtS 𝕋 Said b (Item.pinKept l) := by
  obtain ⟨l, hl, e⟩ := k10_number_of_kind hp hk
  exact ⟨l, hl, e, exchange_pinKept_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl e Said⟩

end

section
variable (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
  (Gr : ProofFile.Ground) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

-- The exact carry at the head's letters; the first chain's thread under the head at that value of carryX.
set_option quotPrecheck false in
local notation "𝕏" => (carryExact (P := ProofFile.InstPub) (Cells := CellsM OnBytes.Flat.numsFull) (Tok := P5J.At.Tok) Zp
  (P5J.At.arr Zp))
set_option quotPrecheck false in
local notation "𝕋X" => (lettersHead h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **From `CarryOwed` at all 25 closings: at each number that has a place of the kind K10, `ExchangeAtS` holds at every
item that the row there owes**, stated with the unused extra hypothesis of `exchange_of_two`. On the use of this theorem
the head says: NOT IN FRONT OF A LAW OVER COINS. -/
theorem exchange_owes_of_kind
    (Ow : ∀ l, l < 25 → ∀ p Qc blk, Tied cF Zp l p Qc blk →
      CarryOwed h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l Qc blk) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K10 →
      ∀ j : Item, j ∈ ((𝕋X).row b).owes →
      (j ∈ (𝕋X).opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS 𝕋X Said b j := by
  intro b p hp hk
  obtain ⟨l, hl, rfl⟩ := k10_number_of_kind hp hk
  exact exchange_owes_top h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said Ow l hl

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.k10_numbers_all
#print axioms ProofFile.Honest.K10.k10_places_all
#print axioms ProofFile.Honest.K10.k10_number_of_kind
#print axioms ProofFile.Honest.K10.k10_kind_of_number
#print axioms ProofFile.Honest.K10.exchange_pinKept_of_kind
#print axioms ProofFile.Honest.K10.exchange_owes_of_kind
