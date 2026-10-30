-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ExchangeByKind.lean: the kind "the code switch" (K2): THE
KIND's WHOLE DEBT UNDER "THE EXCHANGE", BY KIND: at every number at which the library's written list
of places (`P5J.At.ps`) has a place of the kind K2, `ExchangeAtS` at each item that the forward row
owes there, at the first chain's letters at the library's head (`lettersHead`,
Honest/Thread/FirstHead.lean, of other authors). A JOIN: the kind's four laws at one member
(`exchange_pin_switch`, `exchange_sample_switch`, `exchange_carried_switch`,
`exchange_position_switch`, of this folder) are called at each of the 25 written places. One
definition: the form of a premise; closed facts by Lean's kernel, with two controls; statements with
their proofs.

WHO IS TO CALL IT. Its end is, to the sign, the hypothesis hXk of `owesS_framesK`
(Honest/Thread/GatherByKind.lean, of other authors; on no list; not imported) at the kind K2. No
file calls it yet.

  `SwitchPaid`      THE FORM OF THE PREMISE, at one number and one place: there are letters at which
                    the kind's record `K2SeatedL` (Honest/K2/SeatedL.lean) holds, at the segment
                    p.link, with the three further premises of the four laws, to the sign: hFits and
                    hNum, on the verifier's book behind a step; H, `MadeAsks` at whatever is played,
                    shown, laid and returned
  `k2_numbers`      BY LEAN's KERNEL: the numbers at which the written list has the kind K2 are just
                    the 25 written places' numbers, in order
  `k2_owes_full`    BY LEAN's KERNEL: at each of them the forward row owes four items, in this
                    order: "pin l 0", "row l carried", "row l (sample 0)", "row l position", l the
                    place's link
  `k2_owes_no`      a control: one number on, no row owes these four
  `k2_asked_no`     none of the four is open in front of its number: so the exception that the
                    hypothesis grants (a pin that is open in front) spares the kind nothing
  `k2_carry_open`   the claim that the closed segment hands on, "carry (l - 1)", is open in front of
                    each of the 25 numbers: the field asks of the record. A control: "carry l" is
                    open in front of none
  `k2_place_at`, `k2_owes_at`, `k2_carry_at`   these facts at one number
  `four_of_paid`    the four laws, called under `SwitchPaid`
  `k2_exchange_by_kind`   THE TOP

Limits. AN IMPLICATION: `SwitchPaid` IS SHOWN OF NO LETTERS, NO PROVER AND NO SCRIPT. All that its
record and its three premises ask stands as in the four laws' own files: the record's thirty fields;
hFits, hNum and H asked at every run's coins, state and step; four fields of `MadeAsks` speak of
values and are proved of no run. All letters of the record but the number, the place and the segment
stand under "there are": nothing here ties them to the head's. NOT IN FRONT OF A LAW OVER COINS.
The full size; the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeAtPin
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeAtSample
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeAtMade
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNo
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc.First (S Item start)
open VerifiableInference.Desc.First.K2 (P2 AtYes)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread (Letters lettersHead WtF Script)
open P5J (AtMgA CellsM TS)
open _root_.Desc.K14.Law (shownGroups)

/-- **THE FORM OF THE PREMISE, AT ONE NUMBER AND ONE PLACE**: there are letters at which the kind's
record holds, at the segment p.link, with the three further premises of the kind's four laws, to the
sign. A definition. Nothing here proves that it can be met.
NOT IN FRONT OF A LAW OVER COINS. -/
def SwitchPaid {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
    (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat) (p : SwitchPlace) : Prop :=
  ∃ (blk : Block S Cl) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (q : P2)
    (before : S → Except String S) (after : S → S → Except String S) (first : Nat) (Zp : ProofFile.Pub)
    (arr : ℕ → ℕ → ℕ) (seats₀ : List (ℕ × ℕ)) (ms : List Mem) (rad : ℕ → ℕ),
    K2SeatedL L b blk D readers lay segs p q before after p.link first Zp arr seats₀ ms rad ∧
    (∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      VerifiableInference.Desc.Book.BookFits s'.book) ∧
    (∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z) ∧
    ∀ k s m E ds y cols s', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ c V Wl r₁ r₂ s₁ t x z S3 Y rows G cd, handed 0 p k = some c →
        switchRowsLaid D readers (lotClosingAt lay segs) p c m.st.input m.st.heard = .ok V →
        lotClosingAt lay segs p (D m.st.input.x) (readers m.st.input)
          (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries c.2.2) = .ok Wl →
        (roundsOf y.1).map noDigest = [r₁, r₂] → before s = .ok s₁ →
        AtYes q s₁ t r₁ r₂ (shownGroups L.thread.ft blk (roundsOf y.1) cols) x z S3 Y rows G cd →
        after s₁ t = .ok s' → MadeAsks L.N p.link (switchPar p) q s t s' V Wl r₂ x z S3 Y G

/-! ## 1 Closed tests on the written lists -/

set_option maxRecDepth 1000000 in
/-- The numbers at which the written list has the kind K2 are the written places' numbers. -/
theorem k2_numbers :
    (P5J.At.ps.zipIdx.filter fun x => decide (x.1.kind = KindName.K2)).map (·.2) =
      placesW.map switchNo ∧ placesW.length = 25 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The forward row at each of the 25 numbers owes these four items, in this order. -/
theorem k2_owes_full : (placesW.all fun p =>
    decide ((FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).owes =
      [Item.pin p.link 0, Item.row p.link .carried, Item.row p.link (.sample 0),
        Item.row p.link .position])) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: one number on, no row owes these four. -/
theorem k2_owes_no : (placesW.any fun p =>
    decide ((FirstRows.rows P5J.At.links P5J.At.ps (switchNo p + 1)).owes =
      [Item.pin p.link 0, Item.row p.link .carried, Item.row p.link (.sample 0),
        Item.row p.link .position])) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- None of the four is open in front of its number: the row opens them. -/
theorem k2_asked_no : (placesW.any fun p =>
    ([Item.pin p.link 0, Item.row p.link .carried, Item.row p.link (.sample 0),
        Item.row p.link .position]).any
      (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
        (switchNo p)).contains) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The claim that the closed segment hands on is open in front of each of the 25 numbers; a
control: the next segment's is open in front of none. -/
theorem k2_carry_open :
    (placesW.all fun p =>
      (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p)).contains
        (Item.carry (p.link - 1))) = true ∧
    (placesW.any fun p =>
      (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p)).contains
        (Item.carry p.link)) = false := by
  decide +kernel

/-- A place of the kind K2 stands at a written place's number. -/
theorem k2_place_at {b : Nat} {p₀ : VerifiableInference.Desc.Place}
    (hp : P5J.At.ps[b]? = some p₀)
    (hk : p₀.kind = KindName.K2) : ∃ p ∈ placesW, b = switchNo p := by
  have hm : b ∈ (P5J.At.ps.zipIdx.filter fun x => decide (x.1.kind = KindName.K2)).map (·.2) :=
    List.mem_map.2 ⟨(p₀, b), List.mem_filter.2 ⟨List.mem_zipIdx_iff_getElem?.2 hp,
      decide_eq_true hk⟩, rfl⟩
  rw [k2_numbers.1] at hm
  obtain ⟨p, hpW, e⟩ := List.mem_map.1 hm
  exact ⟨p, hpW, e.symm⟩

/-- What the forward row owes at a written place's number. -/
theorem k2_owes_at {p : SwitchPlace} (hp : p ∈ placesW) :
    (FirstRows.rows P5J.At.links P5J.At.ps (switchNo p)).owes =
      [Item.pin p.link 0, Item.row p.link .carried, Item.row p.link (.sample 0),
        Item.row p.link .position] :=
  of_decide_eq_true (List.all_eq_true.1 k2_owes_full p hp)

/-- The claim that the closed segment hands on is open in front of a written place's number. -/
theorem k2_carry_at {p : SwitchPlace} (hp : p ∈ placesW) :
    Item.carry (p.link - 1) ∈
      fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (switchNo p) :=
  List.contains_iff_mem.1 (List.all_eq_true.1 k2_carry_open.1 p hp)

/-! ## 2 The four laws under the one premise -/

/-- **THE FOUR LAWS AT ONE MEMBER, UNDER `SwitchPaid`.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem four_of_paid {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
    {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop} {b : Nat} {p : SwitchPlace}
    (hS : SwitchPaid L Said b p) :
    ExchangeAtS L.thread Said b (.pin p.link 0) ∧
      ExchangeAtS L.thread Said b (.row p.link .carried) ∧
      ExchangeAtS L.thread Said b (.row p.link (.sample 0)) ∧
      ExchangeAtS L.thread Said b (.row p.link .position) := by
  obtain ⟨blk, D, readers, lay, segs, q, before, after, first, Zp, arr, seats₀, ms, rad, R, hFits,
    hNum, hH⟩ := hS
  exact ⟨exchange_pin_switch R Said, exchange_carried_switch R Said hFits hNum hH,
    exchange_sample_switch R Said hFits hNum, exchange_position_switch R Said hFits hNum hH⟩

/-! ## 3 At the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- hSeat IS A PREMISE. **K2's WHOLE DEBT UNDER "THE EXCHANGE", BY KIND.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem k2_exchange_by_kind {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hSeat : ∀ p ∈ placesW,
      SwitchPaid (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (switchNo p) p) :
    ∀ b p₀, P5J.At.ps[b]? = some p₀ → p₀.kind = KindName.K2 →
      ∀ j : Item, j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b j := by
  intro b p₀ hp hk j hj _
  obtain ⟨p, hpW, rfl⟩ := k2_place_at hp hk
  obtain ⟨e1, e2, e3, e4⟩ := four_of_paid (hSeat p hpW)
  have hj' : j ∈ [Item.pin p.link 0, Item.row p.link .carried, Item.row p.link (.sample 0),
        Item.row p.link .position] := (k2_owes_at hpW) ▸ hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
  rcases hj' with rfl | rfl | rfl | rfl
  · exact e1
  · exact e2
  · exact e3
  · exact e4

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.SwitchPaid
#print axioms ProofFile.Honest.K2.Law.k2_numbers
#print axioms ProofFile.Honest.K2.Law.k2_owes_full
#print axioms ProofFile.Honest.K2.Law.k2_owes_no
#print axioms ProofFile.Honest.K2.Law.k2_asked_no
#print axioms ProofFile.Honest.K2.Law.k2_carry_open
#print axioms ProofFile.Honest.K2.Law.k2_place_at
#print axioms ProofFile.Honest.K2.Law.k2_owes_at
#print axioms ProofFile.Honest.K2.Law.k2_carry_at
#print axioms ProofFile.Honest.K2.Law.four_of_paid
#print axioms ProofFile.Honest.K2.Law.k2_exchange_by_kind
