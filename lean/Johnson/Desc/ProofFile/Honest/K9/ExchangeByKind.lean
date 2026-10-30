-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/ExchangeByKind.lean: K9's DEBT UNDER "THE EXCHANGE" (`ExchangeAtS`,
Honest/Thread/SharesS.lean), RESTATED BY THE PLACE's KIND AND AT A LETTER `Said`: a bridge from our laws, which are
stated by number and at `SaidOk`, to the form in which the frame's house's gather over the first chain asks them. Closed
facts on the library's list of places (`P5J.At.ps`) and on the frame's table of rows (`FirstRows.rows`,
Honest/Thread/FirstRows.lean); one joining; no definition; no goal is stated.
  `k9_numbers_all` one walk along the list: at each number the place is not of the kind K9, or the number is 14 l +
      `IM.nAt l` + 2, + 4 or + 6 for some l < 25. By `decide +kernel` (Lean's kernel evaluates a closed sentence; no
      compiled code is trusted; no axiom is added)
  **`k9_number_of_kind`** so: a number at which the list has a place of the kind K9 is a segment's batching's, its "one
      equation"'s or its "the segment is shut"'s
  `k9_places_all` · `k9_kind_of_number` a control, and the converse: at each of these 75 numbers the list does have a
      place of the kind K9. By `decide +kernel`
  `bat_owes` · `eq_owes` · `shut_owes` what the forward row owes at the three sorts: totalB l and the segment's three
      pins · row l equation · nothing. By `decide +kernel`, after the frame's `behind_owes`
      (Honest/Law/Rule/OpenForms.lean), under its three raised options (maxRecDepth · synthInstance.maxSize ·
      synthInstance.maxHeartbeats)
  **`exchange_owes_of_kind`** at the thread of `lettersHead …`, every letter free: hSaid: `Said` gives `SaidOk` (it
      binds a border, a coin and a prover's state under "for all" and hands them on whole) · hB: the 25 shares at
      totalB, at `SaidOk`: A PREMISE. Then at every number that has a place of the kind K9, at every item that the row
      there owes and that is not, being open in front, a pin (the gather's own clause): `ExchangeAtS … Said b j`. HOW:
      totalB l: hB · a pin: open in front (`head_pins_open`), so struck by the clause · row l equation:
      `exchange_rowEq_head` (Honest/K9/EqExchangeHead.lean) · from `SaidOk` to `Said`: the frame's
      `exchangeAtS_mono` (Honest/Thread/SaidMono.lean)
WHAT IS NOT CLAIMED. hB: Honest/K9/TotalExchangeLens.lean has the 25 under premises of its own (an opening, K9's seat,
four to six public readings, htst: a condition on whoever lays the letter test, and at twelve segments `K4Behind`: our
definition, Honest/K9/TotalFront.lean): THEY ARE NOT JOINED HERE; Honest/K9/ExchangeAtHead.lean joins them and pays all but htst. AN
IMPLICATION: NO MEMBER: that the thread stands in front of one of these members at any run is shown by nobody. THE
WORDS THAT GO WITH THE FORMS AT totalB, AND WITH EVERY QUOTATION OF THEM: "at the
filling of record not shown to speak at any of the 25 ([…], argued: empty from 13 on with PlayedTo in Said; L25: not
at SaidOk alone)"; AND OF `K4Behind`: "share IS A FREE LETTER: at share ≡ some _ the debt is met for nothing: wherever
it is paid, share4 is K4's own named, closed test; run4 is pinned in _lay_free, not in the definition". THAT BITES
HARDER HERE THAN THERE: this file is made to be laid at a `Said` that says MORE than `SaidOk`; 48 of the 50 items that
are asked of K9 stand at numbers from 13 on (all but 9 and 11). All other limits in the heads of EqExchangeHead.lean and
TotalExchangeLens.lean hold. The first seven speak of the list and the table alone: of no thread, prover or run.
`exchange_owes_of_kind` and the control `k9_kind_of_number` are called by no line; the others here alone. At the full
size and the format's second hash function alone, as h. Nothing on any property.
GROUND: beneath this file lie files, of several groups of authors, that are no part of the sealed library.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqExchangeHead
import Johnson.Desc.ProofFile.Honest.K9.XkBat
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenForms
import Johnson.Desc.ProofFile.Honest.Thread.SaidMono

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## On the list of places and the table of rows: closed facts -/

/-- Along the list: the place at a number is not of the kind K9, or the number is one of a segment's three. -/
theorem k9_numbers_all :
    ((List.range P5J.At.ps.length).all fun b =>
      (P5J.At.ps[b]?).all fun p =>
        p.kind != KindName.K9 || (List.range 25).any fun l =>
          b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4 || b == 14 * l + IM.nAt l + 6) = true := by
  decide +kernel

/-- **A number at which the list has a place of the kind K9 is a segment's batching's, its "one equation"'s, or its
"the segment is shut"'s.** -/
theorem k9_number_of_kind {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K9) :
    ∃ l, l < 25 ∧ (b = 14 * l + IM.nAt l + 2 ∨ b = 14 * l + IM.nAt l + 4 ∨ b = 14 * l + IM.nAt l + 6) := by
  have hb : b < P5J.At.ps.length := (List.getElem?_eq_some_iff.1 hp).1
  have h0 : ((P5J.At.ps[b]?).all fun p =>
      p.kind != KindName.K9 || (List.range 25).any fun l =>
        b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4 || b == 14 * l + IM.nAt l + 6) = true :=
    List.all_eq_true.1 k9_numbers_all b (List.mem_range.2 hb)
  rw [hp] at h0
  have h1 : (p.kind != KindName.K9 || (List.range 25).any fun l =>
      b == 14 * l + IM.nAt l + 2 || b == 14 * l + IM.nAt l + 4 || b == 14 * l + IM.nAt l + 6) = true := h0
  rw [hk] at h1
  rcases Eq.mp (Bool.or_eq_true _ _) h1 with h2 | h2
  · exact absurd h2 (by decide)
  · obtain ⟨l, hl, e⟩ := List.any_eq_true.1 h2
    refine ⟨l, List.mem_range.1 hl, ?_⟩
    rcases Eq.mp (Bool.or_eq_true _ _) e with e1 | e1
    · rcases Eq.mp (Bool.or_eq_true _ _) e1 with e2 | e2
      · exact Or.inl (beq_iff_eq.1 e2)
      · exact Or.inr (Or.inl (beq_iff_eq.1 e2))
    · exact Or.inr (Or.inr (beq_iff_eq.1 e1))

/-- A control: at each of the 75 numbers the list does have a place of the kind K9. -/
theorem k9_places_all : ∀ l ∈ List.range 25,
    (P5J.At.ps[14 * l + IM.nAt l + 2]?).map (·.kind) = some KindName.K9 ∧
      (P5J.At.ps[14 * l + IM.nAt l + 4]?).map (·.kind) = some KindName.K9 ∧
      (P5J.At.ps[14 * l + IM.nAt l + 6]?).map (·.kind) = some KindName.K9 := by
  decide +kernel

/-- The converse of `k9_number_of_kind`, at each l < 25 and each of the three sorts. -/
theorem k9_kind_of_number (l : Nat) (hl : l < 25) {b : Nat}
    (hb : b = 14 * l + IM.nAt l + 2 ∨ b = 14 * l + IM.nAt l + 4 ∨ b = 14 * l + IM.nAt l + 6) :
    ∃ p, P5J.At.ps[b]? = some p ∧ p.kind = KindName.K9 := by
  obtain ⟨h2, h4, h6⟩ := k9_places_all l (List.mem_range.2 hl)
  rcases hb with rfl | rfl | rfl
  · obtain ⟨p, hp, hk⟩ := Option.map_eq_some_iff.1 h2
    exact ⟨p, hp, hk⟩
  · obtain ⟨p, hp, hk⟩ := Option.map_eq_some_iff.1 h4
    exact ⟨p, hp, hk⟩
  · obtain ⟨p, hp, hk⟩ := Option.map_eq_some_iff.1 h6
    exact ⟨p, hp, hk⟩

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- What the forward row owes at a segment's batching: the item totalB and the segment's three pins. -/
theorem bat_owes : ∀ m, m < 25 →
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * m + IM.nAt m + 2)).owes = Item.totalB m :: pinsOf m := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- At "the one equation": the one item "row m equation". -/
theorem eq_owes : ∀ m, m < 25 →
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * m + IM.nAt m + 4)).owes = [Item.row m .equation] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- At "the segment is shut": nothing. -/
theorem shut_owes : ∀ m, m < 25 →
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * m + IM.nAt m + 6)).owes = [] := by
  decide +kernel

/-! ## At the head's thread -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **K9's WHOLE DEBT UNDER "THE EXCHANGE", BY THE PLACE's KIND, FROM ITS 25 SHARES AT totalB**: at a letter Said that
gives `SaidOk`. hB: the shares at the 25 batchings, at `SaidOk`: a premise. The 25 at "row l equation" are paid by
`exchange_rowEq_head`; a pin is struck by the hypothesis's own clause; at "the segment is shut" nothing is owed. -/
theorem exchange_owes_of_kind (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hB : ∀ l, l < 25 → ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (batchAt P5J.At.links P5J.At.ps l) (Item.totalB l)) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K9 →
      ∀ j : VerifiableInference.Desc.First.Item,
      j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b j := by
  intro b p hp hk j hj hopen
  obtain ⟨l, hl, e | e | e⟩ := k9_number_of_kind hp hk
  · subst e
    have eb : batchAt P5J.At.links P5J.At.ps l = 14 * l + IM.nAt l + 2 := batch_number l hl
    have hj' : j ∈ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 2)).owes := hj
    rw [bat_owes l hl] at hj'
    rcases List.mem_cons.1 hj' with rfl | hpin
    · have k := hB l hl
      rw [eb] at k
      exact exchangeAtS_mono _ hSaid k
    · exfalso
      have ho := head_pins_open h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hpin
      rw [eb] at ho
      have hne := (hopen ho).1
      unfold pinsOf at hpin
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpin
      rcases hpin with rfl | rfl | rfl
      · exact hne l 0 rfl
      · exact hne l 1 rfl
      · exact hne l 2 rfl
  · subst e
    have hj' : j ∈ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 4)).owes := hj
    rw [eq_owes l hl] at hj'
    obtain rfl := List.mem_singleton.1 hj'
    exact exchangeAtS_mono _ hSaid (exchange_rowEq_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl)
  · subst e
    have hj' : j ∈ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).owes := hj
    rw [shut_owes l hl] at hj'
    exact nomatch hj'

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_numbers_all
#print axioms ProofFile.Honest.K9.k9_number_of_kind
#print axioms ProofFile.Honest.K9.k9_places_all
#print axioms ProofFile.Honest.K9.k9_kind_of_number
#print axioms ProofFile.Honest.K9.bat_owes
#print axioms ProofFile.Honest.K9.eq_owes
#print axioms ProofFile.Honest.K9.shut_owes
#print axioms ProofFile.Honest.K9.exchange_owes_of_kind
