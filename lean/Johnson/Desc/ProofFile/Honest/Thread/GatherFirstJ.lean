-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherFirstJ.lean: THE GATHERING OF `OwesS` AT THE FIRST THREAD's
OWN CLAUSE OF KEEPS, `fHeadJ` (FHeadJ.lean). `owesS_framesI` and `owesS_framesK` stand at `fHeadI`.
`fHeadJ` adds one relation at K12: the state after the step is one that the decision at the finish
returns. That relation holds after every accepted step, and the rest of the gathering goes through
`owesS_aboveT`, which takes any clause of keeps that implies `fHeadH`.

  `head_hfinish_paid`   the relation after every accepted step; K12's one place is number 354
  `owesS_firstJ`, `owesS_firstK`   the statements of `owesS_framesI`, `owesS_framesK` at `fHeadJ`

What these are. Conditional lemmas on our own definitions.
 None is one of the library's goals.

Limits.
  * Those of GatherAboveT.lean and GatherSilentK9At.lean.
  * The columns in the hypotheses stay to be paid by the kinds.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherSilentK9At
import Johnson.Desc.ProofFile.Honest.Thread.FHeadJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`relsFinish` after every sub-protocol's accepted step.** -/
theorem head_hfinish_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (_Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s', drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      relsFinish (H2U.p12OfMade Zp.made) blk.place.kind s s' := by
  intro b hb blk hblk k s m E ds y cols s' hd hS
  cases hκ : blk.place.kind with
  | K12 =>
    have hb' : b < 358 := by
      have e : b < cF.blocksInOrder.length := hb
      rw [head_len h] at e
      exact e
    have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk
    obtain rfl := k12_number_of hb' hp hκ
    exact ProofFile.Honest.Sh.yes_at_354 h.toAtMg hblk 0 s s'
      (stepYes_of_stepped (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread hd hS)
  | _ => trivial

/-- **`OwesS` at `fHeadJ`**: `owesS_framesI` with the relation at K12 beside it. -/
theorem owesS_firstJ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (hb₀ : b₀ = 339) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) {Vh : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (htst : ∀ l, l < 25 → ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 →
      PlaysS L.thread Said (14 * l + IM.nAt l + j))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + i + 2)).owes →
      (j ∈ L.thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6 →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ L.thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : Item, j ∈ (L.thread.row (353)).owes →
      (j ∈ L.thread.opened (353) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (353) j)
    (hX354 : ∀ j : Item, j ∈ (L.thread.row (354)).owes →
      (j ∈ L.thread.opened (354) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (354) j)
    (hX355 : ∀ j : Item, j ∈ (L.thread.row (355)).owes →
      (j ∈ L.thread.opened (355) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (355) j)
    (hX356 : ∀ j : Item, j ∈ (L.thread.row (356)).owes →
      (j ∈ L.thread.opened (356) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (356) j)
    (hnx : LaysAtS L.thread Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g)) :
    OwesS L.thread Said := by
  subst hL
  exact owesS_aboveT h H Q test item n₁ n₂ b₀ Vd w Said hSaid hB hσ hb₀ noHalf hhalf
    (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)
    (fun p s s' hk => kpBy_fHeadI _ _ _ _ _ _ p s s' (kpBy_fHeadJ _ _ _ _ _ _ p s s' hk)) rfl
    (fun hF b hb blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨⟨⟨fHeadG_hK h H Q test _ item n₁ n₂ b₀ Vd _ _ w hB hF b hb blk hblk k s m E ds y cols s'
          (thrS_mono _ hSaid hA) hd hS,
        head_hbook_paid h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩,
        head_hreply_paid h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩,
        head_hfinish_paid h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said b hb blk hblk k s m E ds y cols
          s' hd hS⟩)
    htst hPhear hPback hP353 hP354 hP355 hP356 hXhear hXback hX353 hX354 hX355 hX356 hnx hs hstl
    hatt
    (fun b p m hp e hi h1 =>
      cellJ_of_I h H Q test _ item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said <|
      cell_carry_k7_exact h H Q test item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (by
          have e' := (List.getElem?_eq_some_iff.1 hp).1
          have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
          rw [← eW, IM.places_len] at e'
          exact e') hp e hi h1)
    (fun b p m k ρ hp e hi h1 =>
      cellJ_of_I h H Q test _ item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said <|
      cellI_of_H h H Q test _ item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said <|
      cellH_of_G h H Q test _ item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said <|
      cell_worth_k11 h H Q test _ item n₁ n₂ b₀ Vd _ w _ _ _ _ _ Said
        (by
          have e' := (List.getElem?_eq_some_iff.1 hp).1
          have eW : IM.placesW = P5J.At.ps := HashBuild.placesW_full
          rw [← eW, IM.places_len] at e'
          exact e') hp e hi h1)

/-- **`owesS_firstJ` with `hno` place by place**, as `owesS_framesK` has it. -/
theorem owesS_firstK (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (hb₀ : b₀ = 339) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) {Vh : Nat}
    (hno : ∀ l, l < 25 → ∀ j, j = 2 ∨ j = 4 ∨ j = 6 → ∀ p,
      P5J.At.ps[14 * l + IM.nAt l + j]? = some p → ∀ g ∈ H.first, g.place ≠ p)
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (htst : ∀ l, l < 25 → ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (hPhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → PlaysS L.thread Said (14 * l + i + 2))
    (hPback : ∀ l, l < 25 → PlaysS L.thread Said (14 * l + IM.nAt l + 5))
    (hP353 : PlaysS L.thread Said 353) (hP354 : PlaysS L.thread Said 354)
    (hP355 : PlaysS L.thread Said 355) (hP356 : PlaysS L.thread Said 356)
    (hXhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + i + 2)).owes →
      (j ∈ L.thread.opened (14 * l + i + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + i + 2) j)
    (hXback : ∀ l, l < 25 → ∀ c, c = 2 ∨ c = 4 ∨ c = 5 →
      ∀ j : Item, j ∈ (L.thread.row (14 * l + IM.nAt l + c)).owes →
      (j ∈ L.thread.opened (14 * l + IM.nAt l + c) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (14 * l + IM.nAt l + c) j)
    (hX353 : ∀ j : Item, j ∈ (L.thread.row (353)).owes →
      (j ∈ L.thread.opened (353) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (353) j)
    (hX355 : ∀ j : Item, j ∈ (L.thread.row (355)).owes →
      (j ∈ L.thread.opened (355) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (355) j)
    (hX356 : ∀ j : Item, j ∈ (L.thread.row (356)).owes →
      (j ∈ L.thread.opened (356) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS L.thread Said (356) j)
    (hnx : LaysAtS L.thread Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS L.thread Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hstl : ∀ l, l < 24 →
      LaysAtS L.thread Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS L.thread Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g)) :
    OwesS L.thread Said := by
  subst hL
  exact owesS_firstJ h H Q test item n₁ n₂ b₀ Vd w Said hSaid hB hσ hb₀ noHalf hhalf rfl htst
    hPhear
    (fun l hl j hj => by
      rcases hj with rfl | rfl | rfl | rfl
      · exact playsS_k9_silent_at h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hl (Or.inl rfl)
          (hno l hl 2 (Or.inl rfl))
      · exact playsS_k9_silent_at h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hl
          (Or.inr (Or.inl rfl)) (hno l hl 4 (Or.inr (Or.inl rfl)))
      · exact hPback l hl
      · exact playsS_k9_silent_at h H Q test _ item n₁ n₂ b₀ Vd _ _ w Said hl
          (Or.inr (Or.inr rfl)) (hno l hl 6 (Or.inr (Or.inr rfl))))
    hP353 hP354 hP355 hP356 hXhear
    (fun l hl c hc j hj hi => by
      rcases hc with rfl | rfl | rfl | rfl
      · exact hXback l hl 2 (Or.inl rfl) j hj hi
      · exact hXback l hl 4 (Or.inr (Or.inl rfl)) j hj hi
      · exact hXback l hl 5 (Or.inr (Or.inr rfl)) j hj hi
      · exact absurd
          (show j ∈ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).owes from hj)
          (by rw [rows_owe_nil_back hl]; exact List.not_mem_nil))
    hX353
    (fun j hj _ => absurd
      (show j ∈ (FirstRows.rows P5J.At.links P5J.At.ps 354).owes from hj)
      (by rw [rows_owe_nil_354]; exact List.not_mem_nil))
    hX355 hX356 hnx hs hstl hatt

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_hfinish_paid
#print axioms ProofFile.Honest.FirstThread.owesS_firstJ
#print axioms ProofFile.Honest.FirstThread.owesS_firstK
