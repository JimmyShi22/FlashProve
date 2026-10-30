-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorMade.lean: "THE ROW IS MADE": the text that lays the one
equation's terms as a row (K9.termsRow, Johnson/Desc/First/Batch/Lay.lean) returns at the very terms
that K9.allTerms makes, WHERE ONE TEST ON SIZES ACCEPTS. It pays the premise hMade of door_returns
(DoorRow.lean) with no test on values. General laws; nothing is evaluated.

  `termB layout f S born array onI onC`: a term's test on sizes: the array is in the layout · the
    message is read in the present link · at each block of the array: blockB (DoorTensor.lean) at
    the message's row bits and place bits.
  `blocksForm_returns`, **`termsRow_returns`**: every term passes termB: termsRow returns, from
    whichever row.
  `TermAt born array X r t`: t has the sizes of a term of the array X (born in link born, named
    array) and its virtual row r: its link and name are these; its weights on the rows have clog2
    X.R factors of each kind and no written-out vector; its weights on the columns have no factor
    and a written-out vector of r.L's size. Sizes alone.
  `rowTerms_of`: what holds of every such term holds of every term that K9.rowTerms adds.
  **`allTerms_of`**: where madeB accepts, every term that K9.allTerms returns passes termB. (That
    every term that K9.allTerms returns is such a term is allTerms_all, DoorFits.lean.)
  `madeB L F S`: THE TEST ON SIZES, over the listed arrays and their virtual rows.
  **`made_returns`**: madeB accepts and K9.allTerms L F returns terms: then termsRow returns at
    these terms. **`made_pays`**: the same in the form of door_returns' premise.

Limits. ONE WAY. madeB reads the statement's row bits and place bits of a message, the layout and
the frame of the calls: numbers. That madeB accepts at the protocol's sizes is not shown. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Shape.DoorTensor
import Johnson.Desc.First.Batch.Shape.DoorParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.Params (LaidBlock ReqLayout)

/-! ## 1 termsRow returns -/

theorem blocksForm_returns (blocks : List LaidBlock) (tR tP : Nat) (onI onC : IndexWeights)
    (sc : E) (h : (blocks.all fun b => blockB b tR tP (wSh onI) (wSh onC)) = true) :
    ∃ c, blocksForm blocks tR tP onI onC sc = .ok c := by
  unfold blocksForm
  refine foldlM_returns _ _ _ fun b hb f => ?_
  obtain ⟨t, ht⟩ := blockTensor_returns b tR tP onI onC sc (List.all_eq_true.1 h b hb)
  exact ⟨f.add t, by rw [ht]; rfl⟩

/-- A term's test on sizes. -/
def termB (layout : ReqLayout) (f : ReqFrame) (S : Statement) (born : Nat) (array : String)
    (onI onC : WSh) : Bool :=
  match (layout.link[born]?).bind fun arrays => arrays.find? fun a => a.name == array with
  | none => false
  | some a =>
    match messageNow f born a.message with
    | none => false
    | some o => a.blocks.all fun b => blockB b (S.rowBits o .main) (S.placeBits o .main) onI onC

theorem termsRow_returns (layout : ReqLayout) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row : OnBytes.Row),
      (∀ t ∈ ts, termB layout f S t.born t.array (wSh t.onRows) (wSh t.onColumns) = true) →
      ∃ row', termsRow layout f S ts row = .ok row'
  | [], row, _ => ⟨row, rfl⟩
  | t :: ts, row, h => by
    have h0 := h t List.mem_cons_self
    unfold termB at h0
    cases ha : (layout.link[t.born]?).bind fun arrays =>
        arrays.find? fun a => a.name == t.array with
    | none => rw [ha] at h0; exact nomatch h0
    | some a =>
      rw [ha] at h0
      simp only at h0
      cases ho : messageNow f t.born a.message with
      | none => rw [ho] at h0; exact nomatch h0
      | some o =>
        rw [ho] at h0
        simp only at h0
        obtain ⟨c, hc⟩ := blocksForm_returns a.blocks _ _ t.onRows t.onColumns t.scale h0
        obtain ⟨row', hr⟩ := termsRow_returns layout f S ts (row.addForm o c)
          fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
        refine ⟨row', ?_⟩
        unfold termsRow
        simp only [ans_bind, there_ok]
        exact ⟨a, ha, o, ho, c, hc, hr⟩

/-! ## 2 The terms that allTerms makes -/

/-- A fold of steps that may refuse keeps what every step keeps. -/
theorem foldlM_keeps {α β : Type} (f : β → α → Ans β) (P : β → Prop) :
    ∀ (l : List α) (b r : β), P b → (∀ x ∈ l, ∀ c c', P c → f c x = .ok c' → P c') →
      l.foldlM f b = .ok r → P r
  | [], b, r, hb, _, h => by
    obtain rfl : b = r := Except.ok.inj h
    exact hb
  | x :: l, b, r, hb, hs, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨c, hc, hr⟩ := (ans_bind _ _ _).1 h
    exact foldlM_keeps f P l c r (hs x List.mem_cons_self b c hb hc)
      (fun y hy => hs y (List.mem_cons_of_mem _ hy)) hr

/-- The sizes of a term of the array X (its link born, its name array) and its virtual row r. -/
def TermAt (born : Nat) (array : String) (X : HTree) (r : HRow) (t : ReqTerm) : Prop :=
  t.born = born ∧ t.array = array ∧ wSh t.onRows = ⟨clog2 X.R, clog2 X.R, none⟩ ∧
    wSh t.onColumns = ⟨0, 0, some r.L.size⟩

theorem wSh_product (X : HTree) (r : HRow) :
    wSh (rowProduct X r) = ⟨clog2 X.R, clog2 X.R, none⟩ := by
  simp [wSh, rowProduct]

theorem wSh_pick (bits i : Nat) : wSh (pickIndex bits i) = ⟨bits, bits, none⟩ := by
  simp [wSh, pickIndex]

theorem rowTerms_of (born : Nat) (array : String) (X : HTree) (r : HRow) (P : ReqTerm → Prop)
    (hP : ∀ t, TermAt born array X r t → P t) (acc acc' : Array ReqTerm)
    (ha : ∀ t ∈ acc, P t) (h : rowTerms born array X acc r = .ok acc') : ∀ t ∈ acc', P t := by
  unfold rowTerms at h
  simp only [ans_bind, need_ok, exists_const] at h
  obtain ⟨-, h⟩ := h
  by_cases hf : r.rowForm = true
  · rw [if_pos hf] at h
    simp only [ans_bind] at h
    obtain ⟨w, hw, e⟩ := h
    obtain rfl := Except.ok.inj e
    have ew : w = rowProduct X r := by
      unfold rowWeights at hw
      simp only [ans_bind, need_ok, exists_const] at hw
      exact (Except.ok.inj hw.2.2).symm
    intro t ht
    rcases Array.mem_push.1 ht with ht | rfl
    · exact ha t ht
    · exact hP _ ⟨rfl, rfl, by rw [ew]; exact wSh_product X r, rfl⟩
  · rw [if_neg hf] at h
    obtain rfl := Except.ok.inj h
    have key : ∀ (l : List Nat) (A : Array ReqTerm), (∀ t ∈ A, P t) →
        ∀ t ∈ l.foldl (fun (t : Array ReqTerm) i => t.push
          { born := born, array := array, scale := r.coef.getD i zeroE,
            onRows := pickIndex (clog2 X.R) i, onColumns := { values := some r.L } }) A, P t := by
      intro l
      induction l with
      | nil => exact fun A hA => hA
      | cons i l ih =>
        intro A hA
        refine ih _ fun t ht => ?_
        rcases Array.mem_push.1 ht with ht | rfl
        · exact hA t ht
        · exact hP _ ⟨rfl, rfl, wSh_pick _ _, rfl⟩
    exact key _ acc ha

/-- The test on sizes, over the listed arrays and their virtual rows. -/
def madeB (L : LinkCtx) (F : Fork) (S : Statement) : Bool :=
  (List.range L.list.nt.size).all fun ti =>
    let X := F.trees.getD ti {}
    X.rows.all fun r =>
      termB L.check.rows.layout L.check.frame S (L.arrayOf.getD ti (0, "")).1
        (L.arrayOf.getD ti (0, "")).2 ⟨clog2 X.R, clog2 X.R, none⟩ ⟨0, 0, some r.L.size⟩

theorem allTerms_of (L : LinkCtx) (F : Fork) (S : Statement) (hb : madeB L F S = true)
    (terms : Array ReqTerm) (h : allTerms L F = .ok terms) :
    ∀ t ∈ terms, termB L.check.rows.layout L.check.frame S t.born t.array (wSh t.onRows)
      (wSh t.onColumns) = true := by
  unfold allTerms at h
  refine foldlM_keeps _ (fun A : Array ReqTerm => ∀ t ∈ A, termB L.check.rows.layout
    L.check.frame S t.born t.array (wSh t.onRows) (wSh t.onColumns) = true) _ _ _
    (fun t ht => absurd ht (by simp)) (fun ti hti A A' hA hs => ?_) h
  unfold madeB at hb
  have b1 := List.all_eq_true.1 hb ti hti
  simp only [ans_bind, need_ok, exists_const] at hs
  obtain ⟨-, hs⟩ := hs
  rw [← Array.foldlM_toList] at hs
  refine foldlM_keeps _ (fun A : Array ReqTerm => ∀ t ∈ A, termB L.check.rows.layout
    L.check.frame S t.born t.array (wSh t.onRows) (wSh t.onColumns) = true) _ _ _ hA
    (fun r hr B B' hB hq => ?_) hs
  have hr' : r ∈ (F.trees.getD ti {}).rows := Array.mem_toList_iff.1 hr
  have b2 := Array.all_eq_true'.1 b1 r hr'
  refine rowTerms_of _ _ _ r _ (fun t ht => ?_) B B' hB hq
  obtain ⟨e1, e2, e3, e4⟩ := ht
  rw [e1, e2, e3, e4]
  exact b2

/-- **THE ROW IS MADE.** -/
theorem made_returns (L : LinkCtx) (F : Fork) (S : Statement) (hb : madeB L F S = true)
    (terms : Array ReqTerm) (h : allTerms L F = .ok terms) (row : OnBytes.Row) :
    ∃ row', termsRow L.check.rows.layout L.check.frame S terms.toList row = .ok row' :=
  termsRow_returns _ _ _ _ row fun t ht =>
    allTerms_of L F S hb terms h t (Array.mem_toList_iff.1 ht)

/-- **The premise hMade of door_returns (DoorRow.lean), paid by the test on sizes.** -/
theorem made_pays (L : LinkCtx) (F : Fork) (S : Statement)
    (hb : madeB L { F with doorShutF := true } S = true) (q : Equation) (F' : Fork)
    (h : equation L F = .ok (q, F')) :
    ∃ row, termsRow L.check.rows.layout L.check.frame S q.terms.toList {} = .ok row := by
  obtain ⟨-, -, -, terms, mc, ht, -, rfl⟩ := (equation_iff L F F' q).1 h
  exact made_returns L _ S hb terms ht {}

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.made_pays
#print axioms VerifiableInference.Desc.K9.Shape.termsRow_returns
#print axioms VerifiableInference.Desc.K9.Shape.allTerms_of
#print axioms VerifiableInference.Desc.K9.Shape.made_returns
