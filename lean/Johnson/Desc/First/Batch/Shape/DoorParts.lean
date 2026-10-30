-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorParts.lean: THE ONE EQUATION RETURNS (K9.equation,
Johnson/Desc/First/Batch/Text.lean): the two texts that it calls, allTerms and slotsIn, each cut
into a test on numbers and marks and a test on values; and with the cut of DoorCut.lean the law
"these tests accept, so K9.equation returns". General laws; nothing is evaluated.

  `foldlM_returns`: a fold of steps that may refuse returns where every step returns at every value
    gathered so far.
  `rowB X r` (numbers and marks: two sizes, and the first column is 0; where the row has a product
    form, that the form is well formed) and `rowV X r` (A TEST ON VALUES: where the row has a
    product form, the written-out weights are the product's). `rowTerms_returns`.
  `termsB L F`, `termsV L F`: the same over the listed arrays and their virtual rows, with "the
    array is laid" on the side of numbers. **`allTerms_returns`**.
  `slotsV F`: A TEST ON VALUES: a slot with a coefficient that is not 0 is filled.
    **`slotsIn_returns`**: then slotsIn returns, and the coefficients on the mask row are as many as
    the ledger has slots.
  `slotsIn_size`, `equation_size`: the same number, from a return.
  **`equation_returns`**: eqB, termsB (numbers and marks) and outsideV, termsV, slotsV (values)
    accept: then K9.equation L F returns an equation and F with the door shut, and the equation's
    coefficients on the mask row are F.ns. termsB, termsV and slotsV are asked at F with the door
    shut, as the text runs them; none of the three reads that mark.

Limits. ONE WAY. rowB reads the sizes of a virtual row's point and of its two lists of factors: the
shape of a row (Johnson/Desc/First/Shape/Parts.lean) does not hold these three: so termsB is a
test on the ledger, not on its shape. That the three tests on values accept in an honest
prover's run is not shown. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Shape.DoorCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc

/-! ## 1 Folds -/

theorem foldlM_returns {α β : Type} (f : β → α → Ans β) :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ c, ∃ c', f c x = .ok c') → ∃ r, l.foldlM f b = .ok r
  | [], b, _ => ⟨b, rfl⟩
  | x :: l, b, h => by
    obtain ⟨c', hc⟩ := h x List.mem_cons_self b
    obtain ⟨r, hr⟩ := foldlM_returns f l c' fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨r, ?_⟩
    rw [List.foldlM_cons]
    show (f b x >>= fun c => l.foldlM f c) = _
    rw [hc]
    exact hr

/-! ## 2 The terms -/

/-- A virtual row: numbers and marks. -/
def rowB (X : HTree) (r : HRow) : Bool :=
  (r.coef.size == X.R && r.L.size == X.K && r.L0 == 0) && (!r.rowForm || rowFormFits X r)

/-- **A test on values**: the written-out weights are the product form's. -/
def rowV (X : HTree) (r : HRow) : Bool :=
  !r.rowForm ||
    -- bound once, as in the verifier's text: inside the test it would be made anew at every index
    let all := productWritten (rowProduct X r)
    everyBelow X.R fun i => all.getD i zeroE == r.coef.getD i zeroE

theorem rowWeights_ok (X : HTree) (r : HRow) (h1 : rowFormFits X r = true)
    (h2 : (everyBelow X.R fun i =>
      (productWritten (rowProduct X r)).getD i zeroE == r.coef.getD i zeroE) = true) :
    rowWeights X r = .ok (rowProduct X r) := by
  show (need "K9.row-form" (rowFormFits X r) >>= fun _ =>
    need "K9.row-form-values" (everyBelow X.R fun i =>
      (productWritten (rowProduct X r)).getD i zeroE == r.coef.getD i zeroE) >>= fun _ =>
    (pure (rowProduct X r) : Ans IndexWeights)) = _
  rw [h1, h2]
  rfl

theorem rowTerms_returns (born : Nat) (array : String) (X : HTree) (r : HRow)
    (hb : rowB X r = true) (hv : rowV X r = true) (acc : Array ReqTerm) :
    ∃ acc', rowTerms born array X acc r = .ok acc' := by
  unfold rowB at hb
  unfold rowV at hv
  rw [Bool.and_eq_true] at hb
  obtain ⟨h1, h2⟩ := hb
  cases h : rowTerms born array X acc r with
  | ok a => exact ⟨a, rfl⟩
  | error e =>
    exfalso
    unfold rowTerms at h
    rw [h1] at h
    cases hf : r.rowForm with
    | false => simp [need, hf, bind, Except.bind, pure, Except.pure] at h
    | true =>
      rw [hf] at h2 hv
      have h2' : rowFormFits X r = true := by simpa using h2
      have hv' : (everyBelow X.R fun i =>
        (productWritten (rowProduct X r)).getD i zeroE == r.coef.getD i zeroE) = true := by
        simpa using hv
      rw [rowWeights_ok X r h2' hv'] at h
      simp [need, hf, bind, Except.bind, pure, Except.pure] at h

/-- The listed arrays: numbers and marks. -/
def termsB (L : LinkCtx) (F : Fork) : Bool :=
  (List.range L.list.nt.size).all fun ti =>
    let X := F.trees.getD ti {}
    arrayLaid L.check.rows.layout (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2 X.R
      X.K && X.rows.all (rowB X)

/-- **A test on values**, over the listed arrays. -/
def termsV (L : LinkCtx) (F : Fork) : Bool :=
  (List.range L.list.nt.size).all fun ti =>
    let X := F.trees.getD ti {}
    X.rows.all (rowV X)

theorem allTerms_returns (L : LinkCtx) (F : Fork) (hb : termsB L F = true)
    (hv : termsV L F = true) : ∃ terms, allTerms L F = .ok terms := by
  unfold allTerms
  refine foldlM_returns _ _ _ fun ti hti acc => ?_
  unfold termsB at hb
  unfold termsV at hv
  have b1 := List.all_eq_true.1 hb ti hti
  have v1 := List.all_eq_true.1 hv ti hti
  simp only [Bool.and_eq_true] at b1
  obtain ⟨b2, b3⟩ := b1
  obtain ⟨r, hr⟩ : ∃ r, (F.trees.getD ti {}).rows.foldlM
      (rowTerms (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2 (F.trees.getD ti {}))
      acc = .ok r := by
    rw [← Array.foldlM_toList]
    refine foldlM_returns _ _ _ fun x hx c => ?_
    have hx' : x ∈ (F.trees.getD ti {}).rows := Array.mem_toList_iff.1 hx
    exact rowTerms_returns _ _ _ x (Array.all_eq_true'.1 b3 x hx')
      (Array.all_eq_true'.1 v1 x hx') c
  refine ⟨r, ?_⟩
  simp only [ans_bind, need_ok, exists_const]
  exact ⟨b2, hr⟩

/-! ## 3 The slots -/

/-- **A test on values**: a slot with a coefficient is filled. -/
def slotsV (F : Fork) : Bool :=
  (List.range F.LS.size).all fun j => isZeroE (F.LS.getD j zeroE) || F.gotF.getD j false

/-- One step of slotsIn. -/
def slotStep (F : Fork) (x : Nat × Array E × E) (l : E) : Ans (Nat × Array E × E) :=
  if isZeroE l then pure (x.1 + 1, x.2.1, x.2.2)
  else do
    need "K9.slot-with-coefficient-filled" (F.gotF.getD x.1 false)
    pure (x.1 + 1, x.2.1.set! x.1 (subE zeroE (mulE l (F.mf.getD x.1 zeroE))),
      addE x.2.2 (mulE l (F.vp.getD x.1 zeroE)))

theorem slots_fold (F : Fork) : ∀ (l : List E) (x : Nat × Array E × E),
    (∀ k (hk : k < l.length), isZeroE l[k] = true ∨ F.gotF.getD (x.1 + k) false = true) →
    ∃ r, l.foldlM (slotStep F) x = .ok r ∧ r.2.1.size = x.2.1.size
  | [], x, _ => ⟨x, rfl, rfl⟩
  | a :: l, x, h => by
    have h0 := h 0 (Nat.succ_pos _)
    have hs : ∃ y, slotStep F x a = .ok y ∧ y.1 = x.1 + 1 ∧ y.2.1.size = x.2.1.size := by
      unfold slotStep
      by_cases hz : isZeroE a = true
      · rw [if_pos hz]
        exact ⟨_, rfl, rfl, rfl⟩
      · rw [if_neg hz]
        have hg : F.gotF.getD x.1 false = true := by
          rcases h0 with h0 | h0
          · exact absurd h0 hz
          · simpa using h0
        refine ⟨(x.1 + 1, x.2.1.set! x.1 (subE zeroE (mulE a (F.mf.getD x.1 zeroE))),
          addE x.2.2 (mulE a (F.vp.getD x.1 zeroE))), ?_, rfl, ?_⟩
        · simp only [ans_bind, need_ok, exists_const]
          exact ⟨hg, rfl⟩
        · simp
    obtain ⟨y, hy, e1, e2⟩ := hs
    obtain ⟨r, hr, e3⟩ := slots_fold F l y fun k hk => by
      have := h (k + 1) (Nat.succ_lt_succ hk)
      rw [e1, show x.1 + 1 + k = x.1 + (k + 1) by omega]
      simpa using this
    refine ⟨r, ?_, e3.trans e2⟩
    rw [List.foldlM_cons]
    show (slotStep F x a >>= fun c => l.foldlM (slotStep F) c) = _
    rw [hy]
    exact hr

theorem slotsIn_returns (F : Fork) (hv : slotsV F = true) :
    ∃ mc, slotsIn F = .ok mc ∧ mc.1.size = F.ns := by
  obtain ⟨r, hr, e⟩ := slots_fold F F.LS.toList (0, Array.replicate F.ns zeroE, F.c0) fun k hk => by
    unfold slotsV at hv
    have hk' : k < F.LS.size := by simpa using hk
    have := List.all_eq_true.1 hv k (List.mem_range.2 hk')
    rw [Bool.or_eq_true] at this
    rcases this with h | h
    · left
      have e : F.LS.getD k zeroE = F.LS.toList[k] := by
        simp [Array.getD, hk']
      rw [← e]
      exact h
    · right
      simpa using h
  refine ⟨r.2, ?_, by simpa using e⟩
  unfold slotsIn
  simp only [ans_bind]
  refine ⟨r, ?_, rfl⟩
  rw [← Array.foldlM_toList]
  exact hr

theorem slots_size (F : Fork) : ∀ (l : List E) (x r : Nat × Array E × E),
    l.foldlM (slotStep F) x = .ok r → r.2.1.size = x.2.1.size
  | [], x, r, h => by
    obtain rfl : x = r := Except.ok.inj h
    rfl
  | a :: l, x, r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨y, hy, hr⟩ := (ans_bind _ _ _).1 h
    have e : y.2.1.size = x.2.1.size := by
      unfold slotStep at hy
      by_cases hz : isZeroE a = true
      · rw [if_pos hz] at hy
        obtain rfl := Except.ok.inj hy
        rfl
      · rw [if_neg hz] at hy
        simp only [ans_bind, need_ok, exists_const] at hy
        obtain rfl := Except.ok.inj hy.2
        simp
    exact (slots_size F l y r hr).trans e

/-- Where slotsIn returns, the coefficients on the mask row are as many as the slots. -/
theorem slotsIn_size (F : Fork) (mc : Array E × E) (h : slotsIn F = .ok mc) :
    mc.1.size = F.ns := by
  unfold slotsIn at h
  simp only [ans_bind] at h
  obtain ⟨r, hr, e⟩ := h
  obtain rfl := Except.ok.inj e
  rw [← Array.foldlM_toList] at hr
  have := slots_size F F.LS.toList _ r hr
  simpa using this

theorem equation_size (L : LinkCtx) (F F' : Fork) (q : Equation)
    (h : equation L F = .ok (q, F')) : q.onMasks.size = F.ns := by
  obtain ⟨-, -, -, terms, mc, -, hm, rfl⟩ := (equation_iff L F F' q).1 h
  exact slotsIn_size _ mc hm

/-! ## 4 The one equation returns -/

theorem equation_returns (L : LinkCtx) (F : Fork) (h1 : eqB L F = true)
    (h2 : termsB L { F with doorShutF := true } = true) (v1 : outsideV L F = true)
    (v2 : termsV L { F with doorShutF := true } = true)
    (v3 : slotsV { F with doorShutF := true } = true) :
    ∃ q, equation L F = .ok (q, { F with doorShutF := true }) ∧ q.onMasks.size = F.ns := by
  obtain ⟨terms, ht⟩ := allTerms_returns L _ h2 v2
  obtain ⟨mc, hm, e⟩ := slotsIn_returns _ v3
  exact ⟨{ terms := terms, onMasks := mc.1, constant := mc.2 },
    (equation_iff L F _ _).2 ⟨rfl, h1, v1, terms, mc, ht, hm, rfl⟩, e⟩

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.allTerms_returns
#print axioms VerifiableInference.Desc.K9.Shape.slotsIn_returns
#print axioms VerifiableInference.Desc.K9.Shape.equation_size
#print axioms VerifiableInference.Desc.K9.Shape.equation_returns
