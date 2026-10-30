-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/PadForms.lean: THE ROW THAT THE BATCHING's DOOR MAKES OF A SEGMENT's ONE EQUATION (`asRow`,
Johnson/Desc/First/Batch/Text.lean) HAS NO COEFFICIENT ON AN ENTRY THAT MASKS AN ANSWER TO A SAMPLE: the test `padB`
(Johnson/Desc/First/Batch/Shape/DoorFits.lean) accepts, FROM TWO FACTS ON PLACES ALONE, whatever the weights, the scalars and the coefficients on the mask
entries are. No value of a challenge is read: where the two facts hold, no draw can make the test refuse.

The row has no terms and no single entries. Its forms are the sums over the blocks of the arrays that the equation's terms name; its
one run, if there is one, lies on the entries 0, 1, …, n − 1 of the segment's mask row.

  `PadsOffBlocks layout f S ts`   for each term of ts, its array a in the layout and the message o that the segment reads for it: each place
                        of o's pad that lies in the main table is an index of that table which no block of a covers
  `PadsBehindMasks f S n`         each place of the pad of the segment's message with the mask row lies, in the mask table, at n or above

  `takeMask_pads`, `takeN_pads`      the taking of mask entries leaves the groups and each message's pad
  `termsRow_blocks`      each form of the row that `termsRow` makes is the sum over the blocks of a term's array, on the message read for it
  `fold_forms_zero`, **`coefficient_forms`**   the coefficient of a row without terms, single entries and runs
  **`coefficient_run`**     one run more, which does not reach the place
  **`padB_of_places`**      `asRow R f q d = .ok y`, a group at g, the two facts at d's statement ⊢ `padB y.2.st g y.1 = true`

Limits. The two facts are premises: shown of no statement here. Nothing on whether `asRow` returns. This file proves no property of a prover
or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.PadTensor
import Johnson.Desc.First.Batch.Shape.DoorFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray ReqLayout)
open VerifiableInference.Desc
open VerifiableInference.Desc.K9 (Ans need there blocksForm termsRow messageNow asRow takeN St Equation)
open VerifiableInference.Desc.K9.Shape (ans_bind need_ok there_ok padB)
open VerifiableInference.Desc.Ground (has takeMaskP)

/-- The pad of message o, as the statement holds it. -/
def padAt (S : Statement) (o : ℕ) : List (Part × ℕ) := ((S.oracles[o]?).map (·.pad)).getD []

/-- **No block of a named array covers a place of the pad of the message that holds it.** -/
def PadsOffBlocks (layout : ReqLayout) (f : ReqFrame) (S : Statement) (ts : List ReqTerm) : Prop :=
  ∀ t ∈ ts, ∀ (a : ReqArray) (o : ℕ),
    ((layout.link[t.born]?).bind fun arrays => arrays.find? fun a => a.name == t.array) = some a →
    messageNow f t.born a.message = some o → ∀ j, (Part.main, j) ∈ padAt S o →
      j < 2 ^ (S.rowBits o .main + S.placeBits o .main) ∧
        ∀ b ∈ a.blocks, laidCovers b (S.rowBits o .main) j = false

/-- **The pad of the message with the mask row lies behind the first n mask entries.** -/
def PadsBehindMasks (f : ReqFrame) (S : Statement) (n : ℕ) : Prop :=
  ∀ m o, ((f.shape.link[f.link]?.map (·.messages)).getD []).findIdx? (fun x => x.shape.maskRows != 0) = some m →
    messageNow f f.link m = some o → ∀ j, (Part.mask, j) ∈ padAt S o → n ≤ j

/-! ## The taking of mask entries -/

variable {X : Type}

theorem takeMask_pads (d : St X) (o : ℕ) (y : ℕ × St X) (h : takeMaskP d o = some y) :
    y.2.st.groups = d.st.groups ∧ ∀ o', padAt y.2.st o' = padAt d.st o' := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨rfl, fun o' => ?_⟩
    unfold padAt
    show (((d.st.oracles.modify o _)[o']?).map (·.pad)).getD [] = _
    rw [Array.getElem?_modify]
    split
    · rename_i e
      subst e
      cases d.st.oracles[o]? <;> rfl
    · rfl
  · exact nomatch h

theorem takeN_pads (o : ℕ) : ∀ (n : ℕ) (d : St X) (acc : List ℕ) (y : List ℕ × St X),
    takeN o n d acc = .ok y → y.2.st.groups = d.st.groups ∧ ∀ o', padAt y.2.st o' = padAt d.st o'
  | 0, d, acc, y, h => by
    obtain rfl : (acc.reverse, d) = y := Except.ok.inj h
    exact ⟨rfl, fun _ => rfl⟩
  | n + 1, d, acc, y, h => by
    have h' : (there "K9.mask-entry-free" (takeMaskP d o) >>= fun x =>
      takeN o n x.2 (x.1 :: acc)) = .ok y := h
    obtain ⟨x, hx, hy⟩ := (ans_bind _ _ _).1 h'
    obtain ⟨a1, a2⟩ := takeMask_pads d o x ((there_ok _ _ _).1 hx)
    obtain ⟨b1, b2⟩ := takeN_pads o n x.2 _ y hy
    exact ⟨b1.trans a1, fun o' => (b2 o').trans (a2 o')⟩

/-! ## The forms of the row -/

/-- **Each form is the sum over the blocks of a term's array.** -/
theorem termsRow_blocks (layout : ReqLayout) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row row' : OnBytes.Row), termsRow layout f S ts row = .ok row' →
      row'.terms = row.terms ∧ row'.units = row.units ∧ row'.runs = row.runs ∧
        ∀ x ∈ row'.forms, x ∈ row.forms ∨ ∃ t ∈ ts, ∃ a : ReqArray,
          ((layout.link[t.born]?).bind fun arrays => arrays.find? fun a => a.name == t.array) = some a ∧
          messageNow f t.born a.message = some x.oracle ∧
          blocksForm a.blocks (S.rowBits x.oracle .main) (S.placeBits x.oracle .main) t.onRows t.onColumns
            t.scale = .ok x.c
  | [], row, row', h => by
    obtain rfl : row = row' := Except.ok.inj h
    exact ⟨rfl, rfl, rfl, fun x hx => Or.inl hx⟩
  | t :: ts, row, row', h => by
    unfold termsRow at h
    simp only [ans_bind, there_ok] at h
    obtain ⟨a, ha, o, ho, c, hc, h⟩ := h
    obtain ⟨e1, e2, e3, e4⟩ := termsRow_blocks layout f S ts (row.addForm o c) row' h
    refine ⟨e1, e2, e3, fun x hx => ?_⟩
    rcases e4 x hx with hx | ⟨t', ht', r⟩
    · have hx' : x ∈ row.forms.push ⟨o, c⟩ := hx
      rcases Array.mem_push.1 hx' with hx' | rfl
      · exact Or.inl hx'
      · exact Or.inr ⟨t, List.mem_cons_self, a, ha, ho, hc⟩
    · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', r⟩

/-! ## The coefficient -/

theorem fold_forms_zero (o : ℕ) (part : Part) (j : ℕ) : ∀ l : List MainForm,
    (∀ x ∈ l, (x.oracle == o && part == .main) = true → x.c.entry j = zeroE) →
    l.foldl (fun s (f : MainForm) => if f.oracle == o && part == .main then addE s (f.c.entry j) else s) zeroE =
      zeroE
  | [], _ => rfl
  | x :: l, h => by
    rw [List.foldl_cons]
    by_cases hc : (x.oracle == o && part == .main) = true
    · rw [if_pos hc, h x (by simp) hc, addE_zero_zero']
      exact fold_forms_zero o part j l fun y hy => h y (List.mem_cons_of_mem _ hy)
    · rw [if_neg hc]
      exact fold_forms_zero o part j l fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- **A row of forms alone.** -/
theorem coefficient_forms (r : OnBytes.Row) (o : ℕ) (part : Part) (j : ℕ) (h1 : r.terms = #[]) (h2 : r.units = #[])
    (h3 : r.runs = #[])
    (h4 : ∀ x ∈ r.forms, (x.oracle == o && part == .main) = true → x.c.entry j = zeroE) :
    r.coefficient o part j = zeroE := by
  unfold OnBytes.Row.coefficient
  rw [h1, h2, h3]
  simp only [Array.foldl_empty]
  rw [← Array.foldl_toList]
  exact fold_forms_zero o part j _ fun x hx => h4 x (Array.mem_toList_iff.1 hx)

/-- **One run more, which does not reach the place.** -/
theorem coefficient_run (r : OnBytes.Row) (w : Run) (o : ℕ) (part : Part) (j : ℕ) (h1 : r.terms = #[])
    (h2 : r.units = #[]) (h3 : r.runs = #[w])
    (hw : (w.oracle == o && w.part == part && decide (w.first ≤ j) && decide (0 < w.step) &&
      (j - w.first) % w.step == 0 && decide ((j - w.first) / w.step < w.coeffs.size)) = false)
    (h4 : ∀ x ∈ r.forms, (x.oracle == o && part == .main) = true → x.c.entry j = zeroE) :
    r.coefficient o part j = zeroE := by
  unfold OnBytes.Row.coefficient
  rw [h1, h2, h3]
  simp only [Array.foldl_empty]
  have e : (#[w] : Array Run).foldl (fun s (w : Run) =>
      if w.oracle == o && w.part == part && w.first ≤ j && 0 < w.step &&
          (j - w.first) % w.step == 0 && (j - w.first) / w.step < w.coeffs.size then
        addE s (w.coeffs.get ((j - w.first) / w.step)) else s) zeroE = zeroE := by
    rw [← Array.foldl_toList]
    show (if _ then _ else zeroE) = zeroE
    rw [if_neg (by rw [hw]; exact Bool.false_ne_true)]
  rw [e, ← Array.foldl_toList]
  exact fold_forms_zero o part j _ fun x hx => h4 x (Array.mem_toList_iff.1 hx)

/-! ## The test -/

/-- **The door's row has no coefficient on a pad.** -/
theorem padB_of_places (R : ReqRows) (f : ReqFrame) (q : Equation) (d : St X) (y : OnBytes.Row × St X)
    (hy : asRow R f q d = .ok y) (g : ℕ) (hg : (d.st.groups[g]?).isSome = true)
    (hb : PadsOffBlocks R.layout f d.st q.terms.toList) (hm : PadsBehindMasks f d.st q.onMasks.size) :
    padB y.2.st g y.1 = true := by
  unfold asRow at hy
  simp only [ans_bind] at hy
  obtain ⟨row, hrow, hy⟩ := hy
  obtain ⟨t1, t2, t3, t4⟩ := termsRow_blocks R.layout f d.st q.terms.toList {} row hrow
  -- each form has the entry 0 at each place of its message's pad in the main table
  have forms : ∀ o j, (Part.main, j) ∈ padAt d.st o → ∀ x ∈ row.forms, x.oracle = o → x.c.entry j = zeroE := by
    intro o j hj x hx ho
    rcases t4 x hx with hx | ⟨t, ht, a, ha, hmsg, hc⟩
    · exact absurd hx (by simp)
    · subst ho
      obtain ⟨k1, k2⟩ := hb t ht a x.oracle ha hmsg j hj
      exact blocksForm_off _ _ _ _ _ _ _ hc k1 k2
  have formsAt : ∀ o (p : Part × ℕ), p ∈ padAt d.st o → ∀ x ∈ row.forms,
      (x.oracle == o && p.1 == .main) = true → x.c.entry p.2 = zeroE := by
    intro o p hp x hx hc
    rw [Bool.and_eq_true] at hc
    obtain ⟨pp, j⟩ := p
    obtain rfl : pp = Part.main := beq_iff_eq.1 hc.2
    exact forms o j hp x hx (beq_iff_eq.1 hc.1)
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 hg
  split at hy
  · -- no coefficient on a mask entry
    obtain rfl := Except.ok.inj hy
    unfold padB
    show has d.st.groups[g]? _ = true
    rw [hG]
    show (G.members.all fun o => (padAt d.st o).all fun p => Own.allZero (OnBytes.Row.coefficient _ o p.1 p.2)) = true
    refine Array.all_eq_true'.2 fun o _ => List.all_eq_true.2 fun p hp => ?_
    have k := coefficient_forms ({ row with target := subE zeroE q.constant } : OnBytes.Row) o p.1 p.2 t1 t2 t3
      (formsAt o p hp)
    show Own.allZero (OnBytes.Row.coefficient { row with target := subE zeroE q.constant } o p.1 p.2) = true
    rw [k]
    rfl
  · simp only [ans_bind, need_ok, there_ok, exists_const] at hy
    obtain ⟨m, hm1, -, o₁, ho₁, x, hx, -, hy⟩ := hy
    obtain rfl := Except.ok.inj hy
    obtain ⟨g1, g2⟩ := takeN_pads o₁ _ d [] x hx
    unfold padB
    show has x.2.st.groups[g]? _ = true
    rw [g1, hG]
    show (G.members.all fun o => (padAt x.2.st o).all fun p => Own.allZero (OnBytes.Row.coefficient _ o p.1 p.2)) = true
    refine Array.all_eq_true'.2 fun o _ => List.all_eq_true.2 fun p hp => ?_
    rw [g2 o] at hp
    have hr : ({ row.addRun o₁ .mask 0 1 (.own q.onMasks) with target := subE zeroE q.constant } : OnBytes.Row).runs =
        #[⟨o₁, .mask, 0, 1, .own q.onMasks⟩] := by
      show row.runs.push _ = _
      rw [t3]
      rfl
    have k := coefficient_run
      ({ row.addRun o₁ .mask 0 1 (.own q.onMasks) with target := subE zeroE q.constant } : OnBytes.Row)
      ⟨o₁, .mask, 0, 1, .own q.onMasks⟩ o p.1 p.2 t1 t2 hr ?_ (formsAt o p hp)
    · show Own.allZero (OnBytes.Row.coefficient
        { row.addRun o₁ .mask 0 1 (.own q.onMasks) with target := subE zeroE q.constant } o p.1 p.2) = true
      rw [k]
      rfl
    · -- the run does not reach the place
      by_cases c1 : (o₁ == o && Part.mask == p.1) = true
      · rw [Bool.and_eq_true] at c1
        obtain rfl : o₁ = o := beq_iff_eq.1 c1.1
        obtain ⟨pp, j⟩ := p
        obtain rfl : Part.mask = pp := beq_iff_eq.1 c1.2
        have hn := hm m o₁ hm1 ho₁ j hp
        have : decide ((j - 0) / 1 < (Coeffs.own q.onMasks).size) = false := by
          refine decide_eq_false ?_
          show ¬ (j - 0) / 1 < q.onMasks.size
          rw [Nat.sub_zero, Nat.div_one]
          omega
        show (_ && decide ((j - 0) / 1 < (Coeffs.own q.onMasks).size)) = false
        rw [this, Bool.and_false]
      · have c1' : (o₁ == o && Part.mask == p.1) = false := by simpa using c1
        show ((((o₁ == o && Part.mask == p.1) && _) && _) && _ && _) = false
        rw [c1']
        rfl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.takeMask_pads
#print axioms ProofFile.Honest.K9.takeN_pads
#print axioms ProofFile.Honest.K9.termsRow_blocks
#print axioms ProofFile.Honest.K9.fold_forms_zero
#print axioms ProofFile.Honest.K9.coefficient_forms
#print axioms ProofFile.Honest.K9.coefficient_run
#print axioms ProofFile.Honest.K9.padB_of_places
