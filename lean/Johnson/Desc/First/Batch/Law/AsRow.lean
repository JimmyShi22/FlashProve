-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/AsRow.lean
(kind K9's soundness lemma, (T2b)): THEOREMS: the row that K9.asRow makes of the one
equation.
  equation_k9   every term of an equation that K9.equation makes has a product form on the rows and
                a written-out vector on the columns (K9Term).
  asRow_coef    **(T2b), entry by entry**: on each entry of each main table the sum of what the
                terms put there (termAt, Law/Laid.lean); on the entries 0, 1, .. of the segment's
                mask row the equation's coefficients, on no other mask entry anything; the target is
                minus the constant.
  dataOf        THE DATA THAT TABLES HOLD, read by the layout: element (i, c) of an array is the sum
                of the table's entries that the layout's blocks give to (i, c).
  termValue_tab a term's value on these data is its coefficients applied to the table.
  asRow_sum     **(T2b)**: the row applied to the tables (rowSum), less its target, is the left side
                of the one equation on these data (eqValue).
THE PREMISES of asRow_sum are the structure RowPremises: inside (the blocks lie inside their arrays
and are as large in the table as in the array: clauses of the test reqLayoutOk on a layout) · sent,
sentMask (the oracle messages in which the equation's terms and masks lie are below N) · room (the
mask row has an entry for each coefficient). They speak of public data. Law/DoorFacts.lean: where
K9.door returns, its own tests give the last three. NOT PROVED HERE: that under a lawful layout just
one entry of the table is given to each element (then dataOf's sum is that entry): the law holds
without it.

-/
import Johnson.Desc.First.Batch.Law.Laid
import Johnson.Desc.First.Batch.Law.AtBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray)
open VerifiableInference.Desc.K9 (Ans Equation equation allTerms rowTerms asRow St)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## K9's terms have a product form on the rows and a written-out vector on the columns -/

theorem foldlM_invE {α σ : Type} (f : σ → α → Ans σ) (P : σ → Prop)
    (H : ∀ s a s', P s → f s a = .ok s' → P s') :
    ∀ (l : List α) (s s' : σ), P s → l.foldlM f s = .ok s' → P s'
  | [], s, s', hp, h => by
    rw [List.foldlM_nil] at h
    have e : s = s' := Except.ok.inj h
    rw [← e]
    exact hp
  | a :: l, s, s', hp, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t, ht, h2⟩ := ok_bind h
    exact foldlM_invE f P H l t s' (H s a t hp ht) h2

def AllK9 (ts : Array ReqTerm) : Prop := ∀ t ∈ ts.toList, K9Term t

theorem rowTerms_k9 (born : Nat) (array : String) (X : HTree) (acc acc' : Array ReqTerm) (r : HRow)
    (hp : AllK9 acc) (h : rowTerms born array X acc r = .ok acc') : AllK9 acc' := by
  unfold rowTerms at h
  obtain ⟨_, _, h⟩ := ok_bind h
  by_cases hf : r.rowForm = true
  · simp only [if_pos hf] at h
    obtain ⟨w, hw, h⟩ := ok_bind h
    have e := Except.ok.inj h
    have hwv : w.values = none := by
      unfold K9.rowWeights at hw
      obtain ⟨_, _, hw⟩ := ok_bind hw
      obtain ⟨_, _, hw⟩ := ok_bind hw
      rw [← Except.ok.inj hw]
      rfl
    rw [← e]
    intro t ht
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hp t ht
    · exact ⟨hwv, _, rfl⟩
  · simp only [if_neg hf] at h
    have e := Except.ok.inj h
    rw [← e]
    intro t ht
    rw [foldl_push_list, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨i, _, rfl⟩
    · exact hp t ht
    · exact ⟨rfl, _, rfl⟩

theorem allTerms_k9 (L : LinkCtx) (F : Fork) (terms : Array ReqTerm)
    (h : allTerms L F = .ok terms) : AllK9 terms := by
  unfold allTerms at h
  refine foldlM_invE _ AllK9 (fun s ti s' hp hs => ?_) _ _ _ (by intro t ht; simp at ht) h
  rcases hba : L.arrayOf.getD ti (0, "") with ⟨born, array⟩
  rw [hba] at hs
  obtain ⟨_, _, hs⟩ := ok_bind hs
  rw [← Array.foldlM_toList] at hs
  exact foldlM_invE _ AllK9 (fun a r a' hpa hr => rowTerms_k9 born array _ a a' r hpa hr) _ _ _ hp
    hs

theorem equation_k9 (L : LinkCtx) (F G : Fork) (q : Equation) (h : equation L F = .ok (q, G)) :
    AllK9 q.terms := by
  unfold equation at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨terms, hT, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨mc, _, h⟩ := ok_bind h
  have e : q = { terms := terms, onMasks := mc.1, constant := mc.2 } :=
    (congrArg Prod.fst (Except.ok.inj h)).symm
  rw [e]
  exact allTerms_k9 L _ terms hT

/-! ## The row, entry by entry -/

/-- The oracle message that holds the segment's mask row: the first of the segment's messages with
mask rows. -/
def maskOracle (f : ReqFrame) : Option Nat :=
  (((f.shape.link[f.link]?.map (·.messages)).getD []).findIdx? fun x =>
    x.shape.maskRows != 0).bind fun m => f.whereIs f.link m

/-- **(T2b), entry by entry.** The row that K9.asRow makes has, on each entry of each main table,
the sum of what the terms put there; on the entries 0, 1, .. of the segment's mask row the
equation's coefficients, and nothing on any other mask entry; and the target is minus the constant.
-/
theorem asRow_coef {X : Type} (Rr : ReqRows) (f : ReqFrame) (q : Equation) (d d' : St X)
    (row : OnBytes.Row) (hk : AllK9 q.terms) (h : asRow Rr f q d = .ok (row, d')) :
    (∀ o J, ρ.val (row.coefficient o .main J) =
      (q.terms.toList.map fun t => termAt ρ Rr f d.st t o J).sum) ∧
    (∀ o j, ρ.val (row.coefficient o .mask j) =
      if maskOracle f = some o ∧ j < q.onMasks.size then ρ.val (q.onMasks.getD j zeroE) else 0) ∧
    ρ.val row.target = - ρ.val q.constant ∧
    (∃ row0, Rr.addTerms f d.st q.terms.toList {} = some row0) ∧
    (q.onMasks.isEmpty = false → (maskOracle f).isSome = true) := by
  unfold asRow at h
  obtain ⟨row0, h0, h⟩ := ok_bind h
  have h0' := termsRow_ok _ _ _ _ _ _ h0
  obtain ⟨c1, c2⟩ := addTerms_coef ρ Rr f d.st _ {} row0 hk h0'
  by_cases he : q.onMasks.isEmpty = true
  · simp only [he, if_true] at h
    have e1 : row = { row0 with target := subE zeroE q.constant } :=
      (congrArg Prod.fst (Except.ok.inj h)).symm
    rw [e1]
    refine ⟨fun o J => ?_, fun o j => ?_, ?_, ⟨row0, h0'⟩, fun hx => by simp [he] at hx⟩
    · show ρ.val (row0.coefficient o .main J) = _
      rw [c1, coef_empty, zero_add]
    · show ρ.val (row0.coefficient o .mask j) = _
      have hz : q.onMasks.size = 0 := by simpa using he
      rw [c2, coef_empty]
      simp [hz]
    · show ρ.val (subE zeroE q.constant) = _
      rw [ρ.sub, ρ.zero, zero_sub]
  · simp only [he, Bool.false_eq_true, if_false] at h
    obtain ⟨m, hm, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨o', ho, h⟩ := ok_bind h
    obtain ⟨x, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    have e1 : row = { row0.addRun o' .mask 0 1 (.own q.onMasks) with
        target := subE zeroE q.constant } := (congrArg Prod.fst (Except.ok.inj h)).symm
    have hmo : maskOracle f = some o' := by
      unfold maskOracle
      rw [there_ok hm]
      exact there_ok ho
    rw [e1]
    refine ⟨fun o J => ?_, fun o j => ?_, ?_, ⟨row0, h0'⟩, fun _ => by simp [hmo]⟩
    · show ρ.val ((row0.addRun o' .mask 0 1 (.own q.onMasks)).coefficient o .main J) = _
      rw [coef_addRun, c1, coef_empty, zero_add]
      simp
    · show ρ.val ((row0.addRun o' .mask 0 1 (.own q.onMasks)).coefficient o .mask j) = _
      rw [coef_addRun, c2, coef_empty, zero_add, hmo]
      by_cases hoo : o' = o
      · simp [hoo, Run.val, Coeffs.size, Coeffs.get, Nat.mod_one]
      · simp [hoo]
    · show ρ.val (subE zeroE q.constant) = _
      rw [ρ.sub, ρ.zero, zero_sub]

/-! ## The data behind the tables -/

/-- The element (i, c) of an array, as far as one block holds it: the sum of the table's entries
that the block's layout gives to (i, c). (Meant: one entry, or none. Not proved here.) At a block
that is not aligned, or has more row bits than the table, the sum has no meaning; ReqRows.addTerms
returns at no such block (laidBlockOk). -/
def cellOfBlock (b : LaidBlock) (R P : Nat) (tab : Nat → K) (i c : Nat) : K :=
  ∑ J ∈ Finset.range (2 ^ (R + P)), inBlock b R P J *
    (if b.firstI + iOf b (xOf b R J) = i ∧ b.firstC + cOf b (xOf b R J) = c then tab J else 0)

/-- **The data that tables hold**, read by the layout. tab o part J: entry J of a table of the
oracle message number o. -/
def dataOf (Rr : ReqRows) (f : ReqFrame) (S : Statement) (tab : Nat → OnBytes.Part → Nat → K) :
    Bound K where
  cell := fun born name i c =>
    match reqArray Rr.layout born name with
    | none => 0
    | some a =>
      match f.whereIs born a.message with
      | none => 0
      | some o =>
        (a.blocks.map fun b =>
          cellOfBlock b (S.rowBits o .main) (S.placeBits o .main) (tab o .main) i c).sum
  mask := fun j =>
    match maskOracle f with
    | some o => tab o .mask j
    | none => 0

/-- A block is as large in the table as in its array, and lies inside the array: two clauses of the
test on a layout (reqLayoutOk: reqArrayOk, laidMatrixOk). -/
structure Inside (a : ReqArray) (b : LaidBlock) : Prop where
  hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC
  inI : b.firstI + 2 ^ b.bitsI ≤ a.sizeI
  inC : b.firstC + 2 ^ b.bitsC ≤ a.sizeC

theorem block_sum (b : LaidBlock) (R P : Nat) (w : Nat → Nat → K) (tab : Nat → K) (sI sC : Nat)
    (hI : ∀ J, b.firstI + iOf b (xOf b R J) < sI) (hC : ∀ J, b.firstC + cOf b (xOf b R J) < sC) :
    ∑ i ∈ Finset.range sI, ∑ c ∈ Finset.range sC, w i c * cellOfBlock b R P tab i c =
      ∑ J ∈ Finset.range (2 ^ (R + P)), inBlock b R P J *
        w (b.firstI + iOf b (xOf b R J)) (b.firstC + cOf b (xOf b R J)) * tab J := by
  unfold cellOfBlock
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.sum_eq_single (b.firstI + iOf b (xOf b R J))]
  · rw [Finset.sum_eq_single (b.firstC + cOf b (xOf b R J))]
    · simp only [and_self, if_true]
      ring
    · intro c _ hne
      simp [Ne.symm hne]
    · intro hn
      exact absurd (Finset.mem_range.mpr (hC J)) hn
  · intro i _ hne
    apply Finset.sum_eq_zero
    intro c _
    simp [Ne.symm hne]
  · intro hn
    exact absurd (Finset.mem_range.mpr (hI J)) hn

theorem sum2_list {β : Type} (sI sC : Nat) (w : Nat → Nat → K) (l : List β)
    (g : β → Nat → Nat → K) :
    ∑ i ∈ Finset.range sI, ∑ c ∈ Finset.range sC, w i c * (l.map fun b => g b i c).sum =
      (l.map fun b => ∑ i ∈ Finset.range sI, ∑ c ∈ Finset.range sC, w i c * g b i c).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]

theorem sum_list_mul {β : Type} (s : Finset ℕ) (l : List β) (g : β → ℕ → K) (tab : ℕ → K) :
    ∑ J ∈ s, (l.map fun b => g b J).sum * tab J = (l.map fun b => ∑ J ∈ s, g b J * tab J).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih]

/-- **A term's value on the data that the tables hold is its coefficients applied to the table.** -/
theorem termValue_tab (Rr : ReqRows) (f : ReqFrame) (S : Statement)
    (tab : Nat → OnBytes.Part → Nat → K) (dims : Nat → String → Nat × Nat) (t : ReqTerm)
    (a : ReqArray) (o : Nat) (ha : reqArray Rr.layout t.born t.array = some a)
    (ho : f.whereIs t.born a.message = some o) (hd : dims t.born t.array = (a.sizeI, a.sizeC))
    (hin : ∀ b ∈ a.blocks, Inside a b) :
    termValue ρ dims (dataOf Rr f S tab) t =
      ∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
        termAt ρ Rr f S t o J * tab o .main J := by
  simp only [termValue, termAt, dataOf, ha, ho, hd, if_true]
  rw [sum2_list a.sizeI a.sizeC
    (fun i c => ρ.val t.scale * weightAt ρ t.onRows i * weightAt ρ t.onColumns c), sum_list_mul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  have F := hin b hb
  have hx : ∀ J, xOf b (S.rowBits o .main) J < 2 ^ (b.bitsI + b.bitsC) := fun J => by
    rw [← F.hs, Nat.add_comm]
    exact xOf_lt b _ J
  rw [block_sum b _ _ _ _ a.sizeI a.sizeC
    (fun J => Nat.lt_of_lt_of_le (Nat.add_lt_add_left (iOf_lt b _ (hx J)) _) F.inI)
    (fun J => Nat.lt_of_lt_of_le (Nat.add_lt_add_left (cOf_lt b _ (hx J)) _) F.inC)]
  apply Finset.sum_congr rfl
  intro J _
  unfold laidVal
  ring

theorem addTerms_some (Rr : ReqRows) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row row' : OnBytes.Row), Rr.addTerms f S ts row = some row' →
      ∀ t ∈ ts, ∃ a o, reqArray Rr.layout t.born t.array = some a ∧
        f.whereIs t.born a.message = some o
  | [], _, _, _ => by simp
  | t :: ts, row, row', h => by
    rw [ReqRows.addTerms] at h
    obtain ⟨a, ha, h⟩ := some_bind h
    obtain ⟨o', ho, h⟩ := some_bind h
    obtain ⟨c, _, h⟩ := some_bind h
    intro t' ht'
    rcases List.mem_cons.mp ht' with rfl | ht''
    · exact ⟨a, o', ha, ho⟩
    · exact addTerms_some Rr f S ts _ row' h t' ht''

theorem dims_reqArray (c : ChainCheck) (born : Nat) (name : String) (a : ReqArray)
    (h : reqArray c.rows.layout born name = some a) : dimsOf c born name = (a.sizeI, a.sizeC) := by
  unfold reqArray at h
  obtain ⟨arrays, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  unfold dimsOf
  have e : c.rows.layout.link.getD born [] = arrays := by
    rw [List.getD_eq_getElem?_getD, h1, Option.getD_some]
  rw [e, h2]

/-! ## The row applied to the tables -/

/-- A row's coefficients applied to the tables of the oracle messages 0, .., N - 1. -/
def rowSum (S : Statement) (N : Nat) (tab : Nat → OnBytes.Part → Nat → K) (row : OnBytes.Row) : K :=
  ∑ o ∈ Finset.range N,
    ((∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
        ρ.val (row.coefficient o .main J) * tab o .main J) +
      ∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
        ρ.val (row.coefficient o .mask j) * tab o .mask j)

/-- The premises of (T2b), by name: public facts on the layout, the frame and the statement. -/
structure RowPremises (c : ChainCheck) (S : Statement) (N : Nat) (q : Equation) : Prop where
  /-- the layout's blocks lie inside their arrays (clauses of reqLayoutOk) -/
  inside : ∀ born name a, reqArray c.rows.layout born name = some a → ∀ b ∈ a.blocks, Inside a b
  /-- the oracle message that holds a term's array is one of the first N -/
  sent : ∀ t ∈ q.terms.toList, ∀ a o, reqArray c.rows.layout t.born t.array = some a →
    c.frame.whereIs t.born a.message = some o → o < N
  /-- so is the one that holds the segment's mask row, if the equation has coefficients on it -/
  sentMask : ∀ o, q.onMasks.isEmpty = false → maskOracle c.frame = some o → o < N
  /-- the mask row has an entry for each coefficient -/
  room : ∀ o, maskOracle c.frame = some o →
    q.onMasks.size ≤ 2 ^ (S.rowBits o .mask + S.placeBits o .mask)

theorem sum_list_comm {β : Type} (s : Finset ℕ) (l : List β) (g : β → ℕ → K) :
    ∑ o ∈ s, (l.map fun t => g t o).sum = (l.map fun t => ∑ o ∈ s, g t o).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- **(T2b).** The row that K9.asRow makes, applied to the tables, less its target, is the left side
of the one equation on the data that the tables hold. -/
theorem asRow_sum {X : Type} (c : ChainCheck) (q : Equation) (d d' : St X) (row : OnBytes.Row)
    (N : Nat) (tab : Nat → OnBytes.Part → Nat → K) (hk : AllK9 q.terms)
    (P : RowPremises c d.st N q) (h : asRow c.rows c.frame q d = .ok (row, d')) :
    rowSum ρ d.st N tab row - ρ.val row.target =
      eqValue ρ (dimsOf c) (dataOf c.rows c.frame d.st tab) q := by
  obtain ⟨c1, c2, c3, ⟨row0, h0⟩, c5⟩ := asRow_coef ρ c.rows c.frame q d d' row hk h
  have hsome := addTerms_some c.rows c.frame d.st _ _ _ h0
  unfold rowSum eqValue
  rw [Finset.sum_add_distrib, c3, sub_neg_eq_add]
  congr 1
  congr 1
  · -- the main tables
    simp only [c1]
    simp only [sum_list_mul]
    rw [sum_list_comm]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    obtain ⟨a, o, ha, ho⟩ := hsome t ht
    rw [termValue_tab ρ c.rows c.frame d.st tab (dimsOf c) t a o ha ho
      (dims_reqArray c _ _ a ha) (P.inside _ _ a ha)]
    rw [Finset.sum_eq_single o]
    · intro o' _ hne
      apply Finset.sum_eq_zero
      intro J _
      simp only [termAt, ha, ho, if_neg (Ne.symm hne), zero_mul]
    · intro hn
      exact absurd (Finset.mem_range.mpr (P.sent t ht a o ha ho)) hn
  · -- the mask tables
    simp only [c2]
    unfold maskValue
    rw [sumFrom_range _ zeroE, Array.length_toList]
    by_cases he : q.onMasks.isEmpty = true
    · have hz : q.onMasks.size = 0 := by simpa using he
      simp [hz]
    · have he' : q.onMasks.isEmpty = false := by simpa using he
      obtain ⟨om, hom⟩ := Option.isSome_iff_exists.mp (c5 he')
      rw [Finset.sum_eq_single om]
      · rw [← Finset.sum_subset (Finset.range_subset_range.mpr (P.room om hom))]
        · apply Finset.sum_congr rfl
          intro j hj
          simp only [hom, true_and, if_pos (Finset.mem_range.mp hj), Nat.zero_add, toList_getD,
            dataOf]
        · intro j _ hj
          have hj' : ¬ j < q.onMasks.size := fun hlt => hj (Finset.mem_range.mpr hlt)
          simp [hj']
      · intro o' _ hne
        apply Finset.sum_eq_zero
        intro j _
        have hno : ¬ (maskOracle c.frame = some o') := by
          rw [hom]
          intro hx
          exact hne (Option.some.inj hx).symm
        simp [hno]
      · intro hn
        exact absurd (Finset.mem_range.mpr (P.sentMask om he' hom)) hn

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.equation_k9
#print axioms VerifiableInference.Desc.K9L.asRow_coef
#print axioms VerifiableInference.Desc.K9L.termValue_tab
#print axioms VerifiableInference.Desc.K9L.asRow_sum
