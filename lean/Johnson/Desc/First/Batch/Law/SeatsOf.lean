-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/SeatsOf.lean: WHERE THE ROW THAT THE ONE EQUATION's STEP MAKES HAS A
WEIGHT, THE ORACLE MESSAGE IS SEATED IN THE SEGMENT's GROUP: from the promise's public test on the
ledger (`totalIn`, Johnson/Desc/First/Batch/FormsIn.lean) at the state in front of the step.
Theorems.
Why. The one accessor of tables (`tabQ`, Johnson/Desc/Sound/FormsQ.lean) reads 0 at a message that
the book seats nowhere in the group; `RowInside` (RowClamp.lean) and `InsideAt` speak only where a
seat is there. So that a seat IS there, wherever the row weighs, is needed beside them.
  `foldlM_invM`, `rowTerms_names`, `TermsFrom`, `allTerms_from`, `equation_from`: every term of the
    one equation names an array of the link's list, at a number below the list's length; the list of
    names is as long; the ledger has at least as many arrays (two of the equation's own guards).
  `seatAt_step`: **behind a yes of the one equation's step: a weight other than 0 of the group's
    last row on the message o gives a seat of own for o in the book.** On a main table by
    `termAt_ne` (RowInsideOf.lean) and the test's "every array of the ledger is found by the frame
    and seated"; on a mask table by its "the mask row's message is seated". `seats_first`: so
    whatever seat the book gives o is of own.
Limits. The test is asked at the ONE state in front of the step; it is shown of no state here. NOT
SAID: that a member of the plan's list sits at that seat, or with which shape. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.RowInsideOf
import Johnson.Desc.First.Batch.FormsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray)
open VerifiableInference.Desc.K9 (atS Ans Equation equation allTerms rowTerms door asRow seatAt
  arrayIn arrayIn_some maskSeat maskAt ledgerIn totalIn)
open VerifiableInference.Desc.First (S)

/-! ## 1 Whose arrays the one equation's terms name -/

/-- An invariant along a fold that may refuse, the element in hand being of the list. -/
theorem foldlM_invM {α σ : Type} (f : σ → α → Ans σ) (P : σ → Prop) :
    ∀ (l : List α) (s s' : σ), (∀ s a s', a ∈ l → P s → f s a = .ok s' → P s') → P s →
      l.foldlM f s = .ok s' → P s'
  | [], s, s', _, hp, h => by
    rw [List.foldlM_nil] at h
    have e : s = s' := Except.ok.inj h
    rw [← e]
    exact hp
  | a :: l, s, s', H, hp, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t, ht, h2⟩ := ok_bind h
    exact foldlM_invM f P l t s' (fun s a s' ha => H s a s' (List.mem_cons_of_mem _ ha))
      (H s a t (List.mem_cons_self ..) hp ht) h2

/-- One virtual row's terms name the array that is handed in. -/
theorem rowTerms_names (Q : ℕ → String → Prop) (born : ℕ) (array : String) (X : HTree)
    (acc acc' : Array ReqTerm) (r : HRow) (hp : ∀ t ∈ acc.toList, Q t.born t.array)
    (hq : Q born array) (h : rowTerms born array X acc r = .ok acc') :
    ∀ t ∈ acc'.toList, Q t.born t.array := by
  unfold rowTerms at h
  obtain ⟨_, _, h⟩ := ok_bind h
  by_cases hf : r.rowForm = true
  · simp only [if_pos hf] at h
    obtain ⟨w, _, h⟩ := ok_bind h
    rw [← Except.ok.inj h]
    intro t ht
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hp t ht
    · exact hq
  · simp only [if_neg hf] at h
    rw [← Except.ok.inj h]
    intro t ht
    rw [foldl_push_list, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨i, _, rfl⟩
    · exact hp t ht
    · exact hq

/-- Every term names an array of the link's list, at a number below the list's length. -/
def TermsFrom (L : LinkCtx) (terms : Array ReqTerm) : Prop :=
  ∀ t ∈ terms.toList, ∃ ti, ti < L.list.nt.size ∧ L.arrayOf.getD ti (0, "") = (t.born, t.array)

theorem allTerms_from (L : LinkCtx) (F : Fork) (terms : Array ReqTerm)
    (h : allTerms L F = .ok terms) : TermsFrom L terms := by
  unfold allTerms at h
  refine foldlM_invM _ (TermsFrom L) _ _ _ (fun s ti s' hti hp hs => ?_)
    (by intro t ht; simp at ht) h
  rcases hba : L.arrayOf.getD ti (0, "") with ⟨born, array⟩
  rw [hba] at hs
  obtain ⟨_, _, hs⟩ := ok_bind hs
  rw [← Array.foldlM_toList] at hs
  exact foldlM_invE _ (TermsFrom L) (fun a r a' hpa hr =>
    rowTerms_names (fun b n => ∃ ti, ti < L.list.nt.size ∧ L.arrayOf.getD ti (0, "") = (b, n))
      born array _ a a' r hpa ⟨ti, List.mem_range.1 hti, hba⟩ hr) _ _ _ hp hs

/-- **The one equation's terms, and two of its guards.** -/
theorem equation_from (L : LinkCtx) (F G : Fork) (q : Equation) (h : equation L F = .ok (q, G)) :
    TermsFrom L q.terms ∧ L.arrayOf.size = L.list.nt.size ∧ L.list.nt.size ≤ F.trees.size := by
  unfold equation at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, g1, h⟩ := ok_bind h
  obtain ⟨_, g2, h⟩ := ok_bind h
  obtain ⟨terms, hT, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨mc, _, h⟩ := ok_bind h
  have e : q = { terms := terms, onMasks := mc.1, constant := mc.2 } :=
    (congrArg Prod.fst (Except.ok.inj h)).symm
  rw [e]
  exact ⟨allTerms_from L _ terms hT, by simpa using need_ok g1, by simpa using need_ok g2⟩

/-! ## 2 Behind a yes of the one equation's step -/

section
variable {Cl : Type} (own : List (ℕ × ℕ))

/-- **WHERE THE LAST ROW OF THE SEGMENT's GROUP HAS A WEIGHT, THE ORACLE MESSAGE IS SEATED IN own**,
behind a yes of the one equation's step, where the promise's public test on the ledger holds in
front. -/
theorem seatAt_step (p : K9.Where) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S)
    (k : ℕ) (h : (K9.oneEquation (Cl := Cl) atS p).step ft s rs cols = .ok (s', k))
    (hT : totalIn own s = true) :
    ∀ a' G row, atS.get? s' = some a' → a'.d.st.groups[a'.L.check.group]? = some G →
      G.rows.back? = some row → ∀ o part J, Reading.gl.val (row.coefficient o part J) ≠ 0 →
      ∃ x, seatAt own a'.d.book o = some x := by
  obtain ⟨a, out, ha, hdoor, hs'⟩ := oneEquation_inv atS p ft s rs cols s' k h
  obtain ⟨n, q, G₁, row₀, d1, _, hq, _, hr, ho, _, hL⟩ := door_parts _ _ _ _ _ _ hdoor
  have I : ledgerIn own a = true := by
    unfold totalIn at hT
    rw [ha] at hT
    exact hT
  obtain ⟨G0, hG0⟩ := Option.isSome_iff_exists.mp (door_group _ _ _ _ _ _ hdoor)
  have hg1 : d1.st.groups = a.d.st.groups := asRow_groups _ _ _ _ _ _ hr
  obtain ⟨a₁, ha₁, _, hL', hd'⟩ :=
    atS_reads s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
  rw [← hs'] at ha₁
  intro a' G row ha' hG hrow
  obtain rfl : a₁ = a' := Option.some.inj (ha₁.symm.trans ha')
  have eL : a₁.L = a.L := hL'.trans hL
  have eD : a₁.d.st = out.d.st := hd'
  have eB : a₁.d.book = a.d.book := by
    rw [book_part s' a₁ ha', hs', book_set, book_part s a ha]
  have hGb : a₁.d.st.groups[a₁.L.check.group]? = some { G0 with rows := G0.rows.push row₀ } := by
    rw [eD, eL, ho]
    show (Slice.withRow d1.st a.L.check.group row₀).groups[a.L.check.group]? = _
    simp only [Slice.withRow, Array.getElem?_modify, if_true, hg1, hG0, Option.map_some]
  obtain rfl : { G0 with rows := G0.rows.push row₀ } = G := Option.some.inj (hGb.symm.trans hG)
  obtain rfl : row₀ = row := by simpa using hrow
  obtain ⟨c1, c2, _⟩ := asRow_coef Reading.gl a.L.check.rows a.L.check.frame q a.d d1 row₀
    (equation_k9 _ _ _ _ hq) hr
  obtain ⟨hfrom, hsz, hle⟩ := equation_from _ _ _ _ hq
  unfold ledgerIn at I
  simp only [Bool.and_eq_true] at I
  obtain ⟨⟨_, hmask⟩, harr⟩ := I
  intro o part J hne
  rw [eB]
  cases part with
  | main =>
    rw [c1 o J] at hne
    obtain ⟨t, htm, ht⟩ := exists_of_sum_ne q.terms.toList _ hne
    obtain ⟨A, b, hA, hw, _, _⟩ := termAt_ne Reading.gl _ _ _ t o J ht
    obtain ⟨ti, hti, hba⟩ := hfrom t htm
    have h1 := (Eq.mp (Bool.and_eq_true _ _)
      (List.all_eq_true.1 harr ti (List.mem_range.2 (Nat.lt_of_lt_of_le hti hle)))).1
    obtain ⟨A', hA'⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨b', o', x, e1, e2, e3, e4⟩ := arrayIn_some own a ti A' hA'
    have eb : b' = (t.born, t.array) := by
      have k1 : a.L.arrayOf.getD ti (0, "") = b' := by
        simp [Array.getD_eq_getD_getElem?, e1]
      exact k1.symm.trans hba
    subst eb
    obtain rfl : A' = A := Option.some.inj (e2.symm.trans hA)
    obtain rfl : o' = o := Option.some.inj (e3.symm.trans hw)
    exact ⟨x, e4⟩
  | mask =>
    rw [c2 o J] at hne
    by_cases hc : maskOracle a.L.check.frame = some o ∧ J < q.onMasks.size
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hmask
      unfold maskSeat at hx
      obtain ⟨o', ho', hx⟩ := Option.bind_eq_some_iff.1 hx
      obtain rfl : o' = o := Option.some.inj (ho'.symm.trans hc.1)
      exact ⟨x, hx⟩
    · rw [if_neg hc] at hne
      exact absurd rfl hne

/-- **So whatever seat the book gives that message is of own.** -/
theorem seats_first (p : K9.Where) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S)
    (k : ℕ) (h : (K9.oneEquation (Cl := Cl) atS p).step ft s rs cols = .ok (s', k))
    (hT : totalIn own s = true) :
    ∀ a' G row, atS.get? s' = some a' → a'.d.st.groups[a'.L.check.group]? = some G →
      G.rows.back? = some row → ∀ o part J, Reading.gl.val (row.coefficient o part J) ≠ 0 →
      ∀ q, a'.d.book.place[o]? = some q → own.contains q = true := by
  intro a' G row ha' hG hrow o part J hne q hq
  obtain ⟨x, hx⟩ := seatAt_step own p ft s rs cols s' k h hT a' G row ha' hG hrow o part J hne
  unfold seatAt at hx
  rw [hq] at hx
  by_cases hc : own.contains q = true
  · exact hc
  · have hx' : (if own.contains q = true then some q else none) = some x := hx
    rw [if_neg hc] at hx'
    exact nomatch hx'

end

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.equation_from
#print axioms VerifiableInference.Desc.K9L.seatAt_step
#print axioms VerifiableInference.Desc.K9L.seats_first
