-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/RowInsideOf.lean: THE PREMISE `RowInside` OF `rowEqQ_clamp`
(RowClamp.lean), PAID BEHIND A YES OF THE ONE EQUATION's STEP, FROM ANOTHER FILE's ONE NAMED
PREMISE `InsideAt` (Johnson/Desc/Sound/Clamp/FormsClamp.lean) AT THE PART IN FRONT. Theorems.
  `slotsIn_size`, `equation_masks`: the one equation has just one coefficient for each slot of the
    ledger. `exists_of_sum_ne`, `termAt_ne`: where a term puts something on an entry of a main
    table, the entry is in a block of the term's array, and that oracle message holds the array.
  `rowInside_step`: **behind a yes of the one equation's step the row that stands last in the
    segment's group is the one that the step has made (`asRow_coef`, AsRow.lean): a weight other
    than 0 on a main table stands in a block of the layout; on a mask table at the segment's mask
    row, below the number of slots: just where `InsideAt` speaks.** The statement's bits, the book
    and the link's context are those in front.
  `rowEqQ_clamp_step`: so `rowEqQ` at the clamped reader if and only if at `seatTab`, behind that
    yes.
Limits. `InsideAt` IS SHOWN AT NO STATE HERE: it is asked at the ONE part in front of the step (no
sentence over all states). Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.RowClamp
import Johnson.Desc.First.Batch.Law.TableTabs
import Johnson.Desc.Sound.Clamp.FormsClamp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray)
open VerifiableInference.Desc.K9 (atS Ans Equation equation slotsIn door asRow)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound

/-! ## 1 Where the row that the one equation's step makes has a weight -/

/-- The slots put in: as many coefficients as the ledger has slots. -/
theorem slotsIn_size (F : Fork) (mc : Array E × E) (h : slotsIn F = .ok mc) :
    mc.1.size = F.ns := by
  have h' : (F.LS.foldlM (slotStep F) (0, Array.replicate F.ns zeroE, F.c0) >>=
      fun x => (pure x.2 : Ans (Array E × E))) = .ok mc := h
  obtain ⟨x, hx, h2⟩ := ok_bind h'
  have hm : x.2 = mc := Except.ok.inj h2
  rw [← Array.foldlM_toList] at hx
  have k := foldlM_invE (slotStep F) (fun x => x.2.1.size = F.ns) (fun s a s' hp hs => by
    unfold slotStep at hs
    by_cases hz : isZeroE a = true
    · rw [if_pos hz] at hs
      rw [← Except.ok.inj hs]
      exact hp
    · rw [if_neg hz] at hs
      obtain ⟨_, _, h3⟩ := ok_bind hs
      rw [← Except.ok.inj h3]
      simpa using hp) _ _ _ (by simp) hx
  rw [← hm]
  exact k

/-- The one equation has a coefficient for each slot of the ledger. -/
theorem equation_masks (L : LinkCtx) (F G : Fork) (q : Equation)
    (h : equation L F = .ok (q, G)) : q.onMasks.size = F.ns := by
  unfold equation at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨terms, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨mc, hmc, h⟩ := ok_bind h
  have e : q = { terms := terms, onMasks := mc.1, constant := mc.2 } :=
    (congrArg Prod.fst (Except.ok.inj h)).symm
  rw [e]
  exact slotsIn_size { F with doorShutF := true } mc hmc

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

theorem exists_of_sum_ne {α : Type} (l : List α) (f : α → K) (h : (l.map f).sum ≠ 0) :
    ∃ x ∈ l, f x ≠ 0 := by
  by_contra hc
  refine h (List.sum_eq_zero fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  by_contra hne
  exact hc ⟨x, hx, hne⟩

/-- **Where a term puts something on an entry of a main table, the entry is in a block of the term's
array, and the array is held by that oracle message.** -/
theorem termAt_ne (Rr : ReqRows) (f : ReqFrame) (St : Statement) (t : ReqTerm) (o J : ℕ)
    (h : termAt ρ Rr f St t o J ≠ 0) :
    ∃ A b, reqArray Rr.layout t.born t.array = some A ∧ f.whereIs t.born A.message = some o ∧
      b ∈ A.blocks ∧ (inBlock b (St.rowBits o .main) (St.placeBits o .main) J : K) ≠ 0 := by
  unfold termAt at h
  cases hA : reqArray Rr.layout t.born t.array with
  | none =>
    rw [hA] at h
    exact absurd rfl h
  | some A =>
    rw [hA] at h
    cases hw : f.whereIs t.born A.message with
    | none =>
      simp only [hw] at h
      exact absurd rfl h
    | some o' =>
      simp only [hw] at h
      by_cases ho : o' = o
      · subst ho
        rw [if_pos rfl] at h
        obtain ⟨b, hb, hne⟩ := exists_of_sum_ne A.blocks _ h
        exact ⟨A, b, rfl, hw, hb, left_ne_zero_of_mul hne⟩
      · rw [if_neg ho] at h
        exact absurd rfl h

end

/-! ## 2 The premise of `rowEqQ_clamp`, behind a yes of the one equation's step -/

section
variable {Cl : Type} (cs : OnBytes.Codes) (ms : List Mem) (own : List (ℕ × ℕ))

/-- **BEHIND A YES OF THE ONE EQUATION's STEP THE LAST ROW OF THE SEGMENT's GROUP HAS ITS WEIGHTS
INSIDE THE MEMBERS' RANGES**, where the data that the open segment reads in front lie inside. -/
theorem rowInside_step (p : K9.Where) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (s' : S) (k N : ℕ) (h : (K9.oneEquation (Cl := Cl) atS p).step ft s rs cols = .ok (s', k))
    (hin : ∀ a, atS.get? s = some a → InsideAt cs ms own a) :
    ∀ a' G row, atS.get? s' = some a' → a'.d.st.groups[a'.L.check.group]? = some G →
      G.rows.back? = some row → RowInside cs ms own a' N row := by
  obtain ⟨a, out, ha, hdoor, hs'⟩ := oneEquation_inv atS p ft s rs cols s' k h
  obtain ⟨n, q, G₁, row₀, d1, _, hq, _, hr, ho, _, hL⟩ := door_parts _ _ _ _ _ _ hdoor
  have I := hin a ha
  have hb : SameBits a.d.st out.d.st := by
    rw [ho]
    exact (asRow_bits _ _ _ _ _ _ hr).trans (withRow_bits _ _ _)
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
  intro o _ part J hJ hne x y hx hy
  have bR : a₁.d.st.rowBits o part = a.d.st.rowBits o part := by
    rw [eD]
    exact (hb o part).1
  have bP : a₁.d.st.placeBits o part = a.d.st.placeBits o part := by
    rw [eD]
    exact (hb o part).2
  rw [eB] at hx
  rw [bR]
  rw [bR, bP] at hJ
  cases part with
  | main =>
    rw [c1 o J] at hne
    obtain ⟨t, _, ht⟩ := exists_of_sum_ne q.terms.toList _ hne
    obtain ⟨A, b, hA, hw, hbA, hib⟩ := termAt_ne Reading.gl _ _ _ t o J ht
    exact I.main t.born t.array A o b J x y hA hw hbA hJ hib hx hy
  | mask =>
    rw [c2 o J] at hne
    by_cases hc : maskOracle a.L.check.frame = some o ∧ J < q.onMasks.size
    · exact I.mask o J x y hc.1 (Or.inl (equation_masks _ _ _ _ hq ▸ hc.2)) hx hy
    · rw [if_neg hc] at hne
      exact absurd rfl hne

/-- **SO THE ONE EQUATION's ROW AT THE CLAMPED READER IS THE COMPOSED MEANING's OWN, BEHIND THAT
YES.** -/
theorem rowEqQ_clamp_step {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (p : K9.Where) (ft : ℕ) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k N : ℕ)
    (h : (K9.oneEquation (Cl := Cl) atS p).step ft s rs cols = .ok (s', k))
    (hin : ∀ a, atS.get? s = some a → InsideAt cs ms own a) (w : Wit Cells Tok MsgT) :
    rowEqQ own N s' (LinkJoin.rdC cs arr ms w) ↔ rowEqQ own N s' (seatTab cs arr ms w) :=
  rowEqQ_clamp cs arr ms own N s' w (rowInside_step cs ms own p ft s rs cols s' k N h hin)

end

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.equation_masks
#print axioms VerifiableInference.Desc.K9L.termAt_ne
#print axioms VerifiableInference.Desc.K9L.rowInside_step
#print axioms VerifiableInference.Desc.K9L.rowEqQ_clamp_step
