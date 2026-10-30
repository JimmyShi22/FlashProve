-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqRowFwd.lean: K9's MEMBER "THE ONE EQUATION", THE HONEST DIRECTION, OVER THE LIBRARY
ALONE: TWO TWINS OF SEALED LEMMAS. The library goes from the row to the sum (soundness): `equation_last`
(Johnson/Desc/First/Batch/Law/Cores.lean): the group's last row behind the step gives the one sum in front;
`rowEq_of_says` (Johnson/Desc/First/Link/Law/TieThreeEq.lean): the item's sentence on the row gives the kind's own
relation. Both are one-way as stated; beneath them lie equations and "if and only if"s. HERE EACH IS TYPED THE OTHER
WAY, WITH THE SEALED PROOF's STEPS PARTLY REUSED: by a reader's program, of `equation_last_fwd`'s 35 lines 24 are the
library's to the sign, of `says_of_rowEq`'s 67 lines 25; new are the end of the first (the last row behind is the pushed
one; `sub_eq_zero`) and, in the second, that the class's one place is the list's last and the other direction of
`holds_says`. Statements and proofs; no thread, no prover, no head is in this file; no goal is stated.
  **`equation_last_fwd`**   general in the lens and the ring, under `equation_last`'s own premises (lens, P, the step's
      yes): `oneK X ρ s s (dataAt X s tab) = 0` gives `LastRowAt X ρ N s' tab`. By `oneEquation_inv`, `door_parts`,
      `asRow_sum` (the row's sum less its target is the equation's value), `equation_total`, `rowSum_bits`
  **`says_of_rowEq`**   under `rowEq_of_says`' own premises (`EqRowAsks`, hseat, hins; hn is not needed; that K9's lens
      answers is asked): `rowEqQ own N s (seatTab cs arr ms w)` gives `AllSay` of the class's rows at the witness's
      words (`wordsFirst`). AT `seatTab`: the clamped reader is not needed on this road (under hins the library's
      `rowEqQ_clamp` makes the relation at the two readers one). By `holds_says` (an "if and only if"), `rowSum_words`,
      `words_tabQ`, `tabFirst_at_plan`, `real_of_inMsg`
WHAT IS NOT CLAIMED. Any premise at any state. IDLE WHERE THE GROUP IS NOT THERE, OR AT n = 0: then the class's list is
empty (Honest/K9/EqRowNotIdle.lean says what it is behind a step). Called by Honest/K9/EqRowAtHead.lean alone. Nothing
on any property.
GROUND: this file stands over the sealed library alone.
-/
import Johnson.Desc.First.Link.Law.TieThreeEq
import Johnson.Desc.First.Batch.Law.Cores
import Johnson.Desc.First.Batch.Law.RowSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.K9 (atS Where Lens door equation)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (EqRowAsks words_tabQ real_of_inMsg rowSum_words)

section
variable {T K : Type} [CommRing K]

/-- **A yes of the one equation's step, FORWARD: the one sum in front gives the last row behind.** The library's
`equation_last` the other way: its first lines as they lie; the end is new. -/
theorem equation_last_fwd {Cl : Type} (X : Lens T) (ρ : Reading K) (p : K9.Where) (ft : Nat)
    (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat) (N : Nat)
    (tab : Nat → OnBytes.Part → Nat → K)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (P : ∀ a q G, X.get? s = some a → equation a.L a.F = .ok (q, G) →
      RowPremises a.L.check a.d.st N q)
    (h : (K9.oneEquation (Cl := Cl) X p).step ft s rs cols = .ok (s', k))
    (h0 : K9L.oneK X ρ s s (K9L.dataAt X s tab) = 0) : LastRowAt X ρ N s' tab := by
  obtain ⟨a, out, ha, hdoor, hs'⟩ := oneEquation_inv X p ft s rs cols s' k h
  obtain ⟨n, q, G, row, d1, _, hq, _, hr, ho, _, hL⟩ := door_parts _ _ _ _ _ _ hdoor
  have hb : SameBits a.d.st out.d.st := by
    rw [ho]
    exact (asRow_bits _ _ _ _ _ _ hr).trans (withRow_bits _ _ _)
  obtain ⟨G0, hG0⟩ := Option.isSome_iff_exists.mp (door_group _ _ _ _ _ _ hdoor)
  have hg1 : d1.st.groups = a.d.st.groups := asRow_groups _ _ _ _ _ _ hr
  obtain ⟨a', ha', hL', hd'⟩ :=
    lens s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
  rw [← hs'] at ha'
  have eL : a'.L = a.L := hL'.trans hL
  have eD : a'.d.st = out.d.st := hd'
  have hGb : a'.d.st.groups[a'.L.check.group]? = some { G0 with rows := G0.rows.push row } := by
    rw [eD, eL, ho]
    show (Slice.withRow d1.st a.L.check.group row).groups[a.L.check.group]? = _
    simp only [Slice.withRow, Array.getElem?_modify, if_true, hg1, hG0, Option.map_some]
  intro a'' ha'' G' hG' row' hr'
  obtain rfl : a' = a'' := Option.some.inj (ha'.symm.trans ha'')
  obtain rfl : { G0 with rows := G0.rows.push row } = G' := Option.some.inj (hGb.symm.trans hG')
  obtain rfl : row = row' := by simpa using hr'
  rw [eD, rowSum_bits ρ _ _ hb]
  have e := asRow_sum ρ a.L.check q a.d d1 row N tab (equation_k9 _ _ _ _ hq) (P a q G ha hq) hr
  simp only [K9L.oneK, K9L.dataAt, ha] at h0
  rw [← equation_total ρ _ a.L a.F G q hq] at h0
  rw [h0] at e
  exact sub_eq_zero.1 e

end

section
variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (own : List (ℕ × ℕ))

/-- **FROM THE KIND's OWN RELATION TO THE ITEM's SENTENCE**: the library's `rowEq_of_says` the other way, at the
witness's tables by seat: its last lines as they lie; the beginning is new; no clamp. -/
theorem says_of_rowEq (M : List OracleShape) (g i n N : ℕ) (s : S)
    (w : Wit Cells Tok MsgT) (A : EqRowAsks cs ms M g i N s) (hpart : (atS.get? s).isSome = true)
    (hseat : ∀ a G row, atS.get? s = some a → a.d.st.groups[a.L.check.group]? = some G →
      G.rows.back? = some row → ∀ o part J, Reading.gl.val (row.coefficient o part J) ≠ 0 →
      ∀ q, a.d.book.place[o]? = some q → own.contains q = true)
    (hins : ∀ a G row, atS.get? s = some a → a.d.st.groups[a.L.check.group]? = some G →
      G.rows.back? = some row → RowInside cs ms own a N row)
    (h : rowEqQ own N s (seatTab cs arr ms w)) :
    OnBytes.Means.AllSay Reading.gl s.st
      (match s.st.groups[g]? with
        | none => []
        | some G => (List.range n).filterMap fun j => G.rows[i + j]?)
      (wordsFirst arr s.st s.book w) := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hpart
  have hst := st_part s a ha
  have hbk := LinkJoin.book_part s a ha
  intro row hrow
  cases hG' : s.st.groups[g]? with
  | none =>
    rw [hG'] at hrow
    exact absurd hrow List.not_mem_nil
  | some G =>
    rw [hG'] at hrow
    obtain ⟨j, -, ej⟩ := List.mem_filterMap.1 hrow
    have hsz := A.rows G hG'
    have hj : j = 0 := by
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 ej
      omega
    subst hj
    have hr : G.rows.back? = some row := by
      rw [Array.back?_eq_getElem?, hsz]
      exact ej
    have hG : a.d.st.groups[a.L.check.group]? = some G := by
      rw [hst, A.grp a ha]
      exact hG'
    have hfit := fit_of_inOrder atS Reading.gl N s
      (fun a ha => by rw [st_part s a ha]; exact A.order) a ha G hG row hr
    have L := h a ha G hG row hr
    have e : tabAt own (seatTab cs arr ms w) s =
        tabQ own a.d.st a.d.book (seatTab cs arr ms w) := by
      unfold K9L.tabAt
      rw [ha]
    have hin := hins a G row ha hG hr
    have hse := hseat a G row ha hG hr
    unfold RowInside at hin
    rw [e] at L
    rw [hbk] at hse
    rw [hst, hbk] at hin L
    rw [hst] at hfit
    refine (holds_says Reading.gl s.st N _ row A.order.2 hfit.2).1 ?_
    rw [← L]
    refine rowSum_words s.st N _ _ row fun o hoN part J hJ hz => ?_
    have ho : o < s.st.oracles.size := by
      by_contra hc
      exact hz (hfit.2.2 o (by omega) part J)
    obtain ⟨sh, q, hM, hq, hT⟩ :=
      tabFirst_at_plan arr M s.st s.book A.shapes A.numbers A.places w o ho
    have hown := hse o part J hz q hq
    obtain ⟨y, hy, hMy⟩ := A.member G row hG' hr o part J hz q hq
    have hsh : (y.1.l.get y.2).1 = sh := Option.some.inj (hMy.symm.trans hM)
    have hseat' : K9.seatAt own s.book o = some q := by
      unfold K9.seatAt
      rw [hq, Option.bind_some, if_pos hown]
    have hI := hin o hoN part J hJ hz q y hseat' hy
    rw [hsh] at hI
    exact words_tabQ cs arr ms own s.st s.book w o part J sh q y hT hq hown hy hsh A.codes
      (real_of_inMsg cs s.st o part sh _ _ ((A.shapes o ho).trans hM) hI)

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.equation_last_fwd
#print axioms ProofFile.Honest.K9.says_of_rowEq
