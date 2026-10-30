-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/M4.lean: kind K13's text behind W's commitment (Johnson/Desc/K13/Text.lean:
`rows`): where it answers. Statements with their proofs.
Main names:
  `has_lt`, `evalIn_of_rowIn`: what the adding of an open row has tested of (Eval)
    (`OnBytes.Means.RowIn`) gives what `eval_back` asks (`EvalIn`).
  `addRows_one`: the adding of one open row: its tests, and the statement behind.
  `newGroup_codes`, `join_codes`, `joinAll_codes`: the codes stay.
  `rows_ok`: where `rows` answers: the claim is kept; W is the first message sent; (Eval) is made of
    the claim at W's layout under the record's codes; it has passed the tests of the adding; the
    statement behind is the statement with that row added to the own group.
Used of `verify-on-bytes`, pure functions: `linEvalRow`, `addLaid`, `Blk.placeOk`, `withRow`. Of the
ground: `newGroupP`, `joinP`, `addRowsP`.

What is not claimed. Nothing on the joinings but that they leave the codes. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.EvalProofs
import Johnson.Desc.K13.Law.Good
import Johnson.Desc.Means.Page

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Params (LinShape)
open OnBytes.Means (Words Says value tableSize RowIn)
open VerifiableInference.Desc.Ground (newGroupP joinP addRowsP addRowP addRowsFrom)
open VerifiableInference.Desc.First (S rowOfClaim)

/-- A table that the statement has belongs to a message that is there. -/
theorem has_lt {St : Statement} {o : ℕ} {p : OnBytes.Part} (h : St.has o p = true) :
    o < St.oracles.size := by
  by_contra hn
  have e : St.oracles[o]? = none := Array.getElem?_eq_none (not_lt.1 hn)
  unfold Statement.has at h
  rw [e] at h
  cases h

/-- **What the adding of an open row has tested of (Eval)** gives what `eval_back` asks. -/
theorem evalIn_of_rowIn {St : Statement} {G : Group} {row : TensorRow} {w : ℕ} {lay : VectorLay}
    (hb : row.psi.length ≤ lay.bits)
    (h : RowIn St G (addLaid
      { units := (memberClaim row).masks, target := (memberClaim row).target } w lay
      [Tensor.eq (memberClaim row).psi])) : EvalIn St w lay row.masks := by
  have ht := h.terms ⟨w, .main, lay.onTable (Tensor.eq row.psi)⟩
    (by simp [addLaid, Row.add, memberClaim])
  simp only [Blk.placeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨_, hhas⟩, hvars⟩, _⟩ := ht
  have hv := (onTable_vars lay (Tensor.eq row.psi) rfl (by rw [vars_eqTensor]; exact hb)).1
  refine ⟨has_lt hhas, ?_, fun t ht => ?_⟩
  · unfold tableSize
    rw [if_pos hhas, ← hvars, hv]
  · have hu := h.units ⟨t.1.oracle, .mask, t.1.index, t.2⟩ (by
      simp only [addLaid, Row.add, memberClaim, List.foldl_cons, List.foldl_nil]
      exact List.mem_map.2 ⟨t, ht, rfl⟩)
    simp only [Blk.placeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hu
    obtain ⟨⟨⟨_, hhas'⟩, _⟩, hi⟩ := hu
    refine ⟨has_lt hhas', ?_⟩
    unfold tableSize
    rw [if_pos hhas']
    exact hi

/-- The adding of one open row: its tests, and the statement behind. -/
theorem addRows_one {d d' : St} {g : ℕ} {row : OnBytes.Row} (h : addRowsP d g [row] = some d') :
    ∃ G, d.st.groups[g]? = some G ∧ RowIn d.st G row ∧ d'.st = withRow d.st g row := by
  unfold addRowsP at h
  split at h
  · have h' : (addRowP d g row).bind (fun x => some x) = some d' := h
    cases ha : addRowP d g row with
    | none =>
      rw [ha] at h'
      cases h'
    | some x =>
      rw [ha] at h'
      obtain rfl := Option.some.inj h'
      unfold addRowP at ha
      split at ha
      · next c =>
        obtain rfl := Option.some.inj ha
        obtain ⟨G, hG, hr⟩ := OnBytes.Means.rowIn_of_rowL c
        exact ⟨G, hG, hr, rfl⟩
      · cases ha
  · cases h

/-- A new group leaves the codes. -/
theorem newGroup_codes {d : St} {c z : ℕ} {b : ℕ × St} (h : newGroupP d c z = some b) :
    b.2.st.codes = d.st.codes := by
  unfold newGroupP at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

/-- A joining leaves the codes. -/
theorem join_codes {d d' : St} {g o : ℕ} {kept : Bool} (h : joinP d g o kept = some d') :
    d'.st.codes = d.st.codes := by
  unfold joinP at h
  split at h
  · cases hG : d.st.groups[g]? with
    | none =>
      rw [hG] at h
      cases h
    | some G =>
      rw [hG] at h
      obtain rfl := Option.some.inj h
      rfl
  · cases h

/-- So do joinings in a row. -/
theorem joinAll_codes (g : ℕ) : ∀ (l : List ℕ) (d d' : St), joinAll g l d = .ok d' →
    d'.st.codes = d.st.codes
  | [], d, d', h => by rw [pure_ok.1 h]
  | o :: l, d, d', h => by
    simp only [joinAll, bind_ok, there_ok] at h
    obtain ⟨d₁, h1, h2⟩ := h
    rw [joinAll_codes g l d₁ d' h2, join_codes h1]

/-- **Where the text behind W's commitment answers**: the claim is kept; W is the first message
sent; (Eval) is made of the claim at W's layout under the record's codes; it has passed the tests
of the adding; and the statement behind is the statement with that row added to the own group. -/
theorem rows_ok {Sh : LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St} {o : LinFirst × St}
    (h : rows Sh claim ids d = .ok o) :
    ∃ (d₃ : St) (row : OnBytes.Row) (G : Group), o.1.claim = claim ∧ ids[0]? = some o.1.w ∧
      linEvalRow Sh claim o.1.w (linLayW d.st.codes Sh) = some row ∧
      d₃.st.groups[o.1.own]? = some G ∧ RowIn d₃.st G row ∧
      o.2.st = withRow d₃.st o.1.own row ∧ o.2.st.codes = d.st.codes := by
  simp only [rows_is, bind_ok, there_ok, pure_ok] at h
  obtain ⟨w, hw, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, hr, d₄, h4, rfl⟩ := h
  obtain ⟨G, hG, hin, hst⟩ := addRows_one h4
  have hc : d₃.st.codes = d.st.codes := by
    have e2 : d₂.st.codes = d.st.codes := by
      rw [join_codes h2, joinAll_codes _ _ _ _ h1, newGroup_codes hb]
    split at h3
    · rw [join_codes h3, e2]
    · rw [← Option.some.inj h3, e2]
  rw [hc] at hr
  exact ⟨d₃, row, G, rfl, hw, hr, hG, hin, hst, by rw [hst]; exact hc⟩

end VerifiableInference.Desc.K13.Law
