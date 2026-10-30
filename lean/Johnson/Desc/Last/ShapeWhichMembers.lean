-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeWhichMembers.lean: WHICH MESSAGES KIND K13's TEXT LAYS INTO THE OWN GROUP;
AND WHAT "THE STATE HOLDS THE OUT-OF-DOMAIN (OOD) SAMPLE" SAYS OF THE NUMBER OF SAMPLE ROWS.
Statements and proofs; no definition. Toward the earning of `ownTwoB`
(Johnson/Desc/Last/OwnTwo.lean).

Main names (namespace `VerifiableInference.Desc.Last`).
  `joinP_which`, `joinAll_which`: a joining lays the one message and nothing else (by `joinP_mem`,
    Johnson/Desc/Sound/MembersCarried.lean). **`rows_which`**: where `K13.rows` answers, every
    member of the own group is a message that the claim's masks name, or W, or, where the shape
    wants one, the split's message.
  **`whichMembers_rowsB`**: at the block behind W's commitment: if the shape wants no split and the
    one row on the table in front names entries of the message idx alone: every member behind is idx
    or the claim's W.
  **`rows_of_held`**: `smpHeld st book j t = true` (Johnson/Desc/SmpRows.lean) gives the tenant's
    message, by number, with as many sample rows as its shape counts answers.

Every "there is", walked. M, M': tied by `memOf … = some M`. i, x (`rows_of_held`): tied by
`oracleNo book j t = some i` and `oracles[i]? = some x`.
WHAT IS LEFT FOR "ONE SAMPLE ROW EACH". That the state holds the samples of the index masks' tenant
and of W's at the border behind M:4 (the table's own clause `samplesHeld`, where these two are among
the sampled tenants of the open items); that these tenants' numbers by the book are idx and W's;
that both shapes count one answer. NONE IS SHOWN HERE.
Limits. Laws on texts and on one test's text. NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeTwoMembers
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.Ground (newGroupP joinP addRowsP)
open _root_.Desc.K14.Law.Fence (memOf joinP_mem addRowsP_mem)
open K13.Law (OnLedger linAt bind_ok there_ok pure_ok rows_is)

/-! ## 1 Which messages K13's text lays into the own group -/

/-- A joining lays the one message, and nothing else. -/
theorem joinP_which {d d' : K13.St} {g o : ℕ} {kept : Bool} (h : joinP d g o kept = some d')
    {M : Array ℕ} (hM : memOf d g = some M) :
    ∃ M', memOf d' g = some M' ∧ ∀ i ∈ M'.toList, i = o ∨ i ∈ M.toList := by
  refine ⟨_, (joinP_mem d d' g o kept h M hM).1, fun i hi => ?_⟩
  rw [OnBytes.Means.toList_insertIdxIfInBounds,
    List.mem_insertIdx (by rw [Array.length_toList]; exact Array.size_filter_le)] at hi
  exact hi

theorem joinAll_which (g : ℕ) : ∀ (l : List ℕ) (d d' : K13.St), K13.joinAll g l d = .ok d' →
    ∀ M, memOf d g = some M → ∃ M', memOf d' g = some M' ∧ ∀ i ∈ M'.toList, i ∈ l ∨ i ∈ M.toList
  | [], d, d', h, M, hM => by
    obtain rfl : d = d' := Except.ok.inj h
    exact ⟨M, hM, fun i hi => Or.inr hi⟩
  | o :: l, d, d', h, M, hM => by
    simp only [K13.joinAll, bind_ok, there_ok] at h
    obtain ⟨d₁, h1, h2⟩ := h
    obtain ⟨M₁, hM₁, e₁⟩ := joinP_which h1 hM
    obtain ⟨M', hM', e'⟩ := joinAll_which g l d₁ d' h2 M₁ hM₁
    refine ⟨M', hM', fun i hi => ?_⟩
    rcases e' i hi with c | c
    · exact Or.inl (List.mem_cons_of_mem _ c)
    · rcases e₁ i c with c | c
      · exact Or.inl (by rw [c]; exact List.mem_cons_self ..)
      · exact Or.inr c

/-- **WHERE K13's TEXT BEHIND W's COMMITMENT ANSWERS, EVERY MEMBER OF THE OWN GROUP IS: a message
that the claim's masks name, or W, or, where the shape wants one, the split's message.** -/
theorem rows_which {Sh : Params.LinShape} {claim : LinClaim} {ids : Array ℕ} {d : K13.St}
    {o : LinFirst × K13.St} (h : K13.rows Sh claim ids d = .ok o) :
    ∃ M, memOf o.2 o.1.own = some M ∧ ∀ i ∈ M.toList,
      i ∈ listOfT (claim.masks.toList.map (·.oracle)) ∨ i = o.1.w ∨
        (Sh.ownSplitNeeded = true ∧ i = o.1.split) := by
  simp only [rows_is, bind_ok, there_ok, pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, _, d₄, h4, rfl⟩ := h
  obtain ⟨e1, e2⟩ := _root_.Desc.K15.newGroupP_inv d b.2 _ _ b.1 hb
  have h0 : memOf b.2 b.1 = some #[] := by
    unfold memOf
    rw [e2, e1]
    show ((d.st.groups.push _)[d.st.groups.size]?).map (·.members) = _
    rw [Array.getElem?_push_size]
    rfl
  obtain ⟨M₁, hM₁, c₁⟩ := joinAll_which b.1 _ b.2 d₁ h1 _ h0
  obtain ⟨M₂, hM₂, c₂⟩ := joinP_which h2 hM₁
  have k2 : ∀ i ∈ M₂.toList, i ∈ listOfT (claim.masks.toList.map (·.oracle)) ∨ i = w := by
    intro i hi
    rcases c₂ i hi with c | c
    · exact Or.inr c
    · rcases c₁ i c with c | c
      · exact Or.inl c
      · cases c
  by_cases hs : Sh.ownSplitNeeded = true
  · rw [if_pos hs] at h3
    obtain ⟨M₃, hM₃, c₃⟩ := joinP_which h3 hM₂
    refine ⟨M₃, ((addRowsP_mem d₃ d₄ b.1 [row] h4).1 b.1).trans hM₃, fun i hi => ?_⟩
    rcases c₃ i hi with c | c
    · exact Or.inr (Or.inr ⟨hs, c⟩)
    · rcases k2 i c with c | c
      · exact Or.inl c
      · exact Or.inr (Or.inl c)
  · rw [if_neg hs] at h3
    obtain rfl := Option.some.inj h3
    refine ⟨M₂, ((addRowsP_mem d₂ d₄ b.1 [row] h4).1 b.1).trans hM₂, fun i hi => ?_⟩
    rcases k2 i hi with c | c
    · exact Or.inl c
    · exact Or.inr (Or.inl c)

/-- **AT THE BLOCK**: under the premises of `twoMembers_rowsB` every member of the own group behind
the yes is the one message of masks, or W. -/
theorem whichMembers_rowsB {Cl : Type} {P : K13.Where} {s s' : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.rowsB (Cl := Cl) K13.atS P).decide s rs gs = .ok s')
    (hsp : P.lin.ownSplitNeeded = false) {idx : ℕ} {r : TensorRow} (hr : s.rows = [r])
    (hon : OnLedger idx r) :
    ∀ l' G, linAt s' = some l' → s'.st.groups[l'.own]? = some G →
      ∀ i ∈ G.members.toList, i = idx ∨ i = l'.w := by
  obtain ⟨m₀, l, o, owed, hs, hl, hrows, rfl⟩ := K13.Law.rowsB_at h
  have er : r = First.rowOfClaim l.claim := by
    have e : s.rows = [First.rowOfClaim l.claim] := by
      unfold First.S.rows
      rw [hs]
      show (match m₀.lin with
        | some l => [First.rowOfClaim l.claim]
        | none => s.out.pending) = _
      rw [hl]
    rw [hr] at e
    exact List.head_eq_of_cons_eq e
  subst er
  obtain ⟨M, hM, hc⟩ := rows_which hrows
  intro l' G hl' hG i hi
  obtain rfl : o.1 = l' := Option.some.inj hl'
  have hG' : o.2.st.groups[o.1.own]? = some G := hG
  unfold memOf at hM
  rw [hG'] at hM
  have eM : G.members = M := Option.some.inj hM
  rw [eM] at hi
  rcases hc i hi with c | c | ⟨c, _⟩
  · left
    rw [listOfT_eq, Fmt.listOf_mem] at c
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 c
    exact hon (⟨m.oracle, m.index⟩, m.coeff) (List.mem_map.2 ⟨m, hm, rfl⟩)
  · exact Or.inr c
  · rw [hsp] at c
    cases c

/-! ## 2 What "the state holds the sample" says of the sample rows' number -/

/-- **Where the state holds a tenant's sample, that tenant's message has as many sample rows as its
shape counts answers.** -/
theorem rows_of_held {st : Statement} {book : TreeBook} {j t : ℕ}
    (h : smpHeld st book j t = true) :
    ∃ i x, oracleNo book j t = some i ∧ st.oracles[i]? = some x ∧
      x.sampleRows.size = x.shape.answers := by
  unfold smpHeld smpSeed at h
  cases ho : oracleNo book j t with
  | none =>
    rw [ho] at h
    cases h
  | some i =>
    cases hx : st.oracles[i]? with
    | none =>
      rw [ho] at h
      simp [hx] at h
    | some x =>
      refine ⟨i, x, rfl, hx, ?_⟩
      cases hr : smpRows st book j t with
      | none =>
        rw [ho] at h
        simp [hr] at h
      | some rows =>
        unfold smpRows at hr
        rw [ho] at hr
        simp only [Option.bind_some, hx] at hr
        split at hr
        · rename_i c
          simp only [Bool.and_eq_true, beq_iff_eq] at c
          exact c.2
        · cases hr

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.joinP_which
#print axioms VerifiableInference.Desc.Last.joinAll_which
#print axioms VerifiableInference.Desc.Last.rows_which
#print axioms VerifiableInference.Desc.Last.whichMembers_rowsB
#print axioms VerifiableInference.Desc.Last.rows_of_held
