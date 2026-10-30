-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorItems.lean: THE FIRST CHAIN'S TEXT AT THE DOOR (`doorFirstB`,
Johnson/Desc/Last/DoorTexts.lean) FROM WHAT RIDES IN THE FIRST TABLE ALREADY, AND HOW MANY MEMBERS
K13's TEXT LAYS INTO THE OWN GROUP. Statements and proofs; no definition.

Why. SH₃ at the two texts (Johnson/Desc/Last/ShapeDoorAtTexts.lean) asks six tests of the first
chain's last record. Three of them ride already under other names; one is owed along the whole
chain; two are laws on one text of kind K13. Here the six are brought down to these.

Main names (namespace `VerifiableInference.Desc.Last`).
  `joinP_count`, `joinAll_count`: a joining lays one member more (by `joinP_mem`,
    Johnson/Desc/Sound/MembersCarried.lean). **`rows_count`**: where K13's text behind W's
    commitment (`K13.rows`) answers, the own group has one member for each message that the claim's
    masks name, W, and the split's message where the shape wants one: AS A NUMBER.
  `firstOfS_at`: where `firstOfS` hands something the record stands at the chain's end with a claim
    laid, and what is handed has the record's statement and book and the claim's number of the own
    group. `openRow_of_laid`: "the own group has an open row" follows from `K13.Law.EvalLaid` (the
    table's own item `evalLaid`).
  **`doorFirstB_of_items`**: `doorFirstB s` from: `Means.tidy4B s.st` · `bookFitsB s.book` ·
    `First.weightsB s` · `EvalLaid P s` · h2: the own group has two members, each with one sample
    row.

Every "there is", walked. M, M' (the counts): tied by `memOf … = some M`. l (`firstOfS_at`): tied by
`linAt s = some l`. x (h2): tied by `oracles[i]? = some x`.
WHERE THE FIVE STAND. tidy: in the first table's "in order" at a layer in other files. The weights:
"K13.weightsOk" (Johnson/Desc/First/FillWeights.lean). (Eval) laid: the table's own item; earned by
`rowsB_lays`. THE BOOK FITS: rides nowhere yet. h2: two members: `rows_count` gives 2 just where the
claim's masks name ONE message and the shape wants no split: neither is shown; one sample row each:
no law says how many sample rows a sampled message has.
Limits. (1) `rows_count` is a number, at the text; it is not yet called at the block or the record.
(2) Nothing is earned or kept here. (3) NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorAtTexts
import Johnson.Desc.Last.ShapeWeights
import Johnson.Desc.Sound.MembersCarried
import Johnson.Desc.K13.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.Ground (newGroupP joinP addRowsP)
open VerifiableInference.Desc.First (weightsB)
open VerifiableInference.Desc.Sound (bookFitsB)
open _root_.Desc.K14.Law.Fence (memOf joinP_mem addRowsP_mem)
open K13.Law (bind_ok there_ok pure_ok rows_is)

/-! ## 1 How many members K13's text lays into the own group -/

/-- A joining lays one member more. -/
theorem joinP_count {d d' : K13.St} {g o : ℕ} {kept : Bool} (h : joinP d g o kept = some d')
    {M : Array ℕ} (hM : memOf d g = some M) :
    ∃ M', memOf d' g = some M' ∧ M'.size = M.size + 1 := by
  refine ⟨_, (joinP_mem d d' g o kept h M hM).1, ?_⟩
  exact OnBytes.Means.size_insertIdxIfInBounds _ _ _ (Array.size_filter_le)

/-- Joinings in a row lay as many members as there are messages. -/
theorem joinAll_count (g : ℕ) : ∀ (l : List ℕ) (d d' : K13.St), K13.joinAll g l d = .ok d' →
    ∀ M, memOf d g = some M → ∃ M', memOf d' g = some M' ∧ M'.size = M.size + l.length
  | [], d, d', h, M, hM => by
    obtain rfl : d = d' := Except.ok.inj h
    exact ⟨M, hM, rfl⟩
  | o :: l, d, d', h, M, hM => by
    simp only [K13.joinAll, bind_ok, there_ok] at h
    obtain ⟨d₁, h1, h2⟩ := h
    obtain ⟨M₁, hM₁, e₁⟩ := joinP_count h1 hM
    obtain ⟨M', hM', e'⟩ := joinAll_count g l d₁ d' h2 M₁ hM₁
    exact ⟨M', hM', by rw [e', e₁, List.length_cons]; omega⟩

/-- **WHERE K13's TEXT BEHIND W's COMMITMENT ANSWERS, THE OWN GROUP HAS: one member for each message
that the claim's masks name, W, and the split's message where the shape wants one.** -/
theorem rows_count {Sh : Params.LinShape} {claim : LinClaim} {ids : Array ℕ} {d : K13.St}
    {o : LinFirst × K13.St} (h : K13.rows Sh claim ids d = .ok o) :
    ∃ M, memOf o.2 o.1.own = some M ∧
      M.size = (listOfT (claim.masks.toList.map (·.oracle))).length + 1 +
        (if Sh.ownSplitNeeded then 1 else 0) := by
  simp only [rows_is, bind_ok, there_ok, pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, _, d₄, h4, rfl⟩ := h
  obtain ⟨e1, e2⟩ := _root_.Desc.K15.newGroupP_inv d b.2 _ _ b.1 hb
  have h0 : memOf b.2 b.1 = some #[] := by
    unfold memOf
    rw [e2, e1]
    show ((d.st.groups.push _)[d.st.groups.size]?).map (·.members) = _
    rw [Array.getElem?_push_size]
    rfl
  obtain ⟨M₁, hM₁, c₁⟩ := joinAll_count b.1 _ b.2 d₁ h1 _ h0
  obtain ⟨M₂, hM₂, c₂⟩ := joinP_count h2 hM₁
  have c0 : (#[] : Array ℕ).size = 0 := rfl
  by_cases hs : Sh.ownSplitNeeded = true
  · rw [if_pos hs] at h3
    obtain ⟨M₃, hM₃, c₃⟩ := joinP_count h3 hM₂
    refine ⟨M₃, ((addRowsP_mem d₃ d₄ b.1 [row] h4).1 b.1).trans hM₃, ?_⟩
    rw [if_pos hs, c₃, c₂, c₁, c0]
    omega
  · rw [if_neg hs] at h3
    obtain rfl := Option.some.inj h3
    refine ⟨M₂, ((addRowsP_mem d₂ d₄ b.1 [row] h4).1 b.1).trans hM₂, ?_⟩
    rw [if_neg hs, c₂, c₁, c0]
    omega

/-! ## 2 What is handed, read at the record -/

/-- **Where `firstOfS` hands something**: the record stands at the chain's end with a claim l laid;
what is handed has the record's statement and book, l's number of the own group, and the one row. -/
theorem firstOfS_at {s : First.S} {f : FirstEnd₃} (hf : firstOfS s = some f) :
    ∃ l, K13.Law.linAt s = some l ∧ f.st = s.st ∧ f.book = s.book ∧ f.own = l.own := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hf
  unfold First.S.firstEnd? at he
  unfold K13.Law.linAt
  split at he
  · rename_i a ha
    cases hl : a.lin with
    | none =>
      rw [hl] at he
      cases he
    | some l =>
      rw [hl] at he
      have he' : (if l.w != noId then some (⟨s.st, s.book, l⟩ : Proof.FirstEnd) else none) =
          some e := he
      split at he'
      · obtain rfl := Option.some.inj he'
        exact ⟨l, by rw [ha]; exact hl, rfl, rfl, rfl⟩
      · cases he'
  · cases he

/-- **The sixth test follows from the table's own item `evalLaid`**: where (Eval) lies among the own
group's open rows, the group has an open row. -/
theorem openRow_of_laid {P : K13.Where} {s : First.S} {f : FirstEnd₃}
    (hf : firstOfS s = some f) (hL : K13.Law.EvalLaid P s) :
    (match f.st.groups[f.own]? with
      | some G => !G.rows.isEmpty
      | none => false) = true := by
  obtain ⟨l, hl, e1, -, e3⟩ := firstOfS_at hf
  obtain ⟨l', _, r, G, hl', -, -, -, hG, hr, -⟩ := hL
  obtain rfl : l = l' := Option.some.inj (hl.symm.trans hl')
  rw [e1, e3, hG]
  show (!G.rows.isEmpty) = true
  cases hE : G.rows.isEmpty with
  | false => rfl
  | true =>
    rw [Array.isEmpty_iff.1 hE] at hr
    cases hr

/-- **THE FIRST CHAIN's TEXT FROM WHAT RIDES ALREADY, AND TWO TESTS MORE**: tidy (it rides in the
first table's "in order"), the weights ("K13.weightsOk"), (Eval) laid (the table's own `evalLaid`);
that the book fits; and the two tests on the own group's members. -/
theorem doorFirstB_of_items {P : K13.Where} {s : First.S} (ht : Means.tidy4B s.st = true)
    (hb : bookFitsB s.book = true) (hw : weightsB s = true) (hL : K13.Law.EvalLaid P s)
    (h2 : ∀ l G, K13.Law.linAt s = some l → s.st.groups[l.own]? = some G →
      G.members.size = 2 ∧ ∀ i ∈ G.members.toList, ∃ x, s.st.oracles[i]? = some x ∧
        x.sampleRows.size = 1) :
    doorFirstB s = true := by
  unfold doorFirstB
  cases hf : firstOfS s with
  | none => rfl
  | some f =>
    obtain ⟨l, hl, e1, e2, e3⟩ := firstOfS_at hf
    have c3 := weightsClause_of hf hw
    have c6 := openRow_of_laid hf hL
    obtain ⟨l', _, _, G, hl', -, -, -, hG, -, -⟩ := hL
    obtain rfl : l = l' := Option.some.inj (hl.symm.trans hl')
    obtain ⟨m2, m1⟩ := h2 l G hl hG
    show (doorFirstL f).all (·.2) = true
    simp only [doorFirstL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, by rw [e2]; exact hb, c3, ?_, ?_, c6⟩
    · rw [e1]
      exact Bool.and_eq_true_iff.1 ht
    · rw [e1, e3, hG]
      simp [m2]
    · rw [e1, e3, hG]
      simp only [List.all_eq_true]
      intro i hi
      obtain ⟨x, hx, h1⟩ := m1 i hi
      rw [hx]
      simp [h1]

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.firstOfS_at
#print axioms VerifiableInference.Desc.Last.openRow_of_laid
#print axioms VerifiableInference.Desc.Last.doorFirstB_of_items
#print axioms VerifiableInference.Desc.Last.joinP_count
#print axioms VerifiableInference.Desc.Last.joinAll_count
#print axioms VerifiableInference.Desc.Last.rows_count
