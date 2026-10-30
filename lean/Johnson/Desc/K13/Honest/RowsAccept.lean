--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/RowsAccept.lean: kind K13's text behind W's commitment accepts: under which
conditions on the state that W's sending has left. Statements with their proofs.

The text (`rows`, Johnson/Desc/K13/Text.lean) and its sub-protocol (`rowsB`,
Johnson/Desc/K13/Kind.lean) have no round and read no column. They make the request's own group, let
the messages of the claim's masks, W and, where the shape asks it, the split's message join it, and
lay the row (Eval). Every test is on the public state; none is on a sent value.

THE TWELVE CONDITIONS ARE, ROUGHLY, OF THREE SORTS. The senders', on what was sent in front (which
messages, of which shapes, with their OOD samples answered): `first`, `split`, `joins`, `table`,
`bits`, and in `masks` that the messages can join. The plan's, on the codes and the shape, which
nobody sends: `codes`, `room`, `small`. This kind's own, on the claim's row, which the batching has
made of challenges and of its ledger's numbers: `point`, `within`, `pad`, and in `masks` which
messages are named. The sort is not exact: `within` and `pad` also read the shapes and pads that
senders have left, and `split` has a clause on the claim's row.
HOW MUCH IS IN THIS. `first`, `point` and the first clause of `split` are tests of the text in their
own words; `codes` is the test of the new group as one test on the codes. `pad` is the last clause
on a new row, TURNED and asked of all messages where the text asks it of the members: the text
compares a coefficient's machine words with 0, `pad` asks that the coefficient reads as 0 in the
field. That the two agree for a row's coefficient is paid in `Fits` and `rowL_ok`
(Johnson/Desc/Means/Forth/YesRow.lean, by `okE_coefficient`, YesWords.lean). What this file adds:
the tests of the joinings and of the new row are carried back to the one statement behind the
sending; the list of the masks' messages has no repeats; the structured vector of (Eval) is in order
and fits.
Main names:
  `evalOf row w lay`: the row (Eval) for the claim that is made of a row on the matrix.
  `linEvalRow_returns`: the maker of (Eval) returns it, if the column point has a coordinate for
    each column variable.
  `evalOf_fits`: a group takes (Eval) (`OnBytes.Means.Fits`), at a statement that is `Built`.
  `SentAtM4 Sh row ids St w`: **the conditions**, at the statement St behind W's sending.
  `rows_accepts`: under them the text accepts; W's number, the own group's number, the number that
    it takes for the first fold's mask and the claim are as they are named.
  `rowsB_accepts`: the same of the sub-protocol's decision (`Block.decide`), at the first chain's
    state.

What is not claimed. That a sender meets the conditions. That the number taken for the first fold's
mask, where that mask is sent ahead, is the right message's: the text takes the last number handed
on. The two theorems do not say which number is taken for the split's message, nor what the
statement behind is. `SentAtM4.pad` speaks of the coefficients of (Eval), which the verifier makes
of challenges: that it holds at every challenge is shown in Johnson/Desc/K13/Honest/PadFree.lean,
not here. That (Eval) is true of anybody's words: Johnson/Desc/K13/Honest/EvalTrue.lean. The tests
of the format's step in front of a decision (`Block.step`) and the test on the plan (`planOk`) are
not spoken of. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.OwnGroup
import Johnson.Desc.Means.Forth.YesRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Own (placeFits tensorInOrder)
open VerifiableInference.Desc.K13.Law

variable {Cl : Type}

/-- **The row (Eval)** for the claim that is made of a row on the matrix. w: W's number. lay: how W
is laid out in its message. -/
def evalOf (row : TensorRow) (w : ℕ) (lay : VectorLay) : OnBytes.Row :=
  addLaid { units := (memberClaim row).masks, target := (memberClaim row).target } w lay
    [Tensor.eq (memberClaim row).psi]

/-- The maker of (Eval) returns it. -/
theorem linEvalRow_returns (Sh : LinShape) (row : TensorRow) (w : ℕ) (lay : VectorLay)
    (h : row.psi.length = Sh.kCol) :
    linEvalRow Sh (memberClaim row) w lay = some (evalOf row w lay) := by
  have hl : (memberClaim row).psi.length = Sh.kCol := h
  unfold linEvalRow evalOf
  simp [hl]

/-- A summand fits its place. -/
theorem placeFits_of {St : Statement} {G : Group} {o : ℕ} {part : OnBytes.Part} {vars index : ℕ}
    (hm : o ∈ G.members.toList) (ht : St.has o part = true) (hv : vars = St.tableBits o part)
    (hi : index < 2 ^ St.tableBits o part) : placeFits St G o part vars index = true := by
  rw [← VerifiableInference.Desc.Own.placeFits_agrees]
  exact (OnBytes.Means.placeOk_iff _ _ _ _ _ _).2 ⟨hm, ht, hv, hi⟩

/-- The structured vector of (Eval) is in order. -/
theorem inOrder_onTable (lay : VectorLay) (psi : List E) (hb : psi.length ≤ lay.bits)
    (h63 : lay.bits ≤ 63) : tensorInOrder (lay.onTable (Tensor.eq psi)) = true := by
  obtain ⟨hv, hd⟩ := onTable_vars lay (Tensor.eq psi) rfl (by rw [vars_eqTensor]; exact hb)
  have hp : (lay.onTable (Tensor.eq psi)).pairs.length = lay.bits := hv
  simp [VerifiableInference.Desc.Own.tensorInOrder, hd, hp, h63]

/-- **A group takes (Eval)**, at a statement that comes from S₀ by making the group g and by
joinings to it. -/
theorem evalOf_fits {S₀ St : Statement} {g c z : ℕ} {M : ℕ → Prop} (B : Built S₀ St g c z M)
    {row : TensorRow} {w : ℕ} {lay : VectorLay} (hw : M w) (hm : ∀ t ∈ row.masks, M t.1.oracle)
    (hb : row.psi.length ≤ lay.bits) (h63 : lay.bits ≤ 63)
    (hWt : S₀.has w .main = true) (hWb : S₀.tableBits w .main = lay.bits)
    (hMt : ∀ t ∈ row.masks, S₀.has t.1.oracle .mask = true ∧
      t.1.index < 2 ^ S₀.tableBits t.1.oracle .mask)
    (hpad : ∀ (o : ℕ) (x : OnBytes.Oracle), S₀.oracles[o]? = some x → ∀ q ∈ x.pad,
      ρg.val ((evalOf row w lay).coefficient o q.1 q.2) = 0)
    (hall : ∀ o, M o → ∃ x : OnBytes.Oracle, S₀.oracles[o]? = some x) :
    ∃ G : Group, St.groups[g]? = some G ∧ G.inRun = false ∧
      OnBytes.Means.Fits St G (evalOf row w lay) := by
  obtain ⟨G, hG, _, _, hr, hmem⟩ := B.grp
  refine ⟨G, hG, hr, by simp [evalOf, addLaid, Row.add], ?_, ?_, rfl, rfl, ?_⟩
  · intro t ht
    obtain rfl : t = ⟨w, .main, lay.onTable (Tensor.eq row.psi)⟩ := by
      simpa [evalOf, addLaid, Row.add, memberClaim] using ht
    refine ⟨inOrder_onTable lay row.psi hb h63, placeFits_of ((hmem w).2 hw) ?_ ?_ ?_⟩
    · rw [B.tables]
      exact hWt
    · rw [B.bits, hWb]
      exact (onTable_vars lay (Tensor.eq row.psi) rfl (by rw [vars_eqTensor]; exact hb)).1
    · exact Nat.pow_pos (by norm_num)
  · intro u hu
    have hu' := Array.mem_toList_iff.2 hu
    simp only [evalOf, addLaid, Row.add, memberClaim, List.foldl_cons, List.foldl_nil] at hu'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu'
    refine placeFits_of ((hmem _).2 (hm t ht)) ?_ rfl ?_
    · rw [B.tables]
      exact (hMt t ht).1
    · rw [B.bits]
      exact (hMt t ht).2
  · intro o ho x' hx' q hq
    obtain ⟨x, hx⟩ := hall o ((hmem o).1 (Array.mem_toList_iff.2 ho))
    obtain ⟨x'', hx'', _, _, e3⟩ := B.orc o x hx
    rw [hx'] at hx''
    obtain rfl := Option.some.inj hx''
    rw [e3] at hq
    exact hpad o x hx q hq

/-- **What W's sending has to leave**, at the statement St behind it. row: the row that the claim is
made of. ids: the numbers handed on. w: W's number. -/
structure SentAtM4 (Sh : LinShape) (row : TensorRow) (ids : Array ℕ) (St : Statement) (w : ℕ) :
    Prop where
  /-- W is the first of the messages sent -/
  first : ids[0]? = some w
  /-- where the shape asks for a split, its message is the second; it can join; it is neither W nor
  a message of the claim's masks -/
  split : Sh.ownSplitNeeded = true → ∃ sp, ids[1]? = some sp ∧
    CanJoin St Sh.w.code Sh.ownMaskCode sp ∧ sp ≠ w ∧ ∀ t ∈ row.masks, t.1.oracle ≠ sp
  /-- the own group's two codes are there, and the mask code is not longer than the main code -/
  codes : Ground.groupOk St.codes Sh.w.code Sh.ownMaskCode = true
  /-- the messages of the claim's masks can join; none is W -/
  masks : ∀ t ∈ row.masks, CanJoin St Sh.w.code Sh.ownMaskCode t.1.oracle ∧ t.1.oracle ≠ w
  /-- W can join -/
  joins : CanJoin St Sh.w.code Sh.ownMaskCode w
  /-- the claim's point has a coordinate for each column variable -/
  point : row.psi.length = Sh.kCol
  /-- W's vector fits its table -/
  room : Sh.kCol ≤ (linLayW St.codes Sh).bits
  /-- the table has at most 63 index bits -/
  small : (linLayW St.codes Sh).bits ≤ 63
  /-- W has a main table -/
  table : St.has w .main = true
  /-- W's main table has the layout's number of index bits -/
  bits : St.tableBits w .main = (linLayW St.codes Sh).bits
  /-- the claim's mask entries lie within their tables -/
  within : ∀ t ∈ row.masks, St.has t.1.oracle .mask = true ∧
    t.1.index < 2 ^ St.tableBits t.1.oracle .mask
  /-- the coefficient of (Eval) reads as 0 on every entry that masks an OOD answer -/
  pad : ∀ (o : ℕ) (x : OnBytes.Oracle), St.oracles[o]? = some x → ∀ q ∈ x.pad,
    ρg.val ((evalOf row w (linLayW St.codes Sh)).coefficient o q.1 q.2) = 0

/-- Where a number is handed on, there is a last one. -/
theorem back_of_first {ids : Array ℕ} {w : ℕ} (h : ids[0]? = some w) : ∃ v, ids.back? = some v := by
  have h0 : 0 < ids.size := by
    by_contra c
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at h
    cases h
  exact ⟨ids[ids.size - 1], Array.getElem?_eq_getElem (by omega)⟩

/-- **The text behind W's commitment accepts.** -/
theorem rows_accepts {Sh : LinShape} {row : TensorRow} {ids : Array ℕ} {d : St} {w : ℕ}
    (H : SentAtM4 Sh row ids d.st w) :
    ∃ o : LinFirst × St, rows Sh (memberClaim row) ids d = .ok o ∧ o.1.w = w ∧
      o.1.own = d.st.groups.size ∧ o.1.mask = (if Sh.masksAhead then ids.back? else none) ∧
      o.1.claim = memberClaim row := by
  have h0 := _root_.Desc.K14.Honest.newGroupP_of d Sh.w.code Sh.ownMaskCode H.codes
  have B0 : Built d.st ({ d with st := Ground.withGroup d.st Sh.w.code Sh.ownMaskCode } : St).st
      d.st.groups.size Sh.w.code Sh.ownMaskCode fun _ => False :=
    Built.start d.st Sh.w.code Sh.ownMaskCode
  -- the messages of the claim's masks
  have hmem : ∀ o, o ∈ listOfT ((memberClaim row).masks.toList.map (·.oracle)) ↔
      ∃ t ∈ row.masks, t.1.oracle = o := by
    intro o
    rw [listOfT_eq, Fmt.listOf_mem _ o]
    simp [memberClaim]
  have hnd : (listOfT ((memberClaim row).masks.toList.map (·.oracle))).Nodup := by
    rw [listOfT_eq]
    exact (Fmt.listOf_incr _).imp fun h => Nat.ne_of_lt h
  obtain ⟨d₁, hj1, B1⟩ := Built.steps _ _ _ B0
    (fun o ho => by
      obtain ⟨t, ht, rfl⟩ := (hmem o).1 ho
      exact (H.masks t ht).1) hnd (fun _ _ h => h)
  -- W
  obtain ⟨d₂, hj2, B2⟩ := Built.step d₁ B1 H.joins (fun h => h.elim
    (fun h' => by
      obtain ⟨t, ht, e⟩ := (hmem w).1 h'
      exact (H.masks t ht).2 e) id)
  -- the split's message
  obtain ⟨sp, d₃, M₃, hsp, hj3, B3, hM3⟩ : ∃ (sp : ℕ) (d₃ : St) (M₃ : ℕ → Prop),
      (if Sh.ownSplitNeeded then ids[1]? else some noId) = some sp ∧
      (if Sh.ownSplitNeeded then Ground.joinP d₂ d.st.groups.size sp false else some d₂) =
        some d₃ ∧
      Built d.st d₃.st d.st.groups.size Sh.w.code Sh.ownMaskCode M₃ ∧
      (∀ o, M₃ o ↔ ((Sh.ownSplitNeeded = true ∧ o = sp) ∨ o = w ∨
        ∃ t ∈ row.masks, t.1.oracle = o)) := by
    by_cases hs : Sh.ownSplitNeeded = true
    · obtain ⟨sp, h1, h2, h3, h4⟩ := H.split hs
      obtain ⟨d₃, hj3, B3⟩ := Built.step d₂ B2 h2 (fun h => h.elim h3 fun h' => h'.elim
        (fun h'' => by
          obtain ⟨t, ht, e⟩ := (hmem sp).1 h''
          exact h4 t ht e) id)
      refine ⟨sp, d₃, _, by rw [if_pos hs]; exact h1, by rw [if_pos hs]; exact hj3, B3,
        fun o => ?_⟩
      show (o = sp ∨ (o = w ∨ (o ∈ listOfT ((memberClaim row).masks.toList.map (·.oracle)) ∨
        False))) ↔ _
      rw [hmem o]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inl ⟨hs, h⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact h.elim
      · rintro (⟨_, h⟩ | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
    · refine ⟨noId, d₂, _, by rw [if_neg hs], by rw [if_neg hs], B2, fun o => ?_⟩
      show (o = w ∨ (o ∈ listOfT ((memberClaim row).masks.toList.map (·.oracle)) ∨ False)) ↔ _
      rw [hmem o]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact h.elim
      · rintro (⟨h, _⟩ | h | h)
        · exact absurd h hs
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
  -- the number of the first fold's mask
  have hmask : (if Sh.masksAhead then ids.back?.map some else some none) =
      some (if Sh.masksAhead then ids.back? else none) := by
    by_cases ha : Sh.masksAhead = true
    · obtain ⟨v, hv⟩ := back_of_first H.first
      rw [if_pos ha, if_pos ha, hv]
      rfl
    · rw [if_neg ha, if_neg ha]
  -- (Eval)
  have hcodes : d₃.st.codes = d.st.codes := B3.codes
  have hrow := linEvalRow_returns Sh row w (linLayW d₃.st.codes Sh) H.point
  obtain ⟨G, hG, hr, hf⟩ := evalOf_fits B3 (row := row) (w := w) (lay := linLayW d.st.codes Sh)
    ((hM3 w).2 (Or.inr (Or.inl rfl))) (fun t ht => (hM3 _).2 (Or.inr (Or.inr ⟨t, ht, rfl⟩)))
    (by rw [H.point]; exact H.room) H.small H.table H.bits H.within H.pad
    (fun o ho => by
      rcases (hM3 o).1 ho with ⟨hs, rfl⟩ | rfl | ⟨t, ht, rfl⟩
      · obtain ⟨sp', h1, ⟨x, hx, _⟩, _⟩ := H.split hs
        rw [if_pos hs, h1] at hsp
        obtain rfl := Option.some.inj hsp
        exact ⟨x, hx⟩
      · obtain ⟨x, hx, _⟩ := H.joins
        exact ⟨x, hx⟩
      · obtain ⟨x, hx, _⟩ := (H.masks t ht).1
        exact ⟨x, hx⟩)
  rw [hcodes] at hrow
  obtain ⟨d₄, h4⟩ : ∃ d₄ : St, Ground.addRowsP d₃ d.st.groups.size
      [evalOf row w (linLayW d.st.codes Sh)] = some d₄ :=
    ⟨_, OnBytes.Means.addRowsP_of_fits d₃ d.st.groups.size G
      [evalOf row w (linLayW d.st.codes Sh)] hG hr (fun r hr' => by
        rw [List.mem_singleton.1 hr']
        exact hf)⟩
  refine ⟨({ w := w, split := sp, own := d.st.groups.size,
             mask := if Sh.masksAhead then ids.back? else none, claim := memberClaim row }, d₄),
    ?_, rfl, rfl, rfl, rfl⟩
  simp only [rows_is, Law.bind_ok, Law.there_ok, Law.pure_ok]
  exact ⟨w, H.first, _, h0, d₁, hj1, d₂, hj2, sp, hsp, d₃, hj3, _, hmask, _,
    by rw [hcodes]; exact hrow, _, h4, rfl⟩

/-- **The decision of the sub-protocol behind W's commitment accepts**, at the first chain's state.
a: the state's part for the chain's end, behind W's sending. -/
theorem rowsB_accepts {P : Where} {s : S} {a : First.MemOwn} {l : LinFirst} {row : TensorRow}
    {w : ℕ} (hs : s.here = .mem a) (hl : a.lin = some l) (hrow : l.claim = memberClaim row)
    (H : SentAtM4 P.lin row a.ids s.st w) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ∃ (s' : S) (l' : LinFirst), (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s' ∧
      Law.linAt s' = some l' ∧ l'.w = w ∧ l'.own = s.st.groups.size ∧
      l'.mask = (if P.lin.masksAhead then a.ids.back? else none) ∧
      l'.claim = memberClaim row := by
  obtain ⟨o, ho, e1, e2, e3, e4⟩ := rows_accepts (d := dOf s) H
  obtain ⟨p, hp, f1, f2, f3⟩ : ∃ p : K13.Part, atS.get? s = some p ∧ p.lin = a.lin ∧
      p.ids = a.ids ∧ p.d = dOf s := by
    simp only [atS, hs]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  refine ⟨atS.set s { p with lin := some o.1, d := o.2 }, o.1, ?_, ?_, e1, e2, e3, e4⟩
  · simp only [rowsB, still, Law.bind_ok, Law.there_ok, Law.pure_ok, Lens.part]
    exact ⟨p, hp, l, by rw [f1, hl], o, by rw [f2, f3, hrow]; exact ho, rfl⟩
  · simp only [atS, hs]
    rfl

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.linEvalRow_returns
#print axioms VerifiableInference.Desc.K13.Honest.placeFits_of
#print axioms VerifiableInference.Desc.K13.Honest.inOrder_onTable
#print axioms VerifiableInference.Desc.K13.Honest.evalOf_fits
#print axioms VerifiableInference.Desc.K13.Honest.back_of_first
#print axioms VerifiableInference.Desc.K13.Honest.rows_accepts
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_accepts
