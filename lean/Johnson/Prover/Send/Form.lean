-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Send/Form.lean: THE SHARED "SENDING" (the kind K1), THE PROVER's SIDE: THE FORM's
HALF: K1's own decision says yes, and the record behind is a written term. Statements and proofs.

General in the place P : K1.Par, in the carried record and in the chain's own values.

  factors_of_fit   NO STOP: on rounds that fit the kind's rounds no seed's factor is spelt by three
                   words 0: so K1's test "a seed's factor is 0" never refuses behind roundsFit
  send_yes_of      the same from what K1's text reads of the two rounds alone
  send_yes         SendFront and rounds that fit: K1.decideSend = .ok (the numbers, K1.behind ...).
                   NO PREMISE ON WHAT THE PROVER SENDS but roundsFit's count of items
  sendOwn_yes, sendOwn_step   so the block's own decide, and the block as a step: no column is taken
  behind_at        message number k behind the sending, as a term (K1.wr), at all seeds and answers
  wr_sampled, wr_unsampled    its fields, one by one: shape, sampled, sampleRows, pad, groups,
                   ledger (freshLedger: next := 0), spentAsMask
  behind_rest      what the sending leaves as it was; the size; the roots; the book
  answers_fit, fit_answers, answers_lt   the written answers are as many as the kind's second round
                   asks, all of them answers: rounds that fit still fit with them; their words are
                   below the prime
  dsElems_place, shapesOf_at, length_answersAt, answers_flat, sum_range_shapes, length_answers
                   tools
  SendFront.of_lengths        where every code's length is a power of two the clause on the pads'
                   places follows from the tests on the plan

By: zip_factors (Johnson/Prover/Send/Factors.lean); K1.decideSend_iff
(Johnson/Desc/K1/Law/Writes3.lean: the decision's yes as an equivalence, the record behind as
K1.behind); fitB_true, le_seeds, answers_len, answers_sum, pad_isSome (K1/Law/When.lean); outs_get,
offset (K1/Law/Targets2.lean); outs_length (K1/Law/GoodSend3.lean); lt_ofE
(Johnson/Prover/Link/BaseClaim.lean).

Limits. "No factor is 0" is said of words, as K1's text says it; in the field it wants every word
below the prime beside it (K1.okView_factors, Johnson/Desc/K1/Law/OkView.lean). That written rounds
fit (roundsFit) is a premise: the first round's draws are the compiler's. Of the three other texts
that call K1.decideSend (a segment's first and later moments) nothing is said. Nothing on what a row
means (Johnson/Prover/Send/Says.lean), on columns
(Johnson/Prover/Send/Enc.lean), on soundness, or on what any entry discloses
or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Send.Front
import Johnson.Prover.Send.Factors
import Johnson.Desc.K1.Law.When
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Prover.Link.BaseClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open OnBytes OnBytes.Slice OnBytes.Means Cb VerifiableInference.Desc
open _root_.Desc.Plain (DState)

/-! ## No stop -/

/-- What the format lists as the elements of the place's round of seeds. -/
theorem dsElems_place (P : K1.Par) (h0 : P.seeds ≠ 0) :
    Fmt.dsElems (K1.seedEntry P) .seeds = Fmt.dsSeeds P.seeds P.coordinates := by
  have hs : 0 < P.seeds := Nat.pos_of_ne_zero h0
  have e : P.seeds * (P.coordinates + 1) - P.seeds = P.seeds * P.coordinates := by
    rw [Nat.mul_succ, Nat.add_sub_cancel]
  unfold Fmt.dsElems
  rw [if_pos rfl]
  show Fmt.dsSeeds P.seeds ((P.seeds * (P.coordinates + 1) - P.seeds) / P.seeds) ++
    List.replicate ((P.seeds * (P.coordinates + 1) - P.seeds) % P.seeds) Fmt.Draw.elem = _
  rw [e, Nat.mul_div_cancel_left _ hs, Nat.mul_mod_right]
  simp

/-- **NO STOP.** On rounds that fit, no seed's factor is spelt by three words 0. -/
theorem factors_of_fit (P : K1.Par) (r₁ r₂ : Fmt.RoundView)
    (h : roundsFit (K1.rounds P) [r₁, r₂] = true) :
    ∀ s ∈ K1.seedsOf P r₁, isZeroE s.2 = false := by
  by_cases h0 : P.seeds = 0
  · intro s hs
    unfold K1.seedsOf at hs
    rw [h0] at hs
    simp [K1.cutSeeds] at hs
  · have hlen : r₁.drawn.elems.length = P.seeds * (P.coordinates + 1) :=
      (K1.fit_facts P r₁ r₂ h).1
    simp only [K1.rounds, roundsFit, Bool.and_eq_true] at h
    have nz : drawsMarkedNonzeroHaveNonzeroWords { entry := K1.seedEntry P } r₁ = true := h.1.2
    unfold drawsMarkedNonzeroHaveNonzeroWords at nz
    have hkind : Fmt.kindOf (K1.seedEntry P).name = some .seeds := by
      show Fmt.kindOf "SEND seed" = some .seeds
      decide
    rw [hkind] at nz
    simp only [Option.any_some] at nz
    rw [dsElems_place P h0] at nz
    exact zip_factors P.coordinates P.seeds r₁.drawn.elems hlen nz

/-! ## The yes -/

/-- The yes, from what K1's text reads of the two rounds alone: no seed's factor is three words 0,
and round 2 holds as many answers as the place counts. For a caller whose second round goes on
behind the answers, and so does not fit the kind's own second round. -/
theorem send_yes_of {L : Type} (P : K1.Par) (d : DState L) (r₁ r₂ : Fmt.RoundView) (F : SendFront P d)
    (hz : ∀ s ∈ K1.seedsOf P r₁, isZeroE s.2 = false)
    (hn : (K1.answersIn r₂).length = P.answers) :
    K1.decideSend P none d [r₁, r₂] =
      .ok (numbers P d.st.oracles.size, K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂)) := by
  refine (K1.decideSend_iff P none d _ r₁ r₂ _).2 ⟨⟨rfl, F.codes, hz, ?_, ?_⟩, rfl, rfl⟩
  · have hp := F.plan
    simp only [K1.planOkOwn, K1.planOk, Bool.and_eq_true] at hp
    obtain ⟨⟨⟨hsh, hlay⟩, _⟩, _⟩ := hp
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    rw [F.codes]
    exact ⟨hsh, hlay, F.step⟩
  · refine K1.fitB_true _ _ _ _ (fun s hs h0 => ⟨K1.le_seeds P s hs, ?_⟩)
      (by rw [hn, K1.answers_sum])
    rw [← Own.padMade_eq]
    refine F.pads s ?_
    simp only [K1.Par.tuple, List.mem_filter]
    exact ⟨hs, by simpa using h0⟩

/-- **K1's own decision of the sending says yes, and the record behind is K1.behind.** -/
theorem send_yes {L : Type} (P : K1.Par) (d : DState L) (r₁ r₂ : Fmt.RoundView) (F : SendFront P d)
    (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true) :
    K1.decideSend P none d [r₁, r₂] =
      .ok (numbers P d.st.oracles.size, K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂)) :=
  send_yes_of P d r₁ r₂ F (factors_of_fit P r₁ r₂ hfit) (K1.answers_len P r₁ r₂ hfit)

/-- **The block's own decide.** -/
theorem sendOwn_yes {Cl : Type} (P : K1.Par) (d : DState (Array ℕ)) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (F : SendFront P d)
    (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true) :
    (K1.sendOwn P : Block (K1.Owing (DState (Array ℕ))) Cl).decide ⟨none, d⟩ [r₁, r₂] gs =
      .ok ⟨none, { K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂) with
        loc := numbers P d.st.oracles.size }⟩ := by
  show (K1.decideSend P none d [r₁, r₂]).map _ = _
  rw [send_yes P d r₁ r₂ F hfit]
  rfl

/-- **The block as a step**: no column is taken. -/
theorem sendOwn_step {Cl : Type} (ft : ℕ) (P : K1.Par) (d : DState (Array ℕ)) (r₁ r₂ : Fmt.RoundView)
    (cols : List OpenedColumn) (F : SendFront P d) (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true) :
    Block.step ft (K1.sendOwn P : Block (K1.Owing (DState (Array ℕ))) Cl) ⟨none, d⟩ [r₁, r₂] cols =
      .ok (⟨none, { K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂) with
        loc := numbers P d.st.oracles.size }⟩, 0) := by
  have hfit' : roundsFit (K1.rounds P) [noDigest r₁, noDigest r₂] = true := hfit
  have hd := sendOwn_yes (Cl := Cl) P d (noDigest r₁) (noDigest r₂) [] F hfit'
  have hr : roundsFit (K1.sendOwn P : Block (K1.Owing (DState (Array ℕ))) Cl).rounds [r₁, r₂] =
      true := hfit
  have hg : groupsOf ft (K1.sendOwn P : Block (K1.Owing (DState (Array ℕ))) Cl).rounds
      [r₁.drawn, r₂.drawn] = [] := rfl
  unfold Block.step need
  simp only [bind, Except.bind, pure, Except.pure, hr, if_true, hg, List.flatMap_nil,
    List.length_nil, List.take_zero, List.map_nil, beq_self_eq_true, List.map_cons, regroup, hd]
  rfl

/-! ## The record behind, field by field -/

/-- The place's shapes by index. -/
theorem shapesOf_at (P : K1.Par) (k : ℕ) (hk : k < P.sent.size) :
    (K1.shapesOf P)[k]? = some (shapeAt P k) := by
  unfold K1.shapesOf shapeAt
  rw [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hk,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
  rfl

/-- **Message number k behind the sending, as a term.** -/
theorem behind_at {L : Type} (P : K1.Par) (d : DState L) (seeds : List (List E × E))
    (ys : List E) (k : ℕ) (hk : k < P.sent.size) :
    (K1.behind P d seeds ys).st.oracles[d.st.oracles.size + k]? =
      some (K1.wr P.codes seeds (d.st.oracles.size + k) (shapeAt P k)
        (ys.drop (K1.offset P k))) := by
  show ((d.st.oracles.toList ++ K1.outs P.codes seeds d.st.oracles.size (K1.shapesOf P)
    ys).toArray)[d.st.oracles.size + k]? = _
  rw [List.getElem?_toArray, List.getElem?_append_right (by rw [Array.length_toList]; omega),
    Array.length_toList, Nat.add_sub_cancel_left]
  have h := shapesOf_at P k hk
  have hl : k < (K1.shapesOf P).length := (List.getElem?_eq_some_iff.1 h).1
  rw [List.getElem?_eq_getElem hl] at h
  rw [K1.outs_get P.codes seeds (K1.shapesOf P) d.st.oracles.size ys k hl, Option.some.inj h]
  rfl

/-- A sampled message behind the sending, field by field. -/
theorem wr_sampled (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape)
    (ys : List E) (h0 : s.answers ≠ 0) :
    (K1.wr codes seeds o s ys).shape = s ∧ (K1.wr codes seeds o s ys).sampled = true ∧
    (K1.wr codes seeds o s ys).sampleRows = K1.rowsOf codes seeds o s ys ∧
    (K1.wr codes seeds o s ys).pad =
      ((Own.padMade codes s).getD []).map (fun p => (p.part, p.index)) ∧
    (K1.wr codes seeds o s ys).groups = [] ∧
    (K1.wr codes seeds o s ys).ledger = freshLedger codes s ∧
    (K1.wr codes seeds o s ys).spentAsMask = false := by
  unfold K1.wr
  rw [if_neg h0]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A message without a sample is as it was received. -/
theorem wr_unsampled (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape)
    (ys : List E) (h0 : s.answers = 0) : K1.wr codes seeds o s ys = { shape := s } := by
  unfold K1.wr
  rw [if_pos h0]
  rfl

/-- **What the sending leaves as it was; the size; the roots; the book.** -/
theorem behind_rest {L : Type} (P : K1.Par) (d : DState L) (seeds : List (List E × E))
    (ys : List E) :
    (K1.behind P d seeds ys).st.codes = d.st.codes ∧
    (K1.behind P d seeds ys).st.groups = d.st.groups ∧
    (K1.behind P d seeds ys).opened = d.opened ∧ (K1.behind P d seeds ys).loc = d.loc ∧
    (K1.behind P d seeds ys).st.oracles.size = d.st.oracles.size + P.sent.size ∧
    (∀ o, o < d.st.oracles.size → (K1.behind P d seeds ys).st.oracles[o]? = d.st.oracles[o]?) ∧
    (K1.behind P d seeds ys).roots = d.roots + ((layTrees P.codes P.sent).getD {}).shapes.size ∧
    (K1.behind P d seeds ys).book =
      (K1.recvD P.gp.firstTree d P.sent ((layTrees P.codes P.sent).getD {})).book := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, fun o ho => ?_, rfl, rfl⟩
  · show ((d.st.oracles.toList ++ K1.outs P.codes seeds d.st.oracles.size (K1.shapesOf P)
      ys).toArray).size = _
    rw [List.size_toArray, List.length_append, K1.outs_length, Array.length_toList]
    simp [K1.shapesOf]
  · show ((d.st.oracles.toList ++ K1.outs P.codes seeds d.st.oracles.size (K1.shapesOf P)
      ys).toArray)[o]? = _
    rw [List.getElem?_toArray, List.getElem?_append_left (by rw [Array.length_toList]; exact ho),
      Array.getElem?_toList]

/-! ## The written answers, as items -/

theorem length_answersAt (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) (k : ℕ) :
    (answersAt P S' first w' seeds k).length = (shapeAt P k).answers := by
  unfold answersAt
  rw [List.length_map, List.length_range]

/-- The answers, message by message: a message without a sample has none. -/
theorem answers_flat (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) :
    answers P S' first w' seeds =
      (List.range P.sent.size).flatMap (answersAt P S' first w' seeds) := by
  unfold answers
  generalize List.range P.sent.size = l
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.flatMap_cons, ← ih]
    by_cases h0 : (shapeAt P k).answers = 0
    · have e : answersAt P S' first w' seeds k = [] := by
        unfold answersAt
        rw [h0]
        rfl
      rw [e, List.nil_append, List.filter_cons_of_neg (by simp [h0])]
    · rw [List.filter_cons_of_pos (by simp [h0]), List.flatMap_cons]
      rfl

/-- A sum over the first n numbers, against the list of the place's shapes. -/
theorem sum_range_shapes (P : K1.Par) : ∀ n, n ≤ P.sent.size →
    ((List.range n).map fun k => (shapeAt P k).answers).sum = K1.offset P n
  | 0, _ => by simp [K1.offset, K1.offsetOf]
  | n + 1, h => by
    have hn : n < P.sent.size := h
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_shapes P n (Nat.le_of_lt hn)]
    unfold K1.offset K1.offsetOf
    rw [List.take_succ, shapesOf_at P n hn]
    simp

theorem length_answers (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) : (answers P S' first w' seeds).length = P.answers := by
  rw [answers_flat, List.length_flatMap]
  simp only [length_answersAt]
  rw [sum_range_shapes P _ (Nat.le_refl _), K1.answers_sum]
  unfold K1.offset K1.offsetOf
  rw [List.take_of_length_le (by simp [K1.shapesOf])]

/-- **Round 2's items are what the kind's rounds ask**, by the answers' make. -/
theorem answers_fit (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) :
    ((answers P S' first w' seeds).map Fmt.ItemValue.answer).map itemOf =
      (Fmt.DeclaredRound.items { entry := K1.answerEntry P }).filter (· != .root) := by
  have e : (Fmt.DeclaredRound.items { entry := K1.answerEntry P }).filter (· != .root) =
      List.replicate P.answers .answer := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, K1.answerEntry]
  rw [e, List.map_map, ← length_answers P S' first w' seeds]
  generalize answers P S' first w' seeds = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.length_cons, List.replicate_succ, ih]
    rfl

/-- **Rounds that fit still fit where round 2 shows the written answers**: so the premise on round 2
(Johnson/Prover/Send/Says.lean) and roundsFit can be met together. -/
theorem fit_answers (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) (r₁ r₂ : Fmt.RoundView) (h : roundsFit (K1.rounds P) [r₁, r₂] = true) :
    roundsFit (K1.rounds P)
      [r₁, { r₂ with vals := (answers P S' first w' seeds).map .answer }] = true := by
  simp only [K1.rounds, roundsFit, Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨h1, ⟨⟨⟨⟨⟨⟨⟨_, a⟩, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩⟩ := h
  exact ⟨h1, ⟨⟨⟨⟨⟨⟨⟨answers_fit P S' first w' seeds, a⟩, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩⟩

/-- **The written answers' words are below the prime.** -/
theorem answers_lt (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) : ∀ x ∈ answers P S' first w' seeds,
    (x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true := by
  intro x hx
  rw [answers_flat] at hx
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hk
  exact Johnson.Prover.Link.lt_ofE _

/-- Where every code's length is a power of two, the clause on the pads' places follows. -/
theorem SendFront.of_lengths {L : Type} (P : K1.Par) (d : DState L) (hc : d.st.codes = P.codes)
    (hp : K1.planOkOwn P = true) (hs : d.st.oracles.size = d.book.place.size)
    (hl : P.codes.lengthsOk = true) : SendFront P d := by
  refine ⟨hc, hp, hs, fun s hs' => ?_⟩
  have hp' := hp
  simp only [K1.planOkOwn, K1.planOk, Bool.and_eq_true] at hp'
  obtain ⟨⟨⟨hsh, _⟩, _⟩, hpad⟩ := hp'
  have hm := hs'
  simp only [K1.Par.tuple, List.mem_filter] at hm
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hm.1
  rw [Own.padMade_eq]
  exact K1.pad_isSome _ _ hl
    (Array.all_eq_true_iff_forall_mem.1 hsh n (Array.mem_toList_iff.1 hn))
    (List.all_eq_true.1 hpad n.shape hs')

end Johnson.Prover.Send

#print axioms Johnson.Prover.Send.dsElems_place
#print axioms Johnson.Prover.Send.factors_of_fit
#print axioms Johnson.Prover.Send.send_yes_of
#print axioms Johnson.Prover.Send.send_yes
#print axioms Johnson.Prover.Send.sendOwn_yes
#print axioms Johnson.Prover.Send.sendOwn_step
#print axioms Johnson.Prover.Send.shapesOf_at
#print axioms Johnson.Prover.Send.behind_at
#print axioms Johnson.Prover.Send.wr_sampled
#print axioms Johnson.Prover.Send.wr_unsampled
#print axioms Johnson.Prover.Send.behind_rest
#print axioms Johnson.Prover.Send.length_answersAt
#print axioms Johnson.Prover.Send.answers_flat
#print axioms Johnson.Prover.Send.sum_range_shapes
#print axioms Johnson.Prover.Send.length_answers
#print axioms Johnson.Prover.Send.answers_fit
#print axioms Johnson.Prover.Send.fit_answers
#print axioms Johnson.Prover.Send.answers_lt
#print axioms Johnson.Prover.Send.SendFront.of_lengths
