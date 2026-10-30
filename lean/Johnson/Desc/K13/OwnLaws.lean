-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/OwnLaws.lean (kind K13): THEOREMS on Johnson/Desc/K13/Own.lean: WHAT A YES OF EACH
OF THE FIVE GIVES, as a proposition; and THAT EACH AGREES WITH THE FUNCTION OF THE PROGRAM
`verify-on-bytes`, at all arguments.

What a yes gives (each an "if and only if").
  `pileOnTable_iff`: the message of index masks has been sent; it has mask rows alone, is sampled
    and has the mask code of the request's own group; the pile has a row; the table has a column
    variable; and of every row of the pile: every mask entry is an entry of that message, the point
    has kCol coordinates, every weight has kRow variables.
  `pileForm_iff`: the pile has a first row; kCol is at least 1; and of every row: the point has kCol
    coordinates, there is a weight, and every weight has as many variables as the first row's first
    weight.
  `runSum_iff`: the eight comparisons of sizes, three of them on what was SENT (as many rounds were
    heard as there are variables; as many values as maps are shown; in each round one coefficient
    fewer than the variable's polynomial has), and what is handed on is `outOf`, written out.
  `messageW_iff`: a yes just if no mask is sent ahead or the request's own test has a stage.
    `evalRow_iff`: the claim's point has kCol coordinates, and the row is the one written out.

Agreement, at all arguments.
  `pileOnTable_agrees`: `(pileOnTable st S i pile).isOk = memberRowsFit st S i pile` ·
    `pileForm_agrees`: `(pileForm kCol pile).isOk = Batt.fits kCol pile` · `runSum_agrees`: `(runSum
    c S fresh h).toOption = Psc.run c S fresh h` · `messageW_agrees`: `(messageW S).toOption =
    linMessageW S` · `evalRow_agrees`: `(evalRow S claim w lay).toOption = linEvalRow S claim w lay`
    · beneath them `weightFits_agrees`, `splitNeeded_agrees`, `maskNotice_agrees`.

Limits. Equations on what texts return. Nothing on soundness, on an honest prover or on hiding.


-/
import Johnson.Desc.K13.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Own
open OnBytes OnBytes.Params

/-! ## 0 Answers -/

theorem need_iff (n : String) (b : Bool) : need n b = .ok () ↔ b = true := by
  cases b <;> simp [need]

theorem need_bind_iff {α : Type} (n : String) (b : Bool) (k : Unit → Ans α) (x : α) :
    (need n b >>= k) = .ok x ↔ b = true ∧ k () = .ok x := by
  cases b <;> simp [need, bind, Except.bind]

theorem there_bind_iff {α β : Type} (n : String) (o : Option α) (k : α → Ans β) (y : β) :
    (there n o >>= k) = .ok y ↔ ∃ x, o = some x ∧ k x = .ok y := by
  cases o <;> simp [there, bind, Except.bind]

theorem isOk_need (n : String) (b : Bool) : (need n b).isOk = b := by
  cases b <;> rfl

theorem isOk_need_bind {α : Type} (n : String) (b : Bool) (k : Unit → Ans α) :
    (need n b >>= k).isOk = (b && (k ()).isOk) := by
  cases b <;> rfl

theorem toOption_need_bind {α : Type} (n : String) (b : Bool) (k : Unit → Ans α) :
    (need n b >>= k).toOption = if b then (k ()).toOption else none := by
  cases b <;> rfl

theorem ite_ite_none {α : Type} (a b : Bool) (x : Option α) :
    (if a = true then (if b = true then x else none) else none) =
      if (a && b) = true then x else none := by
  cases a <;> cases b <;> rfl

theorem isOk_iff {α : Type} (x : Ans α) : x.isOk = true ↔ ∃ a, x = .ok a := by
  cases x <;> simp [Except.isOk, Except.toBool]

/-! ## 1 The pile against the table -/

theorem pileOnTable_agrees (st : Statement) (S : LinShape) (i : Nat) (pile : List TensorRow) :
    (pileOnTable st S i pile).isOk = memberRowsFit st S i pile := by
  unfold pileOnTable memberRowsFit
  cases st.oracles[i]? with
  | none => rfl
  | some x =>
    show (need _ _ >>= fun _ => need _ _ >>= fun _ => need _ _ >>= fun _ => need _ _).isOk = _
    rw [isOk_need_bind, isOk_need_bind, isOk_need_bind, isOk_need]
    have e : pile.all (rowOnTable S i) = pile.all fun r =>
        (r.masks.all fun m => m.1.oracle == i) && r.psi.length == S.kCol &&
          r.g.all (·.vars == S.kRow) := rfl
    rw [e]
    simp only [masksMessageFits, Bool.and_assoc]

theorem pileOnTable_iff (st : Statement) (S : LinShape) (i : Nat) (pile : List TensorRow) :
    pileOnTable st S i pile = .ok () ↔
      ∃ x, st.oracles[i]? = some x ∧
        (x.shape.mainRows = 0 ∧ 0 < x.shape.maskRows ∧ 0 < x.shape.answers ∧
          x.shape.maskCode = S.ownMaskCode) ∧
        pile ≠ [] ∧ 0 < S.kCol ∧
        ∀ r ∈ pile, (∀ m ∈ r.masks, m.1.oracle = i) ∧ r.psi.length = S.kCol ∧
          ∀ t ∈ r.g, t.vars = S.kRow := by
  unfold pileOnTable
  rw [there_bind_iff]
  refine exists_congr fun x => and_congr_right fun _ => ?_
  rw [need_bind_iff, need_bind_iff, need_bind_iff, need_iff]
  simp [masksMessageFits, rowOnTable, and_assoc]

/-! ## 2 The pile's form -/

theorem pileForm_agrees (kCol : Nat) (pile : List TensorRow) :
    (pileForm kCol pile).isOk = Batt.fits kCol pile := by
  cases pile with
  | nil => rfl
  | cons r l =>
    show (need _ _ >>= fun _ => need _ _).isOk = _
    rw [isOk_need_bind, isOk_need]
    rfl

theorem pileForm_iff (kCol : Nat) (pile : List TensorRow) :
    pileForm kCol pile = .ok () ↔
      ∃ r, pile.head? = some r ∧ 1 ≤ kCol ∧
        ∀ s ∈ pile, s.psi.length = kCol ∧ s.g ≠ [] ∧
          ∀ t ∈ s.g, some t.vars = r.g.head?.map Tensor.vars := by
  unfold pileForm
  rw [there_bind_iff]
  refine exists_congr fun r => and_congr_right fun _ => ?_
  rw [need_bind_iff, need_iff]
  simp [rowForm, and_assoc]

/-! ## 3 One run of the masked sumcheck -/

theorem weightFits_agrees (w : Psc.Weight) : weightFits w = w.fits := rfl

/-- What a run hands on where it says yes, written out. -/
def outOf (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (h : Psc.Heard) : Psc.Out :=
  let vars := Psc.varsOf c S
  let challenges := h.rounds.map (·.2)
  let point := challenges.take c.vars.length
  let a := S.coeffs point h.values
  let hw := Psc.hidingWalk (vars.zip challenges)
  let last := Psc.claimAfter vars h.rounds (addE h.mu (mulE h.eps c.target))
  let beta := if S.shown == 0 then none else challenges.getLast?
  { point := point
    rowMasks := fresh.zip hw.1 ++ Psc.scaleForm (mulE h.eps hw.2) c.masks
    rowMaps := (a.drop 1).map fun x => mulE h.eps x
    rowTarget := subE last (mulE h.eps (a.headD zeroE))
    ends := ((fresh.drop hw.1.length).zip h.values).map fun p =>
      ⟨point, [(p.1, beta.getD zeroE)], p.2⟩
    eps := h.eps
    beta := beta }

theorem runSum_agrees (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (h : Psc.Heard) :
    (runSum c S fresh h).toOption = Psc.run c S fresh h := by
  unfold runSum Psc.run
  have e : c.vars.all weightFits = c.vars.all Psc.Weight.fits := rfl
  simp only [toOption_need_bind, Psc.formOK, e, ite_ite_none, Bool.and_assoc]
  rfl

theorem runSum_iff (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (h : Psc.Heard)
    (o : Psc.Out) :
    runSum c S fresh h = .ok o ↔
      ((S.shown = 0 ↔ S.degree = 0) ∧ (0 < S.shown ∨ c.vars ≠ []) ∧
        (∀ w ∈ c.vars, 2 ≤ w.d ∧ w.moment.length = w.d ∧ w.psi.length ≤ w.d ∧ w.fixed < w.d) ∧
        fresh.length = Psc.masksOf c S ∧
        h.rounds.length = (Psc.varsOf c S).length ∧
        h.values.length = S.shown ∧
        (S.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).length = 1 + S.kept ∧
        ∀ p ∈ (Psc.varsOf c S).zip h.rounds, p.2.1.length + 1 = p.1.d) ∧
      o = outOf c S fresh h := by
  have h1 : ((S.shown == 0) == (S.degree == 0)) = true ↔ (S.shown = 0 ↔ S.degree = 0) := by
    rw [beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  have h2 : (decide (0 < S.shown) || !c.vars.isEmpty) = true ↔ (0 < S.shown ∨ c.vars ≠ []) := by
    cases c.vars <;> simp
  have h3 : c.vars.all weightFits = true ↔
      ∀ w ∈ c.vars, 2 ≤ w.d ∧ w.moment.length = w.d ∧ w.psi.length ≤ w.d ∧ w.fixed < w.d := by
    simp [weightFits, and_assoc]
  have h8 : (((Psc.varsOf c S).zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d) = true ↔
      ∀ p ∈ (Psc.varsOf c S).zip h.rounds, p.2.1.length + 1 = p.1.d := by
    rw [List.all_eq_true]
    exact forall_congr' fun p => imp_congr_right fun _ => beq_iff_eq
  unfold runSum
  simp only [need_bind_iff]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, e⟩
    exact ⟨⟨h1.1 a1, h2.1 a2, h3.1 a3, beq_iff_eq.1 a4, beq_iff_eq.1 a5, beq_iff_eq.1 a6,
      beq_iff_eq.1 a7, h8.1 a8⟩, (Except.ok.inj e).symm⟩
  · rintro ⟨⟨p1, p2, p3, p4, p5, p6, p7, p8⟩, rfl⟩
    exact ⟨h1.2 p1, h2.2 p2, h3.2 p3, beq_iff_eq.2 p4, beq_iff_eq.2 p5, beq_iff_eq.2 p6,
      beq_iff_eq.2 p7, h8.2 p8, rfl⟩

/-! ## 4 W's message, and the row on W -/

theorem splitNeeded_agrees (S : LinShape) : splitNeeded S = S.ownSplitNeeded := rfl

theorem maskNotice_agrees (test : List IoppStage) (leafClass : Nat) :
    (maskNotice test leafClass).toOption = linMaskNotice test leafClass := by
  unfold maskNotice linMaskNotice
  cases test.head? <;> rfl

theorem messageW_agrees (S : LinShape) : (messageW S).toOption = linMessageW S := by
  unfold messageW linMessageW maskNotice linMaskNotice
  cases S.masksAhead <;> cases S.testOwn.head? <;> rfl

theorem messageW_iff (S : LinShape) :
    (∃ a, messageW S = .ok a) ↔ (S.masksAhead = false ∨ S.testOwn ≠ []) := by
  unfold messageW maskNotice
  cases S.masksAhead with
  | false => exact ⟨fun _ => Or.inl rfl, fun _ => ⟨_, rfl⟩⟩
  | true =>
    cases S.testOwn with
    | nil =>
      constructor
      · rintro ⟨a, ha⟩
        cases ha
      · rintro (h | h)
        · cases h
        · exact absurd rfl h
    | cons s l => exact ⟨fun _ => Or.inr (List.cons_ne_nil s l), fun _ => ⟨_, rfl⟩⟩

theorem evalRow_agrees (S : LinShape) (claim : LinClaim) (w : Nat) (lay : VectorLay) :
    (evalRow S claim w lay).toOption = linEvalRow S claim w lay := by
  unfold evalRow linEvalRow
  rw [toOption_need_bind]
  cases (claim.psi.length == S.kCol) <;> rfl

theorem evalRow_iff (S : LinShape) (claim : LinClaim) (w : Nat) (lay : VectorLay) (r : Row) :
    evalRow S claim w lay = .ok r ↔
      claim.psi.length = S.kCol ∧
        r = addLaid { units := claim.masks, target := claim.target } w lay
          [Tensor.eq claim.psi] := by
  unfold evalRow
  rw [need_bind_iff, beq_iff_eq]
  exact and_congr_right fun _ => ⟨fun e => (Except.ok.inj e).symm, fun e => by rw [e]; rfl⟩

end VerifiableInference.Desc.K13.Own
