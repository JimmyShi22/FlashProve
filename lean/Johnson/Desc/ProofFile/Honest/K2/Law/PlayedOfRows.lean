-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlayedOfRows.lean: the kind "the code switch" (K2): WHAT `play`
RETURNS OVER THE HALF's TWO ROUNDS, BOTH ROUNDS NAMED, OF ONE V: the rows that `switchRowsLaid`
(Honest/K2/ScriptLots.lean) lays at what was heard in front. The first round shows the shared
sending's tables of V; the second its `answers` at the held words of V, at any number f of the
sending's first message. `half_played` (Honest/K2/Law/PlaysSeated.lean) has the same premises and
leaves the second round's values unnamed; two clauses of its end are not in this one: the shapes of
the first round's tables, and what the first move says. One statement with its proof; no definition.

  `half_played_rows`

By: `moves_say`, `play_two_is` (PlaysSeated.lean) and the steps of `half_played`'s own proof ·
`says_of_rows` (Honest/K2/Law/RowsTie.lean): the first move · `says_two_of_rows`
(Honest/K2/Law/AnswersTie.lean): the second. Kin, not called: `half_plays`, `lot_plays`,
`lot_plays_fit` (Honest/K2/Law/Plays.lean) and `plays_at_plan`, `plays_at_plan_fit`
(Honest/K2/Law/PlaysAtPlan.lean): that `play` returns over the half; what it returns is not named
there.

Limits. The premises are `half_played`'s, NINE: hb: the member's rounds, paired off with its lists
of messages, are d₁ with o₁ and d₂ with o₂ (the pairing ends with the shorter list) · three public
tests on the place (hs, hr, hf) · four on the two rounds (h1 to h4) · hl: the closing returns at the
input, at what was heard and at the carried stretches in hand. None is shown here. Roads, not
called: hs, hr, hf: `serves_at_head`, `roomy_at_head`, `fits_at_head`
(Honest/K2/Law/PublicAtHead.lean) · where the member's rounds and messages are the kind's at the
place's numbers, hb and h4 are read off, h1 and h3 are `rounds_items` (PlaysSeated.lean) with the
count of answers, and h2 is `place_shapes` (Honest/K2/Law/PlaysAtPlan.lean) · hl, at the lot's own
closing: `returnsLaw` (Honest/K2/Law/SegmentAlike.lean) with `closingOk` and `publicOk`. x₁ IS A
LETTER: where it holds too few elements for the seeds, `answers` reads a default and nothing refuses
(Honest/K2/Law/AnswersTie.lean). AT `coreSender freshTable` ALONE; the closing is a letter. At one
hand c of coins. It says which functions of V and of the first challenge are played: nothing on what
they show. Nothing on the verifier's step. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysSeated
import Johnson.Desc.ProofFile.Honest.K2.Law.AnswersTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Oracle)
open Johnson.Prover.Send (answers)

variable {X W₀ Rc Xi Tr S' Cl : Type}

/-- **BOTH ROUNDS, OF ONE V.** V: the rows laid at what was heard in front. f: any number. -/
theorem half_played_rows (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (b : Block S' Cl) (d₁ d₂ : Fmt.DeclaredRound)
    (o₁ o₂ : List Oracle) (hb : b.rounds.zip b.oracles = [(d₁, o₁), (d₂, o₂)])
    (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (switchHalf (X := X) (coreSender freshTable) D readers closing p).parts)
    (x₁ x₂ : Fmt.Drawn) (m : Mid (Local W₀ Rc Xi Tr) X)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (h1 : d₁.items.filter (· != .root) = [])
    (h2 : o₁.map (fun o => (o.logLength, o.words)) =
      treeShapes p.sizes.codes (switchSent p.sizes p.others))
    (h3 : d₂.items.filter (· != .root) =
      List.replicate (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers .answer)
    (h4 : o₂ = [])
    (hl : (closing p (D m.st.input.x) (readers m.st.input) m.st.heard
      (Stretch.carried p.carries c.1.2.2)).toOption.isSome = true) (f : Nat) :
    ∃ (V : Nat → Johnson.Prover.Send.Rows) (m' : Mid (Local W₀ Rc Xi Tr) X),
      switchRowsLaid D readers closing p c.1 m.st.input m.st.heard = .ok V ∧
      play ((switchHalf (X := X) (coreSender freshTable) D readers closing p).steps b v c)
        [x₁, x₂] [] m = .ok ([⟨b.name, b.place, 0, true, [],
          (K1.treeTables (sendingPar p.sizes.codes (switchSent p.sizes p.others)) V).map some, x₁⟩,
          ⟨b.name, b.place, 0, true,
          (((answers (sendingPar p.sizes.codes (switchSent p.sizes p.others))
            (K1.stAt (sendingPar p.sizes.codes (switchSent p.sizes p.others)) f) f
            (Johnson.Prover.Send.held (fun _ _ _ => 0) f
              (sendingPar p.sizes.codes (switchSent p.sizes p.others)) V)
            (K1.seedsAt (sendingPar p.sizes.codes (switchSent p.sizes p.others))
              [x₁])).map OnBytes.Slice.toE).map Said.answer).map Said.got, [], x₂⟩], m') ∧
      m'.st.input = m.st.input := by
  obtain ⟨Tb, A, s₁, -, f₁, s₂, f₂⟩ := moves_say freshTable p.sizes p.others p.foldVars p.carries
    d₁ d₂ o₁ o₂ c.1 (m.st.narrow (switchWit D readers closing p) fun _ => ())
    (State.narrow (switchWit D readers closing p) (fun _ => ())
      { m.st.hears x₁ with own := (m.st.hears x₁).own }) x₁ rfl rfl hs hr hf h1 h2 h3 h4 hl
  have e₁ : (moveOne (coreSender freshTable) p.sizes p.others p.foldVars p.carries).say c.1 ⟨[], none⟩
      ⟨switchWit D readers closing p m.st.input, m.st.heard, ()⟩ = .ok ⟨[], Tb⟩ := s₁ ⟨[], none⟩
  have e₂ : (moveTwo (coreSender freshTable) p.sizes p.others p.foldVars p.carries).say c.1 ⟨[], none⟩
      ⟨switchWit D readers closing p m.st.input, m.st.heard ++ [x₁], ()⟩ =
        .ok ⟨A.map .answer, []⟩ := s₂ ⟨[], none⟩
  rw [says_of_rows] at e₁
  rw [says_two_of_rows D readers closing p c.1 m.st.input m.st.heard x₁ ⟨[], none⟩ hs hr f] at e₂
  obtain ⟨V, hV⟩ : ∃ V, switchRowsLaid D readers closing p c.1 m.st.input m.st.heard = .ok V := by
    cases hx : switchRowsLaid D readers closing p c.1 m.st.input m.st.heard with
    | ok V => exact ⟨V, rfl⟩
    | error x =>
      rw [hx] at e₁
      cases e₁
  rw [hV] at e₁ e₂
  have hT : K1.treeTables (sendingPar p.sizes.codes (switchSent p.sizes p.others)) V = Tb :=
    congrArg Sending.tables (Except.ok.inj e₁)
  have hA : (((answers (sendingPar p.sizes.codes (switchSent p.sizes p.others))
            (K1.stAt (sendingPar p.sizes.codes (switchSent p.sizes p.others)) f) f
            (Johnson.Prover.Send.held (fun _ _ _ => 0) f
              (sendingPar p.sizes.codes (switchSent p.sizes p.others)) V)
            (K1.seedsAt (sendingPar p.sizes.codes (switchSent p.sizes p.others))
              [x₁])).map OnBytes.Slice.toE).map Said.answer) = A.map Said.answer :=
    congrArg Sending.vals (Except.ok.inj e₂)
  rw [half_steps (coreSender freshTable) D readers closing p b (d₁, o₁) (d₂, o₂) hb v c,
    steps_two _ (lift_moves (coreSender freshTable) p.sizes p.others p.foldVars p.carries
      (fun _ => ()) (switchWit D readers closing p) (fun _ => ()) fun x _ => x)]
  obtain ⟨m', hy, hi⟩ := play_two_is b.name ⟨b.place, 0⟩ d₁ d₂ o₁ o₂ (fun _ _ => none)
    (fun _ _ => v.bind fun _ => none) (fun _ _ => rfl)
    (fun f o => by
      cases v with
      | none => rfl
      | some w => rfl)
    ⟨fun _ => ((moveOne (coreSender freshTable) p.sizes p.others p.foldVars p.carries).lift
      (switchWit D readers closing p) (fun _ => ()) fun x _ => x).say c.1, _⟩
    ⟨fun _ => ((moveTwo (coreSender freshTable) p.sizes p.others p.foldVars p.carries).lift
      (switchWit D readers closing p) (fun _ => ()) fun x _ => x).say c.1, _⟩
    x₁ x₂ m ⟨[], Tb⟩ ⟨A.map .answer, []⟩ (s₁ ⟨m.seen, m.opened⟩) f₁
    (s₂ ⟨m.seen ++ [⟨([] : List Said).map Said.got, x₁⟩], m.opened⟩) f₂
  refine ⟨V, m', hV, ?_, hi⟩
  rw [hT, hA]
  exact hy

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.half_played_rows
