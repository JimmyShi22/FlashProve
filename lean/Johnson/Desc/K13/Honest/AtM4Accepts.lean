--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/AtM4Accepts.lean: the joined sub-protocol at the place of W's commitment
(`K13.atM4`, Johnson/Desc/K13/AtS.lean): its decision accepts, and the row (Eval) that it lays is
true, for any first sub-protocol, state and words that meet the premises. Statements with their
proofs.

The joined sub-protocol is W's commitment, which is another kind's, with kind K13's sub-protocol
behind it. Whoever shows that W's commitment accepts an honest sending has, by this file, that the
joined sub-protocol's decision accepts. THE PREMISES: the first sub-protocol's decision has
accepted, on as many rounds and groups of columns as it declares, and left a state s₁; s₁ stands at
the chain's end, a claim is laid there, and the claim is made of a row on the matrix; s₁ meets the
conditions `SentAtM4` (Johnson/Desc/K13/Honest/RowsAccept.lean). For the truth of (Eval), beside
these: W's message holds the row weights times the matrix (`WIs`, Johnson/Desc/K13/Law/Eval.lean),
and the claim's row is true.
Main names:
  `atM4_accepts`: the joined decision accepts, with the state that kind K13's decision leaves at s₁;
    W's number, the own group's number, the number taken for the first fold's mask and the claim in
    that state are as they are named.
  `atM4_true`: all of that, and (Eval) lies open on the own group, has passed the tests of the
    adding, and says its claim of the words; the codes stay.

What is not claimed. "Accepts" is `Block.decide`'s answer and no more: the tests of the format's
step in front of a decision (`Block.step`: the rounds' and the columns' form) and the test on the
plan (`planOk`) are not spoken of. That W's commitment accepts, or that its sending leaves such a
state: premises. That the claim's row is true: it is what the batching's honest prover has to
deliver; under the condition on W's message its truth and the truth of (Eval) are one, so
`atM4_true` carries truth from the one row to the other and makes none. The number nR of the
matrix's rows is a free parameter. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.RowsAccept
import Johnson.Desc.K13.Honest.EvalTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (Words Says RowIn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

variable {Cl : Type} {nR : ℕ}

/-- **The joined decision accepts.** b: W's commitment. s₁: the state that it leaves. -/
theorem atM4_accepts {P : Where} {b : Block S Cl} {s s₁ : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hr : rs.length = b.rounds.length)
    (hg : gs.length = b.openings) (hb : b.decide s rs gs = .ok s₁)
    {a : First.MemOwn} {l : LinFirst} {row : TensorRow} {w : ℕ}
    (hs : s₁.here = .mem a) (hl : a.lin = some l) (hrow : l.claim = memberClaim row)
    (H : SentAtM4 P.lin row a.ids s₁.st w) :
    ∃ (s' : S) (l' : LinFirst), (atM4 P b).decide s rs gs = .ok s' ∧
      (rowsB (Cl := Cl) atS P).decide s₁ [] [] = .ok s' ∧ Law.linAt s' = some l' ∧ l'.w = w ∧
      l'.own = s₁.st.groups.size ∧
      l'.mask = (if P.lin.masksAhead then a.ids.back? else none) ∧
      l'.claim = memberClaim row := by
  obtain ⟨s', l', h', e⟩ := rowsB_accepts (Cl := Cl) hs hl hrow H [] []
  refine ⟨s', l', ?_, h', e⟩
  unfold atM4
  rw [andThen_decide _ b _ s rs gs hr hg, hb]
  exact h'

/-- **The joined decision accepts, and (Eval) is true of words that meet the two conditions.** mat:
the matrix. m: the words. -/
theorem atM4_true {P : Where} {b : Block S Cl} {s s₁ : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hr : rs.length = b.rounds.length)
    (hg : gs.length = b.openings) (hb : b.decide s rs gs = .ok s₁)
    {a : First.MemOwn} {l : LinFirst} {row : TensorRow} {w : ℕ}
    (hs : s₁.here = .mem a) (hl : a.lin = some l) (hrow : l.claim = memberClaim row)
    (H : SentAtM4 P.lin row a.ids s₁.st w)
    (mat : Fin nR → (Fin P.lin.kCol → Bool) → GE) (m : Words GE)
    (hW : WIs mat m row.g w (linLayW s₁.st.codes P.lin))
    (hH : Law.Holds ρg (witOf mat m) row) :
    ∃ (s' : S) (l' : LinFirst) (r : OnBytes.Row) (G : Group),
      (atM4 P b).decide s rs gs = .ok s' ∧
      (rowsB (Cl := Cl) atS P).decide s₁ [] [] = .ok s' ∧ Law.linAt s' = some l' ∧ l'.w = w ∧
      l'.own = s₁.st.groups.size ∧
      l'.mask = (if P.lin.masksAhead then a.ids.back? else none) ∧
      l'.claim = memberClaim row ∧
      linEvalRow P.lin (memberClaim row) w (linLayW s₁.st.codes P.lin) = some r ∧
      s'.st.groups[l'.own]? = some G ∧ r ∈ G.rows.toList ∧ RowIn s'.st G r ∧
      s'.st.codes = s₁.st.codes ∧ Says ρg s'.st r m := by
  obtain ⟨s', l', h1, h2, f1, f2, f3, f4, f5⟩ := atM4_accepts hr hg hb hs hl hrow H
  obtain ⟨l'', r, G, e1, _, _, e4, e5, e6, e7, e8, e9⟩ :=
    eval_true h2 hs hl hrow H.first H.room mat m hW hH
  rw [f1] at e1
  obtain rfl := Option.some.inj e1
  exact ⟨s', l', r, G, h1, h2, f1, f2, f3, f4, f5, e4, e5, e6, e7, e8, e9⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.atM4_accepts
#print axioms VerifiableInference.Desc.K13.Honest.atM4_true
