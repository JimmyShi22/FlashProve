-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtM4.lean: the joined block at the place of W's commitment (`K13.atM4`): W's
commitment, which is another kind's block, with kind K13's block behind it. Statements with their
proofs.
Main names:
  `rowsB_rows`: the block behind W's commitment leaves the rows on the table (`S.rows`) as they are.
  `rowsB_core`: what goes back over it, at the block's own decision, with the same oracles on both
    sides: so no premise on the pin is left.
  `atM4_goodIn`: **the law of the joined block**, from the law of W's commitment as a premise.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/M4.lean names.

What is not claimed. The law of W's commitment is a premise: that its piece has what it owes from
any (on, R) to: the promise `FrontOk P`, and all rows on the table are true. `WIs` stands in what is
behind: see Johnson/Desc/K13/Law/Eval.lean.
`WIs` is given by no law yet. The number nR of the matrix's rows is a free letter: that it is the
plan's is said nowhere but in Johnson/Desc/K13/Law/Caller.lean. That the joined piece is owed just
its stretch and that its trees are listed, if the first piece is: Johnson/Desc/K13/Law/Joint.lean.

-/
import Johnson.Desc.K13.Law.Then
import Johnson.Desc.K13.Law.M4Proof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Means (Words Says)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- What the block's yes gives at the first chain's state. -/
theorem rowsB_at {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s') :
    ∃ (m₀ : First.MemOwn) (l : LinFirst) (o : LinFirst × St) (owed : Option ℕ),
      s.here = .mem m₀ ∧ m₀.lin = some l ∧ rows P.lin l.claim m₀.ids (dOf s) = .ok o ∧
      s' = { s with st := o.2.st, rowsOwed := owed, here := .mem ⟨m₀.msg, m₀.ids, some o.1⟩ } := by
  obtain ⟨p, l, o, hp, hl, hrows, hb1⟩ := rowsB_ok atS P h
  obtain ⟨m₀, hs, h1, h2, h3⟩ := get_mem hp
  have hmsg : p.msg = m₀.msg := by
    simp only [atS, hs] at hp
    rw [← Option.some.inj hp]
  refine ⟨m₀, l, o, p.owed, hs, by rw [← h1, hl], by rw [← h2, ← h3]; exact hrows, ?_⟩
  rw [hb1]
  simp only [atS, hs, hmsg, h2]

/-- The block leaves the rows on the table as they are. -/
theorem rowsB_rows {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s') : s'.rows = s.rows := by
  obtain ⟨m₀, l, o, owed, hs, hl, hrows, rfl⟩ := rowsB_at h
  obtain ⟨_, _, _, hc, _⟩ := rows_ok hrows
  simp only [S.rows, hs, hl, hc]

/-- **What goes back over the block**, at its own decision. -/
theorem rowsB_core {F : Frame} {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s')
    (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE) (rwW : W → Words GE)
    (Pin : F.E.Str → W → Prop) (y : F.E.Str) (hon : FrontOk P ((s, y) : S × F.E.Str)) (w : W)
    (hw : Behind P rwM rwW Pin (s', y) w) :
    RowsHold (fun w => witOf (rwM w) (rwW w)) Pin (s, y) w := by
  refine ⟨hw.1, ?_⟩
  obtain ⟨m₀, l, o, owed, hs, hl, hrows, rfl⟩ := rowsB_at h
  have hlin : linAt s = some l := by
    unfold linAt
    rw [hs]
    exact hl
  obtain ⟨⟨row, hrow⟩, hbits⟩ := hon l hlin
  obtain ⟨d₃, r, G, hc, _, hr, hG, hin, hst, hcodes⟩ := rows_ok hrows
  rw [hrow] at hr
  have hr' : linEvalRow P.lin (memberClaim row) o.1.w (linLayW s.st.codes P.lin) = some r := hr
  obtain ⟨hlen, hform⟩ := linEvalRow_inv P.lin _ _ _ r hr'
  have hE : EvalIn o.2.st o.1.w (linLayW s.st.codes P.lin) row.masks := by
    rw [hst]
    refine evalIn_withRow _ _ (evalIn_of_rowIn (G := G) ?_ ?_)
    · have : row.psi.length = P.lin.kCol := hlen
      rw [this]
      exact hbits
    · rw [← hform]
      exact hin
  have hS : Says ρg o.2.st r (rwW w) := by
    obtain ⟨G', hG', hmem⟩ := mem_withRow r hG
    rw [← hst] at hG'
    exact hw.2.1.rows _ G' hG' r hmem
  have hW : WIs (rwM w) (rwW w) o.1.claim.g o.1.w (linLayW o.2.st.codes P.lin) := hw.2.2 o.1 rfl
  have hcodes' : o.2.st.codes = s.st.codes := hcodes
  rw [hc, hrow, hcodes'] at hW
  have hH := (eval_back nR P.lin row o.1.w _ r o.2.st (rwW w) (rwM w) hbits hr' hE hW).1 hS
  intro r' hr''
  have hrows' : s.rows = [row] := by
    simp only [S.rows, hs, hl, hrow, rowOfClaim_member]
  rw [hrows'] at hr''
  rw [List.mem_singleton.1 hr'']
  exact hH

/-- **The law of the joined block at the place of W's commitment.** pcW: the piece that holds W's
commitment; its law is the premise. -/
theorem atM4_goodIn {F : Frame} (P : Where) (pcW : Piece (ckP .two) F S Cl W)
    (on : S × F.E.Str → Prop) (R : S × F.E.Str → W → Prop)
    (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE) (rwW : W → Words GE)
    (Pin : F.E.Str → W → Prop)
    (hW : pcW.GoodIn on (FrontOk P) R (RowsHold (fun w => witOf (rwM w) (rwW w)) Pin)) :
    (Piece.then pcW "W's commitment, the own group and (Eval)" (rowsB atS P)).GoodIn on
      (fun _ => True) R (Behind P rwM rwW Pin) :=
  goodIn_then pcW _ (rowsB atS P) rfl on (FrontOk P) (fun _ => True) R _ _ hW
    fun _ _ y hon hd => ⟨trivial, fun w hw => rowsB_core hd rwM rwW Pin y hon w hw⟩

/-- The joined piece holds the description's own joined block. -/
theorem then_is_atM4 {F : Frame} (P : Where) (pcW : Piece (ckP .two) F S Cl W) :
    (Piece.then pcW "W's commitment, the own group and (Eval)" (rowsB atS P)).b = atM4 P pcW.b :=
  rfl

end VerifiableInference.Desc.K13.Law
