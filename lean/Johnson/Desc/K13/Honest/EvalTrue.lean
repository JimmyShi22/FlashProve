--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/EvalTrue.lean: the row (Eval), which kind K13 lays behind W's commitment, is
true of words that meet two conditions. Statements with their proofs.

The sub-protocol behind W's commitment (`rowsB`, Johnson/Desc/K13/Kind.lean) tests no value that a
prover has sent. It lays one open row, (Eval), on the request's own group: W at the claim's column
point, plus the claim's mask form, is the claim's target. A later test reads that row against what
was committed. So an honest prover needs the row to be true of its words. This file says when it is:
the claim's row is true of the matrix and of the words' mask entries, and W's message holds the
claim's row weights times the matrix (`WIs`, Johnson/Desc/K13/Law/Eval.lean).

Beside these two conditions on words the theorems take, as premises on the public state: that the
text or the sub-protocol accepts; that the claim is made of a row on the matrix; and that W's vector
fits its table (kCol is at most the layout's number of index bits). The last two hold where the
batching's joined sub-protocol has accepted (`atM3_front`, Johnson/Desc/K13/Law/M3Fits.lean), and
W's commitment keeps them (Johnson/Desc/K13/Honest/BehindSend.lean).

The soundness law reads the same equivalence (`eval_back`, Johnson/Desc/K13/Law/EvalProofs.lean)
from (Eval) back to the claim's row (`rowsB_core`, Johnson/Desc/K13/Law/AtM4.lean). Here it is read
forward: under the condition on W's message the truth of the claim's row and the truth of (Eval) are
one; the theorem carries truth from the one row to the other and makes none.
Main names:
  `eval_true_rows`: of the text `rows`: where it accepts, (Eval) is made, lies open on the own group
    of the statement behind, has passed the tests of the adding there, and says its claim of the
    words; the codes are those in front.
  `eval_true`: the same of the sub-protocol `rowsB` at the first chain's state. W's number is the
    first of the numbers that W's commitment has handed on.

What is not claimed. That the text or the sub-protocol accepts: that is a matter of sizes and of the
public state (Johnson/Desc/K13/Honest/RowsAccept.lean). That anybody's words meet the two
conditions. That the other open rows of the statement are true. The number nR of the matrix's rows
is a free parameter. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.AtM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Params (LinShape)
open OnBytes.Means (Words Says RowIn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

variable {Cl : Type} {nR : ℕ}

/-- **Where the text behind W's commitment accepts, (Eval) is true of words that meet the two
conditions.** row: the row that the claim is made of. mat: the matrix. m: the words. -/
theorem eval_true_rows {Sh : LinShape} {row : TensorRow} {ids : Array ℕ} {d : St}
    {o : LinFirst × St} (h : rows Sh (memberClaim row) ids d = .ok o)
    (hbits : Sh.kCol ≤ (linLayW d.st.codes Sh).bits)
    (mat : Fin nR → (Fin Sh.kCol → Bool) → GE) (m : Words GE)
    (hW : WIs mat m row.g o.1.w (linLayW d.st.codes Sh))
    (hH : Law.Holds ρg (witOf mat m) row) :
    ∃ (r : OnBytes.Row) (G : Group),
      linEvalRow Sh (memberClaim row) o.1.w (linLayW d.st.codes Sh) = some r ∧
      o.2.st.groups[o.1.own]? = some G ∧ r ∈ G.rows.toList ∧ RowIn o.2.st G r ∧
      o.2.st.codes = d.st.codes ∧ Says ρg o.2.st r m := by
  obtain ⟨d₃, r, G, _, _, hr, hG, hin, hst, hcodes⟩ := rows_ok h
  obtain ⟨hlen, hform⟩ := linEvalRow_inv Sh _ _ _ r hr
  have hE : EvalIn o.2.st o.1.w (linLayW d.st.codes Sh) row.masks := by
    rw [hst]
    refine evalIn_withRow _ _ (evalIn_of_rowIn (G := G) ?_ ?_)
    · have e : row.psi.length = Sh.kCol := hlen
      rw [e]
      exact hbits
    · rw [← hform]
      exact hin
  have hG' : o.2.st.groups[o.1.own]? = some { G with rows := G.rows.push r } := by
    rw [hst]
    exact withRow_group _ _ _ _ hG
  have hin' : RowIn o.2.st { G with rows := G.rows.push r } r := by
    rw [hst]
    exact RowIn.extends (G := G) (OnBytes.Means.extends_withRow d₃.st o.1.own r) (fun _ c => c) hin
  exact ⟨r, _, hr, hG', by simp, hin', hcodes,
    (eval_back nR Sh row o.1.w _ r o.2.st m mat hbits hr hE hW).2 hH⟩

/-- **The same of the sub-protocol**, at the first chain's state. a: the state's part for the
chain's end, in front of the sub-protocol. w: the first of the numbers that W's commitment has
handed on. -/
theorem eval_true {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s')
    {a : First.MemOwn} {l : LinFirst} {row : TensorRow} {w : ℕ}
    (hs : s.here = .mem a) (hl : a.lin = some l) (hrow : l.claim = memberClaim row)
    (hw : a.ids[0]? = some w)
    (hbits : P.lin.kCol ≤ (linLayW s.st.codes P.lin).bits)
    (mat : Fin nR → (Fin P.lin.kCol → Bool) → GE) (m : Words GE)
    (hW : WIs mat m row.g w (linLayW s.st.codes P.lin))
    (hH : Law.Holds ρg (witOf mat m) row) :
    ∃ (l' : LinFirst) (r : OnBytes.Row) (G : Group), Law.linAt s' = some l' ∧ l'.w = w ∧
      l'.claim = memberClaim row ∧
      linEvalRow P.lin (memberClaim row) w (linLayW s.st.codes P.lin) = some r ∧
      s'.st.groups[l'.own]? = some G ∧ r ∈ G.rows.toList ∧ RowIn s'.st G r ∧
      s'.st.codes = s.st.codes ∧ Says ρg s'.st r m := by
  obtain ⟨m₀, l₀, o, owed, hs₀, hl₀, hrows, rfl⟩ := rowsB_at h
  rw [hs] at hs₀
  obtain rfl : a = m₀ := First.Here.mem.inj hs₀
  rw [hl] at hl₀
  obtain rfl := Option.some.inj hl₀
  rw [hrow] at hrows
  obtain ⟨_, _, _, hc, hw₀, _⟩ := rows_ok hrows
  rw [hw] at hw₀
  obtain rfl := Option.some.inj hw₀
  obtain ⟨r, G, hr, hG, hmem, hin, hcodes, hsays⟩ := eval_true_rows hrows hbits mat m hW hH
  exact ⟨o.1, r, G, rfl, rfl, hc, hr, hG, hmem, hin, hcodes, hsays⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.eval_true_rows
#print axioms VerifiableInference.Desc.K13.Honest.eval_true
