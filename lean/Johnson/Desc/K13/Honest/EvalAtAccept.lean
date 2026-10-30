--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/EvalAtAccept.lean: wherever the sub-protocol at the place of W's commitment
accepts, the row (Eval) that it lays is true of words that meet two conditions. Statements with
their proofs.

Johnson/Desc/K13/Honest/AtM4Accepts.lean shows under which conditions on the state that decision
accepts. Here the acceptance is a premise, whoever has played the rounds: no condition on what W's
commitment has left is asked. What is owed behind the place is one open row, (Eval); it is true of
the words if W's message, which is the first new message, holds the claim's row weights times the
matrix, and the claim's row is true of the matrix and the words' mask entries.
Main names:
  `first_number`: the first of the numbers that W's commitment hands on is the number of messages in
    front.
  `eval_at_accept`: **the decision has accepted** from a state at the chain's end with a claim made
    of a row, W's vector fits its table, and the two conditions on the words hold: (Eval) is made,
    lies open on the own group of the statement behind, has passed the tests of the adding there,
    and says its claim of the words; W's number is the number of messages in front; the codes stay.
  `eval_after_m3`: the same behind an accepted run of the batching's sub-protocol, which gives that
    W's vector fits its table (`atM3_fits`, Johnson/Desc/K13/Law/M3Fits.lean).
The laws of the library that are put together: `atM4_mid` (Johnson/Desc/K13/Law/AtRecord.lean),
`sendAtS_full` (K1Ids.lean), `sendAtS_rows` (Johnson/Desc/K1/Law/HereAtRecord.lean), and `eval_true`
(Johnson/Desc/K13/Honest/EvalTrue.lean).

What is not claimed. That the decision accepts. That anybody's words meet the two conditions: of the
first, `wIs_of_rows` (Johnson/Desc/K13/Honest/W.lean) says from which entries of W's rows it
follows. The theorem carries truth from the claim's row to (Eval) and makes none. The number nR of
the matrix's rows is a parameter that nothing here ties to the shape. Nothing on soundness or on
hiding.

-/
import Johnson.Desc.K13.Honest.EvalTrue
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.K13.Law.K1Ids
import Johnson.Desc.K13.Law.M3Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (Words Says RowIn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

variable {Cl : Type} {nR : ℕ}

/-- The first of n numbers from f on is f. -/
theorem first_number {n f : ℕ} (h : 0 < n) : ((Array.range n).map (· + f))[0]? = some f := by
  rw [Array.getElem?_map, Array.getElem?_range, if_pos h]
  exact congrArg some (Nat.zero_add f)

/-- **Wherever the joined decision accepts, (Eval) is true of words that meet the two conditions.**
s₂: the state in front. mat: the matrix. m: the words. -/
theorem eval_at_accept {P : Where} {P' : K1.Par} {s₂ s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s₂ [r₁, r₂] gs = .ok s')
    {msg : Array OracleNotice} {ids₀ : Array ℕ} {row : TensorRow}
    (hs₂ : s₂.here = .mem ⟨msg, ids₀, some { claim := memberClaim row }⟩)
    (hne : 0 < P'.sent.size) (hbits : P.lin.kCol ≤ (linLayW s₂.st.codes P.lin).bits)
    (mat : Fin nR → (Fin P.lin.kCol → Bool) → GE) (m : Words GE)
    (hW : WIs mat m row.g s₂.st.oracles.size (linLayW s₂.st.codes P.lin))
    (hH : Law.Holds ρg (witOf mat m) row) :
    ∃ (l' : LinFirst) (r : OnBytes.Row) (G : Group), Law.linAt s' = some l' ∧
      l'.w = s₂.st.oracles.size ∧ l'.claim = memberClaim row ∧
      linEvalRow P.lin (memberClaim row) l'.w (linLayW s₂.st.codes P.lin) = some r ∧
      s'.st.groups[l'.own]? = some G ∧ r ∈ G.rows.toList ∧ RowIn s'.st G r ∧
      s'.st.codes = s₂.st.codes ∧ Says ρg s'.st r m := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid h
  obtain ⟨a, ha, ha', _⟩ := sendAtS_full P' s₂ s₁ r₁ r₂ g₁ h1
  rw [hs₂] at ha
  obtain rfl := First.Here.mem.inj ha
  have hc : s₁.st.codes = s₂.st.codes := (K1.sendAtS_rows P' s₂ s₁ r₁ r₂ g₁ h1).1
  obtain ⟨l', r, G, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ :=
    eval_true h2 ha' rfl rfl (first_number hne) (by rw [hc]; exact hbits) mat m
      (by rw [hc]; exact hW) hH
  rw [hc] at e4 e8
  exact ⟨l', r, G, e1, e2, e3, by rw [e2]; exact e4, e5, e6, e7, e8, e9⟩

/-- **The same behind an accepted batching.** s: the state in front of the batching. -/
theorem eval_after_m3 {P : Where} {P' : K1.Par} {s s₂ s' : S} {rs : List Fmt.RoundView}
    {gs₃ : List (List (Nat × List UInt64))}
    (h3 : (atM3 (Cl := Cl) P).decide s rs gs₃ = .ok s₂) {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s₂ [r₁, r₂] gs = .ok s')
    {msg : Array OracleNotice} {ids₀ : Array ℕ} {row : TensorRow}
    (hs₂ : s₂.here = .mem ⟨msg, ids₀, some { claim := memberClaim row }⟩)
    (hne : 0 < P'.sent.size)
    (mat : Fin nR → (Fin P.lin.kCol → Bool) → GE) (m : Words GE)
    (hW : WIs mat m row.g s₂.st.oracles.size (linLayW s₂.st.codes P.lin))
    (hH : Law.Holds ρg (witOf mat m) row) :
    ∃ (l' : LinFirst) (r : OnBytes.Row) (G : Group), Law.linAt s' = some l' ∧
      l'.w = s₂.st.oracles.size ∧ l'.claim = memberClaim row ∧
      linEvalRow P.lin (memberClaim row) l'.w (linLayW s₂.st.codes P.lin) = some r ∧
      s'.st.groups[l'.own]? = some G ∧ r ∈ G.rows.toList ∧ RowIn s'.st G r ∧
      s'.st.codes = s₂.st.codes ∧ Says ρg s'.st r m :=
  eval_at_accept h hs₂ hne (atM3_fits h3) mat m hW hH

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.first_number
#print axioms VerifiableInference.Desc.K13.Honest.eval_at_accept
#print axioms VerifiableInference.Desc.K13.Honest.eval_after_m3
