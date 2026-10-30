-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/WRowAtAccept.lean: wherever the sub-protocol at the place of W's commitment
accepts, the library's own sentence on the row (Eval) holds of words that meet two conditions.
Statements with their proofs.

The library's table of the first chain's joints has an item for the row (Eval) (`Item.wrow`,
Johnson/Desc/First/Borders.lean). At the library's own meaning of the items that item's sentence is
`WRow` (Johnson/Desc/K13/Law/Letters.lean; `mgAll_wrow`, Johnson/Desc/Sound/MgAll.lean): whatever
the state holds for the last chain, the row (Eval) that is made of it says its claim of the words.
Johnson/Desc/K13/Honest/EvalAtAccept.lean concludes that a row is made, lies open and says its
claim. Here that is said in the form of `WRow`.
Main names:
  `wRow_at_accept`: the decision has accepted from a state at the chain's end with a claim made of a
    row, W's vector fits its table, W's message holds the claim's row weights times the matrix, and
    the claim's row is true of the matrix and the words' mask entries: `WRow` holds at the state
    behind.
  `wRow_after_m3`: the same behind an accepted run of the batching's sub-protocol.

What is not claimed. That the decision accepts. That anybody's words meet the two conditions. That
the commitment's sub-protocol of the statements (`K1.sendAtS` at a free parameter) is the one that
an IOP as written in Lean lays at the place. `WRow` is of the form "for every row that is made": by
itself it would hold where none is made; that one is made is `eval_at_accept`'s (EvalAtAccept.lean).
Nothing on the other items of the table. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.EvalAtAccept
import Johnson.Desc.K13.Law.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (Words)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

variable {Cl : Type} {nR : ℕ}

/-- **Wherever the decision accepts, `WRow` holds behind, of words that meet the two conditions.**
-/
theorem wRow_at_accept {P : Where} {P' : K1.Par} {s₂ s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s₂ [r₁, r₂] gs = .ok s')
    {msg : Array OracleNotice} {ids₀ : Array ℕ} {row : TensorRow}
    (hs₂ : s₂.here = .mem ⟨msg, ids₀, some { claim := memberClaim row }⟩)
    (hne : 0 < P'.sent.size) (hbits : P.lin.kCol ≤ (linLayW s₂.st.codes P.lin).bits)
    (mat : Fin nR → (Fin P.lin.kCol → Bool) → GE) (m : Words GE)
    (hW : WIs mat m row.g s₂.st.oracles.size (linLayW s₂.st.codes P.lin))
    (hH : Law.Holds ρg (witOf mat m) row) : WRow P s' m := by
  obtain ⟨l', r, _, e1, _, e3, e4, _, _, _, e8, e9⟩ :=
    eval_at_accept h hs₂ hne hbits mat m hW hH
  intro l r' hl hr'
  rw [e1] at hl
  obtain rfl := Option.some.inj hl
  rw [e3, e8, e4] at hr'
  obtain rfl := Option.some.inj hr'
  exact e9

/-- **The same behind an accepted batching.** -/
theorem wRow_after_m3 {P : Where} {P' : K1.Par} {s s₂ s' : S} {rs : List Fmt.RoundView}
    {gs₃ : List (List (Nat × List UInt64))}
    (h3 : (atM3 (Cl := Cl) P).decide s rs gs₃ = .ok s₂) {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s₂ [r₁, r₂] gs = .ok s')
    {msg : Array OracleNotice} {ids₀ : Array ℕ} {row : TensorRow}
    (hs₂ : s₂.here = .mem ⟨msg, ids₀, some { claim := memberClaim row }⟩)
    (hne : 0 < P'.sent.size)
    (mat : Fin nR → (Fin P.lin.kCol → Bool) → GE) (m : Words GE)
    (hW : WIs mat m row.g s₂.st.oracles.size (linLayW s₂.st.codes P.lin))
    (hH : Law.Holds ρg (witOf mat m) row) : WRow P s' m :=
  wRow_at_accept h hs₂ hne (atM3_fits h3) mat m hW hH

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.wRow_at_accept
#print axioms VerifiableInference.Desc.K13.Honest.wRow_after_m3
