-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastAtDot.lean: what the exchange at the last chain's first member asks of the state, from the written shape: `AtDot` and
`Names`. Closed lines that can say no.

  `lin_CF`, `w_A0`, `omega_A0`, `tidy_A0`: the lines.
  `at_of_shape`: the premise `hat` of `exchangeS_first₃`.

What stays open. That a stand has the shape: `ThirdShaped`.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastValues
import E2E.KeyLastExchange
import Johnson.Desc.Last.ShapeDoorLess

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law (AtDot Names)
open AtPublicFiles.AtFiles (Sh₃ sh₃ SF CF borderSh weights_ok)
open AtPublicFiles.AtFiles.Full (A0)

theorem lin_CF : linOk CF SF = true := by decide +kernel

theorem w_A0 : (A0.1.st.oracles[A0.2.w]?).map (·.shape) = some SF.w := by decide +kernel

theorem omega_A0 : A0.2.border.map (fun b => (b.st.oracles[b.omega]?).map (·.shape)) = some (some SF.omega) := by
  decide +kernel

theorem tidy_A0 : A0.2.tidy = true := by decide +kernel

/-- **What the exchange asks of the state, at the written shape.** -/
theorem at_of_shape {p : P₁₄} (hp : p.S = SF) {s : S₃} (hsh : sh₃ SF s = A0) : AtDot p s ∧ Names s := by
  have hc : s.st.codes = CF := (congrArg (fun a : Sh₃ => a.1.st.codes) hsh).trans codes_A0
  have ht : stTidyB s.st = true := (congrArg (fun a : Sh₃ => a.2.tidy) hsh).trans tidy_A0
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hc, hp]
    exact lin_CF
  · have e : ((stSh s.st).oracles[s.loc.w]?).map (·.shape) = some SF.w := by
      have q := w_A0
      rw [← hsh] at q
      exact q
    rw [orc_get] at e
    cases ho : s.st.oracles[s.loc.w]? with
    | none =>
      rw [ho] at e
      cases e
    | some x =>
      rw [ho] at e
      exact ⟨x, rfl, by rw [hp]; exact Option.some.inj e⟩
  · intro b y hb hy
    have e : (s.loc.border.map (borderSh SF s.st.codes)).map
        (fun b => (b.st.oracles[b.omega]?).map (·.shape)) = some (some SF.omega) := by
      have q := omega_A0
      rw [← hsh] at q
      exact q
    rw [hb] at e
    have e' : ((stSh b.shared.st).oracles[b.shared.omega]?).map (·.shape) = some SF.omega :=
      Option.some.inj e
    rw [orc_get, hy] at e'
    rw [hp]
    exact Option.some.inj e'
  · intro b hb
    have q : (sh₃ SF s).2.border.map (·.weights) = some true := by
      rw [hsh]
      exact weights_A0
    have q' : (s.loc.border.map (borderSh SF s.st.codes)).map (·.weights) = some true := q
    rw [hb] at q'
    have q'' : AtPublicFiles.AtFiles.weightsB SF (linLayOmega s.st.codes SF) b.g = true := Option.some.inj q'
    exact weights_ok q''
  · intro G hG r hr o ho
    exact VerifiableInference.Desc.Last.named_is_there (OnBytes.Means.tidy4B_iff.1 ht).inOrder hG hr ho

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.lin_CF
#print axioms AtPublicFiles.KeyLastChain.w_A0
#print axioms AtPublicFiles.KeyLastChain.omega_A0
#print axioms AtPublicFiles.KeyLastChain.tidy_A0
#print axioms AtPublicFiles.KeyLastChain.at_of_shape
