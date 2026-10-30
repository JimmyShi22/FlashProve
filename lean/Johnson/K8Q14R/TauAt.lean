-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K8Q14R/TauAt.lean: "128 COMBINATIONS" AT THE 25 PLACES OF KIND K8: at all public files in
the goals' scope, where the proof file's description can be opened (`IM.Open`,
Johnson/IMR/SeatOpen.lean),
the numbers of the place of kind K8 in link l (`ProofFile.k8ParW`, Johnson/Desc/ProofFile/Lot/K8.lean)
have tau = 128, for every l ≤ 24. One statement; calls alone.

  **`k8_tau_128`**. BY: `ProofFile.k8Par` lays tau := the built link's tl.tau; in scope each built link's
  tl is its own plan's (`IM.ground_tails`, Johnson/IMR/K8Seat.lean); in scope each plan's tau is 128
  (`Meaning.Tau.tau_layers`, `tau_attention`, `tau_head`, Johnson/Goal/Numbers/TauInScope.lean).

SO THE SCOPE FIXES tau: no test on the public parameters is needed for it.
OBJECT: one field of the place's numbers. USER: Johnson/P1K8R/ConstAt.lean; meant: a field of
K8Fill. LETTERS: those of `IM.Open`, l, Xl: free.
Limits. AT THE SECOND HASH FUNCTION ALONE (`OnBytes.secondHashFunction`). That the description can be
opened at any file in scope is a premise. Nothing on soundness.
-/
import Johnson.IMR.K8Seat
import Johnson.Goal.Numbers.TauInScope

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **128 combinations at the 25.** -/
theorem k8_tau_128 {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} {Xl : LinkH} (hl : l ≤ 24)
    (hX : Bs.G₀.built[l]? = some Xl) : (ProofFile.k8ParW Z Bs.G₀ Xl l).tau = 128 := by
  show Xl.tl.tau = 128
  have hW := O.public
  obtain ⟨tails, l24, e24, t24, -⟩ := ground_tails hS hR O.pub O.blank
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : l24 = Xl := Option.some.inj (e24.symm.trans hX)
    rw [t24]
    exact Meaning.Tau.tau_head hS hR hW
  · obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
    have hg12 : g < 12 := by omega
    obtain ⟨hp, a, x, x', ehp, ea, ex, etl, -, -, -, -, ex', etl', -⟩ := tails g hg12
    rcases hg with rfl | rfl
    · obtain rfl : x = Xl := Option.some.inj (ex.symm.trans hX)
      rw [etl]
      exact Meaning.Tau.tau_layers hS hR hW ehp
    · obtain rfl : x' = Xl := Option.some.inj (ex'.symm.trans hX)
      rw [etl']
      exact Meaning.Tau.tau_attention hS hR hW ea

end IM

#print axioms IM.k8_tau_128
