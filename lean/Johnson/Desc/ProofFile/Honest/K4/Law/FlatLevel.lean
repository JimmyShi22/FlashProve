-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatLevel.lean: CONDITIONAL.

What is here. THE TWO TEXTS OF THE VERIFIER's MASKED SUMCHECK, TIED AT A PRODUCT LEVEL. Where the
flat function of a product level returns (`Fl.levelIn`, OnBytes/K/Kc/Flat.lean) on a tape, and the
part's text (`hear`, Johnson/Desc/Part/MaskedSum4.lean) returns on rounds that hold what the tape
holds, from one ledger and at one claimed form, the level's row is the form of the flat text's state
(`Psc`) on the product of the two values as sent, and that state has the letters of what `hear`
hands back (`SameLetters`, Johnson/Desc/Part/MaskedSumFlat.lean): so the level's row is worth what
the part's `rowForm` is worth. Both texts are the verifier's: no prover is named. Statements and
proofs.

  `level_sameLetters`   **the tie**: the row's form, the letters, the two values as sent
  `level_row_worth`   the level's row is worth what `rowForm` is worth

Limits. Premises: both texts return; the call has no lead, two end values of degree 2 in the further
variable, and its variables' weights are the level's (`levelWs`); the ledger is sized; THE TAPE
HOLDS WHAT THE ROUNDS HOLD (`TapeIs`, FlatCore.lean beside this file). Every equation between values
is between readings. It stands on Johnson/Desc/Part/MaskedSumFlat.lean and MaskedSumFlatProofs.lean.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatCore
import Johnson.Desc.Part.MaskedSumFlatProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E mulE addE zeroE)
open OnBytes.Model (Reading World Aff Fork Psc Level)
open OnBytes.K.Kc (Fl Tape FlatRound leading)
open OnBytes.Desc.First.P1 (levelWs levelIn_tape shown_some)
open VerifiableInference.Desc.Part.MaskedSum

/-! ## The tie at a level -/

/-- **Where both texts return on the same rounds, from one ledger and at one claimed form.** p: the
flat text's state. The level's row is p's form on the product of the two values as sent; p has the
letters of what `hear` hands back. -/
theorem level_sameLetters {mu : ℕ} {rho : Array E} {C : Aff} {order : List ℕ} {F G G' : Fork}
    {t u : Tape} {L : Level} (hF : Fl.levelIn mu rho C order F t = some (L, G, u))
    (hS : OnBytes.PscRun.Sized F) (vs : List Var) (hk : vs.map Var.weight = levelWs mu rho order)
    {rounds : List Fmt.RoundView} {h : Heard} (hh : hear C ⟨0, vs, some ⟨2, 2⟩⟩ F rounds = some (h, G'))
    (hT : TapeIs t rounds) :
    ∃ (p : Psc) (rv : Fmt.RoundView) (s : List E), rounds.getLast? = some rv ∧ scalars rv.vals = some s ∧
      L.row = p.rowForm (mulE (s.getD 0 zeroE) (s.getD 1 zeroE)) {} ∧ SameLetters p h := by
  obtain ⟨hom, T, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT, ms, y, shL, shR, v, G1, p, ht,
    hrs, _, _, _, hms, hyy, _, hTp, a1, _, _, _, hvars, hr, hclaim, htar, heps, hstart, hfirst,
    hrow, _, _, _, hv2, hG1, hshL, hshR, _⟩ := levelIn_tape hF
  rw [hms, hyy] at hr hclaim
  rw [hms] at a1
  obtain ⟨hSL, rv, b1, b2⟩ := sameLetters_of_tape (front := []) (dY := 2) (n := 2) ht
    (by rw [levelWs, List.length_map, hom, hrs]) a1 hvars hr hclaim htar heps hstart hfirst hTp vs
    hk hh hT
  have hF' : OnBytes.PscRun.Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) := hS
  obtain ⟨_, _, hin, _⟩ := OnBytes.PscRun.hideRun_ok _ G1 L.sL v y.2.2 hF' hG1
  have hg : ∀ e, v.getD e zeroE = v.toList.getD e zeroE := by
    intro e
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have eL : shL = v.toList.getD 0 zeroE := by
    rw [(shown_some hshL).2.2, ← hg]
    exact (hin 0 (by omega)).2.2.2.1
  have eR : shR = v.toList.getD 1 zeroE := by
    rw [(shown_some hshR).2.2, ← hg]
    exact (hin 1 (by omega)).2.2.2.1
  exact ⟨p, rv, v.toList, b1, b2, by rw [hrow, eL, eR], hSL⟩

/-- **The level's row is worth what the part's `rowForm` is worth**, on the product of the two
values as sent and with nothing kept, at every reading and in every world. -/
theorem level_row_worth {K : Type} [CommRing K] (ρ : Reading K) (W : World K) {mu : ℕ}
    {rho : Array E} {C : Aff} {order : List ℕ} {F G G' : Fork} {t u : Tape} {L : Level}
    (hF : Fl.levelIn mu rho C order F t = some (L, G, u)) (hS : OnBytes.PscRun.Sized F)
    (vs : List Var) (hk : vs.map Var.weight = levelWs mu rho order) {rounds : List Fmt.RoundView}
    {h : Heard} (hh : hear C ⟨0, vs, some ⟨2, 2⟩⟩ F rounds = some (h, G'))
    (hT : TapeIs t rounds) :
    ∃ (rv : Fmt.RoundView) (s : List E), rounds.getLast? = some rv ∧ scalars rv.vals = some s ∧
      L.row.value ρ W = (rowForm h (mulE (s.getD 0 zeroE) (s.getD 1 zeroE)) {}).value ρ W := by
  obtain ⟨p, rv, s, h1, h2, h3, h4⟩ := level_sameLetters hF hS vs hk hh hT
  exact ⟨rv, s, h1, h2, by rw [h3]; exact flatRowTie K ρ W p h _ _ h4⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.level_sameLetters
#print axioms ProofFile.Honest.K4.level_row_worth
