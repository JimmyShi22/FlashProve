-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/AtOfflineRows.lean: THE FIRST SIX ROWS OF THE KEY PROVER's SHARED CHAIN, IN THE OFFLINE FILE's FORM (`rowsAt`, E2E/OfflineRows.lean), ARE `keyRows`' ROWS, where each of the six places is
laid its row's own simulator. General in what is laid at the other places: so it serves `OfflineSimulators.byChain`.

  `rowsAt_six`     **the statement**: place, parts and simulators
  `rowsAt_six_letters`   with the rows' On and bud laid at their places, all four letters: the premise `rows` of `k14_at_key`

Limits. The letters On and bud go in through `c`. No property of the protocol is claimed.
-/
import E2E.OfflineRows
import AtFullSide.K14.Sim.AtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14
open VerifiableInference.Desc (Place Block)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)

variable {W₀ Rc X₀ X Wk S Cl : Type}

/-- What is laid at the six places is the rows' own simulators. -/
structure SimsAtSix (K : KeyParts W₀ Rc X₀ X Wk) (sims : Place → List (Sim TableKey)) : Prop where
  linPoint : sims (place 1) = [quietSim ⟨place 1, 0⟩ 1]
  foldedRowSending : sims (sendPlace 2) = [sendingSim (jobU K.send) ⟨sendPlace 2, 0⟩]
  locColumns : sims (place 4) = [quietSim ⟨place 4, 0⟩ 1]
  omegaSending : sims (sendPlace 5) = [sendingSim (jobOmega K.send) ⟨sendPlace 5, 0⟩]
  linZeta : sims (place 7) = [quietSim ⟨place 7, 0⟩ 1]
  split : sims (place 8) = [splitSim]

/-- **The first six rows are the key prover's six rows.** -/
theorem rowsAt_six (K : KeyParts W₀ Rc X₀ X Wk) (sims : Place → List (Sim TableKey))
    (h : SimsAtSix K sims) (hS : K.lin.S.sharedSplitNeeded = true) {Bk : ProverCoinCounts}
    (c : Place → RowConditions Bk S Empty (Common W₀ Rc TableKey) X₀ TableKey) :
    ((rowsAt (Cl := Cl) sims c (keyProver K).shared).take 6).map (fun L => (L.place, L.row)) =
      (keyRows K).map fun r => (r.place, r.row) := by
  rw [keyRows_half]
  simp [keyRows, weaveRows, ownRows, sendingRows, hS, rowsAt, rowOf, partsBeside, Unlettered.half,
    quietRow, splitRow, h.linPoint, h.foldedRowSending, h.locColumns, h.omegaSending, h.linZeta, h.split]

/-- **With the letters**: where what is laid at the rows' places is the rows' own On and bud, each of the first six rows has all four letters of one of the key prover's six: the premise `rows` of `k14_at_key`. -/
theorem rowsAt_six_letters (K : KeyParts W₀ Rc X₀ X Wk) (sims : Place → List (Sim TableKey))
    (h : SimsAtSix K sims) (hS : K.lin.S.sharedSplitNeeded = true) {Bk : ProverCoinCounts}
    (c : Place → RowConditions Bk S Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (hc : ∀ r ∈ keyRows K, (c r.place).atPart = r.On ∧ (c r.place).positions = r.bud) :
    ∀ L ∈ (rowsAt (Cl := Cl) sims c (keyProver K).shared).take 6, ∃ r ∈ keyRows K,
      L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud := by
  intro L hL
  have hm : (L.place, L.row) ∈
      ((rowsAt (Cl := Cl) sims c (keyProver K).shared).take 6).map (fun L => (L.place, L.row)) :=
    List.mem_map_of_mem hL
  rw [rowsAt_six K sims h hS c] at hm
  obtain ⟨r, hr, e⟩ := List.mem_map.1 hm
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hL)
  refine ⟨r, hr, e1.symm, e2.symm, ?_, ?_⟩
  · have e3 : g.place = r.place := e1.symm
    show (c g.place).atPart = _
    rw [e3]
    exact (hc r hr).1
  · have e3 : g.place = r.place := e1.symm
    show (c g.place).positions = _
    rw [e3]
    exact (hc r hr).2

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.rowsAt_six_letters
#print axioms AtPublicFiles.OfflineRows.rowsAt_six
