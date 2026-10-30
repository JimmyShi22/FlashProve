-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/AtOffline.lean: K14's SIX LISTS OF SIMULATORS IN THE OFFLINE FILE's ROWS (E2E/OfflineSides.lean).

  `k14Lists`       the six lists of `TheirSimulators` that are K14's and K1's at the shared chain, from the rows' own simulators; the other four stay the argument's
  `k14Lists_fit`   each has one member
  `offlineRows_six`   **the first six rows of `offlineRows`'s shared chain are `keyRows`' rows: place, parts and simulators**

Limits. The letters On and bud go in through the argument `c`: nothing here says that `c` lays the rows' own. No property of the protocol is claimed.
-/
import E2E.OfflineSides
import AtFullSide.K14.Sim.AtOfflineRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14
open VerifiableInference.Desc (FileDescription)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)

variable {W₀ Rc X₀ X Wk : Type}

/-- **K14's six lists**, from the rows' own simulators. -/
def k14Lists (K : KeyParts W₀ Rc X₀ X Wk) (T : TheirSimulators) : TheirSimulators :=
  { T with
    linPoint := [quietSim ⟨place 1, 0⟩ 1]
    foldedRowSending := [sendingSim (jobU K.send) ⟨sendPlace 2, 0⟩]
    locColumns := [quietSim ⟨place 4, 0⟩ 1]
    omegaSending := [sendingSim (jobOmega K.send) ⟨sendPlace 5, 0⟩]
    linZeta := [quietSim ⟨place 7, 0⟩ 1]
    split := [splitSim] }

/-- Each has one member. -/
theorem k14Lists_fit (K : KeyParts W₀ Rc X₀ X Wk) (T : TheirSimulators) (h : T.Fit) :
    (k14Lists K T).Fit :=
  { h with
    linPoint := rfl, foldedRowSending := rfl, locColumns := rfl, omegaSending := rfl
    linZeta := rfl, split := rfl }

/-- What is laid at the six places is the rows' own simulators. -/
theorem simsAtSix_laid (K : KeyParts W₀ Rc X₀ X Wk) (T : TheirSimulators) :
    SimsAtSix K (laidSimulators K (k14Lists K T)).byChain.shared :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The first six rows of the offline rows' shared chain are the key prover's six rows**: place, parts and simulators. -/
theorem offlineRows_six (K : KeyParts W₀ Rc X₀ X Wk) (T : TheirSimulators)
    (hS : K.lin.S.sharedSplitNeeded = true) (Fx : FileDescription KeyInst) (Bk : ProverCoinCounts)
    (c : ConditionsByChain Fx Bk W₀ Rc TableKey Unit X₀ X) :
    ((offlineRows Fx Bk K (laidSimulators K (k14Lists K T)) c).shared.take 6).map
        (fun L => (L.place, L.row)) =
      (keyRows K).map fun r => (r.place, r.row) :=
  rowsAt_six K _ (simsAtSix_laid K T) hS c.shared

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.k14Lists_fit
#print axioms AtPublicFiles.OfflineRows.simsAtSix_laid
#print axioms AtPublicFiles.OfflineRows.offlineRows_six
