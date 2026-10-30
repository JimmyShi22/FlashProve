-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RunHeard.lean: the run made of what was heard, and what the library's
typed ledger gives at it.

Main names:
  `runHeard`: the library's run (Cb/Pv/Att/OwnLast.lean: P.Run, P.runOf) inside the chain's last
    statement on the typed
    transcripts made of what was heard (OnBytes/Tie/Pv/Att/OwnTie.lean: ownTrs).
  `last_of_cl`: Fits, and the pull-backs of all claims of the library's ledger ownCl at that run
    (Cb/Pv/Att/End/Cl.lean),
    give the chain's last claim on the run: by own_last_run, own_last_bill, att_bill.

Nothing is claimed on soundness, completeness or hiding.

-/
import Cb.Pv.Att.End.ClIff
import Cb.Pv.Att.OwnAt
import OnBytes.Tie.Pv.Att.OwnTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (UnitsH TailH ownTrs)
open Cb.Pv.Att.End (EndLay JoinLay Fits ownCl attA att_bill)

variable {K : Type} [Field K] [Fintype K] {X Mg : Type}

/-- **The run made of what was heard.** -/
noncomputable def runHeard {ρ : Reading K} (P : OwnPar K Mg X) (x0 : X)
    (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail) :
    P.Run :=
  P.runOf (theMeans K P.D P.C P.kap)
    ((P.own (theMeans K P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt))

/-- The typed ledger's pull-back at that run gives the chain's last claim on the run. -/
theorem last_of_cl {ρ : Reading K} (P : OwnPar K Mg X) {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay P J₂}
    {Q : JoinLay P} (hF : Fits Ly Q) (x0 : X) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units)
    (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail) (m : Mg)
    (h : ∀ f ∈ ownCl Ly Q (runHeard P x0 du dt), (Cb.Sub.pullF (attA Ly (runHeard P x0 du dt)) f).Holds (P.msg m)) :
    (P.own (theMeans K P.D P.C P.kap)).ch.Last (fun _ _ => True)
      ((P.own (theMeans K P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt)) m :=
  (P.own_last_run _ (fun _ _ => True) x0 _ m).2
    ((P.own_last_bill _ (fun _ _ => True) _ m).2 ⟨trivial, att_bill (theMeans K P.D P.C P.kap) hF _ m h⟩)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.last_of_cl
