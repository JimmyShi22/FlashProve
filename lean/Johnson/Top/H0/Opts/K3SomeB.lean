-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/K3SomeB.lean: ONE LINE: P1Opts.k3Some_at_written
(Johnson/Top/H0/Opts/K3SomeAtWritten.lean) AT THE NAME UNDER WHICH THE JOIN OF THE NAMED
CONDITIONS ASKS IT: P5J.At.k3SomeB (Johnson/Goal/Skeleton/K3Some.lean): its body
is k3Some_at_written's end, sign for sign. NO BLOCK IMPORTS THIS FILE. No soundness is claimed.

-/
import Johnson.Top.H0.Opts.K3SomeAtWritten
import Johnson.Goal.Skeleton.K3Some

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (proofSizedFull)

theorem k3SomeB_at_written {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (hrr : P5J.rowsRead Z)
    (hS : P5J.At.shape Zp = proofSizedFull.request) (hp : P5J.At.pseats Zp = P5T.psFull) :
    P5J.At.k3SomeB Zp Z.lay = true := k3Some_at_written hl L hrr hS hp

end P1Opts

#print axioms P1Opts.k3SomeB_at_written
