-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/LkAtFullStatement.lean: UNDER THE LIBRARY's HYPOTHESIS ON THE PUBLIC FILES
(`P5J.AtMgA`) AT THE FULL SIZE THE KIND's LAYOUT HAS 18 COLUMN BITS AND 3,076,096 ROWS; SO 2 lk + 3
IS 39: A STATEMENT ALONE: a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and it is
none of the library's goals: it is a lemma's statement. WHAT 2 lk + 3 COUNTS IS NOT SAID HERE: it
stands in the library's `lay_room_at` (Johnson/Top/H0/MergeLaw/PlanNumsAt.lean: 2 lk + 3 is at most
the kind's number of slots) and in the clause on the count of slots of `MergeReady`
(Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedStatement.lean, a file that is not in this
library).

  `LkAtFull`   (K11.parOf Zp Bs.G₀).lay.lk = 18 · its m0 = 3076096 · 2 * lk + 3 = 39; Bs: what the
               maker's base returns

Limits. The hypothesis is a premise; it stands at the earlier hash. Numbers of the public layout
alone. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.AtFullStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- The statement. The letters: as in `HeadMergeAtFull`. Not proved here; a lemma's statement, none
of the library's goals. -/
def LkAtFull : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (_ : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (K11.parOf Zp Bs.G₀).lay.lk = 18 ∧ (K11.parOf Zp Bs.G₀).lay.m0 = 3076096 ∧
      2 * (K11.parOf Zp Bs.G₀).lay.lk + 3 = 39

end Johnson.Desc.First.ForkMerge.Exchange

#print axioms Johnson.Desc.First.ForkMerge.Exchange.LkAtFull
