-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PubPBehind.lean: the kind "the code switch" (K2): UNDER THE
HEAD, AT EVERY PLACE OF THE KIND ON THE FIRST CHAIN: WHAT THE PUBLIC ITEMS THAT ARE OPEN AT THE
BORDER BEHIND SAY BESIDE THEIR TESTS HOLDS THERE, AT EVERY STATE. One statement with its proof; no
definition. A joining of the library's theorems.

  `k2_pubP_behind`   at the letters `P5J.At.links`, `P5J.At.ps`, `P5J.mgAtAll`: the library's
                    `pubP_behind` (Johnson/Top/H0/K2Ties/PubBehind.lean) at its test's yes
                    (`P1K2.said_at`): behind a code switch no open public item is of a sort that has
                    a sentence beside its test: by Lean's kernel at the 25 of the written list
                    (`said_full`, there)

Limits. The head is a letter of the meaning alone: none of its fields is spent. At the composed
meaning over its closed base. The full size alone. THE THREE FILES WHOSE THEOREMS AND DEFINITION ARE
JOINED (Johnson/Top/H0/K2Ties/PubBehind.lean; Johnson/P1K2R/TableAtConst.lean, TieTwo.lean) ARE
NOT REVIEWED; none of the other files that the statement names is known here to be
reviewed. The line that strikes an instance below stands in the imported file too. Nothing on any
property.
-/
import Johnson.P1K2R.LastLineOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K2Caller

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k2_pubP_behind (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) {k : Nat}
    {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) (a : ProofFile.InstPub × VerifiableInference.Desc.First.S) :
    ∀ q ∈ P1K2.pubAt (P5J.mgAtAll Hd) P5J.At.links P5J.At.ps (k + 1),
      (P5J.mgAtAll Hd).pubP q a :=
  VerifiableInference.Desc.First.K2Ties.pubP_behind (dC Hd) P5J.fullLinks P5J.At.ps k
    (P1K2.said_at ha hk) a

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.k2_pubP_behind
