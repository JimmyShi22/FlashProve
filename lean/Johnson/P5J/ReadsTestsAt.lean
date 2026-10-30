-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReadsTestsAt.lean: OF THE THREE CLOSED TESTS IN FRONT OF THE READING LAW ONE FALLS: "NO
PLACE THAT THE HIDDEN DATA READS IS A PAD's" COMES OF THE HEAD. Two theorems.

Why. `AtMgA.reads_at_kind_of_head` (Johnson/P5J/ReadsOfHead.lean) stands under `ReadsTests Zp cF`:
pads, seat, below. The first is a theorem under the head (`k03_pads_at`,
Johnson/P5J/K03TestsAt.lean: by the door's pin). `ReadsTests` itself does not turn: others call it.

What is said. `AtMg.readsTests`: `ReadsTests Zp cF` from the head and the two tests on what
`At.laid? Zp` lists. `AtMgA.reads_at_kind_of_two`: the reading law in a kind's condition's form,
under the head and these two.

Limits. Nothing on soundness. The two tests are shown met here by nobody (each has run true at the
stored sets' public files, at both sizes, with negative tests that bite).

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.ReadsOfHead
import Johnson.P5J.K03TestsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace P5J
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.Sound (ReadsOkAtQR frameAt allOf)
open VerifiableInference.Desc.K13.Law (planBelowB)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`ReadsTests` from the head and two tests.** -/
theorem AtMg.readsTests (h : AtMg o Z D r Zp Np cF)
    (seat : ∀ L, At.laid? Zp = some L →
      L.places[(At.N Zp cF).indexNo]? = some (At.N Zp cF).index)
    (below : ∀ L, At.laid? Zp = some L → planBelowB L At.ps.length (At.told cF) = true) :
    ReadsTests Zp cF :=
  ⟨(k03_pads_at h).2, seat, below⟩

theorem AtMgA.reads_at_kind_of_two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (seat : ∀ L, At.laid? Zp = some L →
      L.places[(At.N Zp cF).indexNo]? = some (At.N Zp cF).index)
    (below : ∀ L, At.laid? Zp = some L → planBelowB L At.ps.length (At.told cF) = true)
    (kd : KindName) :
    ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = kd →
      ReadsOkAtQR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch i :=
  h.reads_at_kind_of_head (h.toAtMg.readsTests seat below) kd

end P5J

#print axioms P5J.AtMg.readsTests
#print axioms P5J.AtMgA.reads_at_kind_of_two
