-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReadsHeadAlone.lean: THE READING LAW AT THE CONSTANT, FROM THE HEAD ALONE. Four
theorems.

Why. `AtMgA.reads_at_kind_of_head` (Johnson/P5J/ReadsOfHead.lean) stands under the head and
`ReadsTests Zp cF`: three closed tests on public data. Each of the three is a theorem under the
head: pads (`k03_pads_at`, Johnson/P5J/K03TestsAt.lean), seat and below (`seat_at_head`,
`below_at_head`, Johnson/P5J/ReadsTestsAtHead.lean). Here they are laid in.

What is said. `AtMg.readsTests_head`: `ReadsTests Zp cF` under the head at the format's second hash
function. `AtMgA.readsOk_head`: at every border of the first chain up to the last, at the constant
`mgAtAll h`, at `h.toAtMg.rch`: every rider's sentence reads only what the table books (asked, as
`ReadsOkAtQR` asks it, at statements inside the promise, with rch, without a mark): NO PREMISE BUT
THE HEAD. `AtMgA.reads_at_place_head`, `AtMgA.reads_at_kind_head`: the same in the form in which
a kind's condition asks it.

Limits. Nothing on soundness: it is one premise of each sub-protocol's fifth tie. That there is a
head is shown elsewhere (`head_exists_at_name`), under premises on the public files.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.ReadsTestsAt
import Johnson.P5J.ReadsTestsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace P5J
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.Sound (ReadsOkAtQR frameAt allOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The three closed tests, under the head.** -/
theorem AtMg.readsTests_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : ReadsTests Zp cF :=
  h.readsTests (seat_at_head h) (below_at_head h)

/-- **At every border of the first chain: no premise but the head.** -/
theorem AtMgA.readsOk_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (i : ℕ)
    (hi : i ≤ At.ps.length) :
    ReadsOkAtQR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      h.𝔇.arr h.𝔇.N (mgAtAll h) At.links At.ps (fun a => a) h.toAtMg.rch i :=
  h.readsOk_of_head h.toAtMg.readsTests_head i hi

theorem AtMgA.reads_at_place_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ (i : ℕ) (a : Place), At.ps[i]? = some a →
      ReadsOkAtQR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch i :=
  h.reads_at_place_of_head h.toAtMg.readsTests_head

theorem AtMgA.reads_at_kind_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (kd : KindName) :
    ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = kd →
      ReadsOkAtQR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch i :=
  h.reads_at_kind_of_head h.toAtMg.readsTests_head kd

end P5J

#print axioms P5J.AtMg.readsTests_head
#print axioms P5J.AtMgA.readsOk_head
#print axioms P5J.AtMgA.reads_at_place_head
#print axioms P5J.AtMgA.reads_at_kind_head
