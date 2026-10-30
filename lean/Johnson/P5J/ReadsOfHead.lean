-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReadsOfHead.lean: THE READING LAW AT THE CONSTANT, FROM THE HEAD AND THREE CLOSED TESTS
BY NAME. One structure, three theorems.

Why. `AtMgA.readsOk` (Johnson/P5J/ReadsOwedAt.lean) takes FoldFacts at listed seats L, and two tests
at that same L. FoldFacts at the head is a theorem from the head alone
(`atMgR_rch_of_head`, Johnson/P5J/StartAtHead.lean): "there are listed seats L with …". Here the two
are joined, so that all premises speak of one L: what `At.laid? Zp` lists.

What is said. `ReadsTests Zp cF`: the three closed tests on public data that are left: no place that
the hidden data reads is a pad's (`padsAtZ`); of whatever `At.laid? Zp` lists: it has the index
masks' seat at its number, and the list's bound holds (`planBelowB`). `AtMgA.readsOk_of_head`: under
the head at the second hash function and these: `ReadsOkAtQR` at every border up to the last.
`AtMgA.reads_at_place_of_head`, `AtMgA.reads_at_kind_of_head`: the same in the form in which a
kind's condition asks it.

Limits. Nothing on soundness. The three tests are shown met here by nobody (each has run true at the
stored full-size set's public files).

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.ReadsOwedAt
import Johnson.P5J.StartAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace P5J
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.Sound (ReadsOkAtQR frameAt allOf)
open VerifiableInference.Desc.K13.Law (planBelowB)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The closed tests on public data that are left in front of the reading law.** -/
structure ReadsTests (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) : Prop where
  pads : OffPad.padsAtZ Zp = true
  seat : ∀ L, At.laid? Zp = some L →
    L.places[(At.N Zp cF).indexNo]? = some (At.N Zp cF).index
  below : ∀ L, At.laid? Zp = some L → planBelowB L At.ps.length (At.told cF) = true

/-- **At every border of the first chain, from the head.** -/
theorem AtMgA.readsOk_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (T : ReadsTests Zp cF) (i : ℕ) (hi : i ≤ At.ps.length) :
    ReadsOkAtQR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      h.𝔇.arr h.𝔇.N (mgAtAll h) At.links At.ps (fun a => a) h.toAtMg.rch i := by
  obtain ⟨L, R⟩ := atMgR_rch_of_head h
  exact h.readsOk R.fold T.pads (T.seat L R.listed) (T.below L R.listed) i hi

theorem AtMgA.reads_at_place_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (T : ReadsTests Zp cF) :
    ∀ (i : ℕ) (a : Place), At.ps[i]? = some a →
      ReadsOkAtQR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch i :=
  fun i _ ha => h.readsOk_of_head T i (Nat.le_of_lt (List.getElem?_eq_some_iff.1 ha).1)

theorem AtMgA.reads_at_kind_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (T : ReadsTests Zp cF) (kd : KindName) :
    ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = kd →
      ReadsOkAtQR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch i :=
  fun i a ha _ => h.reads_at_place_of_head T i a ha

end P5J

#print axioms P5J.AtMgA.readsOk_of_head
#print axioms P5J.AtMgA.reads_at_place_of_head
#print axioms P5J.AtMgA.reads_at_kind_of_head
