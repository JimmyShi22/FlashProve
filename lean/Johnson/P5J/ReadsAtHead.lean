-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReadsAtHead.lean: AT THE COMPOSED MEANING's CONSTANT, AT EVERY BORDER OF THE FIRST
CHAIN: EVERY RIDER's SENTENCE READS ONLY WHAT THE TABLE BOOKS. One structure, four theorems.

Why. Every sub-protocol's fifth tie asks `ReadsOkAtQR … i` at its own border i, at the constant
`mgAtAll h`. It is stated here once, so that each kind's law calls one theorem.

What is said. `At.readsOpen_at`, `At.rowsApart_at`, `At.unmarked_at`: the table's three closed tests
at the constant's written lists, by the kernel. `ReadsOwed h Rch M L`: ALL THAT IS STILL OWED, BY
NAME: the five congruences of `HidReads`; what the laws that read through the state's book ask
(`BookPrem`, at every border); the weights' sentence's one; the parameter that says `carry`; `worth`
under its fence; and the closed test `ridersFitB` at every border. `AtMgA.readsOk_at`: under it,
`ReadsOkAtQR` at every border up to the last, general in the condition Rch beside the promise. (That
it is stated at `mgAtAll h` and proved at `mgAll h.𝔇 mgBase` is Lean's word that the two spellings
are one.)

Limits. `ReadsOwed` is paid by nobody here; of its fields some have payers that lie in other files.
Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.Sound.ReadsSortsMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace P5J
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (Item start readsOpen)
open VerifiableInference.Desc.Sound (Frame HidReads BookPrem ReadsItemQR ReadsOkAtQR ridersFitB
  rowsApart sameQ mgAll mgBase readsOkAtQR_of_sorts sortsPaid_mg)
open VerifiableInference.Desc.K12.Door (Laid)
open OnBytes.Maker (WholeD)

theorem At.readsOpen_at : readsOpen At.links At.ps (start At.links) = true := by decide +kernel

theorem At.rowsApart_at : rowsApart At.links At.ps = true := by decide +kernel

theorem At.unmarked_at : Item.unmarked ∈ start At.links := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **All that the reading law at the constant still owes, by name.** -/
structure ReadsOwed (h : AtMgA o Z D r Zp Np cF x) {Fr : Frame}
    (Rch : ℕ → (ProofFile.InstPub × TS) × Fr.E.Str → Prop) (M : List OnBytes.OracleShape) (L : Laid) :
    Prop where
  hid : HidReads h.𝔇 At.links
  book : ∀ i, BookPrem h.𝔇 mgBase M L (fun a => a) Rch i
  wtForms : ∀ m j a y w w',
    (∀ c ∈ (Item.forms m j "weights").reads h.𝔇.arr h.𝔇.N At.links, sameQ c w w') →
    h.𝔇.wt m a y w → h.𝔇.wt m a y w'
  carry : ∀ m a y w w', (∀ c ∈ (Item.carry m).reads h.𝔇.arr h.𝔇.N At.links, sameQ c w w') →
    h.𝔇.cr1 m a y w → h.𝔇.cr1 m a y w'
  worth : ∀ i m j s, 3 < j → m < At.links.length →
    ReadsItemQR h.𝔇.arr h.𝔇.N (mgAll h.𝔇 mgBase) At.links At.ps (fun a => a) Rch i (.worth m j s)
  fit : ∀ i, i ≤ At.ps.length → ridersFitB (mgAll h.𝔇 mgBase).more At.links At.ps i = true

/-- **At every border of the first chain, at the constant.** -/
theorem AtMgA.readsOk_at (h : AtMgA o Z D r Zp Np cF x) {Fr : Frame}
    (Rch : ℕ → (ProofFile.InstPub × TS) × Fr.E.Str → Prop) {M : List OnBytes.OracleShape} {L : Laid}
    (O : ReadsOwed h Rch M L) (i : ℕ) (hi : i ≤ At.ps.length) :
    ReadsOkAtQR (Fr := Fr) h.𝔇.arr h.𝔇.N (mgAtAll h) At.links At.ps (fun a => a) Rch i :=
  readsOkAtQR_of_sorts h.𝔇 mgBase At.links At.ps (fun a => a) Rch i At.readsOpen_at
    At.rowsApart_at At.unmarked_at hi (O.fit i hi)
    (sortsPaid_mg O.hid (O.book i) O.wtForms O.carry (O.worth i))

end P5J

#print axioms P5J.At.readsOpen_at
#print axioms P5J.At.rowsApart_at
#print axioms P5J.At.unmarked_at
#print axioms P5J.AtMgA.readsOk_at
