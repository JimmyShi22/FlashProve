-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OneOwnAt.lean: THE LOOKUP ARGUMENT's LAW: "one" AND "own" AT THE COMPOSED MEANING's
OWN PARAMETERS, UNDER THE HEAD `AtMgA`, EACH FROM A NAMED TEST WITH CODE. Two definitions with code;
three theorems, proved.
  `AtMgA.oneC h l` := `K03.oneB` and `AtMgA.namedC h l` := `K03.namedB` (Johnson/P5J/K03OneOwn.lean)
    at: X := At.X Zp · what the list of rounds sends := At.sentAt Zp · rad3At · num := At.num Zp ·
    idx := the lookups' `idxAt (At.sentAt Zp) (At.num Zp) l` (a parameter of each link) · tls :=
    Meaning.tlAt X · the seats seat3At Zp l false · arr := At.arr Zp · N := At.N Zp cF.
  `AtMgA.three`: under the head the programs' three tests on codes, shape and layout accept at the
    parameters' own values (`three_at_pure`, Johnson/P5J/InsideAtPure.lean, at the head's "value";
    its public part is Zp by the head's "pub").
  `AtMgA.one_at`: l < 25 · `h.oneC l = true` give the ledger's field "one" at link l, to the letter
    of `AttOwedR` | `LayOwedR` (Johnson/Desc/Sound/MgAt/K3Owed.lean) at x.link := l.
  `AtMgA.own_at`: l < 25 · `h.namedC l = true` · `h.toAtMg.offC = true`
    (Johnson/P5J/HidBearsAtMg.lean) give the field "own".
SO THE TWO FIELDS HANG ON THREE NAMED TESTS: oneC l · namedC l (l < 24) · offC. EACH IS HAD FROM THE
HEAD IN ANOTHER FILE: oneC by `H2K5.Door.oneC_at_head`
(Johnson/Desc/First/Att/Door/Law/K5OneOfHead.lean) · namedC by `AtMgA.namedC_head`
(Johnson/P5J/K03NamedHead.lean) · offC by `k03_offC_at` (Johnson/P5J/K03TestsAt.lean).
CAN THEY BE MET? See Johnson/P5J/K03OneOwn.lean's head.
Limits. That a place x of link l's calls has x.link = l is not said here. Nothing at the digits.
Nothing on soundness.

-/
import Johnson.P5J.K03OneOwn
import Johnson.P5J.K03Terms
import Johnson.P5J.HidBearsAtMg
import Johnson.P5J.InsideAtPure
import Johnson.Desc.First.Look.K3IdxAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (idxAt sigListCalls)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The named test for "one" at link l. -/
def AtMgA.oneC (_ : AtMgA o Z D r Zp Np cF x) (l : ℕ) : Bool :=
  K03.oneB (At.X Zp) (At.sentAt Zp) (At.rad3At Zp Z.lay) (At.num Zp)
    (idxAt (At.sentAt Zp) (At.num Zp) l) (_root_.Meaning.tlAt (At.X Zp)) l
    (fun j => At.seat3At Zp l false j) (At.arr Zp) id

/-- The named test for the first half of "own" at link l. -/
def AtMgA.namedC (_ : AtMgA o Z D r Zp Np cF x) (l : ℕ) : Bool :=
  K03.namedB (At.X Zp) (At.sentAt Zp) (At.num Zp) (_root_.Meaning.tlAt (At.X Zp)) l (At.arr Zp)
    (At.N Zp cF)

/-- Under the head the programs' three tests accept. -/
theorem AtMgA.three (h : AtMgA o Z D r Zp Np cF x) :
    (At.cs Zp).lengthsOk = true ∧ reqShapeOk (At.shape Zp) = true ∧
      reqLayoutOk (At.cs Zp) (At.shape Zp) (At.layout Zp) = true := by
  obtain ⟨Z', hZ, hC, hS, hL⟩ := three_at_pure h.laid.value
  have e : Z' = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  subst e
  exact ⟨hC, hS, hL⟩

/-- **The ledger's "one" at link l.** -/
theorem AtMgA.one_at (h : AtMgA o Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (hB : h.oneC l = true) :
    OneNumber (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (At.num Zp)
      (idxAt (At.sentAt Zp) (At.num Zp) l) (_root_.Meaning.tlAt (At.X Zp)) l
      (fun j : Fin (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 l).length =>
        (h.toAtMg.𝔇 h.𝔇).seat3 l false j.1) (h.toAtMg.𝔇 h.𝔇).arr id :=
  K03.oneNumber_of_B (D := At.sentAt Zp) hl h.plan.laid h.three.1 h.three.2.1 h.three.2.2 hB

/-- **The ledger's "own" at link l.** -/
theorem AtMgA.own_at (h : AtMgA o Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (hB : h.namedC l = true) (hC : h.toAtMg.offC = true) :
    OwnNamed (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (At.num Zp) (_root_.Meaning.tlAt (At.X Zp)) l
      (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms (h.toAtMg.𝔇 h.𝔇).N :=
  K03.ownNamed_of (D := At.sentAt Zp) hl h.plan.laid hB (h.toAtMg.placesOff hC)

end P5J

#print axioms P5J.AtMgA.three
#print axioms P5J.AtMgA.one_at
#print axioms P5J.AtMgA.own_at
