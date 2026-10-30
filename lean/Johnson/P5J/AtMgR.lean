-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/AtMgR.lean: THE ONE HEAD OF A COUNTED STATEMENT, WITH THE FACTS ON EVERY REACHED STATE. One structure, one theorem. The public numbers that the facts read are A CLOSED TERM: At.foldD Zp cF L (Johnson/P5J/FoldAt.lean): every field at the closed letters.


THE COUNTED FORM: in scope · where the verifier's own value is laid · where the named conditions on the list of rounds hold · where the facts on every reached state hold → … at the composed meaning's constant. Johnson/P5J/AtMg.lean bundles the first three (with "the two roads' public data are one"). HERE THE FOURTH COMES BESIDE:
  AtMgR o Z D r Zp Np cF Rch at_ L : Prop: A STRUCTURE THAT EXTENDS AtMg BY THREE FIELDS:
    listed  At.laid? Zp = some L: the listed seats of the first chain's oracle messages are there (NO DEFAULT: L is handed in with this equation)
    start   FillP1.startB Zp ‹the planner's first chain's oracle messages' shapes› ‹the index masks' number› = true: it fences the silent 0 of foldD's free0 (no shape at that number), and is the one premise under which other files carry "room" from its other term to this one
    fold    First.FoldFacts Rch at_ (At.foldD Zp cF L) At.reqW At.links At.ps (Johnson/Desc/First/FoldFacts.lean: a field a fact; STATEMENTS ALONE there)
  LETTERS LEFT: Rch (what "reached" means) and at_ (how a statement is read as a public part and a state): the chain of promises' own.
  free0 STANDS IN foldD AT ONE OF ITS TWO TERMS (FillP1.free0Of …); "room" is paid in other files at the other (K1.free0Of ‹the blank ground's first› (gpOf Z)): the equation of the two is left to those files; by runs they are one number.
  AtMgR.head: it is an AtMg: whatever ends in AtMg can be called.

Limits. A bundling. At Rch := never "fold" is free: the weight lies in the meant Rch and in the induction along the run: not here. It shows nothing to hold. The full size alone. NO MEMBER. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.AtMg
import Johnson.P5J.FoldAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (FoldFacts)
open OnBytes.Maker (WholeD)

/-- **THE ONE HEAD, WITH THE FACTS ON EVERY REACHED STATE.** -/
structure AtMgR (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × TS) (L : VerifiableInference.Desc.K12.Door.Laid) : Prop
    extends AtMg o Z D r Zp Np cF where
  listed : At.laid? Zp = some L
  start : VerifiableInference.Desc.First.FillP1.startB Zp
    (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true
  fold : FoldFacts Rch at_ (At.foldD Zp cF L) At.reqW At.links At.ps

theorem AtMgR.head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {X : Type}
    {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × TS} {L : VerifiableInference.Desc.K12.Door.Laid}
    (h : AtMgR o Z D r Zp Np cF Rch at_ L) : AtMg o Z D r Zp Np cF := h.toAtMg

end P5J

#print axioms P5J.AtMgR.head
