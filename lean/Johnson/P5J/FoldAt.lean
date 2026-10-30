-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FoldAt.lean: THE PUBLIC NUMBERS OF THE FACTS ON REACHED STATES, AS ONE CLOSED TERM
BESIDE THE COMPOSED MEANING's CONSTANT. One definition, eleven theorems, each by rfl.

Why. `FoldFacts Rch at_ d reqW links ps` (Johnson/Desc/First/FoldFacts.lean) reads a `FoldData` d.
At the composed meaning's constant d was a letter. Here every field of d is a term with code of the
public parameters Zp, the first chain cF of the IOP as written in Lean, and the list of seats L.

What is said. `At.foldD Zp cF L`: ft := 0 · L · M := the shapes of the planning program's notices ·
sent := the constant's codes, shape and layout, with the segments' lists of arrays · groupAt := the
table's numbers' own · ownAt, keptAt := the terms (Johnson/Desc/First/SentAtMoment.lean) at the
constant's shape, numbers, list of segments and list of places · free0, fvs := fillP1's own terms
(Johnson/Top/H0/Fill/D1At.lean). The theorems unfold each field; `foldD_groupAt`: the group of
segment l is l.

L is handed in: it is the value of `At.laid? Zp` under the named test `At.laidB Zp`
(Johnson/P5J/LettersAt2.lean): no default stands in its place.

Limits. Definitions and unfoldings. Nothing on soundness. THIS TERM ITSELF HAS BEEN EVALUATED
NOWHERE: the facts were evaluated on an honest run at both stored sizes at a FoldData laid by the
same makers, but through `atBlocks`, the chain's own lists of segments and places, and another term
for free0.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.LettersAt2
import Johnson.Desc.First.FoldFacts
import Johnson.Desc.First.SentAtMoment
import Johnson.Top.H0.Fill.D1At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (FoldData FillSent.ownAt FillSent.keptAt)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)

variable (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl)

/-- **The public numbers of the facts on reached states, at the closed values.** -/
def foldD (L : Laid) : FoldData where
  ft := 0
  L := L
  M := msgsOfChain Zp.made.proof.1
  sent := ⟨cs Zp, shape Zp, layout Zp, Zp.made.p.built.links.map (·.arrayOf)⟩
  groupAt := (N Zp cF).groupAt
  ownAt := FillSent.ownAt (shape Zp) (N Zp cF) links ps Zp.made.p.built.links
  keptAt := FillSent.keptAt (shape Zp) (N Zp cF) links ps Zp.made.p.built.links
  free0 := VerifiableInference.Desc.First.FillP1.free0Of (cs Zp) (msgsOfChain Zp.made.proof.1)
    (N Zp cF).indexNo
  fvs := VerifiableInference.Desc.First.FillP1.fvsAt Zp

theorem foldD_ft (L : Laid) : (foldD Zp cF L).ft = 0 := rfl

theorem foldD_L (L : Laid) : (foldD Zp cF L).L = L := rfl

theorem foldD_M (L : Laid) : (foldD Zp cF L).M = msgsOfChain Zp.made.proof.1 := rfl

theorem foldD_d12 (L : Laid) :
    (foldD Zp cF L).ft = (d12 Zp L).ft ∧ (foldD Zp cF L).L = (d12 Zp L).L ∧
      (foldD Zp cF L).M = (d12 Zp L).M := ⟨rfl, rfl, rfl⟩

theorem foldD_codes (L : Laid) : (foldD Zp cF L).sent.codes = cs Zp := rfl

theorem foldD_shape (L : Laid) : (foldD Zp cF L).sent.shape = shape Zp := rfl

theorem foldD_layout (L : Laid) : (foldD Zp cF L).sent.layout = layout Zp := rfl

theorem foldD_groupAt (L : Laid) (l : ℕ) : (foldD Zp cF L).groupAt l = l := rfl

theorem foldD_free0 (L : Laid) :
    (foldD Zp cF L).free0 = VerifiableInference.Desc.First.FillP1.free0Of (cs Zp)
      (msgsOfChain Zp.made.proof.1) (N Zp cF).indexNo := rfl

theorem foldD_fvs (L : Laid) :
    (foldD Zp cF L).fvs = VerifiableInference.Desc.First.FillP1.fvsAt Zp := rfl

theorem foldD_fvs_seat (L : Laid) :
    (foldD Zp cF L).fvs = Johnson.Desc.First.Walk.Seat.fvsOf Zp.p.built.links := rfl

end P5J.At

#print axioms P5J.At.foldD_d12
#print axioms P5J.At.foldD_groupAt
#print axioms P5J.At.foldD_fvs_seat
