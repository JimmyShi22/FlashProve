-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/WideAt.lean: THE STRUCK PARTS' DATA AT THE CLOSED VALUES: the second argument of the
wider meaning (`mgWide 𝔇 E Mg`, Johnson/Desc/Sound/MgWide.lean) as a term off the proof file's
public part. Definitions and three equations.
Why. Ties that were typed before thirteen public tests left the table stand at the wider meaning,
and are carried to the composed meaning by a bridge. The wider meaning takes, beside the composed
meaning's parameters 𝔇, the data E of the parts that were struck. 𝔇 has its closed term
(`At.𝔇All`, Johnson/P5J/LettersAll.lean); this file gives E's.
  `At.dP Zp cF`: the pending claim's and the approximate range proof's data: each field its own
    authors' term (Johnson/Top/H0/Fill/D1At.lean): `tlAt Zp`, `fvsAt Zp`, `free0Of` at the first
    chain's codes, the list of the chain's oracle messages' shapes and the number of the index
    masks' message.
  `At.E Zp cF L`: d12 := `At.d12 Zp L` (Johnson/P5J/LettersAt2.lean; L: the listed seats, handed
    in under that file's named test `laidB`), dP := `At.dP Zp cF`, reqW := `At.reqW`.
  `E_ft`, `E_M`, `E_reqW`: the first tree's number is 0; the listed shapes are `msgsOfChain
    Zp.made.proof.1`; the request's words are the request file's bytes as words: by unfolding.
Limits: definitions. ONE SILENT DEFAULT INSIDE AN OWNER's TERM: `free0Of` answers 0 where the list
has no shape at that number: its authors' named test is `FillP1.startB Zp M ix`: whoever spends
free0 asks it. `tlAt` answers none where the blank ground cannot be made. Nothing has been
evaluated. No soundness is claimed.

-/
import Johnson.P5J.LettersAt2
import Johnson.Top.H0.Fill.D1At
import Johnson.Desc.Sound.MgWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (FillP1.PlusData FillP1.tlAt FillP1.fvsAt FillP1.free0Of)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open VerifiableInference.Desc.Sound (WideData)

variable (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl)

/-- The pending claim's and the approximate range proof's data, each field its authors' term. -/
def dP : FillP1.PlusData where
  tl := FillP1.tlAt Zp
  fvs := FillP1.fvsAt Zp
  free0 := FillP1.free0Of (cs Zp) (msgsOfChain Zp.made.proof.1) (N Zp cF).indexNo

/-- **The struck parts' data at the closed values.** -/
def E (L : Laid) : WideData ProofFile.InstPub where
  d12 := d12 Zp L
  dP := dP Zp cF
  reqW := reqW

theorem E_ft (L : Laid) : (E Zp cF L).d12.ft = 0 := rfl

theorem E_M (L : Laid) : (E Zp cF L).d12.M = msgsOfChain Zp.made.proof.1 := rfl

theorem E_reqW (L : Laid) (q : ProofFile.InstPub) :
    (E Zp cF L).reqW q = OnBytes.Model.Verify.words32 q.request := rfl

end P5J.At

#print axioms P5J.At.E_ft
#print axioms P5J.At.E_M
#print axioms P5J.At.E_reqW
