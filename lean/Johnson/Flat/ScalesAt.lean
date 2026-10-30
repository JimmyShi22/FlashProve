-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ScalesAt.lean: the table of scales in the claim of Johnson/Flat/LedgerClaim.lean as a
written term of the verifier's own public part, and the meaning at it.

One definition and two theorems. In RelL s M x the table s stands in every condition. The sub-proofs
are checked at the table that the verifier reads from its scale file. So s must be that table.
  scalesAt X: for the public part X that the verifier's function publicOf returns on the parameter
    file and the scale file (OnBytes/Model/VerifyPublic.lean): the library's table of the scale
    words X.layers.sc at the layers' shape of X.P, cut by the verifier's own rule, with the final
    normalisation of the head's shape X.hS (scalesOf, Johnson/Road/FormsKeysScl.lean).
  scalesAt_lawful: it is lawful, under three public hypotheses: publicOf has returned X; 46 numbers
    and two switches of the parameter file are the reference's (Hd.PublicAt, decidable); the words
    of the scale file are the reference's (lawful_of_at, Johnson/Road/Lane5TopPub.lean).
  sound_core_at: sound_core at scalesAt X, under these three.
That the table read off the two files' bytes by the format's page is this one:
Johnson/Flat/ScalesSame.lean.

Limits: nothing on a protocol. That the sub-proofs' checks read the scales as scalesAt X reads them
is not shown here. The three hypotheses are met by runs at the full-size example's files, by no
theorem. The reference sizes and exact match alone.

-/
import Johnson.Road.Lane5TopPub
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles.Flat

open Inst.Model OnBytes OnBytes.Road OnBytes.Road.L5
open Inst.Model.Layout (kRef hRef)
open OnBytes.Model.Verify (publicOf layerShape)

/-- **The table of scales of the verifier's public part.** -/
def scalesAt (X : Model.Verify.Public) : Cm.Scales :=
  OnBytes.Road.scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- It is lawful, at the reference's numbers and scale words. -/
theorem scalesAt_lawful (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) : (scalesAt X).Lawful :=
  lawful_of_at h A hW

/-- **The meaning at the verifier's own table of scales.** -/
theorem sound_core_at (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) {rows cols : ℕ} (hr : rows ≤ hRef)
    (hc : cols ≤ 2 ^ kRef) {M : Fin rows → Fin cols → GE} {x' : List Token × List Token}
    {b : List Token} {x : Instance ppref} (hb : requestOfTokens x' b = some x)
    (hR : RelL (scalesAt X) M x) :
    ∀ position (hp : position < x'.2.length),
      nextTok (scalesAt X) M (x'.1 ++ x'.2.take position) = some x'.2[position] :=
  sound_core (scalesAt_lawful h A hW) hr hc hb hR

end VerifiableInference.OnPublicFiles.Flat

#print axioms VerifiableInference.OnPublicFiles.Flat.scalesAt_lawful
#print axioms VerifiableInference.OnPublicFiles.Flat.sound_core_at
