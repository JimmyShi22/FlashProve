-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Laid/ProofInstFits.lean: THE KEY OF THE PROOF FILE's INSTANCE HAS ITS SIZES BY MAKE. A
law file.

The proof file's decision is asked at `instanceAsPlainRecord z`, z a request and a record of the full size's TYPE
(`RecFull`: `RecP NZ frS.P.v 29 1`). The instance's key is the program's key written of that record
(`instOf_key`, by definition), and a key so written has as many entries, seeds and coordinates as
the
type says (`OnBytes.Slice.keyOf_fits`, OnBytes/Slice/KeyOfRec.lean). So it fits every shape of an
index
that has these three numbers, whatever the record holds.

  instOf_key_fits     **the instance's key fits a shape with the full size's three numbers**

What it does not say: that the shape which a chain's blocks read HAS these three numbers: that is a
fact on the plan, owed by whoever calls this. The full size alone. Nothing on what a yes gives.

-/
import Johnson.Desc.Laid.ProofFullLaw
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.Maker
open OnBytes

/-- **The instance's key fits a shape with the full size's three numbers.** -/
theorem instOf_key_fits (z : XF × RecFull) (sh : OnBytes.Params.IndexShape)
    (hv : sh.v = frS.P.v) (hs : sh.answers = 1) (hl : sh.cubeBits = 29) :
    (instanceAsPlainRecord z).pub.key.fits sh = true := by
  rw [instOf_key]
  exact keyOf_fits _ z.2 sh hv hs hl

end LPFD.Full

#print axioms LPFD.Full.instOf_key_fits
