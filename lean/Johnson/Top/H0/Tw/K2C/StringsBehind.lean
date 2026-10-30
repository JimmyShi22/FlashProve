-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/StringsBehind.lean: code switching (the kind K2): «SHOWN» AND «NO COLLISION»
AT EVERY TENANT WHOSE PIN IS OPEN BEHIND A SWITCH: the index masks' message's tenant, which rides,
and the new sending's tenants. A joining. For the tie t2's premise on the strings' side. NO BLOCK
IMPORTS THIS FILE.
  sn_behind   at an accept of a piece over the verifier's state, the public part z beside it: the
              index masks' tenant's tree was sent in front of the piece (N.index.1 < p.base) · the
              table's reader of OOD samples gives behind what it gives in front at the members
              that sit there · «shown» and «no collision» there in front · both at every tenant of
              N.sent m 0 behind (K2C/StringsNew.lean) ⟹ both at every member of N.index :: N.sent
              m 0 behind
CALLED: shownJT_rides · noCollJT_rides (Johnson/Desc/Sound/SigRides.lean), at the reader
with z laid in. That N.index :: N.sent m 0 is what the promise behind a switch speaks of: by
Lean's kernel at the written list (Johnson/P1K2R/PinsBehind.lean: sampled_behind).
No soundness is claimed.
-/
import Johnson.Desc.Sound.SigRides
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (FileDescription Strs)
open VerifiableInference.Desc.Sound

theorem sn_behind {P Xi Cl W : Type} {C : CK} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (N : Numbers) (m : ℕ) (p : Piece C Fr S Cl W) (z : P) (a b : S × Fr.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b) (hI : N.index.1 < p.base)
    (hSI : ∀ x ∈ ms, SitsAt x N.index.1 N.index.2 → smp (z, b.1) x.1 x.2 = smp (z, a.1) x.1 x.2)
    (hf : shownJT cs G ms N.index.1 N.index.2 (strsOf Fr a.2) ∧
      noCollJT cs G smp ms N.index.1 N.index.2 (z, a.1) (strsOf Fr a.2))
    (hnew : ∀ x ∈ N.sent m 0, shownJT cs G ms x.1 x.2 (strsOf Fr b.2) ∧
      noCollJT cs G smp ms x.1 x.2 (z, b.1) (strsOf Fr b.2)) :
    ∀ x ∈ N.index :: N.sent m 0, shownJT cs G ms x.1 x.2 (strsOf Fr b.2) ∧
      noCollJT cs G smp ms x.1 x.2 (z, b.1) (strsOf Fr b.2) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ⟨shownJT_rides cs G p ms _ _ hI a b τ hb hf.1,
      noCollJT_rides cs G (fun s => smp (z, s)) p ms _ _ hI a b τ hb hSI hf.2⟩
  · exact hnew x hx

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sn_behind
