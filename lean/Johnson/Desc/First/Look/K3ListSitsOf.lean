-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3ListSitsOf.lean: the kind "lookup" (K3), the lookup argument on the calls:
THE LOOKUPS' AUTHORS' `ListSits` (Johnson/Desc/First/Look/K3CallsFill.lean: what is asked of the
list of rounds' seats and of the two readers of OOD samples) AT THE NAMED READERS: TWO OF ITS FIVE
FIELDS FALL.

Main name:
  `listSits_named`: where the table's reader of OOD samples is `smpNamed D.codes seats` and the
    lookup's is `smpCalls seats D rad seat x` (Johnson/Desc/Sound/SmpNamed.lean, SmpNamedK3.lean):
    bySeat (`smpNamed_bySeat`) and smpIs (`smpCalls_is`, by unfolding) hold; so `ListSits` follows
    from its other three: some (a member alike, in shape, radius and seat), sent (each seat is among
    what the segment sends at moment 0), fits.

Limits: the three are premises; tests with code that give them lie in Johnson/P5J/Rad3Seat3At.lean
and Rad3Seat3Tests.lean (they have run nowhere).
(Where this and lean/THEOREM.md differ, the page
holds.)
Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3CallsFill
import Johnson.Desc.Sound.SmpNamedK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers)

/-- **`ListSits` at the named readers, from three.** -/
theorem listSits_named {P Xi : Type} (G : Desc.FileDescription Xi) (x : Desc.First.Look.Place)
    (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ) (seat : ℕ → Bool → ℕ → ℕ × ℕ)
    (seats : List (ℕ × ℕ)) (ms : List Mem) (N : Numbers) (m : ℕ)
    (hsome : ∀ i, ∃ y ∈ ms,
      Alike y ⟨callsSending x D rad (fun j => seat x.link false j.1), i⟩)
    (hsent : ∀ i : Fin (sigListCalls D rad x.link).length, seat x.link false i.1 ∈ N.sent m 0)
    (hfits : SeatFits G D.codes (sigListCalls D rad x.link) fun j => seat x.link false j.1) :
    ListSits (P := P) G x D rad (fun j => seat x.link false j.1) (smpNamed D.codes seats)
      (smpCalls seats D rad seat x) ms N m :=
  ⟨hsome, smpNamed_bySeat _ _, hsent, hfits, fun z s i => smpCalls_is seats D rad seat x z s i⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.listSits_named
