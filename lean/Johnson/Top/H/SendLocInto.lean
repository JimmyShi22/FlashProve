-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/SendLocInto.lean: the two kinds of block "SEND seed, LOC", without and with a rider,
between the joints with their own conditions, as values of `Kind` (Johnson/Top/Kind.lean), at any
written list of sizes.

Nothing new is proved: every line is a call of Cb/Pv/Switch/SendLocInto.lean. The reductions,
extractors and errors are those of `kSendLoc` and `kSendLocRide` (Johnson/Top/H/SendLoc.lean,
SendLocRide.lean); the joints are the library's joints over the open oracle messages AS THEY STAND
(`Sig.over`), not with the condition moved (`IOR.Rels.cf`).
Main names:
  `kSendLocInto L`, `kSendLocRideInto L`: the kinds.
  `…_know`, `…_point`, `…_local`: under the condition at every size of the list.
  `…_good`: `KObj.BK.Good` at every size of the list; its third clause, knowledge soundness INTO the
    joint behind, is `hAtInto` itself. There is no `…_onOut`: that clause does not hold of a
sending.
Limits: as in the two files named.
-/
import Johnson.Top.Kind
import Cb.Pv.Switch.SendLocInto
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

section
variable {E : Type} [Field E] [Fintype E]

/-- "SEND seed, LOC" between the joints with their conditions. -/
@[reducible] noncomputable def kSendLocInto (L : List (Cb.Pv.SendLoc.Size E)) : Kind.{1} where
  Size := Cb.Pv.SendLoc.Size E
  sizes := L
  src := fun s => jOf (Cb.Pv.SendLoc.inJP s)
  dst := fun s => jOf (Cb.Pv.SendLoc.outJP s)
  block := fun s => ⟨Cb.Pv.SendLoc.R s, Cb.Pv.SendLoc.ext s, Cb.Pv.SendLoc.eps s⟩

/-- The same with a rider. -/
@[reducible] noncomputable def kSendLocRideInto (L : List (Cb.Pv.SendLocRide.Size E)) : Kind.{1}
  where
  Size := Cb.Pv.SendLocRide.Size E
  sizes := L
  src := fun s => jOf (Cb.Pv.SendLocRide.inJP s)
  dst := fun s => jOf (Cb.Pv.SendLocRide.outJP s)
  block := fun s => ⟨Cb.Pv.SendLocRide.R s, Cb.Pv.SendLocRide.ext s, Cb.Pv.SendLocRide.eps s⟩

section Plain
variable (L : List (Cb.Pv.SendLoc.Size E)) (h : ∀ s ∈ L, Cb.Pv.SendLoc.OK s)
include h

theorem kSendLocInto_know : (kSendLocInto L).Know := fun s hs =>
  Cb.Pv.SendLoc.know_plain s (Cb.Pv.SendLoc.hAtInto s (h s hs))

theorem kSendLocInto_point : (kSendLocInto L).Point := fun s hs => Cb.Pv.SendLoc.point s (h s hs)

theorem kSendLocInto_local : (kSendLocInto L).Local := fun s hs => Cb.Pv.SendLoc.isLocal s (h s hs)

theorem kSendLocInto_good : ∀ s ∈ L, ((kSendLocInto L).block s).Good := fun s hs =>
  ⟨Cb.Pv.SendLoc.point s (h s hs), Cb.Pv.SendLoc.isLocal s (h s hs),
    Cb.Pv.SendLoc.hAtInto s (h s hs)⟩

end Plain

section Ride
variable (L : List (Cb.Pv.SendLocRide.Size E)) (h : ∀ s ∈ L, Cb.Pv.SendLocRide.OK s)
include h

theorem kSendLocRideInto_know : (kSendLocRideInto L).Know := fun s hs =>
  Cb.Pv.SendLocRide.know_plain s (Cb.Pv.SendLocRide.hAtInto s (h s hs))

theorem kSendLocRideInto_point : (kSendLocRideInto L).Point := fun s hs =>
  Cb.Pv.SendLocRide.point s (h s hs)

theorem kSendLocRideInto_local : (kSendLocRideInto L).Local := fun s hs =>
  Cb.Pv.SendLocRide.isLocal s (h s hs)

theorem kSendLocRideInto_good : ∀ s ∈ L, ((kSendLocRideInto L).block s).Good := fun s hs =>
  ⟨Cb.Pv.SendLocRide.point s (h s hs), Cb.Pv.SendLocRide.isLocal s (h s hs),
    Cb.Pv.SendLocRide.hAtInto s (h s hs)⟩

end Ride

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.kSendLocInto_good
#print axioms VerifiableInference.OnPublicFiles.kSendLocRideInto_good
