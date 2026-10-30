-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/KeyPoints.lean: the two cuts that `verify-on-bytes` takes of a lookup call's key
point (`Head.ztOf`, `Head.zjOf`, OnBytes/Model/HeadHeard.lean), where the key point ends as the
lookup's point does. Tools for the tie of the weights at the output head's seat.

All of this file is a tool: it holds for all shapes, layouts and records of a lookup, and names no
description of the protocol.

Why. The routine that makes the output head's list of tables takes the positions' point of three
tables from a call's key point (`ztOf`), and the point on a block's features of one table from the
tail of a call's point on its columns (`zjOf`, cut by `cutLast`, OnBytes/Model/Tensors.lean). The
kind takes both off the end of the lookup's own point. The kind's text tests, of every call, that
its key point has as many coordinates as the call's columns and the positions ask, and ends as the
lookup's point does. Under that test the two agree, whichever call is taken.

What is here. J: the layout's number of coordinates on the columns of call q.
  `ztOf_tail`: `ztOf h L G q` is the last lt coordinates of the lookup's point.
  `zjOf_tail`: the cut of `zjOf L G q` at its last ls coordinates returns, and these are the first
    ls of the last ls + lt coordinates of the lookup's point.

Premises of both. The key point of call q has J + lt coordinates. Its last ls + lt are those of the
lookup's point. ls is at most J. The lookup's point has ls + lt coordinates at least.

Of OnBytes/Model/ this file names `Head.Shape`, `Head.HL`, `Forest.Heard`, `Head.ztOf`, `Head.zjOf`
and `cutLast`.

Limits. That the layout's J is the number that the kind's test reads is a premise of whoever calls
these. Nothing on when a point is drawn. Nothing on soundness.


-/
import Johnson.Desc.Reads.PointCuts
import OnBytes.Model.HeadHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open OnBytes.Model (cutLast)
open OnBytes.Model.Head (Shape HL ztOf zjOf)
open VerifiableInference.Desc.Kinds (Point)

/-- The positions' part of a call's key point is the end of the lookup's point. -/
theorem ztOf_tail (h : Shape) (L : HL) (G : OnBytes.Model.Forest.Heard) (q : ℕ) {ls : ℕ}
    (hs : (G.zk.getD q #[]).size = (L.calls.getD q default).lJ + h.lt)
    (hl : Point.last (G.zk.getD q #[]) (ls + h.lt) = Point.last G.zx (ls + h.lt))
    (hJ : ls ≤ (L.calls.getD q default).lJ) (hz : ls + h.lt ≤ G.zx.size) :
    ztOf h L G q = Point.last G.zx h.lt :=
  (key_tail (G.zk.getD q #[]) G.zx hs hl hJ hz).1

/-- The tail of a call's point on its columns is the lookup's point on a block's features. -/
theorem zjOf_tail (h : Shape) (L : HL) (G : OnBytes.Model.Forest.Heard) (q : ℕ) {ls : ℕ}
    (hs : (G.zk.getD q #[]).size = (L.calls.getD q default).lJ + h.lt)
    (hl : Point.last (G.zk.getD q #[]) (ls + h.lt) = Point.last G.zx (ls + h.lt))
    (hJ : ls ≤ (L.calls.getD q default).lJ) (hz : ls + h.lt ≤ G.zx.size) :
    ∃ lowN, cutLast (zjOf L G q) ls = .ok lowN ∧
      lowN.2 = (Point.last G.zx (ls + h.lt)).extract 0 ls := by
  have hsz : (zjOf L G q).size = (L.calls.getD q default).lJ := by
    unfold zjOf
    simp only [Array.size_extract]
    omega
  unfold cutLast
  rw [if_neg (by omega)]
  refine ⟨_, rfl, ?_⟩
  show (zjOf L G q).extract ((zjOf L G q).size - ls) (zjOf L G q).size = _
  rw [hsz]
  exact (key_tail (G.zk.getD q #[]) G.zx hs hl hJ hz).2

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.ztOf_tail
#print axioms VerifiableInference.Reads.zjOf_tail
