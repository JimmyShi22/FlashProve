-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseAtS.lean: Johnson/Road/K4/CloseLater.lean's `Plan4.k04LawAt_later` AT THE BLOCK
THAT RIDES IN THE FIRST CHAIN: `blockAtS par` (Johnson/Desc/First/K4/AtS.lean: K4's own block, typed
at its part of the carried record and lifted), read through the seat `seatS` at that record
(Johnson/Desc/First/K4/SeatS.lean). One lemma and one theorem, of one line each.

  `hearsAs_S`: `HearsAs seatS par (blockAtS par)` (SeatS.lean's `hearsAs_atS`).
  `Plan4.leads_atS`: for a piece pc of the first chain's record with pc.b = below (blockAtS par),
    pc.ds = dsLater par, pc.back = []: for each tuple m of pinned messages the piece's reduction
    leads to: the promise behind holds, and for every world whose pinned part is m, what the row
    opens gives what it closes: the conclusion of `K04LawAt` (Johnson/Desc/Plain/K04Plain.lean) at
    L := seatS, from `Plan4.Meets`, profile 3, the errors' premise and `Plan4.Pays`.

Limits. K04_law IS NOT PROVED BY THIS: those of CloseLater.lean: `Plan4.Pays`' eleven fields are
unpaid. Outside a layers' link `seatS` reads an empty ledger and nothing heard: its laws hold inside
a link alone (SeatS.lean). A group that is not the first.
-/
import Johnson.Road.K4.CloseLater
import Johnson.Desc.First.K4.SeatS

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Aff)
open OnBytes.Desc.First.K4 (Par blockAtS seatS hearsAs_atS)
open OnBytes.Desc.First.P1 (TailNums)
open _root_.Run (ckP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Front Behind HearsAs)
open Inst.Model (Scl)

/-- The block that rides hears as K4's own at the seat `seatS`. -/
theorem hearsAs_S (par : Par) : HearsAs seatS par (blockAtS par) := hearsAs_atS par

variable [scl : Scl] {Mm X Wt : Type} {Fr : Frame} {Q : Plan4 Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The law's conclusion at the block that rides**, at a group that is not the first, from the
premises that stay. -/
theorem Plan4.leads_atS (A : Q.Meets par hS pcl) (hp3 : hS.p3 = true)
    (N : TailNums Q.full.own.toOwn.tail) (Sm : Sem Wt) (Lt : Letters S Wt Fr) (Ex : ExtSpec)
    (pc : Piece (ckP .two) Fr S Aff Wt) (hds : pc.ds = dsLater par)
    (fa : S × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E) (hb : pc.b = below (blockAtS par))
    (hback : pc.back = [])
    (herr : Err.le ((Plan4.mapsAt A N Ex hds).err ((chF Q.full).eps Ex)) pc.err)
    (H : Plan4.Pays A N seatS Ex pc hds fa part Lt.on Lt.on' (Front Lt) (Behind seatS Sm Lt par)
      zt) (m : Mm) :
    pc.ior.red.Leads Lt.on
      (fun a b => Lt.on' b ∧ ∀ w, part w = m → Behind seatS Sm Lt par b w → Front Lt a w)
      pc.err :=
  Plan4.k04LawAt_later A hp3 N seatS Sm Lt Ex (blockAtS par) pc hds fa part zt hback herr H hb
    (hearsAs_S par) m

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hearsAs_S
#print axioms OnBytes.Road.K4.Plan4.leads_atS
