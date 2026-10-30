-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseSeated.lean: Johnson/Road/K4/CloseLater.lean's `Plan4.k04LawAt_later` AT BLOCKS
OF THE FIRST CHAIN's RECORD WHOSE YES IS A YES OF `blockAtS par`, AT ANY TYPE OF CLAIMS; AND AT THE
TYPE Unit, AT THE FORM OF THE TERM THAT THE FILE's DESCRIPTION SEATS AT K4's PLACE. Three theorems,
of a few lines.

  `seatOk_S`: `SeatOk seatS s` (CloseBehind.lean) wherever seatS.look s = some fo.
  `Plan4.leads_sameYes`: for bk' : Block S Cl' with «a yes of bk' is a yes of blockAtS par, with the
    same record behind», and a piece pc at Cl' with pc.b = below bk': the conclusion of `K04LawAt`
    (Johnson/Desc/Plain/K04Plain.lean) at L := seatS, from the premises of `k04LawAt_later`.
  `Plan4.leads_guarded`: the same at Cl' := Unit and bk' := { gd (bare (blockAtS par)) with name :=
    n }, for every gd : Block S Unit → Block S Unit that only refuses more («a yes of gd b is a yes
    of b, with the same record behind»), and every name n. WHY SO: the description's driver seats
    K4's block bare of its claims, under a guard that refuses a marked record, and under a name of
    its own; that guard's text lies outside this library's folders: so it is a letter here.

Limits. K04_law IS NOT PROVED BY THIS: those of CloseLater.lean: `Plan4.Pays`' fields are unpaid.
That the driver's own guard only refuses more is a premise (hgd). A group that is not the first.

-/
import Johnson.Road.K4.CloseAtS
import Johnson.Road.K4.CloseBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes.Flat OnBytes.Maker
open OnBytes.Desc.First.K4 (Par blockAtS seatS bare)
open OnBytes.Desc.First.P1 (TailNums)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Front Behind HearsAs hearsAs_of_yes)
open Inst.Model (Scl)

variable [scl : Scl] {Mm X Wt Cl' : Type} {Fr : Frame} {Q : Plan4 Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

omit scl in
/-- **The seat's two laws at the first chain's record, wherever the seat finds what the lookup
returned**: that is so inside a layers' link alone. -/
theorem seatOk_S {s : S} {fo : OnBytes.Model.Forest.Heard} (h : seatS.look s = some fo) :
    SeatOk seatS s := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  cases here with
  | lay a => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | _ => cases h

/-- **The law's conclusion at every block whose yes is a yes of the block that rides.** -/
theorem Plan4.leads_sameYes (A : Q.Meets par hS pcl) (hp3 : hS.p3 = true)
    (N : TailNums Q.full.own.toOwn.tail) (Sm : Sem Wt) (Lt : Letters S Wt Fr) (Ex : ExtSpec)
    (bk' : Block S Cl')
    (hy : ∀ s rs cols s', bk'.decide s rs cols = .ok s' →
      (blockAtS par).decide s rs cols = .ok s')
    (pc : Piece (ckP .two) Fr S Cl' Wt) (hds : pc.ds = dsLater par)
    (fa : S × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E) (hb : pc.b = below bk') (hback : pc.back = [])
    (herr : Err.le ((Plan4.mapsAt A N Ex hds).err ((chF Q.full).eps Ex)) pc.err)
    (H : Plan4.Pays A N seatS Ex pc hds fa part Lt.on Lt.on' (Front Lt) (Behind seatS Sm Lt par)
      zt) (m : Mm) :
    pc.ior.red.Leads Lt.on
      (fun a b => Lt.on' b ∧ ∀ w, part w = m → Behind seatS Sm Lt par b w → Front Lt a w)
      pc.err :=
  Plan4.k04LawAt_later A hp3 N seatS Sm Lt Ex bk' pc hds fa part zt hback herr H hb
    (hearsAs_of_yes seatS par (blockAtS par) bk' hy (hearsAs_S par)) m

/-- **At the type Unit, at the form of the seated term.** -/
theorem Plan4.leads_guarded (A : Q.Meets par hS pcl) (hp3 : hS.p3 = true)
    (N : TailNums Q.full.own.toOwn.tail) (Sm : Sem Wt) (Lt : Letters S Wt Fr) (Ex : ExtSpec)
    (gd : Block S Unit → Block S Unit)
    (hgd : ∀ (b : Block S Unit) s rs cols s', (gd b).decide s rs cols = .ok s' →
      b.decide s rs cols = .ok s') (n : String)
    (pc : Piece (ckP .two) Fr S Unit Wt) (hds : pc.ds = dsLater par)
    (fa : S × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E)
    (hb : pc.b = below { gd (bare (blockAtS par)) with name := n }) (hback : pc.back = [])
    (herr : Err.le ((Plan4.mapsAt A N Ex hds).err ((chF Q.full).eps Ex)) pc.err)
    (H : Plan4.Pays A N seatS Ex pc hds fa part Lt.on Lt.on' (Front Lt) (Behind seatS Sm Lt par)
      zt) (m : Mm) :
    pc.ior.red.Leads Lt.on
      (fun a b => Lt.on' b ∧ ∀ w, part w = m → Behind seatS Sm Lt par b w → Front Lt a w)
      pc.err :=
  Plan4.leads_sameYes A hp3 N Sm Lt Ex
    ({ gd (bare (blockAtS par)) with name := n } : Block S Unit)
    (fun s rs cols s' hd => hgd (bare (blockAtS par)) s rs cols s' hd) pc hds fa part zt hb hback
    herr H m

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.seatOk_S
#print axioms OnBytes.Road.K4.Plan4.leads_sameYes
#print axioms OnBytes.Road.K4.Plan4.leads_guarded
