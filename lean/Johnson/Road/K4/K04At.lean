-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04At.lean: THE LAST LINE BUT ONE OF K4's ROAD: `K04LawAt`, the statement of
the law of the layers' own rounds with the world's pinned part outside the game, FROM THE PREMISES
OF Johnson/Road/K4/CarriageLedger.lean AND, FOR THE FIRST GROUP, CarriageFirst.lean. Two theorems,
of one line each.

`K04LawAt` is stated in Johnson/Desc/Plain/K04Plain.lean.
There the block that rides at K4's place is a letter bk, at any type Cl of claims, of which the law
reads only what its yes gives (`HearsAs L par bk`): so the statement can be called at the real row's
piece, whose block is K4's own, typed at a part of the record and lifted. Behind `K04LawAt` stands
one more line: `k04_of_at` there gives the row's law `K04Law` from it and a pin.

  `k04LawAt_of_ledger`: for a piece that puts no round behind its own, maps that are as asked,
    errors that bear the carried ones, the library's three records and `Plan4.HeardL` at the
    statement's own letters (`Lt.on`, `Lt.on'`, `Front Lt`, `Behind L Sm Lt par`): `K04LawAt L Sm Lt
    part par bk pc`, at every block bk.
  `k04LawAt_first`: the same from `Plan4F.HeardL` and the library's four records of the first chain.

Limits. K04_law IS NOT PROVED BY THIS: EVERY PREMISE WITH CONTENT IS UNPAID, among them: the five
fields of `Plan4.HeardL` | `Plan4F.HeardL` (kept, coin, pending, ledger, first), the library's
records on names, forms and sizes, the maps and the errors; a `Plan4` | `Plan4F` at a real plan; the
seat's laws; and, behind this file, the pin. Nothing shows that they can be met together. The
statement's letters (`Sem`, `Letters`) are filled by nobody yet. Neither theorem has a premise on g:
which of the two can be fed at a place is decided by the fields `ledger` and `first`, not by the
maps' type.
-/
import Johnson.Road.K4.CarriageLedger
import Johnson.Road.K4.CarriageFirst
import Johnson.Desc.Plain.K04Plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop TWhole Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes.Flat OnBytes.Maker
open OnBytes.Desc.First.K4 (Par Seat)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Front Behind K04LawAt)
open Inst.Model (Scl)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {Nm J₂ : Type} [Fintype J₂]
  [DecidableEq J₂]
  {Y : LateLay Nm J₂} {ιN : NormsNm → Nm} {ιT : TermsNm → Nm} {ιG : GatedNm → Nm}

/-- **`K04LawAt` from the premises of the carriage.** -/
theorem k04LawAt_of_ledger (Q : Plan4 Cb.Gl.E Mm X) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (par : Par)
    (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) {Mp : Maps pc.ds ((chF Q.full).R Ex).shape}
    {fa : T × Fr.E.Str → X × Ex.Str} (part : Wt → Mm)
    {fm : (tailF Q.full).s7.Nx → Nm → TWhole.Aff Cb.Gl.E Q.full.J}
    {zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E} {b s B sG : ℕ}
    {R : (tailF Q.full).s7.Nx → Rest3 Cb.Gl.E (Q.full.J ⊕ J₂)}
    (hback : pc.back = []) (hOK : Mp.OK)
    (herr : Err.le (Mp.err ((chF Q.full).eps Ex)) pc.err)
    (N : NormsOk Q.full.toOwnPar Q.full.wPart Y ιN fm zt b s B) (Tm : TermsOk Q.full Y ιT fm)
    (G : GatedOk Q.full Y ιG fm sG)
    (H : Q.HeardL L Ex par pc Mp fa part Lt.on Lt.on' (Front Lt) (Behind L Sm Lt par) Y ιN ιT ιG
      fm zt b B sG R) :
    K04LawAt L Sm Lt part par bk pc := fun hb hk m =>
  Q.leads_ledger L Ex hk hb hback hOK herr N Tm G H m

/-- **`K04LawAt` in the first group, from the premises of its carriage.** -/
theorem k04LawAt_first {ιE : EmbNm → Nm} (Q : Plan4F Cb.Gl.E Mm X) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (par : Par)
    (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt)
    {Mp : Maps pc.ds ((chFF Q.fullF).R Ex).shape}
    {fa : T × Fr.E.Str → X × Ex.Str} (part : Wt → Mm)
    {fm : (tailW Q.fullF).s7.Nx → Nm → TWhole.Aff Cb.Gl.E Q.fullF.J}
    {zt : (tailW Q.fullF).s7.Nx → ℕ → Cb.Gl.E} {b s B sG : ℕ}
    {R : (tailW Q.fullF).s7.Nx → Rest2 Cb.Gl.E (Q.fullF.J ⊕ J₂)}
    (hback : pc.back = []) (hOK : Mp.OK)
    (herr : Err.le (Mp.err ((chFF Q.fullF).eps Ex)) pc.err)
    (N : NormsOkF Q.fullF Y ιN fm zt b s B) (Tm : TermsOkF Q.fullF Y ιT fm)
    (G : GatedOkF Q.fullF Y ιG fm sG) (Em : EmbOkF Q.fullF Y ιE fm)
    (H : Q.HeardL L Ex par pc Mp fa part Lt.on Lt.on' (Front Lt) (Behind L Sm Lt par) Y ιN ιT ιG
      ιE fm zt b B sG R) :
    K04LawAt L Sm Lt part par bk pc := fun hb hk m =>
  Q.leads_ledger L Ex hk hb hback hOK herr N Tm G Em H m

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04LawAt_of_ledger
#print axioms OnBytes.Road.K4.k04LawAt_first
