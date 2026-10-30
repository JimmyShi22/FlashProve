-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CloseFirst.lean: `K04LawAt` AT THE FIRST GROUP (g = 0), WITH THE CARRIAGE's LETTERS
FIXED AND WHAT IS PROVED ELSEWHERE LAID IN: the maps, the late entries' names and forms, the four
records on names, forms and sizes, and the field `coin` are no premises. The twin of
Johnson/Road/K4/CloseLater.lean. Four definitions, a record of the premises that stay, and one
theorem. Glue: no new argument, no count.

FIXED HERE, at a place par whose plan meets the first value (`Plan4F.MeetsF`,
  Johnson/Road/K4/PlanMapsFirst.lean): the maps := `Plan4F.mapsAtF` (CloseYesFirst.lean); the late
  entries, their names and forms := `lateF`, `fmOfF` (LateNamesFirst.lean) at
  b := lPd - ls, s := sG := ls, B := d / S2 of the place's layout; the two parts of the ledger that
  are letters in the library := empty (`noRest2`, CarriagePartsFirst.lean).
  `roomKF`: the room for the late entries' names at a place.
  `Plan4F.eKF`: what the first chain puts out on the maps' image of a transcript.
  `Plan4F.clKF`: the library's ledger `clFirst`, part by part, off a last statement, at these
    letters.
  `Plan4F.yKF`: the entries at which its parts are asked: the messages', and each late entry at its
    form's value.

  `Plan4F.PaysF`: THE PREMISES THAT STAY, TWELVE FIELDS, each at every `Yes` of K4's block: `kept`
    (the promise behind) · and, from what the row opens: `pending` (`PendF`: the first group's
    pending row on the committed weights) · the nine parts `sq`, `bat`, `led`, `terms`, `gated`,
    `hot`, `emb`, `stack`, `merge` of `clKF` at `yKF` · `first` (what is claimed before the chain's
    first round gives what the row closes).
  `Plan4F.k04LawAt_firstGroup`: `K04LawAt L Sm Lt part par bk pc`, at every block bk, at any type Cl
    of claims, from `MeetsF`, profile 3, pc.ds = dsFirst par, pc.back = [], the piece's errors bear
    the carried ones, and `PaysF`.

Limits. K04_law IS NOT PROVED BY THIS: `Plan4F.PaysF`' TWELVE FIELDS ARE UNPAID, and so are
`MeetsF` at a real plan, a `Plan4F` at a real plan, the equation on pc.ds and the errors; nothing
shows that they can be met together. «There are seven states
and targets at which `TailH.Claims` holds» holds no content: it
is proved outright (`Plan4F.claimsAtF_exist`, CloseYesFirst.lean). THAT THE CHAIN's VALUE SPEAKS OF
K4's OWN RECORDS (the targets are the records') IS THEREFORE ASKED BY NO FIELD BY NAME: it lies
inside the nine parts and `pending`, which are said of `eKF`, the chain's value itself: WHOEVER PAYS
THESE OWES `TailH.Claims` AT THE RECORDS' OWN TARGETS. A DEBT THAT THE FIRST GROUP ALONE
HAS, AND NO FIELD NAMES: THE TOKENS: the chain reads `Q.tok (fa a).1`, K4's hearing reads
`L.tokv a.1`; fa and Q.tok are letters, and nothing here ties them: it lies inside `pending`,
`merge` and `first`. zt (meant for the tail of the lookup's point) is a letter. Behind `K04LawAt`
stands the pin (K04Plain.lean's `k04_of_at`). Those of K04At.lean (which stands over K04Plain.lean),
CarriageFirst.lean, Cb/Pv/Lay/At/OwnFirstW.lean (among them: a token that is not below the
vocabulary's size) and Cb/Pv/Lay/End/LayFirst.lean. The first group.
-/
import Johnson.Road.K4.K04At
import Johnson.Road.K4.CloseYesFirst
import Johnson.Road.K4.CarriagePartsFirst
import Johnson.Road.K4.LateNamesFirst
import Johnson.Road.K4.PlanClauses

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop TWhole Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Aff)
open OnBytes.Desc.First.K4 (Par Seat)
open OnBytes.Desc.First.P1 (TailNums)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Front Behind K04LawAt)
open Inst.Model (Scl)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {Q : Plan4F Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The room for the late entries' names at a place of the first group. -/
noncomputable def roomKF (Q : Plan4F Cb.Gl.E Mm X) (par : Par) (hS : OnBytes.Model.Layer.Shape) :
    ℕ :=
  roomF Q.fullF.D (hS.d / par.P.y.S2) par.P.y.ls Q.fullF.nb

/-- What the first chain puts out on the maps' image of a transcript. -/
noncomputable def Plan4F.eKF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : ExtSpec) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (z : X × Ex.Str) (τ : Tr (uLT (ckP .two) pc.ds)) : (tailW Q.fullF).s7.Nx :=
  ((chFF Q.fullF).val Ex z ((Plan4F.mapsAtF A N Ex hds).view τ)).1

/-- The library's ledger of the first group, part by part, off a last statement, at the letters
fixed here. -/
noncomputable def Plan4F.clKF (Q : Plan4F Cb.Gl.E Mm X) (par : Par)
    (hS : OnBytes.Model.Layer.Shape) (zt : (tailW Q.fullF).s7.Nx → ℕ → Cb.Gl.E)
    (e : (tailW Q.fullF).s7.Nx) :=
  clFirst Q.fullF (lateF (roomKF Q par hS)) (fun x => Sum.inl (Sum.inl x))
    (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr
    (noRest2 Q.fullF) zt (par.P.y.lPd - par.P.y.ls) (hS.d / par.P.y.S2) par.P.y.ls e

/-- The entries at which the parts are asked. -/
noncomputable def Plan4F.yKF (Q : Plan4F Cb.Gl.E Mm X) (par : Par)
    (hS : OnBytes.Model.Layer.Shape) (zt : (tailW Q.fullF).s7.Nx → ℕ → Cb.Gl.E)
    (e : (tailW Q.fullF).s7.Nx) (m : Mm) : Q.fullF.J ⊕ J4 (roomKF Q par hS) → Cb.Gl.E :=
  Sum.elim (Q.fullF.msg m) (lateAtF Q.fullF (lateF (roomKF Q par hS))
    (fmOfF Q.fullF zt (par.P.y.lPd - par.P.y.ls) par.P.y.ls par.P.y.ls) e m)

/-- **The premises that stay.** -/
structure Plan4F.PaysF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (L : Seat T) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsFirst par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (on on' : T × Fr.E.Str → Prop)
    (Front Behind : T × Fr.E.Str → Wt → Prop)
    (zt : (tailW Q.fullF).s7.Nx → ℕ → Cb.Gl.E) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, on a → Yes L par pc a τ fo o G → on' (behindOf L pc a τ o G)
  /-- what the row opens gives the first group's pending row on the committed weights -/
  pending : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G →
    Behind (behindOf L pc a τ o G) w →
    PendF Q.fullF (Plan4F.eKF A N Ex hds (fa a) τ) (part w)
  /-- what the row opens gives each of the nine parts of the library's ledger -/
  sq : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ)).sq
      (Q.yKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ) (part w))
  bat : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ)).bat
      (Q.yKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ) (part w))
  led : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ)).led
      (Q.yKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ) (part w))
  terms : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ)).terms
      (Q.yKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ) (part w))
  gated : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ)).gated
      (Q.yKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ) (part w))
  hot : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ)).hot
      (Q.yKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ) (part w))
  emb : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ)).emb
      (Q.yKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ) (part w))
  stack : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ)).stack
      (Q.yKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ) (part w))
  merge : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ)).merge
      (Q.yKF par hS zt (Plan4F.eKF A N Ex hds (fa a) τ) (part w))
  /-- with what the row opens, what is claimed before the chain's first round gives what the row
  closes -/
  first : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Q.fullF.ownF.pT (fa a).1 (part w) → Front a w

/-- **`K04LawAt` at the first group, from the premises that stay**, at every block bk (the statement
asks of bk that it hears as K4's own at the seat L). -/
theorem Plan4F.k04LawAt_firstGroup (A : Q.MeetsF par hS pcl) (hp3 : hS.p3 = true)
    (N : TailNums Q.fullF.ownF.toOwn.tail) (L : Seat T) (Sm : Sem Wt) (Lt : Letters T Wt Fr)
    (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsFirst par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (zt : (tailW Q.fullF).s7.Nx → ℕ → Cb.Gl.E) (hback : pc.back = [])
    (herr : Err.le ((Plan4F.mapsAtF A N Ex hds).err ((chFF Q.fullF).eps Ex)) pc.err)
    (H : Plan4F.PaysF A N L Ex pc hds fa part Lt.on Lt.on' (Front Lt) (Behind L Sm Lt par) zt) :
    K04LawAt L Sm Lt part par bk pc :=
  have hn := norms_sizes A.hy A.Z
  have hg := gated_sizes A.hy hp3 A.Z
  k04LawAt_first Q L Sm Lt Ex par bk pc part hback (Plan4F.mapsAtF_ok A N Ex hds) herr
    (normsOkF_of Q.fullF zt _ _ _ par.P.y.ls hn.1 hn.2.1 hn.2.2.1)
    (termsOkF_of Q.fullF zt (par.P.y.lPd - par.P.y.ls) par.P.y.ls (hS.d / par.P.y.S2) par.P.y.ls)
    (gatedOkF_of Q.fullF zt (par.P.y.lPd - par.P.y.ls) par.P.y.ls (hS.d / par.P.y.S2) par.P.y.ls
      hg.1 hg.2.1 hg.2.2.1 hg.2.2.2)
    (embOkF_of Q.fullF zt (par.P.y.lPd - par.P.y.ls) par.P.y.ls (hS.d / par.P.y.S2) par.P.y.ls)
    { kept := H.kept
      coin := fun a τ _ _ _ _ hy => Plan4F.coin_yesF A N Ex L hds a τ hy (fa a)
      pending := H.pending
      ledger := fun a τ fo o G w ha hy hB =>
        ledgerF_of_parts Q.fullF _ zt _ _ _ _ (part w) (H.sq a τ fo o G w ha hy hB)
          (H.bat a τ fo o G w ha hy hB) (H.led a τ fo o G w ha hy hB)
          (H.terms a τ fo o G w ha hy hB) (H.gated a τ fo o G w ha hy hB)
          (H.hot a τ fo o G w ha hy hB) (H.emb a τ fo o G w ha hy hB)
          (H.stack a τ fo o G w ha hy hB) (H.merge a τ fo o G w ha hy hB)
      first := H.first }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.k04LawAt_firstGroup
