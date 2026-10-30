-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseLater.lean: `K04LawAt` AT A GROUP THAT IS NOT THE FIRST, WITH THE CARRIAGE's
LETTERS FIXED AND WHAT IS PROVED ELSEWHERE LAID IN: the maps, the late entries' names and forms, the
three records on names, forms and sizes, and the field `coin` are no premises any more. («There are
states and targets with `TailH.Claims`» is no field of the record: that sentence holds with no
premise, `claims_exist`, OnBytes/Desc/First/P1/ClaimsFree.lean, and is spent here for `coin`; that
the targets are K4's own records' is another file's: ClaimsYes.lean's `AtYes`.) Five
definitions, a record of the premises that stay, and one theorem. Glue: no new argument, no count.

FIXED HERE, at a place par whose plan meets the value (`Plan4.Meets`,
  Johnson/Road/K4/PlanMaps.lean): the maps := `Plan4.mapsAt` (CloseYes.lean); the late entries,
  their names and forms := `lateOf`, `fmOf` (LateNames.lean) at b := lPd - ls, s := sG := ls, B := d
  / S2 of the place's layout; the three parts of the ledger that are letters in the library := empty
  (`noRest3`, CarriageParts.lean).
  `Plan4.eK`: what the chain puts out on the maps' image of a transcript.
  `Plan4.clK`: the library's ledger, part by part, off a last statement, at these letters.
  `Plan4.yK`: the entries at which its parts are asked: the messages', and each late entry at its
    form's value.

  `Plan4.Pays`: THE PREMISES THAT STAY, each at every `Yes` of K4's block: `kept` (the promise
    behind) · and, from what the row opens: `pending` (the pending row on the committed
    weights) · the eight parts `sq`, `bat`, `led`, `terms`, `gated`, `hot`, `stack`, `merge` of
    `clK` at `yK` · `first` (what is claimed before the chain's first round gives what the row
    closes).
  `ztK`: the tail of the lookup's point off a last statement: what zt is meant to be.
  `Plan4.k04LawAt_later`: `K04LawAt L Sm Lt part par bk pc`, at every block bk, from `Meets`,
    profile 3, pc.ds = dsLater par, pc.back = [], the piece's errors bear the carried ones, and
    `Pays`.

Limits. K04_law IS NOT PROVED BY THIS: `Plan4.Pays`' ELEVEN FIELDS ARE UNPAID, and so are `Meets`
at a real plan, a `Plan4` at a real plan, the equation on pc.ds and the errors; nothing shows that
they can be met together. zt (meant for the tail of the lookup's point) is a letter. Behind
`K04LawAt` stands the pin (K04Plain.lean's `k04_of_at`). A group that is not the first.

-/
import Johnson.Road.K4.K04At
import Johnson.Road.K4.CloseYes
import OnBytes.Desc.First.P1.ClaimsFree
import Johnson.Road.K4.CarriageParts
import Johnson.Road.K4.LateNames
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

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {Q : Plan4 Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The room for the late entries' names at a place. -/
noncomputable def roomK (Q : Plan4 Cb.Gl.E Mm X) (par : Par) (hS : OnBytes.Model.Layer.Shape) : ℕ :=
  roomFor Q.full.D (hS.d / par.P.y.S2) par.P.y.ls

/-- What the chain puts out on the maps' image of a transcript. -/
noncomputable def Plan4.eK (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : ExtSpec) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par)
    (z : X × Ex.Str) (τ : Tr (uLT (ckP .two) pc.ds)) : (tailF Q.full).s7.Nx :=
  ((chF Q.full).val Ex z ((Plan4.mapsAt A N Ex hds).view τ)).1

/-- The library's ledger, part by part, off a last statement, at the letters fixed here. -/
noncomputable def Plan4.clK (Q : Plan4 Cb.Gl.E Mm X) (par : Par) (hS : OnBytes.Model.Layer.Shape)
    (zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E) (e : (tailF Q.full).s7.Nx) :
    LayCl Cb.Gl.E (Q.full.J ⊕ J3 (roomK Q par hS)) :=
  clAt Q.full.toOwnPar Q.full.wPart (lateOf (roomK Q par hS)) Sum.inl
    (restAt Q.full (lateOf (roomK Q par hS)) (fun x => Sum.inr (Sum.inl x))
      (fun x => Sum.inr (Sum.inr x)) (noRest3 Q.full) par.P.y.ls)
    zt (par.P.y.lPd - par.P.y.ls) (hS.d / par.P.y.S2) e

/-- The entries at which the parts are asked. -/
noncomputable def Plan4.yK (Q : Plan4 Cb.Gl.E Mm X) (par : Par) (hS : OnBytes.Model.Layer.Shape)
    (zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E) (e : (tailF Q.full).s7.Nx) (m : Mm) :
    Q.full.J ⊕ J3 (roomK Q par hS) → Cb.Gl.E :=
  Sum.elim (Q.full.msg m) (lateAt Q.full (lateOf (roomK Q par hS))
    (fmOf Q.full zt (par.P.y.lPd - par.P.y.ls) par.P.y.ls par.P.y.ls) e m)

/-- **The premises that stay.** -/
structure Plan4.Pays (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail) (L : Seat T)
    (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsLater par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (on on' : T × Fr.E.Str → Prop)
    (Front Behind : T × Fr.E.Str → Wt → Prop)
    (zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, on a → Yes L par pc a τ fo o G → on' (behindOf L pc a τ o G)
  /-- what the row opens gives the pending row on the committed weights -/
  pending : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G →
    Behind (behindOf L pc a τ o G) w →
    OkMore Q.full (fun _ _ => True) (Plan4.eK A N Ex hds (fa a) τ) (part w)
  /-- what the row opens gives each of the eight parts of the library's ledger -/
  sq : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clK par hS zt (Plan4.eK A N Ex hds (fa a) τ)).sq
      (Q.yK par hS zt (Plan4.eK A N Ex hds (fa a) τ) (part w))
  bat : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clK par hS zt (Plan4.eK A N Ex hds (fa a) τ)).bat
      (Q.yK par hS zt (Plan4.eK A N Ex hds (fa a) τ) (part w))
  led : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clK par hS zt (Plan4.eK A N Ex hds (fa a) τ)).led
      (Q.yK par hS zt (Plan4.eK A N Ex hds (fa a) τ) (part w))
  terms : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clK par hS zt (Plan4.eK A N Ex hds (fa a) τ)).terms
      (Q.yK par hS zt (Plan4.eK A N Ex hds (fa a) τ) (part w))
  gated : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clK par hS zt (Plan4.eK A N Ex hds (fa a) τ)).gated
      (Q.yK par hS zt (Plan4.eK A N Ex hds (fa a) τ) (part w))
  hot : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clK par hS zt (Plan4.eK A N Ex hds (fa a) τ)).hot
      (Q.yK par hS zt (Plan4.eK A N Ex hds (fa a) τ) (part w))
  stack : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clK par hS zt (Plan4.eK A N Ex hds (fa a) τ)).stack
      (Q.yK par hS zt (Plan4.eK A N Ex hds (fa a) τ) (part w))
  merge : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (Q.clK par hS zt (Plan4.eK A N Ex hds (fa a) τ)).merge
      (Q.yK par hS zt (Plan4.eK A N Ex hds (fa a) τ) (part w))
  /-- with what the row opens, what is claimed before the chain's first round gives what the row
  closes -/
  first : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Q.full.own.pT (fa a).1 (part w) → Front a w

/-- **`K04LawAt` at a group that is not the first, from the premises that stay**, at every block bk
(the statement asks of bk that it hears as K4's own at the seat L). -/
theorem Plan4.k04LawAt_later (A : Q.Meets par hS pcl) (hp3 : hS.p3 = true)
    (N : TailNums Q.full.own.toOwn.tail) (L : Seat T) (Sm : Sem Wt) (Lt : Letters T Wt Fr)
    (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsLater par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E) (hback : pc.back = [])
    (herr : Err.le ((Plan4.mapsAt A N Ex hds).err ((chF Q.full).eps Ex)) pc.err)
    (H : Plan4.Pays A N L Ex pc hds fa part Lt.on Lt.on' (Front Lt) (Behind L Sm Lt par) zt) :
    K04LawAt L Sm Lt part par bk pc :=
  have hn := norms_sizes A.hy A.Z
  have hg := gated_sizes A.hy hp3 A.Z
  k04LawAt_of_ledger Q L Sm Lt Ex par bk pc part hback (Plan4.mapsAt_ok A N Ex hds) herr
    (normsOk_of Q.full zt _ _ _ par.P.y.ls hn.1 hn.2.1 hn.2.2.1)
    (termsOk_of Q.full zt (par.P.y.lPd - par.P.y.ls) par.P.y.ls (hS.d / par.P.y.S2) par.P.y.ls)
    (gatedOk_of Q.full zt (par.P.y.lPd - par.P.y.ls) par.P.y.ls (hS.d / par.P.y.S2) par.P.y.ls
      hg.1 hg.2.1 hg.2.2.1 hg.2.2.2)
    { kept := H.kept
      coin := fun a τ fo o G ha hy => by
        obtain ⟨a7, hc⟩ := OnBytes.Desc.First.P1.claims_exist (Plan4.tailMK A N)
          (ksOf { par.P with tokv := L.tokv a.1 } par.hp) ((tapeAt par pc τ).drop 1)
          (Plan4.nzAt A (L.tokv a.1) hds τ _) ((fa a).1, ptOf Q (tapeAt par pc τ))
        exact Plan4.coin_of_yes A N Ex L hds a τ hy (fa a) a7 hc
      pending := H.pending
      ledger := fun a τ fo o G w ha hy hB =>
        ledger_of_parts Q.full _ zt _ _ _ _ (part w) (H.sq a τ fo o G w ha hy hB)
          (H.bat a τ fo o G w ha hy hB) (H.led a τ fo o G w ha hy hB)
          (H.terms a τ fo o G w ha hy hB) (H.gated a τ fo o G w ha hy hB)
          (H.hot a τ fo o G w ha hy hB) (H.stack a τ fo o G w ha hy hB)
          (H.merge a τ fo o G w ha hy hB)
      first := H.first }

/-- The tail of the lookup's point, as the library has it, off a last statement: what the letter zt
is meant to be. -/
noncomputable def ztK (Q : Plan4 Cb.Gl.E Mm X) (e : (tailF Q.full).s7.Nx) : ℕ → Cb.Gl.E :=
  Inst.Model.FFSeg.zpos Q.full.D ((tailF Q.full).b4 e).2.st.z

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.k04LawAt_later
