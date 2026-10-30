-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseKFirst.lean: `K04LawAt` (Johnson/Desc/Plain/K04Plain.lean) AT THE FIRST GROUP,
AT THE FIRST GROUP's VALUE WITH ITS SLOTS AND ORDERS LAID (`Plan4LF.planF`, ValueSlotsFirst.lean),
WITH WHAT THE FILES OF THIS FOLDER CONCLUDE LAID IN. Of the twelve fields of `Plan4F.PaysF`
(CloseFirst.lean) ten are concluded here from the records below: `pending`, eight of the nine parts
(sq bat led terms gated hot stack merge), and `first`; kept and emb are handed through: `OwesF.emb`
is the same sentence as `PaysF.emb` (the part emb is the ledger of that one claim). The twin of
Johnson/Road/K4/CloseK.lean and CloseK2.lean in one. Two records, a definition and three theorems.
Glue: no new argument, no draw, no count.

  `Plan4F.zt_eKF`: the lookup's point in the first chain's last statement is the one that the first
    statement holds.
  `rider_of_hotF`: from the part hot of `clFirst` at `yLF`: for each routed layer the extension over
    the positions of "the sum of the selector's entries less 1" vanishes at the letter zt.
  `Plan4LF.ReadsAtF`: matrices Mt whose reads are true in the world of every ledger later than the
    one that the hearing returned, and whose cells are the message's.
  `Plan4LF.LettersAreF`: WHAT THE STATEMENT's LETTERS MUST MEAN FOR THIS ROAD: SEVEN LINES, those of
    `Plan4L.LettersAre` (CloseK.lean) at these letters, BUT ONE: idn: the 17 identities AND (J11) AT
    THE TOKENS `QF.tok (fa a).1` (`Plan4F.J11`, ValueSaysFirst.lean) give idn.
  `Plan4LF.OwesF`: WHAT IS STILL OWED: TEN FIELDS: the nine of `Plan4L.Owes2` (CloseK2.lean) at
    these letters (kept · seat · ns · lines · ties · rope · reads · planes · wo, the last at
    `LedG`, `TgRecF` and `WoSaysF`), and emb: THE LIBRARY's CLAIM ON THE STREAM THAT COMES IN IS
    WORTH 0.
  `Plan4LF.k04LawAt_KF`: `K04LawAt L Sm Lt part par bk pc` at every block bk and every type of
    claims, from `MeetsF`, pc.ds = dsFirst par, pc.back = [], the errors' premise, C, hk, `ValueIs`,
    `ValueMoreF`, `LettersAreF`, `FrontIs` and `OwesF`.

The promise in front is asked by the later groups' own record `Plan4L.FrontIs` (CloseK2.lean), and
the choices of the value's letters by `Plan4L.ValueIs` (CloseSevenK.lean), both at the letters that
the value shares with a later group's (QF.toPlan4L): neither is typed for one kind of group:
`FrontIs` reads no group; `ValueIs` reads the place's own par.g (in nI, scl and L0), and its field
nI counts one weight claim fewer where that group is the first.

Limits. K04_law IS NOT PROVED BY THIS: EVERY FIELD OF `OwesF`, EVERY LINE OF `LettersAreF` AND OF
`FrontIs` IS UNPAID HERE, and so are `MeetsF` at a real plan, a `Plan4LF` with `ValueIs` and
`ValueMoreF` at a real plan, the equation on pc.ds, pc.back = [], the errors, C and hk. THE ERRORS'
PREMISE IS NOT CONCLUDED AT THE CAP HERE: `Plan4F.herr_capF` (CapFromMeetsFirst.lean) concludes it,
and CloseCapFirst.lean lays it in.
THE TOKENS: THE CHAIN READS `QF.tok (fa a).1`, K4's HEARING READS `L.tokv a.1`: NOTHING HERE TIES
THE TWO: no proof in this file needs the tie; it lies inside the field wo (the row weights read the
typed state's tok), and in what the line idn is worth. The field emb reads no token.
ValueSeatFirst.lean makes the tie by definition.
THE VOCABULARY's SIZE: K4's hearing bounds the tokens by par.P.V and lays a table of that length
(`ClaimEnv.claimE`, OnBytes/Model/LayerPanels.lean; called at OnBytes/Desc/First/K4/Hear.lean:189);
the chain's embedding `embR` has D.P.V rows. `PubLines.Zw` gives s.V = D.P.V for the weights' shape
s; par.P.V IS TIED TO NEITHER BY ANY PREMISE HERE. A later group never reads P.V. It makes nothing
here false: like the tokens' tie it lies inside the field wo; it is a public number of the plan,
owed by whoever pays wo at a real plan.
`OwesF.lines` holds hfl for all eight calls: by LayerEnds34.lean's head that fails at the small
shipped example. The lines of `LettersAreF` bound the five letters of `Front` from above alone: at
letters that are always true they hold for nothing. THAT THE PIECE IN FRONT OF K4's IS THE LOOKUP's
is said by nobody's theorem. The letters `Sem`, `Letters`, part, fa, Ex, nu, first, h3, Q3 are not
filled in this file: CloseFillFirst.lean lays `Letters` (`Plan4KF.lettersOfF`) and CloseFill.lean
`Sem` and nu (`Plan4K.semOf`, `nuOf`) from the others, which they do not fill. NOTHING SHOWS THAT
ALL CAN BE MET TOGETHER. Behind `K04LawAt` stands the pin. The first group alone.
-/
import Johnson.Road.K4.CloseNineFirst
import Johnson.Road.K4.CloseK2
import Johnson.Road.K4.HeadsLedFirst
import Johnson.Road.K4.ValueSaysFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2 Level Tsc)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par Seat k0)
open OnBytes.Desc.First.P1 (gl aS7 Tg7 NzT tailT addsOf)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Front Behind AllZero frontRun K04LawAt)
open VerifiableInference.OnPublicFiles (K3Stands K3OutPlanes K4ReadsTrue K3LeftAt)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW d10 lDd)

section Small
variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The lookup's point rides through the first chain unturned**: under `ClaimsAtF` at a7, the
point in the batched sumcheck's state, in the chain's last statement, is the one that the first
statement holds. -/
theorem Plan4F.zt_eKF {Q : Plan4F Cb.Gl.E Mm X} (A : Q.MeetsF par hS pcl)
    (N : OnBytes.Desc.First.P1.TailNums Q.fullF.ownF.toOwn.tail) (Ex : ExtSpec) (tk : Array Nat)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (τ : Tr (uLT (ckP .two) pc.ds)) (z : X × Ex.Str)
    (a7 : OnBytes.Desc.First.P1.Adds7 Q.fullF.ownF.toOwn.tail)
    (hc : Plan4F.ClaimsAtF A N tk hds τ z.1 a7) :
    ztSF Q.fullF (Plan4F.eKF A N Ex hds z τ) =
      Inst.Model.FFSeg.zpos Q.fullF.D (Q.fullF.zOf z.1) := by
  have he : Plan4F.eKF A N Ex hds z τ = _ := Plan4F.val_of_claimsF A N Ex tk hds τ z a7 hc
  have e := congrArg (fun p : Cb.Gl.E × Q.fullF.ip.St => p.2.z) hc.c4
  unfold ztSF
  rw [he]
  exact congrArg (Inst.Model.FFSeg.zpos Q.fullF.D) e.symm

variable {K : Type} [Field K] [Fintype K] {M X0 : Type} (P : FullFPar K M X0)
  (zt : (tailW P).s7.Nx → ℕ → K) (b B sG : ℕ)

/-- From the part hot of the first group's ledger at `yLF`, under the norms' three clauses on
sizes. -/
theorem rider_of_hotF (nl : lDd P.D = b + sG) (nd : P.D.d = B * 2 ^ sG) (nB : B ≤ 2 ^ b)
    (R : (tailW P).s7.Nx → Rest2 K (P.J ⊕ J4 (roomF P.D B sG P.nb))) (e : (tailW P).s7.Nx)
    (m : M)
    (h : Ledger.Holds (clFirst P (lateF (roomF P.D B sG P.nb)) (fun x => Sum.inl (Sum.inl x))
      (fun x => Sum.inl (Sum.inr (Sum.inl x))) (fun x => Sum.inl (Sum.inr (Sum.inr x))) Sum.inr R
      zt b B sG e).hot (yLF P zt b B sG e m)) :
    ∀ l, l < P.D.ne → Blocks.ext P.D.lT (d10 P.D (P.rd (P.msg m)) l) (zt e) = 0 :=
  hot_last (namesAt P.ofp.nr (readsAt (lateF (roomF P.D B sG P.nb)) fun x => Sum.inl (Sum.inl x)))
    (eAtF P.ofp P.wfPart e (zt e)) P.D (P.rd (P.msg m)) (yLF P zt b B sG e m)
    (late_normsF P zt b B sG nl nd nB e m).sel ((ledOf_holds _ _).1 h)

end Small

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QF : Plan4LF Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The matrices' reads are true, and their cells are the message's**: in the world of every
ledger later than the one that the hearing returned, at the statement's masks and entries. -/
def Plan4LF.ReadsAtF (QF : Plan4LF Cb.Gl.E Mm X) (par : Par) (hS : OnBytes.Model.Layer.Shape)
    (L : Seat T) (Sm : Sem Wt) (part : Wt → Mm) (s : T) (fo : Forest.Heard) (o : Own) (G : Fork)
    (w : Wt) (Mt : Mats Cb.Gl.E) : Prop :=
  (∀ (Xp : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
    PubAt Xp { par.P with tokv := L.tokv s } par.hp fo o G2 t4 QF.planF.fullF.D QF.planF.fullF.tb
      hS →
    ∀ Fl, Fo.Later G Fl → Xp.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt) ∧
  cellsOf QF.planF.fullF.D (cellsAt par.P.y Mt) =
    QF.planF.fullF.rd (QF.planF.fullF.msg (part w))

/-- **What the statement's letters must mean for this road, in the first group.** -/
structure Plan4LF.LettersAreF (A : QF.planF.MeetsF par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst par) (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (nu : Wt → _root_.Fo.Pl → Cb.Gl.E) (first : ℕ) : Prop where
  mask : ∀ w, Sm.mask w = QF.planF.maskAt (part w)
  maskNu : ∀ w j, Sm.mask w j = nu w (_root_.Fo.Pl.mask j)
  ctx : ∀ a τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
    Lt.ctx (behindOf L pc a τ o G) w → Lt.ctx a w
  /-- the 17 identities and (J11), at the tokens that the value reads off the first statement -/
  idn : ∀ a w, Lt.on a → QF.planF.toPlan4.Idn (part w) → QF.planF.J11 (fa a).1 (part w) →
    Lt.idn a w
  keys : ∀ a w fo, Lt.on a → L.look a.1 = some fo → QF.planF.fullF.zOf (fa a).1 = zAt fo →
    QF.planF.fullF.kTg (fa a).1 = kTgAt fo (L.fork a.1) →
    (∀ s, QF.planF.kIncS (fa a).1 s = kIncAt fo (L.fork a.1) s) →
    QF.planF.toPlan4.Keys (fa a).1 (part w) → Lt.worthKeys a w
  planes : ∀ a w fo, Lt.on a → L.look a.1 = some fo →
    K3Stands fo.shape par.P.y.h.lmb first gl fo (L.fork a.1) →
    K3OutPlanes fo.shape par.P.y.h.lmb first (nu w) gl fo (L.fork a.1) → Lt.worthPlanes a w
  rider : ∀ a w fo, Lt.on a → L.look a.1 = some fo →
    (∀ l, l < QF.planF.fullF.D.ne → Blocks.ext QF.planF.fullF.D.lT
      (d10 QF.planF.fullF.D (QF.planF.fullF.rd (QF.planF.fullF.msg (part w))) l)
      (Inst.Model.FFSeg.zpos QF.planF.fullF.D (zAt fo)) = 0) →
    Lt.worthRider a w

/-- **What is still owed, in the first group.** -/
structure Plan4LF.OwesF (A : QF.planF.MeetsF par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst par) (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (nu : Wt → _root_.Fo.Pl → Cb.Gl.E) (s : WsShape) (lk : ℕ)
    (s0 : OnBytes.Model.Forest.Shape) (tl : HTailF2) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G → Lt.on' (behindOf L pc a τ o G)
  /-- the seat's two laws -/
  seat : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G → SeatOk L a.1
  /-- the ledger's number of slots against the value's -/
  ns : ∀ a, Lt.on a → (L.fork a.1).ns ≤ QF.ns + 1
  /-- the plan's public lines -/
  lines : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QF.planF.fullF.D
    QF.planF.fullF.tb s lk s0 tl
  /-- the value's three letters at the first statement are the lookup's return's -/
  ties : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G →
    QF.planF.fullF.zOf (fa a).1 = zAt fo ∧
      QF.planF.fullF.kTg (fa a).1 = kTgAt fo (L.fork a.1) ∧
      ∀ s, QF.planF.kIncS (fa a).1 s = kIncAt fo (L.fork a.1) s
  /-- the rotary tables' fit at what was heard -/
  rope : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G →
    ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QF.planF.fullF.D QF.planF.fullF.tb (par.g * par.P.y.Lam) lam
  /-- matrices whose reads are true, and whose cells are the message's -/
  reads : ∀ a τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
    Behind L Sm Lt par (behindOf L pc a τ o G) w →
    ∃ Mt : Mats Cb.Gl.E, Plan4LF.ReadsAtF QF par hS L Sm part a.1 fo o G w Mt
  /-- the three planes' tables' reads are true in the world of the ledger behind the first run -/
  planes : ∀ a τ fo o G w fs₁ F₁, Lt.on a → Yes L par pc a τ fo o G →
    Behind L Sm Lt par (behindOf L pc a τ o G) w → frontRun par o G = some (fs₁, F₁) →
    K4ReadsTrue gl o.v fo F₁ (nu w) (Sm.entryT o w)
  /-- what the row opens on the committed weights gives the first group's pending row at the merge's
  record, its row weights at the typed state of the seventh stage, at the hearing's own ledgers and
  records and at targets that are these records' -/
  wo : ∀ a τ fo o G w (g7 : Tg7) H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5, Lt.on a →
    Yes L par pc a τ fo o G →
    LedG { par.P with tokv := L.tokv a.1 } par.hp par.g fo o (L.fork a.1) G (tapeAt par pc τ) []
      H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5 →
    TgRecF g7 { par.P with tokv := L.tokv a.1 } par.hp par.g o (tapeAt par pc τ) H1 tT F4 G2 G3
      G3' →
    Lt.wo (behindOf L pc a τ o G) w →
    WoSaysF QF.planF.fullF
      (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
        (ksOf { par.P with tokv := L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
        (Plan4F.nzAtF A (L.tokv a.1) hds τ _) (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).1.1
      (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
        (ksOf { par.P with tokv := L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
        (Plan4F.nzAtF A (L.tokv a.1) hds τ _) (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).2
      o.wo (part w)
  /-- the library's claim on the stream that comes in is worth 0 -/
  emb : ∀ a τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
    Behind L Sm Lt par (behindOf L pc a τ o G) w →
    Blocks.Form.val (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))
      (embClaim (lateF (roomKF QF.planF par hS)) Sum.inr
        (((tailW QF.planF.fullF).y7 (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).1.2
          (0 : Fin 1))
        QF.planF.fullF.mkE QF.planF.fullF.nb QF.planF.fullF.gB
        (stF QF.planF.fullF (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).pb) = 0

/-- **`K04LawAt` at the first group**, from `MeetsF`, the piece's rounds and back, the errors'
premise, C, hk, `ValueIs`, `ValueMoreF`, `LettersAreF`, `FrontIs` and `OwesF`. -/
theorem Plan4LF.k04LawAt_KF (A : QF.planF.MeetsF par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsFirst par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (hback : pc.back = [])
    (herr : Err.le ((Plan4F.mapsAtF A (numsKF QF.planF.fullF) Ex hds).err
      ((chFF QF.planF.fullF).eps Ex)) pc.err)
    (C : QF.planF.D.ChOK)
    (hk : ∀ l, l < QF.planF.D.nl → (QF.planF.D.Pl l).kq = (QF.planF.D.Pl l).kk ∨
      (16 ≤ (QF.planF.D.Pl l).kq ∧ 16 ≤ (QF.planF.D.Pl l).kk))
    (V : Plan4L.ValueIs QF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QF)
    (lw : ℕ → LW Cb.Gl.E) {s : WsShape} {lk : ℕ} {s0 h3 : OnBytes.Model.Forest.Shape}
    {tl : HTailF2} {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ} {Q3 : Fork → Prop}
    (M : Plan4LF.LettersAreF A L Sm Lt Ex pc hds fa part nu first)
    (N : Plan4L.FrontIs QF.toPlan4L par L Lt first s0 h3 Q3)
    (O : Plan4LF.OwesF A L Sm Lt Ex pc hds fa part nu s lk s0 tl) :
    K04LawAt L Sm Lt part par bk pc := by
  have fr := fun (a : T × Fr.E.Str) (ha : Lt.on a) =>
    front_of_leftAt L (N.on a ha) (Pp := { par.P with tokv := L.tokv a.1 }) N.fo N.pub N.ok
  have nx : ∀ a, Lt.on a → QF.n0 = (L.fork a.1).next := fun a ha => by
    rw [(fr a ha).2.1]
    exact N.n0
  have nine : ∀ (a : T × Fr.E.Str) τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
      Behind L Sm Lt par (behindOf L pc a τ o G) w →
      Plan4LF.EightAt A Ex hds fa part a τ w ∧
        Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
            (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).merge
          (QF.planF.yKF par hS (ztSF QF.planF.fullF)
            (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) := by
    intro a τ fo o G w ha Y hB
    obtain ⟨K, hfil, he, hsl, _⟩ := (fr a ha).2.2 fo Y.look
    obtain ⟨hz0, hk0, hkS⟩ := O.ties a τ fo o G ha Y
    obtain ⟨Mt, hR, hcells⟩ := O.reads a τ fo o G w ha Y hB
    exact Plan4LF.nine_at A L Sm Lt Ex hds fa part a τ Y w hB (O.seat a τ fo o G ha Y) (fr a ha).1
      (O.lines (L.tokv a.1)) K (O.rope a τ fo o G ha Y) lw hz0 hk0 hkS hfil he
      (fun y hy => Nat.lt_of_lt_of_le (hsl y hy) (O.ns a ha)) Mt hR hcells V V2 (nx a ha)
      (M.mask w) (O.emb a τ fo o G w ha Y hB)
  have hp3 : hS.p3 = true := by
    rw [← (laySizes_of_layout A.hy).shape]
    exact (covers_shape A.hc).2.1
  have hn := norms_sizes A.hy A.Z
  refine Plan4F.k04LawAt_firstGroup A hp3 (numsKF QF.planF.fullF) L Sm Lt Ex bk pc hds fa part
    (ztSF QF.planF.fullF) hback herr
    { kept := O.kept
      pending := fun a τ fo o G w ha Y hB => ?_
      sq := fun a τ fo o G w ha Y hB => (nine a τ fo o G w ha Y hB).1.1
      bat := fun a τ fo o G w ha Y hB => (nine a τ fo o G w ha Y hB).1.2.1
      led := fun a τ fo o G w ha Y hB => (nine a τ fo o G w ha Y hB).1.2.2.1
      terms := fun a τ fo o G w ha Y hB => (nine a τ fo o G w ha Y hB).1.2.2.2.1
      gated := fun a τ fo o G w ha Y hB => (nine a τ fo o G w ha Y hB).1.2.2.2.2.1
      hot := fun a τ fo o G w ha Y hB => (nine a τ fo o G w ha Y hB).1.2.2.2.2.2.1
      emb := fun a τ fo o G w ha Y hB => (nine a τ fo o G w ha Y hB).1.2.2.2.2.2.2.2
      stack := fun a τ fo o G w ha Y hB => (nine a τ fo o G w ha Y hB).1.2.2.2.2.2.2.1
      merge := fun a τ fo o G w ha Y hB => (nine a τ fo o G w ha Y hB).2
      first := fun a τ fo o G w ha Y hB hp => ?_ }
  · obtain ⟨K, hfil, _⟩ := (fr a ha).2.2 fo Y.look
    obtain ⟨hz0, hk0, _⟩ := O.ties a τ fo o G ha Y
    obtain ⟨hinv, hscl, hvy, _, _, _⟩ :=
      Plan4LF.heard_KF A Y.hears (fr a ha).1 (small_of_all _ _ _ Y.small) V.scl V.L0
    have B := O.lines (L.tokv a.1)
    obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, g7, Ld, I, hc⟩ :=
      Plan4F.atYesF A (numsKF QF.planF.fullF) L hds a τ Y (fa a).1 (fr a ha).1 B.S B.hs B.hg B.hrd
        B.hmats B.hρ B.hc B.hN B.hfl K.hsx K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL B.hlw B.h4
        (O.rope a τ fo o G ha Y) B.htm B.hNM B.hpad hinv hscl hvy (A.lamM (L.tokv a.1)) gl_half
        (nums4_num4K QF.planF.fullF.toFullPar) lw hz0 hk0 hfil
    have he : Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ = _ :=
      Plan4F.val_of_claimsF A (numsKF QF.planF.fullF) Ex (L.tokv a.1) hds τ (fa a) _ hc
    have hw := O.wo a τ fo o G w g7 H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5 ha Y Ld I hB.2.2
    -- the tape behind three single drops is the tape on which the lower files speak
    have key : ∀ (t' : Tape), (tapeAt par pc τ).drop (k0 par.g) = t' →
        ∀ nz : NzT QF.planF.fullF.ownF.toOwn.tail
          (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t',
        Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ =
          (tailT (Plan4F.tailMKF A (numsKF QF.planF.fullF))
            (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
            (addsOf (Plan4F.tailMKF A (numsKF QF.planF.fullF))
              (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
              (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7)).z7
            (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) →
        WoSaysF QF.planF.fullF
          (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
            (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
            (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).1.1
          (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
            (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
            (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).2
          o.wo (part w) →
        PendF QF.planF.fullF (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w) := by
      intro t' e nz he' hw'
      subst e
      rw [he']
      exact ((pendingF_of_led QF.planF.fullF (Plan4F.tailMKF A (numsKF QF.planF.fullF)) Ld rfl nz
        (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7 I.t7
        (fits7F QF.planF.fullF _ _ (outTies_KF A (L.tokv a.1) Ld.c4).k7) rfl (part w)).2 hw').1
    exact key _ (tb3_eq _ A.hg) _ he hw
  · obtain ⟨hc, ⟨fs₁, F₁, _, _, h1, _, z1, _⟩, _⟩ :=
      forms_of_behind L Sm Lt par pc a τ o G w (O.seat a τ fo o G ha Y) hB
    have hT := O.planes a τ fo o G w fs₁ F₁ ha Y hB h1
    have hok := ((fr a ha).2.2 fo Y.look).2.2.2.2
    obtain ⟨_, _, hvy, _, _, _⟩ :=
      Plan4LF.heard_KF A Y.hears (fr a ha).1 (small_of_all _ _ _ Y.small) V.scl V.L0
    have hm : Sm.mask w = fun j => nu w (_root_.Fo.Pl.mask j) := funext (M.maskNu w)
    have hpl := planes_of_yes (P := { par.P with tokv := L.tokv a.1 }) gl (fr a ha).1 Y.hears h1
      first (nu w) (Sm.entryT o w) hok
      (fun f hf => by
        have q := (z1 f hf).2
        rw [hm] at q
        exact q) hT
    rw [hvy] at hpl
    have hst : K3Stands fo.shape par.P.y.h.lmb first gl fo (L.fork a.1) := by
      obtain ⟨F, F', g, rs, _, hf, Lf, hg, hF'⟩ := N.on a ha
      have eg : g = fo := Option.some.inj (hg.symm.trans Y.look)
      have eF : L.fork a.1 = F' := Option.some.inj hF'
      subst eg
      rw [eF, Lf.shape, ← hf]
      exact ⟨rs, Lf.heardIs⟩
    obtain ⟨hI, hK, hJ⟩ := (QF.planF.pTF_iff C hk (fa a).1 (part w)).1 hp
    obtain ⟨hz0, hk0, hkI⟩ := O.ties a τ fo o G ha Y
    obtain ⟨a7, hc7⟩ := Plan4F.claimsAtF_exist A (numsKF QF.planF.fullF) (L.tokv a.1) hds τ (fa a).1
    have hzt := Plan4F.zt_eKF A (numsKF QF.planF.fullF) Ex (L.tokv a.1) hds τ (fa a) a7 hc7
    have hr := rider_of_hotF QF.planF.fullF (ztSF QF.planF.fullF) (par.P.y.lPd - par.P.y.ls)
      (hS.d / par.P.y.S2) par.P.y.ls hn.1 hn.2.1 hn.2.2.1 (noRest2 QF.planF.fullF) _ (part w)
      (nine a τ fo o G w ha Y hB).1.2.2.2.2.2.1
    rw [hzt, hz0] at hr
    exact ⟨M.ctx a τ fo o G w ha Y hc, M.idn a w ha hI hJ,
      M.planes a w fo ha Y.look hst hpl,
      M.keys a w fo ha Y.look hz0 hk0 hkI hK, M.rider a w fo ha Y.look hr⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.zt_eKF
#print axioms OnBytes.Road.K4.rider_of_hotF
#print axioms OnBytes.Road.K4.Plan4LF.k04LawAt_KF
