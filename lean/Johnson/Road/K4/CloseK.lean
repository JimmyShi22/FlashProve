-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseK.lean: `K04LawAt` (Johnson/Desc/Plain/K04Plain.lean) AT A GROUP THAT IS NOT
THE FIRST, AT THE VALUE WITH ITS SLOTS AND ORDERS LAID (`Plan4L`), WITH WHAT THE FILES OF THIS
FOLDER CONCLUDE LAID IN. Of the eleven fields of `Plan4.Pays` (CloseLater.lean) nine are concluded
here: `pending`, the seven parts sq bat led terms gated hot stack, and `first`. Two records, a
definition and four theorems. Glue: no new argument, no count.

  `Plan4L.LettersAre`: WHAT THE STATEMENT's LETTERS MUST MEAN FOR THIS ROAD: SEVEN LINES. Two on the
  mask row: mask: the statement's mask row (`Sem.mask`) is the value's at part w · maskNu: it is the
  lookup's valuation nu w at the masks' places. Five implications between `Letters`' fields and
  sentences: ctx rides back from behind a yes to in front · the 17 identities give idn · the
  lookup's own sentence on the planes (`K3OutPlanes`, Johnson/Top/H/K3RowOut.lean, at the heard
  shape, the valuation nu w, the ledger in front) gives worthPlanes (where the seat finds what the
  lookup returned, and that record stands for some rounds at first: `K3Stands`) · the keys' one
  weighted sum gives worthKeys (where the seat finds what the lookup returned, and zOf, kTg, kIncS
  at the first statement are that return's) · «at the token part of the point that the lookup
  returned, every routed layer's selector sums to 1» gives worthRider (where the seat finds that
  return). The five bound the five letters of `Front` from above alone: at letters that are always
  true they hold for nothing: the record bears only at a filling.
  `Plan4L.Owes`: WHAT IS STILL OWED: THIRTEEN FIELDS: lines under no premise; sized and next under
  the promise in front; the other ten under that promise and at a `Yes`: kept · the seat's two laws
  · the ledger's sizes · its next free slot is the value's n0 (ONE number for every record under the
  promise: payable only if the plan fixes how many slots are taken in front of K4's block) · the
  plan's public lines · what the lookup left (its five clauses; zOf, kTg and kIncS at the first
  statement; the end form's slots filled) · the rotary tables' fit · matrices whose reads are true
  and whose cells are the message's (a line on the letters `Sem` and part, and the reads' own law) ·
  stands: the heard record stands for some rounds at the ends that begin at first (`K3Stands`) ·
  planes: the heard shape passes the lookup's test on numbers, and the three planes' tables' reads
  are true (`K4ReadsTrue`, Johnson/Top/H/K4PlanesWorth.lean) in the world of the ledger behind the
  first run · the five own rows · wo behind a yes gives `WoSays` at the merge's record, the row
  weights at the typed state of the seventh stage, at the hearing's own ledgers and records (`Led7`)
  and at targets that are these records' (`TgRec`) (that these weights are what the record spells is
  a debt on K4's own hearing) · the part merge.
  `Plan4L.k04LawAt_K`: `K04LawAt L Sm Lt part par bk pc` at every block bk and every type of claims,
  from `Plan4.Meets`, pc.ds = dsLater par, pc.back = [], the errors' premise, two public conditions
  of the library's join (C, hk), the choices of the value's letters (`ValueIs`, CloseSevenK.lean),
  `LettersAre` and `Owes`.
  `Plan4L.k04LawAt_cap`: the same at a piece whose errors are `Err.cap 128`: the errors' premise is
  concluded.
  `Plan4.zt_eK`: the lookup's point in the chain's last statement is the one that the first
  statement holds.
  `Plan4L.ReadsAt`: matrices Mt whose reads are true in the world of every ledger later than the one
  that the hearing returned, and whose cells are the message's.
  `Plan4L.seven_of_owes`: the seven parts (`SevenAt`, CloseSevenK.lean) from `Owes`.

Limits. K04_law IS NOT PROVED BY THIS: EVERY FIELD OF `Owes` AND OF `LettersAre` IS UNPAID HERE, and
so are `Meets` at a real plan, a `Plan4L` with `ValueIs` at a real plan, the equation on pc.ds,
pc.back = [], the errors (or that they are the cap), C and hk. `Owes.lines` holds hfl for all eight
calls: by LayerEnds34.lean's head that fails at the small shipped example: THE ROAD REACHES THE
FULL-SIZE KIND OF SHAPE ALONE. Of `LettersAre`'s lines ctx is a law at a yes, not a wording alone.
THE NUMBER first AND THE VALUATION nu ARE LETTERS OF THE CALLER, each ONE for every record under the
promise. `Owes.stands` says that at this first the heard record stands for some rounds, so that
`K3OutPlanes` is not empty there; that it stands at no other first is not said here. nu is tied by
`maskNu` at the masks' places and by `K4ReadsTrue` at the planes' cells. NOTHING SHOWS THAT THEY CAN
BE MET TOGETHER. The statement's letters (`Sem`, `Letters`) are not filled in this file:
CloseFill.lean lays them from further letters (`Plan4K.semOf`, `Plan4K.lettersOf`), which it does
not fill. Behind `K04LawAt` stands the pin. A group that is not the first.
-/
import Johnson.Road.K4.CloseSevenK
import Johnson.Road.K4.PendingLed
import Johnson.Road.K4.ValueSays
import Johnson.Road.K4.CapFromMeets
import Johnson.Road.K4.PlanesOfYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2 Level Tsc)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par Seat)
open OnBytes.Desc.First.P1 (gl aS7 Tg7)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Front Behind AllZero frontRun K04LawAt)
open VerifiableInference.OnPublicFiles (K3Stands K3OutPlanes K4ReadsTrue)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW d10)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QL : Plan4L Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The lookup's point rides through the chain unturned**: the point in the batched sumcheck's
state, in the chain's last statement, is the one that the first statement holds. -/
theorem Plan4.zt_eK {Q : Plan4 Cb.Gl.E Mm X} (A : Q.Meets par hS pcl)
    (N : OnBytes.Desc.First.P1.TailNums Q.full.own.toOwn.tail) (Ex : ExtSpec) (tk : Array Nat)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par)
    (τ : Tr (uLT (ckP .two) pc.ds)) (z : X × Ex.Str)
    (a7 : OnBytes.Desc.First.P1.Adds7 Q.full.own.toOwn.tail)
    (hc : Plan4.ClaimsAt A N tk hds τ z.1 a7) :
    ztS Q.full (Plan4.eK A N Ex hds z τ) = Inst.Model.FFSeg.zpos Q.full.D (Q.full.zOf z.1) := by
  have he : Plan4.eK A N Ex hds z τ = _ := Plan4.val_of_claims A N Ex tk hds τ z a7 hc
  have e := congrArg (fun p : Cb.Gl.E × Q.full.ip.St => p.2.z) hc.c4
  unfold ztS
  rw [he]
  exact congrArg (Inst.Model.FFSeg.zpos Q.full.D) e.symm

/-- **The matrices' reads are true, and their cells are the message's**: in the world of every
ledger later than the one that the hearing returned, at the statement's masks and entries. -/
def Plan4L.ReadsAt (QL : Plan4L Cb.Gl.E Mm X) (par : Par) (hS : OnBytes.Model.Layer.Shape)
    (L : Seat T) (Sm : Sem Wt) (part : Wt → Mm) (s : T) (fo : Forest.Heard) (o : Own) (G : Fork)
    (w : Wt) (Mt : Mats Cb.Gl.E) : Prop :=
  (∀ (Xp : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
    PubAt Xp { par.P with tokv := L.tokv s } par.hp fo o G2 t4 QL.plan.full.D QL.plan.full.tb hS →
    ∀ Fl, Fo.Later G Fl → Xp.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt) ∧
  cellsOf QL.plan.full.D (cellsAt par.P.y Mt) = QL.plan.full.rd (QL.plan.full.msg (part w))

/-- **What the statement's letters must mean for this road.** -/
structure Plan4L.LettersAre (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (nu : Wt → _root_.Fo.Pl → Cb.Gl.E) (first : ℕ) : Prop where
  mask : ∀ w, Sm.mask w = QL.plan.maskAt (part w)
  maskNu : ∀ w j, Sm.mask w j = nu w (_root_.Fo.Pl.mask j)
  ctx : ∀ a τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
    Lt.ctx (behindOf L pc a τ o G) w → Lt.ctx a w
  idn : ∀ a w, Lt.on a → QL.plan.Idn (part w) → Lt.idn a w
  keys : ∀ a w fo, Lt.on a → L.look a.1 = some fo → QL.plan.full.zOf (fa a).1 = zAt fo →
    QL.plan.full.kTg (fa a).1 = kTgAt fo (L.fork a.1) →
    (∀ s, QL.plan.kIncS (fa a).1 s = kIncAt fo (L.fork a.1) s) →
    QL.plan.Keys (fa a).1 (part w) → Lt.worthKeys a w
  planes : ∀ a w fo, Lt.on a → L.look a.1 = some fo →
    K3Stands fo.shape par.P.y.h.lmb first gl fo (L.fork a.1) →
    K3OutPlanes fo.shape par.P.y.h.lmb first (nu w) gl fo (L.fork a.1) → Lt.worthPlanes a w
  rider : ∀ a w fo, Lt.on a → L.look a.1 = some fo →
    (∀ l, l < QL.plan.full.D.ne → Blocks.ext QL.plan.full.D.lT
      (d10 QL.plan.full.D (QL.plan.full.rd (QL.plan.full.msg (part w))) l)
      (Inst.Model.FFSeg.zpos QL.plan.full.D (zAt fo)) = 0) →
    Lt.worthRider a w

/-- **What is still owed.** -/
structure Plan4L.Owes (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (nu : Wt → _root_.Fo.Pl → Cb.Gl.E) (first : ℕ) (s : WsShape) (lk : ℕ)
    (s0 : OnBytes.Model.Forest.Shape) (tl : HTailF2) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G → Lt.on' (behindOf L pc a τ o G)
  /-- the seat's two laws; the ledger's sizes and its next free slot, under the promise in front -/
  seat : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G → SeatOk L a.1
  sized : ∀ a, Lt.on a → PscRun.Sized (L.fork a.1)
  next : ∀ a, Lt.on a → QL.n0 = (L.fork a.1).next
  /-- the plan's public lines -/
  lines : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QL.plan.full.D QL.plan.full.tb s
    lk s0 tl
  /-- what the lookup left -/
  look : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G →
    LookLines { par.P with tokv := L.tokv a.1 } fo s0 ∧ QL.plan.full.zOf (fa a).1 = zAt fo ∧
      QL.plan.full.kTg (fa a).1 = kTgAt fo (L.fork a.1) ∧
      (∀ s, QL.plan.kIncS (fa a).1 s = kIncAt fo (L.fork a.1) s) ∧ Fo.FilledA (L.fork a.1) fo.cEnd
  /-- the rotary tables' fit at what was heard -/
  rope : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G →
    ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QL.plan.full.D QL.plan.full.tb (par.g * par.P.y.Lam) lam
  /-- matrices whose reads are true, and whose cells are the message's -/
  reads : ∀ a τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
    Behind L Sm Lt par (behindOf L pc a τ o G) w →
    ∃ Mt : Mats Cb.Gl.E, Plan4L.ReadsAt QL par hS L Sm part a.1 fo o G w Mt
  /-- the heard record stands for some rounds at the ends that begin at first -/
  stands : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G →
    K3Stands fo.shape par.P.y.h.lmb first gl fo (L.fork a.1)
  /-- the heard shape passes the lookup's own test on numbers, and the three planes' tables' reads
  are true in the world of the ledger behind the first run -/
  planes : ∀ a τ fo o G w fs₁ F₁, Lt.on a → Yes L par pc a τ fo o G →
    Behind L Sm Lt par (behindOf L pc a τ o G) w → frontRun par o G = some (fs₁, F₁) →
    FoNums.ok fo.shape = true ∧ K4ReadsTrue gl o.v fo F₁ (nu w) (Sm.entryT o w)
  /-- the five own rows -/
  rows : ∀ a τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
    Behind L Sm Lt par (behindOf L pc a τ o G) w →
    Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (u1At QL.plan.full.nr
        ((tailF QL.plan.full).b1 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2) = 0 ∧
    Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (u2At QL.plan.full.nr
        ((tailF QL.plan.full).b2 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2) = 0 ∧
    Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (prodU QL.plan.full.fp.gp
        ((tailF QL.plan.full).b5 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2) = 0 ∧
    Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (prodU QL.plan.full.fp.rt.L
        ((tailF QL.plan.full).b6 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2) = 0 ∧
    Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (upForm (J₂ := J3 (roomK QL.plan par hS)) (Cb.Sub.formU QL.plan.full.ip.inn.toSum.T.par
        (fun _ b _ _ => PEmpty.elim b)
        ((tailF QL.plan.full).b4 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2)) = 0
  /-- what the row opens on the committed weights gives the pending row at the merge's record, its
  row weights at the typed state of the seventh stage, at the hearing's own ledgers and records and
  at targets that are these records' -/
  wo : ∀ a τ fo o G w (g7 : Tg7) H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4, Lt.on a →
    Yes L par pc a τ fo o G →
    Led7 { par.P with tokv := L.tokv a.1 } par.hp par.g fo o (L.fork a.1) G (tapeAt par pc τ) []
      H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 →
    TgRec g7 { par.P with tokv := L.tokv a.1 } par.hp o (tapeAt par pc τ) H1 tT F4 G2 G3 G3' →
    Lt.wo (behindOf L pc a τ o G) w →
    WoSays QL.plan.full (aS7 (Plan4.tailMK A (numsK QL.plan.full))
      (ksOf { par.P with tokv := L.tokv a.1 } par.hp) ((tapeAt par pc τ).drop 1)
      (Plan4.nzAt A (L.tokv a.1) hds τ _) ((fa a).1, ptOf QL.plan (tapeAt par pc τ)) g7)
      o.wo (part w)
  /-- the part merge -/
  merge : ∀ a τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
    Behind L Sm Lt par (behindOf L pc a τ o G) w →
    Ledger.Holds (QL.plan.clK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).merge
      (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))

/-- The seven parts, from `Meets`, the piece's rounds, `ValueIs`, the masks' line and `Owes`. -/
theorem Plan4L.seven_of_owes (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (V : Plan4L.ValueIs QL par hS)
    (lw : ℕ → LW Cb.Gl.E) {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    {tl : HTailF2} {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ}
    (hSm : ∀ w, Sm.mask w = QL.plan.maskAt (part w))
    (O : Plan4L.Owes A L Sm Lt Ex pc hds fa part nu first s lk s0 tl) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) (fo : Forest.Heard) (o : Own) (G : Fork) (w : Wt)
    (ha : Lt.on a) (Y : Yes L par pc a τ fo o G)
    (hB : Behind L Sm Lt par (behindOf L pc a τ o G) w) :
    Plan4L.SevenAt A Ex hds fa part a τ w := by
  obtain ⟨K, hz0, hk0, _, hfil⟩ := O.look a τ fo o G ha Y
  obtain ⟨Mt, hR, hcells⟩ := O.reads a τ fo o G w ha Y hB
  obtain ⟨u1, u2, u5, u6, u4⟩ := O.rows a τ fo o G w ha Y hB
  exact Plan4L.seven_at A L Sm Lt Ex hds fa part a τ Y w hB (O.seat a τ fo o G ha Y)
    (O.sized a ha) (O.lines (L.tokv a.1)) K (O.rope a τ fo o G ha Y) lw hz0 hk0 hfil Mt hR hcells V
    (O.next a ha) (hSm w) u1 u2 u5 u6 u4

/-- **`K04LawAt` at a group that is not the first**, from `Meets`, the piece's rounds and back, the
errors' premise, C, hk, `ValueIs`, `LettersAre` and `Owes`. -/
theorem Plan4L.k04LawAt_K (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsLater par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (hback : pc.back = [])
    (herr : Err.le ((Plan4.mapsAt A (numsK QL.plan.full) Ex hds).err
      ((chF QL.plan.full).eps Ex)) pc.err)
    (C : QL.plan.D.ChOK)
    (hk : ∀ l, l < QL.plan.D.nl → (QL.plan.D.Pl l).kq = (QL.plan.D.Pl l).kk ∨
      (16 ≤ (QL.plan.D.Pl l).kq ∧ 16 ≤ (QL.plan.D.Pl l).kk))
    (V : Plan4L.ValueIs QL par hS)
    (lw : ℕ → LW Cb.Gl.E) {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    {tl : HTailF2} {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ}
    (M : Plan4L.LettersAre A L Sm Lt Ex pc hds fa part nu first)
    (O : Plan4L.Owes A L Sm Lt Ex pc hds fa part nu first s lk s0 tl) :
    K04LawAt L Sm Lt part par bk pc := by
  have seven := Plan4L.seven_of_owes A L Sm Lt Ex pc hds fa part V lw M.mask O
  have hn := norms_sizes A.hy A.Z
  refine Plan4.k04LawAt_later A A.p3 (numsK QL.plan.full) L Sm Lt Ex bk pc hds fa part
    (ztS QL.plan.full) hback herr
    { kept := O.kept
      pending := fun a τ fo o G w ha Y hB => ?_
      sq := fun a τ fo o G w ha Y hB => (seven a τ fo o G w ha Y hB).1
      bat := fun a τ fo o G w ha Y hB => (seven a τ fo o G w ha Y hB).2.1
      led := fun a τ fo o G w ha Y hB => (seven a τ fo o G w ha Y hB).2.2.1
      terms := fun a τ fo o G w ha Y hB => (seven a τ fo o G w ha Y hB).2.2.2.1
      gated := fun a τ fo o G w ha Y hB => (seven a τ fo o G w ha Y hB).2.2.2.2.1
      hot := fun a τ fo o G w ha Y hB => (seven a τ fo o G w ha Y hB).2.2.2.2.2.1
      stack := fun a τ fo o G w ha Y hB => (seven a τ fo o G w ha Y hB).2.2.2.2.2.2
      merge := O.merge
      first := fun a τ fo o G w ha Y hB hp => ?_ }
  · obtain ⟨K, hz0, hk0, _, hfil⟩ := O.look a τ fo o G ha Y
    obtain ⟨hinv, hscl, hvy, _, _, _⟩ :=
      Plan4L.heard_K A Y.hears (O.sized a ha) (small_of_all _ _ _ Y.small) V.scl V.L0
    have B := O.lines (L.tokv a.1)
    obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, g7, Ld, I, hc⟩ :=
      Plan4.atYes A (numsK QL.plan.full) L hds a τ Y (fa a).1 (O.sized a ha) B.S B.hs B.hg B.hrd
        B.hmats B.hρ B.hc B.hN B.hfl K.hsx K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL B.hlw B.h4
        (O.rope a τ fo o G ha Y) B.htm B.hNM B.hpad hinv hscl hvy (A.lamM (L.tokv a.1)) gl_half
        (nums4_numsK QL.plan.full) lw hz0 hk0 hfil
    have he := Plan4.val_of_claims A (numsK QL.plan.full) Ex (L.tokv a.1) hds τ (fa a) _ hc
    show OkMore QL.plan.full (fun _ _ => True)
      (QL.plan.full.own.toOwn.ch.val Ex (fa a)
        ((Plan4.mapsAt A (numsK QL.plan.full) Ex hds).view τ)).1 (part w)
    rw [he]
    exact (pending_of_led QL.plan.full (Plan4.tailMK A (numsK QL.plan.full)) Ld
      (outTies_K A (L.tokv a.1) Ld.c4).k7 rfl _ _ g7
      I.t7 rfl (part w)).2 (O.wo a τ fo o G w g7 H1 hd2 tT F4 F7 F8 G1 G1' G2 G3
      G3' G4 ha Y Ld I hB.2.2)
  · obtain ⟨hc, ⟨fs₁, F₁, _, _, h1, _, z1, _⟩, _⟩ :=
      forms_of_behind L Sm Lt par pc a τ o G w (O.seat a τ fo o G ha Y) hB
    obtain ⟨hok, hT⟩ := O.planes a τ fo o G w fs₁ F₁ ha Y hB h1
    obtain ⟨_, _, hvy, _, _, _⟩ :=
      Plan4L.heard_K A Y.hears (O.sized a ha) (small_of_all _ _ _ Y.small) V.scl V.L0
    have hm : Sm.mask w = fun j => nu w (_root_.Fo.Pl.mask j) := funext (M.maskNu w)
    have hpl := planes_of_yes (P := { par.P with tokv := L.tokv a.1 }) gl (O.sized a ha) Y.hears h1
      first (nu w) (Sm.entryT o w) hok
      (fun f hf => by
        have q := (z1 f hf).2
        rw [hm] at q
        exact q) hT
    rw [hvy] at hpl
    obtain ⟨hI, hK⟩ := (QL.plan.pT_iff C hk (fa a).1 (part w)).1 hp
    obtain ⟨_, hz0, hk0, hkI, _⟩ := O.look a τ fo o G ha Y
    obtain ⟨a7, hc7⟩ := OnBytes.Desc.First.P1.claims_exist (Plan4.tailMK A (numsK QL.plan.full))
      (ksOf { par.P with tokv := L.tokv a.1 } par.hp) ((tapeAt par pc τ).drop 1)
      (Plan4.nzAt A (L.tokv a.1) hds τ _) ((fa a).1, ptOf QL.plan (tapeAt par pc τ))
    have hzt := Plan4.zt_eK A (numsK QL.plan.full) Ex (L.tokv a.1) hds τ (fa a) a7 hc7
    have hr := rider_of_hot QL.plan.full
      (normsOk_of QL.plan.full (ztS QL.plan.full) _ _ _ par.P.y.ls hn.1 hn.2.1 hn.2.2.1)
      (noRest3 QL.plan.full) _ (part w) (seven a τ fo o G w ha Y hB).2.2.2.2.2.1
    rw [hzt, hz0] at hr
    exact ⟨M.ctx a τ fo o G w ha Y hc, M.idn a w ha hI,
      M.planes a w fo ha Y.look (O.stands a τ fo o G ha Y) hpl,
      M.keys a w fo ha Y.look hz0 hk0 hkI hK, M.rider a w fo ha Y.look hr⟩

/-- **The same at a piece whose errors are the cap** (128 bits a written challenge): the errors'
premise is concluded (`Plan4.herr_cap`, CapFromMeets.lean). -/
theorem Plan4L.k04LawAt_cap (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsLater par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (C : QL.plan.D.ChOK)
    (hk : ∀ l, l < QL.plan.D.nl → (QL.plan.D.Pl l).kq = (QL.plan.D.Pl l).kk ∨
      (16 ≤ (QL.plan.D.Pl l).kq ∧ 16 ≤ (QL.plan.D.Pl l).kk))
    (V : Plan4L.ValueIs QL par hS)
    (lw : ℕ → LW Cb.Gl.E) {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    {tl : HTailF2} {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ}
    (M : Plan4L.LettersAre A L Sm Lt Ex pc hds fa part nu first)
    (O : Plan4L.Owes A L Sm Lt Ex pc hds fa part nu first s lk s0 tl) :
    K04LawAt L Sm Lt part par bk pc :=
  Plan4L.k04LawAt_K A L Sm Lt Ex bk pc hds fa part hback
    (hcap ▸ Plan4.herr_cap A (numsK QL.plan.full) Ex hds) C hk V lw M O

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4L.k04LawAt_K
#print axioms OnBytes.Road.K4.Plan4L.k04LawAt_cap
