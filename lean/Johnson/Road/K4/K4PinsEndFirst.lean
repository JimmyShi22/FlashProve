-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsEndFirst.lean: K4's ROW AT THE TABLE OF JOINTS IN THE FIRST GROUP, OVER A
LETTER Mg, ITS PREMISES SORTED BY WHO CAN PROVE THEM. The twin of Johnson/Road/K4/K4PinsEnd.lean's
end. Glue over `k4_own_allF` (Johnson/Road/K4/K4PinsAllFirst.lean),
Johnson/Road/K4/K4PinsConstr.lean and `emb_at_table` (Johnson/Road/K4/K4IdnFirst.lean). `sig_of_eqs`
and the structure `K4MeanEqs` (K4PinsEnd.lean) name no group: they are taken as they stand. No draw,
no count.

  `idn_constrQAtM`: the filler's line for the part idn at `P5J.constrQAt`, with its premise asked
    ONLY WHERE THE ITEM ASKS: at every matrix that the decoder gives, every index that it holds, and
    the item's own request. It names no group.
  `inOrder_of_onQ`: the table's promise at an unmarked statement holds "in order".
  `K4PlanFitF`: THE CONDITIONS ON PUBLIC LETTERS: `K4PlanFit` without `SeamFit`.
  `K4IdnFitF`: WHAT THE LINE idn WANTS MORE IN THE FIRST GROUP: `ReqTies` (K4IdnFirst.lean) at H's
    request and put · "in order" gives: the words in the verifier's state are the request file's,
    and `backReq` reads something off that file · the caller's reader of a weight's cell, at the
    image of a witness's cells under enc, reads that cell.
  **`k4_own_endF`**: the piece that holds K4's block has `Own` at the table's own promises and
    relations AT Mg, from: the premises of `RefSeat.k4_own_refKF` but `K4Lines` · `readsOpen` ·
    `K4PlanFitF` · `K4MeanEqs` · `K4IdnFitF` · `RecRides` · the lines forms, wo.

HOW idn IS HAD AT g = 0. `NormField`: from the 17 identities (`norm_fieldsF`, K4PinsIdnFirst.lean).
`EmbField`, at the index's matrix and the item's request alone: from (J11) at the seat's tokens by
`emb_at_table`: the decoder's matrix IS the witness's cells (the pin on the stored table, which ctx
holds, against the item's own «the decoder gives M») · the words in the verifier's state are the
request file's ("in order", which the promise in front holds, under `K4IdnFitF.order`) · the value's
committed matrix is matAt, cut (`RefSeat.Wn_eqF`, K4PinsMatFirst.lean) · matAt at the pinned part
spells the cells (under `K4IdnFitF.enc`) · the value's matrices are the casts of what the prover
hides (`mats_mgF`). SO THE LINE idn IS GIVEN HERE ONLY UNDER `K4IdnFitF`: whether the table's
meaning meets its three lines is not shown.

THE CELLS ARE A MATRIX ON THE REFERENCE ROWS AND COLUMNS: Cells := Fin hRef → Fin (2 ^ kRef) → the
field (K4PinsEnd.lean leaves rows and cols letters; `emb_at_table` speaks at the reference numbers).

OBJECT: as in CloseAtTableFirst.lean. USER: k04_own_first (Johnson/Road/K4/K04LawOf.lean), which
k04_of_head (K04OfHead.lean) reaches by calls. LETTERS: those of K4PinsEnd.lean; reqB, reqW. At
k04_own_first they are fields of the data Dk and of a member of K4FirstAt, or k04_own_first's own
binders (Xp, m, Mg, z, links, ps, k); along the calls from k04_of_head, Dk is k4DataWide hA.𝔇 (eAll
Zp cF L) mgBase, at the head hA's own structure of data (K04LawKind.lean), and the head hA is a
premise of k04_of_head.

Limits. K04_law IS NOT PROVED BY THIS. OF NO SORTED KIND: `RecRides` (at the term's data k4DataWide
it is proved by `rides_wide`, Johnson/Road/K4/K4PinsAtWide.lean, from 𝔇.smp = smpNamed 𝔇.cs seats
and Stored.NoRec 𝔇.decT) · the lines forms (nothing here proves them; K4PinsEnd.lean's Limits) and
wo (K4PinsEnd.lean's Limits; the core of wo at the first group is proved by `k04_wo_first`,
Johnson/Road/K4/K04LawOf.lean, under nine premises, `K4Means` and `K4FirstAt` among them) · AND, THE
FIRST GROUP's ALONE: `K4IdnFitF.enc`: a
property of the two letters enc and wOf, asked at every witness's cells: NOTHING HERE SHOWS THAT A
REAL PAIR MEETS IT; who could prove it: whoever fixes the oracle message, enc and wOf at which the
lookup's own law on the stored table stands, by a lemma that its reader reads the witness's cell
there: no such lemma is seen or called here, nor that its ranges are the reference rows and columns;
K4PinsEnd.lean asks nothing of enc · `K4IdnFitF.ties`: on four letters that the table's term leaves
free. `K4IdnFitF.order` is an implication, not an equation: an equation of the field
inOrder gives it if that field holds the two conjuncts. NOTHING IS ASKED OF posI, NOR THAT A MEMBER
OF ms SITS AT N.index: the index masks may be read off the zero table in silence; none of the seven
exchanged lines spends them: that falls on forms and wo (`WoRowF` reads them). SEVEN LINES OF
`K4Lines` ARE EXCHANGED HERE, NOT DISCHARGED: `K4MeanEqs`' three lines on worth are implications
that somebody must prove. THE THREE PUBLIC PREMISES THAT THE FIRST GROUP ALONE ASKS (la = 16, the
size of the vocabulary, `EmbNums`) ARE PROVED AT ALL PUBLIC FILES IN THE GOALS' SCOPE THAT ARE READ,
WHERE `publicOf` RETURNS, by `scope_la` (Johnson/Road/K4/RefInScope.lean) and `emb_public_in_scope`
(Johnson/Goal/Meaning/EmbScope.lean). Where the files are read and `publicOfO o` returns,
`EmbScope.emb_public_in_scopeO` (Johnson/Goal/Numbers/PublicAtMeaning.lean) proves the size of the
vocabulary and `EmbNums`; la = 16 is stated there by no theorem of its own: it is number 12 of the
41 of `ScopeCore.core_of_scopeO` (the same file), as `scope_la` takes it from `core_of_scope`. The
calls are not made here. NO CONDITION HAS RUN; NOTHING IS TRIED FOR EMPTINESS; NO MEANING IS SHOWN
TO MEET THESE
PREMISES TOGETHER. The first group; the reference sizes.
-/
import Johnson.Road.K4.K4PinsEnd
import Johnson.Road.K4.K4PinsAllFirst
import Johnson.Road.K4.K4PinsMatFirst
import Johnson.Road.K4.K4IdnFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Fork Forest.elems)
open OnBytes.Model.Layer (matIx)
open OnBytes.Model.Verify (Public layerShape)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block FileDescription Wit Strs smpHeld)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers readsOpen start)
open VerifiableInference.Desc.First.Look (Sent sigListCalls msgLay LayPub layLay layRider szOf)
open VerifiableInference.Desc.Sound (Frame Piece below onQ meansQ insQ outsQ Sending Mem MsgT
  meaningSig pinJT noCollJT shownJT pinWOf decodesOf strsOf)
open VerifiableInference.Desc.Plain.K04 (HearsAs FormsT frontRun)
open VerifiableInference.OnPublicFiles (K3WorthPlanes K3WorthKeys K3WorthRider)
open Johnson.Pack (sigOf)
open Cb.Pv.Tail (Size)
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open OnBytes.Road.Rows.Norms (NormField EmbField)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (LW Dim Dk)

/-- **The filler's line for the part idn, at the table's filling, asked only where the item
asks**: at every matrix M that the decoder gives and every index i that M holds: at i.mat and at the
item's own request. (`idn_constrQAt`, K4PinsConstr.lean, asks the two clauses at every matrix and
every request.) -/
theorem idn_constrQAtM {X : Public} {P W : Type} {rows cols : ℕ} (hd : ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq) (H : P5J.HidAt X P W rows cols)
    (headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Strs → W → Prop)
    (digitsPart : ℕ → P × P5J.TS → Strs → W → Prop) (g : ℕ) (hne : 2 * g ≠ hd) (a : P × P5J.TS)
    (y : Strs) (w : W)
    (h : ∀ M (i : Cm.Idx), H.dec a y = some M → VerifiableInference.OnPublicFiles.Flat.Holds M i →
      NormField (layerShape X.P) X.layers.sc X.y g ((H.hid w).MG g) i.mat
          (put (H.req a) (H.hid w).tok).val ∧
        EmbField (layerShape X.P) X.layers.sc X.y g ((H.hid w).MG g) i.mat
          (put (H.req a) (H.hid w).tok).val) :
    P5J.constrQAt hd put H headPart digitsPart (2 * g) .idn a y w := by
  unfold P5J.constrQAt
  rw [if_neg (by decide)]
  refine ⟨fun h' => absurd h' (by decide), fun M i hM hH => ?_⟩
  rw [if_neg hne, if_pos (Nat.mul_mod_right 2 g), Nat.mul_div_cancel_left g (by decide)]
  exact h M i hM hH

/-- "In order", off the table's promise at an unmarked statement. -/
theorem inOrder_of_onQ {P W : Type} {Fr : Frame} (N : Numbers) (Mq : Meaning P W) (Z : P)
    {links : List ModelPart} {ps : List VerifiableInference.Desc.Place} {k : ℕ} {a : S × Fr.E.Str}
    (ha : onQ N Mq links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none) :
    Mq.inOrder (Z, a.1) = true := by
  obtain ⟨hB, _⟩ := ha.2.resolve_left fun h => h hu
  simp only [Bool.and_eq_true] at hB
  exact hB.1.1.2

variable [scl : Scl] {P Tok Cl Xi : Type} {Fr : Frame} {pol KL : ByteArray} {X : Public} {p : Par}
  {tk : Array Nat} (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub)
  (D : Sent) (rad : OnBytes.OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (posI : ℕ → Bool × ℕ × ℕ)
  (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
  (nM nR nC n0 ns nx v7 : ℕ) (G : FileDescription Xi)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.codes s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E))
  (Mg : Meaning P (Wit (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) Tok MsgT)) (Zt : P) (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place) (k first : ℕ) (Q3 : Fork → Prop) (s : ℕ → Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (hd : ℕ)
  (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
  (H : P5J.HidAt X P (Wit (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) Tok MsgT) hRef (2 ^ kRef))
  (headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Strs →
    Wit (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) Tok MsgT → Prop)
  (digitsPart : ℕ → P × P5J.TS → Strs → Wit (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) Tok MsgT → Prop)

/-- the value -/
local notation "𝐅" => RefSeat.atRecF (PinPlan.seatN (planAt x D rad seatT
  (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y nM nR nC n0 ns nx v7) X p
/-- the filling's letters, at Mg, with the promise behind that remembers the accepting run of c -/
local notation "𝐋⟨" c "⟩" => Plan4KF.lettersOfF (Fr := Fr) (RefSeat.atRecF (PinPlan.seatN
  (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y nM nR nC n0 ns nx
  v7) X p)
  (partOf D.codes arr ms N m) p first p.P.y.fo Q3 (tableOn0 N Mg Zt links ps k)
  (keptFrom (tableOn0 N Mg Zt links ps k) p c)
  (tableCtx0 N Mg Zt m) (decOf D.codes G smp ms decT N Zt m)

/-- **The conditions on public letters, in the first group**: `K4PlanFit` (K4PinsEnd.lean) without
`SeamFit`. -/
structure K4PlanFitF : Prop where
  sits : SitsIn (sigListCalls D rad x.link) seatT ms N m
  covers : Covers p.hp.tl nM nR nC
  place : PlaceIs x p first
  keys : KeysFit X p q
  size : szOf p.hp.tl = s (2 * p.g)
  syms : SymsOne (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) p.hp.tl arr N (2 * p.g)
    (s (2 * p.g)) (seat (2 * p.g))
  segment : m = 2 * p.g
  notHead : m ≠ hd

/-- **What the line idn wants more in the first group**: three premises, of three kinds. -/
structure K4IdnFitF (reqB : P → ByteArray) (reqW : P → Array UInt32) : Prop where
  /-- ON FOUR LETTERS OF THE TABLE's MEANING: the words are the bytes' words; the request is what
  `backReq` reads off the bytes; put is `putReq` -/
  ties : ReqTies reqB reqW H.req put
  /-- AN IMPLICATION FROM A FIELD OF Mg: "in order" holds that the words in the verifier's state are
  the request file's and that `backReq` reads something off that file -/
  order : ∀ t : S, Mg.inOrder (Zt, t) = true →
    t.req = reqW Zt ∧ (Meaning.backReq (reqB Zt)).isSome = true
  /-- ON THE TWO LETTERS enc AND wOf: NO Bool ON THE PUBLIC PARAMETERS, NO FACT ON THE PIECE, NO
  EQUATION OF A FIELD: the lookup's caller's reader of a weight's cell, at the image of a witness's
  cells, reads that cell, inside the reference rows and columns -/
  enc : ∀ (w : Wit (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) Tok MsgT) (r : Fin hRef)
    (c : Fin (2 ^ kRef)), wOf (enc w.cells) r.val c.val = w.cells r c

/-- **K4's row at the table in the first group, over a letter Mg**: from the premises of
`RefSeat.k4_own_refKF` but `K4Lines`; `readsOpen`; `K4PlanFitF`; `K4MeanEqs`; `K4IdnFitF`;
`RecRides`; and the lines forms, wo. -/
theorem k4_own_endF (hscl : scl = sclX X p.g) (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) (hy : q.y = X.layers.y)
    (Ex : ExtSpec) (bk : Block S Cl)
    (pc : Piece (ckP .two) Fr S Cl (Wit (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) Tok MsgT))
    (hds : pc.ds = dsFirst p) (fe : S × Fr.E.Str → Ex.Str) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (lw : ℕ → LW Cb.Gl.E)
    (hn : n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ ns + 1)
    (hV : p.P.V = ppref.V) (NE : EmbNums p.P.y)
    (hb : pc.b = below bk) (hh : HearsAs seatS p bk)
    (hx : ∀ a τ b w, pc.ior.red.out a τ = some b → pc.ext a τ w = w)
    {pl pl' : VerifiableInference.Desc.Place} (Hk : AtK4 links ps k m pl)
    (hr : readsOpen links ps (start links) = true)
    (Kf : K4Front Mg Zt links ps m p.P.y.fo p.P.y.h.lmb first Q3)
    (Kp : K4Keeps N Mg Zt links ps k m pl pl' pc p)
    (Pf : K4PlanFitF (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms N m nM nR nC first s
      seat hd)
    (E : K4MeanEqs (X := X) (p := p) x q D rad seatT oW enc wOf arr ms N m G smp decT Mg Zt s seat
      hd put H headPart digitsPart)
    {reqB : P → ByteArray} {reqW : P → Array UInt32}
    (I : K4IdnFitF (X := X) oW enc wOf Mg Zt put H reqB reqW)
    (R : RecRides D.codes smp decT Zt)
    (forms : ∀ b w, (𝐋⟨pc⟩).on' b → onQ N Mg links ps (fun s => (Zt, s)) (k + 1) b →
      b.1.failed = none → meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.formsT m 3 "own") b w →
      FormsT seatS ((𝐅).toPlan4K.semOf (partOf D.codes arr ms N m) p.hp.tl) (frontRun p) formsBack
        b.1 w)
    (wo : ∀ b w, (𝐋⟨pc⟩).on' b → onQ N Mg links ps (fun s => (Zt, s)) (k + 1) b →
      b.1.failed = none → meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.wo m) b w → (𝐋⟨pc⟩).wo b w) :
    pc.Own (onQ N Mg links ps (fun s => (Zt, s)) k) (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))
      (meansQ N Mg (fun s => (Zt, s))) (insQ links ps k) (outsQ links ps k) := by
  obtain ⟨Mg0, rfl⟩ : ∃ Mg0, Mg = meaningSig D.codes G arr smp ms decT Mg0 :=
    ⟨Mg, sig_of_eqs D.codes G arr smp ms decT Mg E.pin E.noColl E.shown E.held E.pinW E.decodes⟩
  refine k4_own_allF x q D rad seatT posI oW enc wOf arr ms N m nM nR nC n0 ns nx v7 G smp decT
    Mg0 Zt links ps k first Q3 s seat hscl St B hP hG hg0 hla hy Ex bk pc hds fe hback hcap lw hn
    hQ hV NE hb hh hx Hk hr Kf Kp ?_ forms wo
  exact
    { rides := R
      small := smallRides_constrQAt hd put H headPart digitsPart decT E.decIs Zt m Pf.notHead Mg0
        E.constr pc.base R.table
      sits := Pf.sits
      covers := Pf.covers
      place := Pf.place
      keys := Pf.keys
      size := Pf.size
      syms := Pf.syms
      fillI := fun a w hon hc hN hJ hMz => by
        show (meaningSig D.codes G arr smp ms decT Mg0).constr m .idn (Zt, a.1) (strsOf Fr a.2) w
        rw [E.constr, Pf.segment]
        refine idn_constrQAtM hd put H headPart digitsPart p.g (Pf.segment ▸ Pf.notHead) _ _ w
          fun M i hM hH => ?_
        rw [E.hidIs w, show X.y = q.y from hy.symm]
        refine ⟨hN i.mat _, ?_⟩
        -- the decoder's matrix is the witness's cells: the pin on the stored table, which ctx holds
        have hpw : decT (strsOf Fr a.2).cell (Zt, a.1) = some w.cells := hc.1.2.1
        have hM' : decT (strsOf Fr a.2).cell (Zt, a.1) = some M := by
          rw [E.decIs] at hM
          exact hM
        obtain rfl : w.cells = M := Option.some.inj (hpw.symm.trans hM')
        -- the words in the verifier's state are the request file's: "in order", which the promise
        -- in front holds
        obtain ⟨h1, h2⟩ := I.order a.1 (inOrder_of_onQ N _ Zt hon.1.1 hon.1.2)
        exact emb_at_table ((planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI).seatN x.ns N
            p.hp.tl q.y nM nR nC n0 ns nx v7) rfl X p hscl Pf.keys.lam _ _ hMz I.ties (Zt, a.1) h1
          h2 hJ (H.hid w).tok (fun r c => RefSeat.Wn_eqF _ X p _ r c) hH
          (fun r c => by
            show (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI).mat
              (partOf D.codes arr ms N m w) r.val c.val = _
            rw [PinPlan.mat_some _ (C := w.cells) rfl]
            show cutW enc wOf hRef (2 ^ kRef) w.cells r.val c.val = _
            unfold cutW
            rw [if_pos ⟨r.isLt, c.isLt⟩]
            exact I.enc w r c)
      fillP := fun a w h => E.planes a.1 _ w h
      fillK := fun a w h => E.keys a.1 _ w h
      fillR := fun a w h => E.rider a.1 _ w h }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.idn_constrQAtM
#print axioms OnBytes.Road.K4.inOrder_of_onQ
#print axioms OnBytes.Road.K4.k4_own_endF
