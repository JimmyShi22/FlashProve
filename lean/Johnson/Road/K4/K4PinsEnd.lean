-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsEnd.lean: K4's ROW AT THE TABLE OF JOINTS OVER A LETTER Mg, ITS PREMISES
SORTED BY WHO CAN PAY THEM: EQUATIONS OF Mg's FIELDS · CONDITIONS ON PUBLIC LETTERS · the premises
of
`RefSeat.k4_own_refK` (Johnson/Road/K4/CloseAtTableK.lean) · AND WHAT IS OF NO SUCH KIND, BY NAME.
Glue over `k4_own_all` (Johnson/Road/K4/K4PinsAll.lean) and Johnson/Road/K4/K4PinsConstr.lean. No
draw, no count.

  `sig_of_eqs`: a meaning whose six fields pin, noColl, shown, held, pinW, decodes are the oracles'
    layer's own terms IS `meaningSig` of itself: so what is stated at `meaningSig … Mg`, Mg any,
    speaks of it.
  `K4PlanFit`: THE CONDITIONS ON PUBLIC LETTERS, in one Lean structure: `SitsIn` · `Covers` ·
    `PlaceIs` ·
    `KeysFit` · "the plan's structure for the smallness test has the
    size s (2 p.g)" · `SymsOne` at segment 2 p.g · `SeamFit` · the table's segment is 2 p.g and is
    not the head's.
  `K4MeanEqs`: THE EQUATIONS OF FIELDS THAT THE SEVEN LINES SPEND: the six above · constr is
    `P5J.constrQAt hd put H headPart digitsPart` · H's decoder is decT at the stored table's cells ·
    H's list of group p.g is `Meaning.mgOf` of the segments' own lists · the item worth m 2 at
    "planes", "keys", "rider" follows from `K3WorthPlanes`, `K3WorthKeys`, `K3WorthRider` at the
    caller's letters.
  **`k4_own_end`**: the piece that holds K4's block has `Own` at the table's own promises and
    relations AT Mg, from: the premises of `RefSeat.k4_own_refK` but `K4Lines` · `readsOpen` ·
    `K4PlanFit` · `K4MeanEqs` · `RecRides` · the lines forms, wo.

THE CELLS ARE A MATRIX: Cells := Fin rows → Fin cols → the field (the type at which `constrQAt`'s
decoder speaks).

STANDS OVER Johnson/Top/H/K3Worth.lean · Johnson/P5J/MeansQ.lean, which stand in this tree.

OBJECT: as in CloseAtTable.lean. USER: Johnson/Road/K4/K4PinsEndFirst.lean; meant: the assembly of
K4's law at all places. LETTERS, filled by nobody: those of K4PinsAll.lean; hd, put, H, headPart,
digitsPart.

Limits. K04_law IS NOT PROVED BY THIS. THE PROMISE BEHIND REMEMBERS THE ACCEPTING RUN: the filling's
letter on' is `keptFrom (tableOn0 …) p pc` (Johnson/Road/K4/CloseRefFillK.lean): "b is what stands
behind an accepting run of the piece from a state that meets the promise in front": so the lines
forms and wo are asked under more than before. OF NO SORTED KIND, AND WITHOUT A PAYER TODAY:
`RecRides` (a property of the two letters smp and decT: a theorem the day they are terms:
K4Pins.lean's and K4PinsW.lean's doors) · the lines forms and wo. NOTHING IS ASKED OF enc: that it
is the coding by which the stored table's decoder and the lookup's external member are one is owed
at the joint with the lookup's own law, by whoever writes the stored table as an oracle message.
`K4MeanEqs`' three lines on worth are implications, not equations: an equation gives them. OF
`K4PlanFit` THE TESTS THEMSELVES HAVE NOT RUN (plain twins of `SitsIn`, `SymsOne`, `SeamFit` have,
at picked symbols of the real plans of both sizes: yes, with controls that said no); NOTHING IS
TRIED FOR EMPTINESS. UNGUARDED, BY NAME: the index masks (the value's letter idxAt: nothing is asked
of posI, nor that a member of ms sits at N.index: it falls on forms and wo:
Johnson/Road/K4/K4PinsIndex.lean has the guard) · the weights off the statement where decT gives
nothing (a zero matrix: the guard is the promise "the stored table decodes") · seatT at a member
that bears no symbol. x.link IS TIED TO NEITHER m NOR p.g. `KeysFit`'s lines on the trees, the
calls, the bounds and the four layers are asked again here though `PublicSteps` and `RefPub` stand
beside them: the calls that would draw them are not made in this file. A group that is not the
first; the reference sizes.
-/
import Johnson.Road.K4.K4PinsAll
import Johnson.Road.K4.K4PinsConstr

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
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (LW Dim Dk)

/-- **A meaning whose six fields are the oracles' layer's own terms is `meaningSig` of itself.** -/
theorem sig_of_eqs {Xi P Cells Tok : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (h1 : Mg.pin = pinJT cs G arr smp ms)
    (h2 : Mg.noColl = noCollJT cs G smp ms) (h3 : Mg.shown = shownJT cs G ms)
    (h4 : Mg.held = fun j t (a : P × S) => smpHeld a.2.st a.2.book j t)
    (h5 : Mg.pinW = pinWOf decT) (h6 : Mg.decodes = decodesOf decT) :
    Mg = meaningSig cs G arr smp ms decT Mg := by
  unfold meaningSig
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6]

variable [scl : Scl] {P Tok Cl Xi : Type} {Fr : Frame} {pol KL : ByteArray} {X : Public} {p : Par}
  {tk : Array Nat} {rows cols : ℕ} (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub)
  (D : Sent) (rad : OnBytes.OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (posI : ℕ → Bool × ℕ × ℕ)
  (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
  (nM nR nC n0 ns nx v7 : ℕ) (hg : p.g < 12) (G : FileDescription Xi)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.codes s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Fin rows → Fin cols → Cb.Gl.E))
  (Mg : Meaning P (Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT)) (Zt : P) (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place) (k first : ℕ) (Q3 : Fork → Prop) (s : ℕ → Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (hd : ℕ)
  (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
  (H : P5J.HidAt X P (Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT) rows cols)
  (headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Strs →
    Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT → Prop)
  (digitsPart : ℕ → P × P5J.TS → Strs → Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT → Prop)

/-- the value -/
local notation "𝐐" => RefSeat.atRec (PinPlan.seatN (planAt x D rad seatT
  (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y nM nR nC n0 ns nx v7) X p hg
/-- the filling's letters, at Mg -/
local notation "𝐋⟨" c "⟩" => Plan4K.lettersOf (Fr := Fr) (RefSeat.atRec (PinPlan.seatN (planAt x D
  rad
  seatT (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y nM nR nC n0 ns nx v7) X p hg)
  (partOf D.codes arr ms N m) p first p.P.y.fo Q3 (tableOn0 N Mg Zt links ps k)
  (keptFrom (tableOn0 N Mg Zt links ps k) p c)
  (tableCtx0 N Mg Zt m) (decOf D.codes G smp ms decT N Zt m)

/-- **The conditions on public letters.** -/
structure K4PlanFit : Prop where
  sits : SitsIn (sigListCalls D rad x.link) seatT ms N m
  covers : Covers p.hp.tl nM nR nC
  place : PlaceIs x p first
  keys : KeysFit X p q
  size : szOf p.hp.tl = s (2 * p.g)
  syms : SymsOne (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) p.hp.tl arr N (2 * p.g)
    (s (2 * p.g)) (seat (2 * p.g))
  seam : SeamFit arr ms N s seat D.codes q.y p.g
  segment : m = 2 * p.g
  notHead : m ≠ hd

/-- **The equations of fields that the seven lines spend.** -/
structure K4MeanEqs : Prop where
  pin : Mg.pin = pinJT D.codes G arr smp ms
  noColl : Mg.noColl = noCollJT D.codes G smp ms
  shown : Mg.shown = shownJT D.codes G ms
  held : Mg.held = fun j t (a : P × S) => smpHeld a.2.st a.2.book j t
  pinW : Mg.pinW = pinWOf decT
  decodes : Mg.decodes = decodesOf decT
  constr : Mg.constr = P5J.constrQAt hd put H headPart digitsPart
  decIs : H.dec = fun a y => decT y.cell a
  hidIs : ∀ w, (H.hid w).MG p.g = Meaning.mgOf X.y (ownW arr ms N s seat D.codes w) p.g
  planes : ∀ (t : S) (y : Strs) w,
    K3WorthPlanes (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
      (fun w => nuLay x D rad p.hp.tl oW wOf hRef (2 ^ kRef) (matIx p.P.y).iB
        (tupleW x D rad seatT oW enc arr w)) t w → Mg.worth m 2 "planes" (Zt, t) y w
  keys : ∀ (t : S) (y : Strs) w,
    K3WorthKeys (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
      (fun w => nuLay x D rad p.hp.tl oW wOf hRef (2 ^ kRef) (matIx p.P.y).iB
        (tupleW x D rad seatT oW enc arr w))
      (fun w => Cb.Fo.forK Cb.Gl.E
        (layLay q x.fs x.lm x.F.next x.ns p.hp.tl hRef (2 ^ kRef)) ()
        (Cb.Fo.zext (msgLay x p.hp.tl D rad oW wOf hRef (2 ^ kRef)
          (tupleW x D rad seatT oW enc arr w)))) t w → Mg.worth m 2 "keys" (Zt, t) y w
  rider : ∀ (t : S) (y : Strs) w,
    K3WorthRider (fun s : S => s.fork?) (fun s : S => s.lookHeard?)
      (layRider x q p.hp.tl D rad oW wOf hRef (2 ^ kRef) Iop.extNone Unit) x.lm x.F.next
      (fun _ => ()) (fun w => tupleW x D rad seatT oW enc arr w) t w →
    Mg.worth m 2 "rider" (Zt, t) y w

/-- **K4's row at the table, over a letter Mg**: from the premises of `RefSeat.k4_own_refK` but
`K4Lines`; `readsOpen`; `K4PlanFit`; `K4MeanEqs`; `RecRides`; and the lines forms, wo. -/
theorem k4_own_end (hscl : scl = sclX X p.g) (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hy : q.y = X.layers.y) (Ex : ExtSpec) (bk : Block S Cl)
    (pc : Piece (ckP .two) Fr S Cl (Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT))
    (hds : pc.ds = dsLater p) (fe : S × Fr.E.Str → Ex.Str) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (lw : ℕ → LW Cb.Gl.E)
    (hn : n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ ns + 1)
    (hb : pc.b = below bk) (hh : HearsAs seatS p bk)
    (hx : ∀ a τ b w, pc.ior.red.out a τ = some b → pc.ext a τ w = w)
    {pl pl' : VerifiableInference.Desc.Place} (Hk : AtK4 links ps k m pl)
    (hr : readsOpen links ps (start links) = true)
    (Kf : K4Front Mg Zt links ps m p.P.y.fo p.P.y.h.lmb first Q3)
    (Kp : K4Keeps N Mg Zt links ps k m pl pl' pc p)
    (Pf : K4PlanFit (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms N m nM nR nC first s
      seat hd)
    (E : K4MeanEqs (X := X) (p := p) x q D rad seatT oW enc wOf arr ms N m G smp decT Mg Zt s seat
      hd put H headPart digitsPart)
    (R : RecRides D.codes smp decT Zt)
    (forms : ∀ b w, (𝐋⟨pc⟩).on' b → onQ N Mg links ps (fun s => (Zt, s)) (k + 1) b →
      b.1.failed = none → meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.formsT m 3 "own") b w →
      FormsT seatS ((𝐐).semOf (partOf D.codes arr ms N m) p.hp.tl) (frontRun p) formsBack b.1 w)
    (wo : ∀ b w, (𝐋⟨pc⟩).on' b → onQ N Mg links ps (fun s => (Zt, s)) (k + 1) b →
      b.1.failed = none → meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.wo m) b w → (𝐋⟨pc⟩).wo b w) :
    pc.Own (onQ N Mg links ps (fun s => (Zt, s)) k) (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))
      (meansQ N Mg (fun s => (Zt, s))) (insQ links ps k) (outsQ links ps k) := by
  obtain ⟨Mg0, rfl⟩ : ∃ Mg0, Mg = meaningSig D.codes G arr smp ms decT Mg0 :=
    ⟨Mg, sig_of_eqs D.codes G arr smp ms decT Mg E.pin E.noColl E.shown E.held E.pinW E.decodes⟩
  refine k4_own_all x q D rad seatT posI oW enc wOf arr ms N m nM nR nC n0 ns nx v7 hg G smp decT
    Mg0 Zt links ps k first Q3 s seat hscl St B hP hG hg0 hy Ex bk pc hds fe hback hcap lw hn hQ hb
    hh hx Hk hr Kf Kp ?_ forms wo
  exact
    { record := R
      small := smallRides_constrQAt hd put H headPart digitsPart decT E.decIs Zt m Pf.notHead Mg0
        E.constr pc.base R.table
      sits := Pf.sits
      covers := Pf.covers
      place := Pf.place
      keys := Pf.keys
      size := Pf.size
      syms := Pf.syms
      seam := Pf.seam
      fillI := fun a w h => by
        show (meaningSig D.codes G arr smp ms decT Mg0).constr m .idn (Zt, a.1) (strsOf Fr a.2) w
        rw [E.constr, Pf.segment]
        refine idn_constrQAt hd put H headPart digitsPart p.g (Pf.segment ▸ Pf.notHead) _ _ w
          fun Wi xx => ?_
        rw [E.hidIs w, show X.y = q.y from hy.symm]
        exact h Wi xx
      fillP := fun a w h => E.planes a.1 _ w h
      fillK := fun a w h => E.keys a.1 _ w h
      fillR := fun a w h => E.rider a.1 _ w h }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sig_of_eqs
#print axioms OnBytes.Road.K4.k4_own_end
