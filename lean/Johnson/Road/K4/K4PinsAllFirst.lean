-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsAllFirst.lean: K4's ROW AT THE TABLE OF JOINTS IN THE FIRST GROUP
(`RefSeat.k4_own_refKF`, Johnson/Road/K4/CloseAtTableKFirst.lean) WITH SEVEN LINES OF `K4Lines`
EXCHANGED IN ONE PLACE, AT ONE SEAT: pin, ctxRides, decRides for `FencedB`, `RecRides`,
`SmallRides`; planes, keys, rider, idn EACH CARRIED TO A FILLER's LINE THAT IS ITSELF A FIELD OF
`AllFitF` (fillP, fillK, fillR, fillI): EXCHANGED, NOT DISCHARGED. The twin of
Johnson/Road/K4/K4PinsAll.lean. One structure of premises and one theorem. Glue: calls
(K4PinsPlanesFirst.lean, K4PinsKeysFirst.lean, K4PinsRiderFirst.lean, K4PinsIdnFirst.lean;
K4Pins.lean and K4PinsFence.lean as they stand; `look_of_front` of K4PinsAll.lean and `ns_of_leftAt`
of CloseK3.lean as they stand); no draw, no count.

  `AllFitF`: the fields of `AllFit` (K4PinsAll.lean), WITH TWO CHANGES: `SeamFit` is not asked (no
    stream comes in from a group in front); the filler's line on idn is another. THERE: `NormField`
    and `EmbField` AT EVERY MATRIX OF WEIGHTS AND EVERY REQUEST give constr m idn: in the first
    group `EmbField` is no empty clause (it names the request's tokens and the matrix of weights),
    and nothing here gives it at every matrix and every request. HERE: under the filling's promise
    in front and ctx: `NormField` at every matrix and request, (J11) AT THE SEAT's TOKENS at the
    pinned part of w, and «the value's matrices off that part are the casts of what the prover
    hides» give constr m idn.
  **`k4_own_allF`**: the piece that holds K4's block has `Own` at the table's own promises and
    relations, from: the premises of `RefSeat.k4_own_refKF` but `K4Lines` · the table's test
    `readsOpen` · `AllFitF` · THE TWO LINES THAT STAY: forms, wo.

OBJECT: as in CloseAtTableFirst.lean. USER: none here. LETTERS, filled by nobody: as in
K4PinsAll.lean.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE: every premise of `RefSeat.k4_own_refKF`
but `K4Lines` · `readsOpen` · every field of `AllFitF` · the lines forms, wo. THE LINE idn IS NOT
PAID: FROM (J11) TO `EmbField` AT THE REQUEST THAT THE TABLE's ITEM MEANS THERE STAND THE TIE OF THE
SEAT's TOKENS TO THAT REQUEST AND THE TIE OF THE COMMITTED MATRIX TO THE STORED TABLE's CELLS
(Johnson/Road/K4/K4IdnFirst.lean has both under premises; not called here): CloseAtTableFirst.lean's
open question stands. All limits of K4PinsAll.lean stand, but «the first group is not covered». NO
MEANING, NO PLAN AND NO STATE OF THE VERIFIER IS SHOWN TO MEET THESE PREMISES TOGETHER. The
reference sizes alone. The first group alone.
-/
import Johnson.Road.K4.K4PinsAll
import Johnson.Road.K4.K4PinsKeysFirst
import Johnson.Road.K4.K4PinsIdnFirst
import Johnson.Road.K4.CloseAtTableKFirst

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
open OnBytes.Road.Rows.Norms (NormField EmbField)
open VerifiableInference.Desc.First.Look (szOf)
open Cb.Pv.Tail (Size)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par seatS formsBack seatS_look)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block FileDescription Wit)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers readsOpen start)
open VerifiableInference.Desc.First.Look (Sent sigListCalls msgLay LayPub layLay layRider)
open VerifiableInference.Desc.Sound (Frame Piece below onQ meansQ insQ outsQ Sending Mem MsgT
  meaningSig)
open VerifiableInference.Desc.Plain.K04 (HearsAs FormsT frontRun)
open VerifiableInference.OnPublicFiles (K3WorthPlanes K3WorthKeys K3WorthRider)
open Johnson.Pack (sigOf)
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (LW Dim Dk)

variable [scl : Scl] {P Tok Cl Xi : Type} {Fr : Frame} {pol KL : ByteArray} {X : Public} {p : Par}
  {tk : Array Nat} (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type} (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E)
  (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ) (nM nR nC n0 ns nx v7 : ℕ)
  (G : FileDescription Xi)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.codes s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
  (Mg : Meaning P (Wit Cells Tok MsgT)) (Zt : P) (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place) (k first : ℕ) (Q3 : Fork → Prop) (s : ℕ → Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- the value -/
local notation "𝐅" => RefSeat.atRecF (PinPlan.seatN (planAt x D rad seatT
  (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y nM nR nC n0 ns nx v7) X p
/-- the meaning -/
local notation "𝐌" => meaningSig D.codes G arr smp ms decT Mg
/-- the filling's letters, at a promise behind o -/
local notation "𝐋⟨" o "⟩" => Plan4KF.lettersOfF (Fr := Fr) (RefSeat.atRecF (PinPlan.seatN
  (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y nM nR nC n0 ns nx
  v7) X p)
  (partOf D.codes arr ms N m) p first p.P.y.fo Q3
  (tableOn0 N (meaningSig D.codes G arr smp ms decT Mg) Zt links ps k) o
  (tableCtx0 N (meaningSig D.codes G arr smp ms decT Mg) Zt m)
  (decOf D.codes G smp ms decT N Zt m)
/-- the promise behind that remembers the accepting run of the piece c -/
local notation "𝐊⟨" c "⟩" => keptFrom
  (tableOn0 N (meaningSig D.codes G arr smp ms decT Mg) Zt links ps k) p c

/-- **The premises that these lines leave, in the first group.** on': the filling's promise behind
(the line fillI reads the letters on and ctx alone, which do not read it). -/
structure AllFitF (base : ℕ) (on' : S × Fr.E.Str → Prop) : Prop where
  rides : RecRides D.codes smp decT Zt
  small : SmallRides Zt m Mg Fr base
  sits : SitsIn (sigListCalls D rad x.link) seatT ms N m
  covers : Covers p.hp.tl nM nR nC
  place : PlaceIs x p first
  keys : KeysFit X p q
  /-- for the line idn: conditions on public letters -/
  size : szOf p.hp.tl = s (2 * p.g)
  syms : SymsOne (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) p.hp.tl arr N (2 * p.g)
    (s (2 * p.g)) (seat (2 * p.g))
  /-- the fillers' lines -/
  fillI : ∀ (a : S × Fr.E.Str) w, (𝐋⟨on'⟩).on a → (𝐋⟨on'⟩).ctx a w →
    (∀ (Wi : Inst.Model.Mat) (xx : Cm.Seg.XI),
      NormField (layerShape X.P) X.layers.sc q.y p.g
          (Meaning.mgOf q.y (ownW arr ms N s seat D.codes w) p.g) Wi xx) →
    (𝐅).toLF.planF.J11 a.1 (partOf D.codes arr ms N m w) →
    (𝐅).mats (partOf D.codes arr ms N m w) =
      OnBytes.Road.Rows.Norms.castM (Meaning.mgOf q.y (ownW arr ms N s seat D.codes w) p.g) →
    meansQ (Fr := Fr) N (𝐌) (fun s => (Zt, s)) (.constr m .idn) a w
  fillP : ∀ (a : S × Fr.E.Str) w,
    K3WorthPlanes (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
      (fun w => nuLay x D rad p.hp.tl oW wOf hRef (2 ^ kRef) (matIx p.P.y).iB
        (tupleW x D rad seatT oW enc arr w)) a.1 w →
    meansQ (Fr := Fr) N (𝐌) (fun s => (Zt, s)) (.worth m 2 "planes") a w
  fillK : ∀ (a : S × Fr.E.Str) w,
    K3WorthKeys (fun s : S => s.fork?) (fun s : S => s.lookHeard?) x.fs x.lm x.F.next
      (fun w => nuLay x D rad p.hp.tl oW wOf hRef (2 ^ kRef) (matIx p.P.y).iB
        (tupleW x D rad seatT oW enc arr w))
      (fun w => Cb.Fo.forK Cb.Gl.E
        (layLay q x.fs x.lm x.F.next x.ns p.hp.tl hRef (2 ^ kRef)) ()
        (Cb.Fo.zext (msgLay x p.hp.tl D rad oW wOf hRef (2 ^ kRef)
          (tupleW x D rad seatT oW enc arr w)))) a.1 w →
    meansQ (Fr := Fr) N (𝐌) (fun s => (Zt, s)) (.worth m 2 "keys") a w
  fillR : ∀ (a : S × Fr.E.Str) w,
    K3WorthRider (fun s : S => s.fork?) (fun s : S => s.lookHeard?)
      (layRider x q p.hp.tl D rad oW wOf hRef (2 ^ kRef) Iop.extNone Unit) x.lm x.F.next
      (fun _ => ()) (fun w => tupleW x D rad seatT oW enc arr w) a.1 w →
    meansQ (Fr := Fr) N (𝐌) (fun s => (Zt, s)) (.worth m 2 "rider") a w

/-- **K4's row at the table in the first group, seven lines of `K4Lines` exchanged at one seat**:
from the premises of `RefSeat.k4_own_refKF` on the table of scales, `PublicSteps`, `RefPub`, la =
16, the size of the vocabulary, `EmbNums`, the place, the layout, the piece (rounds, back, errors,
block, extractor), `HearsAs`, `AtK4`, n0, the bound on Q3, `K4Front`, `K4Keeps`; from `readsOpen`;
from `AllFitF`; and from the lines forms, wo. -/
theorem k4_own_allF (hscl : scl = sclX X p.g) (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) (hy : q.y = X.layers.y)
    (Ex : ExtSpec) (bk : Block S Cl)
    (pc : Piece (ckP .two) Fr S Cl (Wit Cells Tok MsgT)) (hds : pc.ds = dsFirst p)
    (fe : S × Fr.E.Str → Ex.Str) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (lw : ℕ → LW Cb.Gl.E)
    (hn : n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ ns + 1)
    (hV : p.P.V = ppref.V) (NE : EmbNums p.P.y) (hb : pc.b = below bk) (hh : HearsAs seatS p bk)
    (hx : ∀ a τ b w, pc.ior.red.out a τ = some b → pc.ext a τ w = w)
    {pl pl' : VerifiableInference.Desc.Place} (H : AtK4 links ps k m pl)
    (hr : readsOpen links ps (start links) = true)
    (Kf : K4Front (𝐌) Zt links ps m p.P.y.fo p.P.y.h.lmb first Q3)
    (Kp : K4Keeps N (𝐌) Zt links ps k m pl pl' pc p)
    (A : AllFitF (Fr := Fr) (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms N m nM nR nC n0
      ns nx v7 G smp decT Mg Zt links ps k first Q3 s seat pc.base (𝐊⟨pc⟩))
    (forms : ∀ b w, (𝐋⟨𝐊⟨pc⟩⟩).on' b → onQ N (𝐌) links ps (fun s => (Zt, s)) (k + 1) b →
      b.1.failed = none → meansQ (Fr := Fr) N (𝐌) (fun s => (Zt, s)) (.formsT m 3 "own") b w →
      FormsT seatS ((𝐅).toPlan4K.semOf (partOf D.codes arr ms N m) p.hp.tl) (frontRun p) formsBack
        b.1 w)
    (wo : ∀ b w, (𝐋⟨𝐊⟨pc⟩⟩).on' b → onQ N (𝐌) links ps (fun s => (Zt, s)) (k + 1) b →
      b.1.failed = none → meansQ (Fr := Fr) N (𝐌) (fun s => (Zt, s)) (.wo m) b w →
      (𝐋⟨𝐊⟨pc⟩⟩).wo b w) :
    pc.Own (onQ N (𝐌) links ps (fun s => (Zt, s)) k) (onQ N (𝐌) links ps (fun s => (Zt, s)) (k + 1))
      (meansQ N (𝐌) (fun s => (Zt, s))) (insQ links ps k) (outsQ links ps k) :=
  RefSeat.k4_own_refKF hscl ((planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI).seatN x.ns N
      p.hp.tl q.y nM nR nC n0 ns nx v7) rfl St B hP hG hg0 hla hy Ex bk pc hds fe
    (partOf D.codes arr ms N m) hback hcap lw hn hQ hV NE hb hh hx N (𝐌) Zt H Kf Kp
    (k4Lines_of_six D.codes G arr smp ms decT N Zt m Mg _ p _
      (fencedB_of_below N pc.base H hr Kp.below) A.rides A.small _
      { forms := forms
        wo := wo
        idn := fun a w hon hc hI => A.fillI a w hon hc
          (fun Wi xx => norm_fieldsF (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns
              N
            p.hp.tl q.y nM nR nC n0 ns nx v7 X p (beq_iff_eq.mp hg0) hscl A.keys.lam A.covers arr ms
                m
            A.sits s seat A.size A.syms w hI.1 Wi xx)
          hI.2
          (mats_mgF (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y nM
            nR nC n0 ns nx v7 X p (beq_iff_eq.mp hg0) A.covers arr ms m A.sits s seat A.size A.syms
                w)
        planes := fun a w hon _ hW => A.fillP a w
          (planes_worthF x D rad seatT posI p.hp.tl oW enc wOf hRef (2 ^ kRef) arr ms N m A.sits
            q.y nM nR nC n0 ns nx v7 X p A.covers A.place a w
            (look_of_front N (𝐌) Zt H Kf hon.1.1 hon.1.2) hon hW)
        keys := fun a w hon _ hW => A.fillK a w
          (keys_worthF x q D rad seatT posI p.hp.tl oW enc wOf arr ms N m nM nR nC n0 ns nx v7 X p
            (beq_iff_eq.mp hg0) A.sits hscl A.covers A.place A.keys a w (look_of_front N (𝐌) Zt H Kf
                hon.1.1 hon.1.2)
            (Nat.le_trans (ns_of_leftAt seatS hon.2 hQ)
              (Nat.succ_le_succ (Nat.le_succ_of_le (Nat.le_max_left _ _)))) hon
            hW)
        rider := fun a w hon _ hW => A.fillR a w
          (rider_worthF x q D rad seatT posI p.hp.tl oW enc wOf hRef (2 ^ kRef) arr ms N m A.sits
            nM nR nC n0 ns nx v7 X p A.covers A.place A.keys.trees.dT deep_ref a w
            (look_of_front N (𝐌) Zt H Kf hon.1.1 hon.1.2) hon hW) })

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_own_allF
