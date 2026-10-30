-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsAll.lean: K4's ROW AT THE TABLE OF JOINTS (`RefSeat.k4_own_refK`,
Johnson/Road/K4/CloseAtTableK.lean) WITH ALL LINES OF `K4Lines` BUT forms AND wo EXCHANGED, NOT
DISCHARGED, IN ONE PLACE, AT ONE SEAT, FOR THE FIELDS OF `AllFit` (four of the seven, idn, planes,
keys, rider, are carried to a filler's line that is itself a field): pin, ctxRides, decRides
(Johnson/Road/K4/K4Pins.lean), planes, keys, rider (K4PinsPlanes.lean, K4PinsKeys.lean,
K4PinsRider.lean) and idn (K4PinsIdn.lean), at the seat whose mask row is cut at the lookup's
place's number of slots, at the plan's structure for the smallness test, at the reference rows and
columns of the committed matrix. One Lean structure of premises and one theorem. Glue: calls; no
draw, no count.

WHY. The pieces were typed one by one, some at `PinPlan.seat`, some at `PinPlan.seatN`. Here they
are laid into ONE call: what does not fit would not compile.

  `AllFit`: THE PREMISES THAT THESE LINES LEAVE, in one Lean structure: `RecRides` ·
    `SmallRides` · `SitsIn` · `Covers` · `PlaceIs` · `KeysFit` ·
    "the plan's structure for the smallness test has the size s (2 p.g)" · `SymsOne` at segment 2
    p.g ·
    `SeamFit` · THE FILLERS' LINES: `K3WorthPlanes`, `K3WorthKeys`, `K3WorthRider` at the caller's
    letters give the table's items worth m 2 "planes", "keys", "rider"; `NormField` and `EmbField`
    at "what the prover hides", at every matrix of weights and every request, give constr m idn.
  `look_of_front`: A PREMISE OF THE THREE LINES ON THE LOOKUP THAT IS NO DEBT: what `S.lookHeard?`
    finds the seat's reader finds (from `AtK4` and `K4Front`'s line on the public item look m). A
    second one, the ledger's number of slots: `ns_of_leftAt` (Johnson/Road/K4/CloseK3.lean), called.
  **`k4_own_all`**: the piece that holds K4's block has `Own` at the table's own promises and
    relations, from: the premises of `RefSeat.k4_own_refK` but `K4Lines` · the table's test
    `readsOpen` (with the line below of `K4Keeps` it gives `FencedB` at the piece's own base:
    Johnson/Road/K4/K4PinsFence.lean) · `AllFit` · THE TWO LINES THAT STAY: forms, wo.

STANDS OVER Johnson/Top/H/K3Worth.lean, which stands in this tree.

OBJECT: as in CloseAtTable.lean: the block bk is a letter with `HearsAs seatS p bk`. USER:
`k4_own_end` (Johnson/Road/K4/K4PinsEnd.lean).
LETTERS, filled by nobody: those of CloseAtTable.lean but M, part, dec and the value's four readers
of a tuple; those of K4PinsKeys.lean (among them Cells and enc) but tl (:= the plan's p.hp.tl).

Limits. K04_law IS NOT PROVED BY THIS. THE PROMISE BEHIND REMEMBERS THE ACCEPTING RUN: the filling's
letter on' is `keptFrom (tableOn0 …) p pc` (Johnson/Road/K4/CloseRefFillK.lean): "b is what stands
behind an accepting run of the piece from a state that meets the promise in front": so the lines
forms and wo are asked under more than before. WHAT STAYS A PREMISE: every premise of
`RefSeat.k4_own_refK` but `K4Lines` (among them `RefPub`, `HearsAs`, `AtK4`, every line of `K4Front`
and of `K4Keeps`) · `readsOpen` · every field of `AllFit` (who could pay each: the Limits of the
files named) · the lines forms, wo. NO MEANING, NO PLAN AND NO STATE OF THE VERIFIER IS SHOWN TO
MEET THESE PREMISES TOGETHER: NOTHING IS TRIED FOR EMPTINESS. NO GUARD AGAINST A READER's SILENT 0
BUT `SitsIn` AND
`Covers` IS ASKED (K4PinsRead.lean's Limits list what more a reading wants). UNGUARDED, BY NAME: (1)
THE INDEX MASKS: the value's letter idxAt is the table at the seat N.index at the places posI j:
NOTHING HERE ASKS THAT A MEMBER OF ms SITS THERE, NOR ANYTHING OF posI: none of the seven lines
spends it: it falls on forms and wo (the guard: Johnson/Road/K4/K4PinsIndex.lean) · (2) THE WEIGHTS
OFF THE STATEMENT: where decT gives nothing `decOf` holds no cells and the value reads A ZERO
MATRIX: the guard is the table's promise "the stored table decodes", not called here · (3) seatT:
`SitsIn` does not pin it; `SymsOne` pins it only at members that bear a symbol: at the mask row's
member nothing in this cone does (`MaskOne`, K4PinsMaskQ.lean, would). NOTHING TIES THE CALLER's
LINK x.link TO THE TABLE's SEGMENT m OR THE GROUP p.g; m and p.g are tied in K4PinsEnd.lean alone.
THE TABLE's TYPE OF CELLS IS FREE; THE LOOKUP's CALLER READS THE WEIGHTS OFF AN ORACLE MESSAGE
(`Cb.OMsg`), THE IMAGE OF THE CELLS UNDER THE LETTER enc: nothing is asked of enc here: that it is
the reading by which the stored table's decoder and the lookup's external member are one is owed by
whoever fills oW, enc and wOf. The fillers' lines hold by unfolding only at a meaning whose fields
worth and constr are filled by these definitions at these letters: they are not filled so. THE
FIRST GROUP IS NOT COVERED (the road's own premise: p.g is not 0). The reference sizes alone.

-/
import Johnson.Road.K4.K4PinsKeys
import Johnson.Road.K4.K4PinsFence
import Johnson.Road.K4.K4PinsIdn
import Johnson.Road.K4.CloseAtTableK

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
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (LW Dim Dk)

variable [scl : Scl] {P Tok Cl Xi : Type} {Fr : Frame} {pol KL : ByteArray} {X : Public} {p : Par}
  {tk : Array Nat} (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type} (enc : Cells → oW.Msg)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E)
  (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ) (nM nR nC n0 ns nx v7 : ℕ)
  (hg : p.g < 12) (G : FileDescription Xi)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.codes s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
  (Mg : Meaning P (Wit Cells Tok MsgT)) (Zt : P) (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place) (k first : ℕ) (Q3 : Fork → Prop) (s : ℕ → Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- the value -/
local notation "𝐐" => RefSeat.atRec (PinPlan.seatN (planAt x D rad seatT
  (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y nM nR nC n0 ns nx v7) X p hg
/-- the meaning -/
local notation "𝐌" => meaningSig D.codes G arr smp ms decT Mg
/-- the filling's letters -/
local notation "𝐋⟨" c "⟩" => Plan4K.lettersOf (Fr := Fr) (RefSeat.atRec (PinPlan.seatN (planAt x D
  rad
  seatT (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y nM nR nC n0 ns nx v7) X p hg)
  (partOf D.codes arr ms N m) p first p.P.y.fo Q3
  (tableOn0 N (meaningSig D.codes G arr smp ms decT Mg) Zt links ps k)
  (keptFrom (tableOn0 N (meaningSig D.codes G arr smp ms decT Mg) Zt links ps k) p c)
  (tableCtx0 N (meaningSig D.codes G arr smp ms decT Mg) Zt m)
  (decOf D.codes G smp ms decT N Zt m)

omit scl in
/-- **What `S.lookHeard?` finds the seat's reader finds**, at an unmarked statement under the
table's promise in front of K4's block: from `AtK4` and `K4Front` (its line on the public item
look m). -/
theorem look_of_front {W : Type} (N : Numbers) (Mq : Meaning P W) (Z : P) {links : List ModelPart}
    {ps : List VerifiableInference.Desc.Place} {k m : ℕ} {pl : VerifiableInference.Desc.Place}
    (H : AtK4 links ps k m pl) {h3 : OnBytes.Model.Forest.Shape} {lm first : ℕ} {Q3 : Fork → Prop}
    (Kf : K4Front Mq Z links ps m h3 lm first Q3) {a : S × Fr.E.Str}
    (ha : onQ N Mq links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none)
    (g : OnBytes.Model.Forest.Heard) (hg : a.1.lookHeard? = some g) : seatS.look a.1 = some g := by
  obtain ⟨b1, _, _⟩ := bools_of_onQ N Mq Z ha hu
  rw [H.here] at b1
  obtain ⟨al, hal⟩ := lay_of_shape H b1
  have e := Kf.look a.1 al (k4_pub_front N Mq Z H Kf.fit ha hu _ (by simp)) hal
  rw [seatS_look hal, e]
  unfold VerifiableInference.Desc.First.S.lookHeard? at hg
  rw [hal] at hg
  exact hg

/-- **The premises that these lines leave.** -/
structure AllFit (base : ℕ) : Prop where
  record : RecRides D.codes smp decT Zt
  small : SmallRides Zt m Mg Fr base
  sits : SitsIn (sigListCalls D rad x.link) seatT ms N m
  covers : Covers p.hp.tl nM nR nC
  place : PlaceIs x p first
  keys : KeysFit X p q
  /-- for the line idn: conditions on public letters -/
  size : szOf p.hp.tl = s (2 * p.g)
  syms : SymsOne (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) p.hp.tl arr N (2 * p.g)
    (s (2 * p.g)) (seat (2 * p.g))
  seam : SeamFit arr ms N s seat D.codes q.y p.g
  /-- the fillers' lines -/
  fillI : ∀ (a : S × Fr.E.Str) w,
    (∀ (Wi : Inst.Model.Mat) (xx : Cm.Seg.XI),
      NormField (layerShape X.P) X.layers.sc q.y p.g
          (Meaning.mgOf q.y (ownW arr ms N s seat D.codes w) p.g) Wi xx ∧
        EmbField (layerShape X.P) X.layers.sc q.y p.g
          (Meaning.mgOf q.y (ownW arr ms N s seat D.codes w) p.g) Wi xx) →
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

/-- **K4's row at the table, all lines but forms and wo paid at one seat**: from the premises of
`RefSeat.k4_own_refK` on the table of scales, `PublicSteps`, `RefPub`, the place, the layout, the
piece (rounds, back, errors, block, extractor), `HearsAs`, `AtK4`, n0, the bound on Q3, `K4Front`,
`K4Keeps`; from `readsOpen`; from `AllFit`; and from the lines forms, wo. -/
theorem k4_own_all (hscl : scl = sclX X p.g) (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hy : q.y = X.layers.y) (Ex : ExtSpec) (bk : Block S Cl)
    (pc : Piece (ckP .two) Fr S Cl (Wit Cells Tok MsgT)) (hds : pc.ds = dsLater p)
    (fe : S × Fr.E.Str → Ex.Str) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (lw : ℕ → LW Cb.Gl.E)
    (hn : n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ ns + 1)
    (hb : pc.b = below bk) (hh : HearsAs seatS p bk)
    (hx : ∀ a τ b w, pc.ior.red.out a τ = some b → pc.ext a τ w = w)
    {pl pl' : VerifiableInference.Desc.Place} (H : AtK4 links ps k m pl)
    (hr : readsOpen links ps (start links) = true)
    (Kf : K4Front (𝐌) Zt links ps m p.P.y.fo p.P.y.h.lmb first Q3)
    (Kp : K4Keeps N (𝐌) Zt links ps k m pl pl' pc p)
    (A : AllFit (Fr := Fr) (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms N m nM nR nC G
      smp decT Mg Zt first s seat pc.base)
    (forms : ∀ b w, (𝐋⟨pc⟩).on' b → onQ N (𝐌) links ps (fun s => (Zt, s)) (k + 1) b →
      b.1.failed = none → meansQ (Fr := Fr) N (𝐌) (fun s => (Zt, s)) (.formsT m 3 "own") b w →
      FormsT seatS ((𝐐).semOf (partOf D.codes arr ms N m) p.hp.tl) (frontRun p) formsBack b.1 w)
    (wo : ∀ b w, (𝐋⟨pc⟩).on' b → onQ N (𝐌) links ps (fun s => (Zt, s)) (k + 1) b →
      b.1.failed = none → meansQ (Fr := Fr) N (𝐌) (fun s => (Zt, s)) (.wo m) b w → (𝐋⟨pc⟩).wo b w) :
    pc.Own (onQ N (𝐌) links ps (fun s => (Zt, s)) k) (onQ N (𝐌) links ps (fun s => (Zt, s)) (k + 1))
      (meansQ N (𝐌) (fun s => (Zt, s))) (insQ links ps k) (outsQ links ps k) :=
  RefSeat.k4_own_refK hscl ((planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI).seatN x.ns N
      p.hp.tl q.y nM nR nC n0 ns nx v7) rfl hg St B hP hG hg0 hy Ex bk pc hds fe
    (partOf D.codes arr ms N m) hback hcap lw hn hQ hb hh hx N (𝐌) Zt H Kf Kp
    (k4Lines_of_six D.codes G arr smp ms decT N Zt m Mg _ p _
      (fencedB_of_below N pc.base H hr Kp.below) A.record A.small _
      { forms := forms
        wo := wo
        idn := fun a w _ _ hI => A.fillI a w fun Wi xx =>
          idn_fields (planAt x D rad seatT (cutW enc wOf hRef (2 ^ kRef)) posI) x.ns N p.hp.tl q.y
            nM nR nC n0 ns nx v7 X p hg hscl A.keys.lam
            (fun h => by rw [h] at hg0; exact absurd hg0 (by decide)) A.covers arr ms m A.sits s
            seat A.size A.syms w A.seam hI Wi xx
        planes := fun a w hon _ hW => A.fillP a w
          (planes_worth x D rad seatT posI p.hp.tl oW enc wOf hRef (2 ^ kRef) arr ms N m A.sits
            q.y nM nR nC n0 ns nx v7 X p hg A.covers A.place a w
            (look_of_front N (𝐌) Zt H Kf hon.1.1 hon.1.2) hon hW)
        keys := fun a w hon _ hW => A.fillK a w
          (keys_worth x q D rad seatT posI p.hp.tl oW enc wOf arr ms N m nM nR nC n0 ns nx v7 X p hg
            A.sits hscl A.covers A.place A.keys a w (look_of_front N (𝐌) Zt H Kf hon.1.1 hon.1.2)
            (Nat.le_trans (ns_of_leftAt seatS hon.2 hQ) (Nat.succ_le_succ (Nat.le_max_left _ _)))
              hon
            hW)
        rider := fun a w hon _ hW => A.fillR a w
          (rider_worth x q D rad seatT posI p.hp.tl oW enc wOf hRef (2 ^ kRef) arr ms N m A.sits
            nM nR nC n0 ns nx v7 X p hg A.covers A.place A.keys.trees.dT deep_ref a w
            (look_of_front N (𝐌) Zt H Kf hon.1.1 hon.1.2) hon hW) })

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_own_all
