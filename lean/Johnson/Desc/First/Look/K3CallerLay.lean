-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerLay.lean: THE CALLER OF THE PROVED LOOKUP BLOCK, WITH ITS RIDER, AT
THE LOOKUP ON THE CALLS OF A LAYERS' LINK of the proof's first chain, CLOSED BUT FOR THE STORED
TABLE's READING; and from the joint in front of the block there to two clauses of the meaning's row:
layKey («every entry of the eight key vectors, in which every product with a weight matrix stands,
is an entry of its table») and layHot («a router's selector has entries that sum to 1»), as the
library's own KeyField and HotField (Johnson/Road/Rows/LayerTop.lean). Definitions, statements and
proofs. NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

IT SPEAKS OF THE FULL SIZE ALONE: the library's KeyField and HotField stand at the reference sizes
DF, the reference layout kRef of the weights and the reference tables tbRef, which are the full
size's; at the small example the calls have other sizes, and LayOK.sizes | tabs cannot hold there.

What differs from attention's caller (K3CallerAtt.lean), whose frame it shares (h from the kind's
own parameters; St₀ := Unit; the cells are the one unpacking of the committed symbols; the planes'
cells; the mask row; R0 quiet; the first chain's part of the signature: the kept messages, then the
link's own of moment 0).
 (1) THE KEYS READ THE WEIGHTS. So the entries have a third sort: the cells of the committed matrix
     of weights (nr rows, nc columns); the signature has ONE EXTERNAL MEMBER oW beside the first
     chain's messages: the stored table's oracle message; and msg₀ reads a weight's cell off it by
     wOf. oW, wOf, nr AND nc ARE LETTERS: by the table of joints
     the stored table is an oracle of every statement of the first
     chain, and «the witness's cells are what the stored table decodes to, with the key
     file's record» stands beside every block that reads the weights; who fills the decoder and the
     record is for the writers of that table and of the key file's description to say.
 (2) L.K IS THE VERY TERM OF KeyField: the library's key vector of a feed-forward segment at the
     reference sizes DF, the reference layout kRef of the weights, the reference tables tbRef, the
     scales that Johnson/Road/FormsKeysFits.lean makes of the verifier's scale file (sclOf h sc g
     4), the cells by cellsOf DF (cellsAt y ·), the layers' matrices by layerR ppref kRef ·.
 (3) EIGHT CALLS; THE FULL SIZE ALONE: the reference sizes are the full size's.
 (4) THE RIDER is the library's crHot: identity j10, one member for each layer with experts, at the
     last DF.lT places of the first part of the key point.

THE TWO NAMED READINGS.
  MatsAre m Mz: the matrices that msg₀ reads off the messages m are the casts of the integer
    matrices Mz. It is paid, as at attention, where the committed symbols are the packing of small
    integers (lay_mats_cast).
  WeightsAre g m Wi: the matrices of the group's layers, as layerR ppref kRef cuts them out of what
    msg₀ reads off the stored table's message, are those that it cuts out of the casts of the
    index's matrix Wi. (Asked of the layers' matrices, not of every cell: outside nr × nc the
    caller reads 0, and Wi need not be 0 there. IT CAN BE PAID ONLY WHERE nr AND nc COVER ALL THAT
    layerR READS: nothing here ties them to kRef.) NOBODY PAYS IT HERE: it is the pin's.

Limits. Those of K3CallerAtt.lean, (1) to (7), with the layers' names for attention's: cellsAt,
cellsOf, keyVec, layerR, sclOf are the library's, and that they are what the programs lay is shown
by no theorem (Johnson/Road/FormsKeysCaller.lean's head says how far that road has come, and that
its theorems do not apply at the small example's numbers). LayOK's fields are premises on public
data; NONE HAS BEEN RUN. LayOK.tabs and LayOK.sizes compare the verifier's record with the library's
reference tables and sizes: whether they hold at the full-size example is not known to us.
THE CLAIM ON THE WEIGHTS that the programs' sumcheck leaves, and its way to the merge, is other
kinds' matter: nothing of it is here. That the programs' key FORMS are worth these vectors'
extensions at the key points is the calling kind's debt.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAttMeans
import Johnson.Road.Rows.LayerTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open OnBytes.Road (Mats cellsOf cellsAt)
open OnBytes.Road.Rows (Addr)
open OnBytes.Road.Rows.Norms (castM KeyField HotField)
open OnBytes.Model.Layer (Lay Scales)
open Inst.Model (Mat ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Idn idnVal keyVec layerR lut aC)
open Cb.Pv.Tail (JCell BaseAt cellValS)

/-- **The entries**: the mask row's; the cells behind the committed symbols; the cells of the
committed matrix of weights; one more, read as 0. -/
abbrev JLay (ns : Nat) (tl : HTailF2) (nr nc : Nat) : Type :=
  Option ((Fin ns ⊕ JCell (szOf tl)) ⊕ (Fin nr × Fin nc))

/-- A cell, a mask entry, a weight's cell, as entries. -/
def lyCell (ns : Nat) (tl : HTailF2) (nr nc a r c : Nat) : JLay ns tl nr nc :=
  (cellJ (szOf tl) a r c).map fun j => Sum.inl (Sum.inr j)
def lyMask (ns : Nat) (tl : HTailF2) (nr nc j : Nat) : JLay ns tl nr nc :=
  (finOf ns j).map fun k => Sum.inl (Sum.inl k)
def lyW (ns : Nat) (tl : HTailF2) (nr nc a b : Nat) : JLay ns tl nr nc :=
  (finOf nr a).bind fun a' => (finOf nc b).map fun b' => Sum.inr (a', b')

noncomputable section
open Johnson.Pack VerifiableInference.OnPublicFiles Cb.Fo Cb.Rider

/-- The matrices of the sub-proof's list, off the entries: total; what stands at the entry that is
none outside the bounds. -/
def matsOfE {ns : Nat} {tl : HTailF2} {nr nc : Nat} (μ : JLay ns tl nr nc → Cb.Gl.E) :
    Mats Cb.Gl.E := fun a r c => μ (lyCell ns tl nr nc a r c)

/-- The committed matrix of weights, off the entries. -/
def wOfE {ns : Nat} {tl : HTailF2} {nr nc : Nat} (μ : JLay ns tl nr nc → Cb.Gl.E) :
    ℕ → ℕ → Cb.Gl.E := fun a b => μ (lyW ns tl nr nc a b)

/-- **The signature**: the first chain's messages that stand sent, and one external member. -/
abbrev laySg (x : Place) (D : Sent) (rad : OracleShape → Nat) (oW : Cb.OMsg Cb.Gl.E) :
    Cb.Sig Cb.Gl.E := (sigOf D.codes (sigListCalls D rad x.link)).add oW

/-- The first chain's part of a tuple of messages. -/
def ownPart {x : Place} {D : Sent} {rad : OracleShape → Nat} {oW : Cb.OMsg Cb.Gl.E}
    (m : (laySg x D rad oW).Msg) : (sigOf D.codes (sigListCalls D rad x.link)).Msg :=
  fun a => m (some a)

/-- **The caller's reading msg₀.** -/
def msgLay (x : Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
    (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : Nat)
    (m : (laySg x D rad oW).Msg) : JLay x.ns tl nr nc → Cb.Gl.E
  | none => 0
  | some (.inl (.inl k)) =>
    (valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) (ownPart m)
      (.mask k.val)).getD 0
  | some (.inl (.inr j)) =>
    cellValS (symAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl (ownPart m)) j
  | some (.inr ab) => wOf (m none) ab.1.val ab.2.val

/-- The public letters of a layers' link: the shape, the scale file, the layout, the group. -/
structure LayPub where
  h : Model.Layer.Shape
  sc : Scales
  y : Lay
  g : Nat

/-- **The layout of the lookup on a layers' link's calls.** -/
def layLay (p : LayPub) (fs : Forest.Shape) (lm first ns : Nat) (tl : HTailF2) (nr nc : Nat) :
    Cb.Fo.Lay Cb.Gl.E Unit (JLay ns tl nr nc) where
  K := fun _ μ c X =>
    if hc : c < 8 then
      keyVec (scl := Road.sclOf p.h p.sc p.g 4) DF (cellsOf DF (cellsAt p.y (matsOfE μ)))
        Inst.Model.tbRef (4 * p.g) (fun l => layerR ppref kRef (wOfE μ) (4 * p.g + l)) ⟨c, hc⟩ X
    else 0
  bc := fun t c j =>
    lyCell ns tl nr nc (Model.Layer.matIx p.y).iB (FoNums.cellRC fs lm (t, c, j)).1
      (FoNums.cellRC fs lm (t, c, j)).2
  mkS := fun s => lyMask ns tl nr nc (first + s)

section
variable (x : Place) (p : LayPub) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
  (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : Nat) (Ex : Iop.ExtSpec)
  (Wp : Type)

/-- **THE CALLER OF THE LOOKUP ON A LAYERS' LINK's CALLS.** -/
@[reducible] def layCaller : LookupCCaller where
  h := x.fs
  St₀ := Unit
  J₀ := JLay x.ns tl nr nc
  finJ := inferInstance
  decJ := inferInstance
  L := layLay p x.fs x.lm x.F.next x.ns tl nr nc
  Ex := Ex
  Kc := Unit
  Wp := Wp
  Sg := laySg x D rad oW
  R0 := quiet Ex _ Wp
  msg₀ := msgLay x tl D rad oW wOf nr nc

/-- The segment's cells, off the tuple of messages. -/
def layCells (m : (laySg x D rad oW).Msg) : Inst.Model.FFSeg.Cell → Cb.Gl.E :=
  cellsOf DF (cellsAt p.y (matsOfE (msgLay x tl D rad oW wOf nr nc m)))

/-- **THE SAME WITH ITS RIDER**: the library's crHot, its letter «cells» filled. -/
@[reducible] def layRider : LookupCRCaller :=
  crHot (scl := Road.sclOf p.h p.sc p.g 4) (layCaller x p tl D rad oW wOf nr nc Ex Wp) DF
    fun _ m => layCells x p tl D rad oW wOf nr nc m

end

/-- **What is asked of the public data at a layers' link's calls**, as far as the theorems below use
it. The tests on the reading (every symbol and mask entry has a seat that fits; a kept message has
the born one's shape; one answer a message) are attention's, at this link: not repeated. -/
structure LayOK (set : Params.Setting) (x : Place) : Prop where
  /-- the kind's own parameters make the plan's record -/
  shape : (P.ofPlace set false x).shape = some x.fs
  /-- there are the library's eight calls -/
  eight : x.fs.NC = 8
  /-- a position's bits lie in the first part of the key point -/
  hot : DF.lT ≤ x.fs.dT
  /-- each call has room for the library's key vector -/
  sizes : ∀ c : Fin 8, aC DF c ≤ Cb.LdLkp.Port.nOf x.fs c
  /-- every row of the verifier's table of a call is an entry of the library's table of that call -/
  tabs : ∀ (c : Fin 8) (u : ℕ), u < 2 ^ Cb.LdLkp.Port.kOf x.fs c →
    ∃ v ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
      ((FoNums.tauN x.fs c u : ℕ) : Cb.Gl.E) = algebraMap Cb.Gl.F Cb.Gl.E v

section
variable {set : Params.Setting} {x : Place} {p : LayPub} {tl : HTailF2} {D : Sent}
  {rad : OracleShape → Nat} {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : Nat}
  (Ex : Iop.ExtSpec) (Wp : Type)

theorem lay_ok (H : LayOK set x) :
    OkLookupC (callersCR [layRider x p tl D rad oW wOf nr nc Ex Wp]) :=
  okLookupC_of_made fun c hc => by
    obtain rfl := List.mem_singleton.1 hc
    obtain ⟨h₀, a, b, e⟩ := shape_made H.shape
    exact ⟨_, _, h₀, _, a, b, e⟩

theorem lay_sel (H : LayOK set x) : SelLookupCR [layRider x p tl D rad oW wOf nr nc Ex Wp] :=
  fun r hr => by
    obtain rfl := List.mem_singleton.1 hr
    exact crHot_sel (scl := Road.sclOf p.h p.sc p.g 4) _ _ _ H.hot

/-- **The library's theorem applies.** -/
theorem lay_good (H : LayOK set x) :
    ((kLookupCR [layRider x p tl D rad oW wOf nr nc Ex Wp]).toKind.block
      (layRider x p tl D rad oW wOf nr nc Ex Wp)).Good :=
  lookupCR_good _ (lay_ok Ex Wp H) (lay_sel Ex Wp H) _ (List.mem_singleton.2 rfl)

/-- At a call below 8 the layout's key is the library's. -/
theorem layLay_K (fs : Forest.Shape) (lm first ns : Nat) (μ : JLay ns tl nr nc → Cb.Gl.E)
    (c : Fin 8) (X : Nat) :
    (layLay p fs lm first ns tl nr nc).K () μ c.val X =
      keyVec (scl := Road.sclOf p.h p.sc p.g 4) DF (cellsOf DF (cellsAt p.y (matsOfE μ)))
        Inst.Model.tbRef (4 * p.g) (fun l => layerR ppref kRef (wOfE μ) (4 * p.g + l)) c X := by
  show (if hc : c.val < 8 then _ else _) = _
  rw [dif_pos c.isLt]

/-- **THE BASE JOINT IN FRONT OF THE BLOCK, UNFOLDED.** -/
theorem lay_says (a : Unit × Ex.Str) (w : (laySg x D rad oW).Msg × Wp) :
    ((kLookupCR [layRider x p tl D rad oW wOf nr nc Ex Wp]).A
        (layRider x p tl D rad oW wOf nr nc Ex Wp)).relR a w ↔
      (∀ k < x.fs.NC, ∀ b < 2 ^ Cb.LdLkp.Port.nOf x.fs k, ∃ u < 2 ^ Cb.LdLkp.Port.kOf x.fs k,
        (layLay p x.fs x.lm x.F.next x.ns tl nr nc).K () (msgLay x tl D rad oW wOf nr nc w.1) k b =
          ((FoNums.tauN x.fs k u : ℕ) : Cb.Gl.E)) ∧
      ∀ (emb : ℕ → ℕ → Cb.Gl.E) (tok : ℕ → ℕ) (first : Bool) (l i : ℕ),
        (Idn.j10 l i).Valid DF first →
          idnVal (scl := Road.sclOf p.h p.sc p.g 4) DF (layCells x p tl D rad oW wOf nr nc w.1) emb
            tok (.j10 l i) = 0 := by
  have e := crHot_src (scl := Road.sclOf p.h p.sc p.g 4)
    (layCaller x p tl D rad oW wOf nr nc Ex Wp) DF
    (fun _ m => layCells x p tl D rad oW wOf nr nc m) w.1 a
  constructor
  · intro h
    exact ⟨h.2, e.1 h.1.2⟩
  · intro h
    exact ⟨⟨trivial, e.2 h.2⟩, h.1⟩

/-! ### the two named readings, and the two clauses -/

/-- **THE NAMED READING OF THE CELLS.** -/
def MatsAre (x : Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
    (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : Nat)
    (m : (laySg x D rad oW).Msg) (Mz : Mats ℤ) : Prop :=
  matsOfE (msgLay x tl D rad oW wOf nr nc m) = castM Mz

/-- **THE NAMED READING OF THE WEIGHTS**: the pin's. g: the group. -/
def WeightsAre (x : Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
    (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc g : Nat)
    (m : (laySg x D rad oW).Msg) (Wi : Mat) : Prop :=
  ∀ l, layerR ppref kRef (wOfE (msgLay x tl D rad oW wOf nr nc m)) (4 * g + l) =
    layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)

/-- **The reading of the cells is paid where the committed symbols are the packing of small
integers.** -/
theorem lay_mats_cast (m : (laySg x D rad oW).Msg)
    (Mz : ∀ μ : Fin (szOf tl).NM, Fin ((szOf tl).k μ) → Fin ((szOf tl).m μ) → ℤ)
    (B : BaseAt
      (symAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl (ownPart m)) Mz) :
    MatsAre x tl D rad oW wOf nr nc m (zsOf (szOf tl) Mz) := by
  funext a r c
  show msgLay x tl D rad oW wOf nr nc m (lyCell x.ns tl nr nc a r c) =
    ((zsOf (szOf tl) Mz a r c : ℤ) : Cb.Gl.E)
  unfold lyCell cellJ zsOf
  by_cases h : a < (szOf tl).NM ∧ c < (szOf tl).k a ∧ r < (szOf tl).m a
  · rw [dif_pos h, dif_pos h]
    exact B.2.2 ⟨⟨_, h.1⟩, ⟨_, h.2.1⟩, ⟨_, h.2.2⟩⟩
  · rw [dif_neg h, dif_neg h]
    exact Int.cast_zero.symm

/-- **THE CLAUSE layKey**: the library's KeyField, at the integer matrices and the index's matrix of
the two readings. -/
theorem lay_layKey (H : LayOK set x) (a : Unit × Ex.Str) (w : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [layRider x p tl D rad oW wOf nr nc Ex Wp]).A
      (layRider x p tl D rad oW wOf nr nc Ex Wp)).relR a w)
    (Mz : Mats ℤ) (hM : MatsAre x tl D rad oW wOf nr nc w.1 Mz)
    (Wi : Mat) (hW : WeightsAre x tl D rad oW wOf nr nc p.g w.1 Wi) :
    KeyField p.h p.sc p.y p.g Mz Wi := by
  intro c X hX
  obtain ⟨u, hu, e⟩ := ((lay_says Ex Wp a w).1 h).1 c.val (by rw [H.eight]; exact c.isLt) X
    (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (H.sizes c)))
  rw [layLay_K, hM, show (fun l => layerR ppref kRef
      (wOfE (msgLay x tl D rad oW wOf nr nc w.1)) (4 * p.g + l)) =
    fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * p.g + l) from
      funext hW] at e
  obtain ⟨v, hv, ev⟩ := H.tabs c u hu
  exact ⟨v, hv, e.trans ev⟩

/-- **THE CLAUSE layHot**: the library's HotField. -/
theorem lay_layHot (a : Unit × Ex.Str) (w : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [layRider x p tl D rad oW wOf nr nc Ex Wp]).A
      (layRider x p tl D rad oW wOf nr nc Ex Wp)).relR a w)
    (Mz : Mats ℤ) (hM : MatsAre x tl D rad oW wOf nr nc w.1 Mz) (Wi : Mat) (xi : Cm.Seg.XI) :
    HotField p.h p.sc p.y p.g Mz Wi xi := by
  intro l i hv
  have e := ((lay_says Ex Wp a w).1 h).2
    (Inst.Model.FFSeg.embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX xi) _ l i hv
  unfold layCells at e
  rw [hM] at e
  exact e

end

end

#print axioms lay_good
#print axioms lay_says
#print axioms lay_mats_cast
#print axioms lay_layKey
#print axioms lay_layHot

end VerifiableInference.Desc.First.Look
