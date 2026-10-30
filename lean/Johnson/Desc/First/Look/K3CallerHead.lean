-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
head_says, head_rows, head_guests, head_tgt: that their premises can be met
together is shown at no record (HeadOK alone has been evaluated: see Limits).
Johnson/Desc/First/Look/K3CallerHead.lean: THE CALLER OF THE PROVED LOOKUP BLOCK, WITH ITS RIDERS,
AT THE LOOKUP ON THE CALLS OF THE OUTPUT HEAD's LINK of the proof's first chain, IN THE LETTERS OF
THE OUTPUT HEAD's KIND (K6); and from the joint in front of the block there to what that kind's law
BACK takes: «every place of every call's table is a row of the call's table in the verifier's
record» and CornerGuests. Definitions, statements and proofs. NO SOUNDNESS OF ANY TEXT THAT RUNS IS
CLAIMED.

OBJECT: no text that runs: the library's lookup block with riders, at a caller made of the public
  record's numbers at the head's link.
USER: Johnson/Desc/First/Look/K3CallerHeadParts.lean, K3CallerHeadTests.lean.
LETTERS: see Limits.
Compiled with the whole library.



Why. K6's law of the head meets the lookup BY THE CALL (Johnson/Desc/Kinds/HeadOutLaw.lean):
OUT: the value of call c's key vector is the multilinear extension, at the call's own key point, of
keyTable c: a table that the cells fix; BACK: if every place of every call's table is a row of the
call's lookup table, the key fields of its relations on cells hold. «OUT's conclusion ⇒ BACK's
premise» is K3's law. This file lays the caller at which the library's theorem says just that.

WHAT THE CALLER IS MADE OF. The frame is the layers' caller's (K3CallerLay.lean): h: the plan's
record; the entries JLay: the mask row's, every cell behind the committed symbols, the cells of the
committed matrix of weights; the signature laySg: the kept messages sent anew, the link's own of
moment 0, and one further member for the stored table; msg₀ := msgLay; R0 quiet. What differs:
 (1) St₀ := ℕ: THE REPLY's TOKEN THAT WAS HEARD. The head's keys read the token (the table of
     joints (Johnson/Desc/First/Borders.lean) has «lookCallsHeard» for it): a key may read no
     free part of the witness, so the token is a part of the STATEMENT in front: K6's class
     Token is filled from the state.
 (2) Lay.K st μ c i := rd (keyTable (cellsH adr μ) c (i / T) (i % T)): K6's OWN TABLE, read.
 (3) K6's CELLS ARE INTEGERS; THE BLOCK's ENTRIES ARE FIELD ELEMENTS. intOf x: the one integer
     below 2^18 in size whose cast x is; 0 where there is none (intOf_cast: it undoes the cast of
     such an integer). 2^18 IS THE BOUND OF K6's OWN PREMISE «small» (K06BackStatement;
     HeadParts.small | smallS) and of the integer model's clauses on smallness. SO «small» HOLDS OF
     THESE CELLS BY THEIR MAKE (intOf_small), AND SAYS NOTHING: WHERE AN ENTRY IS THE CAST OF NO
     SMALL INTEGER THE CELL IS A SILENT 0. What shuts that is the smallness test's clause (the
     committed symbols are the packing of small integers): it has to stand beside. FOR THE WEIGHTS,
     as K6's bound on them asks, the lift intW of the same make at size ≤ 2^12: its bound
     |Wh k v| ≤ 2^12 then holds by the make too (cellsH_small), and the question moves into «the
     claim on the weights is true» and the pin.
 (4) WHERE A CELL LIES: adr: PUBLIC DATA: for each of K6's four matrices (wide, act, row; the
     stream): (feature, position) ↦ (number in the sub-proof's list, row, column). The theorems hold
     at every adr. adrOf h L b IS THE LIBRARY's OWN MAP (Johnson/Road/HeadPlace.lean: placeIn |
     Hd.cellsH: the parts of hf from number 0 on, hd at NHf, hr at NHf + 1, the planes' matrix at
     NHf + 2, the stream at NHf + 3 through the border's record): adrOf_wide |
     _act | _row | _stream say so by rfl. THAT K6's NUMBERS OF FEATURES ARE THE LIBRARY's IS
     HELD BY NOBODY.
 (4') THE WEIGHTS (held at the text): A WEIGHT OF THE OUTPUT
     MATRIX STANDS IN TWO CELLS OF THE COMMITTED MATRIX: «two bytes, in the rows o_U + j and o_U +
     5,120 + j of column ι» (Inst/Model/Head/Trace.lean:199-203: Hof). An adr.wh that
     names ONE cell: no filling makes Wh the index's output matrix: A SILENT WRONG. Here Wh k v
     := intW (Hof (the weights off the entries) k v). Hof IS WRITTEN AT THE FULL SIZE: SO Wh SPEAKS
     OF THE FULL SIZE ALONE.
 (5) THE RIDERS: the two arrays t ↦ rd (clipAt | tableAt (the cells) (corner 0 t)) at the last lt
     places of zx (K3RiderTail.lean's tailIds; K3RiderK6.lean has the like at a fixed token).

Main names: intOf, intOf_cast · intW, intW_cast · cellsH_small · HeadAdr · adrOf · cellsH · headLay
· headCaller · allO · headClip | headTable · headArrs · headRider · sizesOf | policyOf | headAt |
headRiderAt (the letters filled from the public record, as Johnson/Stored/HeadSeatAt.lean fills
them) · HeadOK (premises on public data) · head_good · head_says · head_rows (the keys' half, in the
form that K6's tie of the tables takes) · head_guests (CornerGuests at the heard token) ·
head_tgt (the riders' clause BEHIND headRider's block is «K06OutStatement's two sums are 0»:
so K6's OUT meets THIS block, not another) · head_readsOnly · head_cells_cast | head_wh_cast (the
reading's lemmas).

Limits. Those of K3CallerLay.lean. LETTERS at headRiderAt: K6's class Request; the stored table's
message and its reading, with the matrix's two sizes; the chain's record D; the radius. THE KEYS'
HALF BEHIND THE BLOCK (K6's outCall's conclusion ⇒ the block's claim on the key vectors at this K)
IS STATED NOWHERE. No guard of the reading stands here for the cells that adr names (that they lie
inside the list's matrices): A SILENT 0 is possible there. EVALUATED, IN RUNS OUTSIDE THIS LIBRARY:
HeadOK's Bool (headB, K3CallerHeadTests.lean): yes at two stored plans at the floors 0, dT and
Head.keyFloor, and at the library's small example at Head.keyFloor; of HeadTabs' Bool the clauses
rowsOk and «k is bitsOf»: yes at two stored plans; its planOk: not known. THE PUBLIC FACTOR AND THE
COUNT OF PADDING are the plan's record's own (h.pub), not made of keyTable's columns: keyTable holds
the padding key at the columns that no entry takes, and nowhere else, while the format counts
further places as padding: soundness leans on neither; whether an honest prover's counts fit: not
spoken of. K6's files are imported as this library has them.

Not claimed: the soundness of any text that runs; anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerLay
import Johnson.Top.H.K3RiderK6
import Johnson.Desc.Kinds.HeadOutLaw
import Johnson.Road.HeadPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE OracleShape)
open OnBytes.Model (HTailF2)
open Norm (lt ls d S2 T)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look
open Cb.LdLkp (TX)

/-! ### integers off field elements -/

/-- The one integer below 2^18 in size whose cast x is; 0 where there is none. -/
noncomputable def intOf (x : Cb.Gl.E) : ℤ := by
  classical
  exact if h : ∃ z : ℤ, |z| < 2 ^ 18 ∧ ((z : ℤ) : Cb.Gl.E) = x then h.choose else 0

/-- Two integers below 2^18 in size with one cast are one. -/
theorem small_cast_inj {a b : ℤ} (ha : |a| < 2 ^ 18) (hb : |b| < 2 ^ 18)
    (e : ((a : ℤ) : Cb.Gl.E) = ((b : ℤ) : Cb.Gl.E)) : a = b := by
  have e2 : ((a - b : ℤ) : Cb.Gl.E) = 0 := by rw [Int.cast_sub, e, sub_self]
  have hd : ((Cb.Gl.p : ℕ) : ℤ) ∣ a - b := (CharP.intCast_eq_zero_iff Cb.Gl.E Cb.Gl.p _).1 e2
  have hp : ((Cb.Gl.p : ℕ) : ℤ) = 18446744069414584321 := by
    have h : Cb.Gl.p = 18446744069414584321 := Code.pGold_eq
    rw [h]
    norm_num
  rw [hp] at hd
  have h1 := abs_lt.1 ha
  have h2 := abs_lt.1 hb
  have h0 : a - b = 0 :=
    Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨by omega, by omega⟩)
  omega

/-- Whatever intOf returns is below 2^18 in size. -/
theorem intOf_small (x : Cb.Gl.E) : |intOf x| < 2 ^ 18 := by
  unfold intOf
  split
  · rename_i h
    exact h.choose_spec.1
  · norm_num

/-- **intOf undoes the cast of a small integer.** -/
theorem intOf_cast {z : ℤ} (hz : |z| < 2 ^ 18) : intOf ((z : ℤ) : Cb.Gl.E) = z := by
  have h : ∃ w : ℤ, |w| < 2 ^ 18 ∧ ((w : ℤ) : Cb.Gl.E) = ((z : ℤ) : Cb.Gl.E) := ⟨z, hz, rfl⟩
  unfold intOf
  rw [dif_pos h]
  exact small_cast_inj h.choose_spec.1 hz h.choose_spec.2

/-- The weights' lift (K6's bound on the weights asks it): the one integer of size at most
2^12 whose cast x is; 0 where there is none. -/
noncomputable def intW (x : Cb.Gl.E) : ℤ := by
  classical
  exact if h : ∃ z : ℤ, |z| ≤ 2 ^ 12 ∧ ((z : ℤ) : Cb.Gl.E) = x then h.choose else 0

/-- Whatever intW returns is of size at most 2^12. -/
theorem intW_small (x : Cb.Gl.E) : |intW x| ≤ 2 ^ 12 := by
  unfold intW
  split
  · rename_i h
    exact h.choose_spec.1
  · norm_num

/-- **intW undoes the cast of such an integer.** -/
theorem intW_cast {z : ℤ} (hz : |z| ≤ 2 ^ 12) : intW ((z : ℤ) : Cb.Gl.E) = z := by
  have h : ∃ w : ℤ, |w| ≤ 2 ^ 12 ∧ ((w : ℤ) : Cb.Gl.E) = ((z : ℤ) : Cb.Gl.E) := ⟨z, hz, rfl⟩
  unfold intW
  rw [dif_pos h]
  exact small_cast_inj (lt_of_le_of_lt h.choose_spec.1 (by norm_num))
    (lt_of_le_of_lt hz (by norm_num)) h.choose_spec.2

/-! ### the cells, off the entries -/

/-- **WHERE A CELL LIES**: public data; a letter. -/
structure HeadAdr where
  /-- (matrix, feature, position) ↦ (number in the sub-proof's list, row, column) -/
  cell : Matrix → ℕ → ℕ → ℕ × ℕ × ℕ
  /-- the like for the stream behind the last layer -/
  stream : ℕ → ℕ → ℕ × ℕ × ℕ
  /-- the number in the list of the matrix that holds the lookup's planes -/
  iB : ℕ

/-- **K6's record of cells, off the caller's entries.** -/
noncomputable def cellsH {ns : ℕ} {tl : HTailF2} {nr nc : ℕ} (adr : HeadAdr)
    (μ : JLay ns tl nr nc → Cb.Gl.E) : NCells where
  cell := fun M f t =>
    intOf (matsOfE μ (adr.cell M f t).1 (adr.cell M f t).2.1 (adr.cell M f t).2.2)
  Wh := fun k v => intW (Inst.Model.Head.Hof (wOfE μ) k v)
  stream := fun f t =>
    intOf (matsOfE μ (adr.stream f t).1 (adr.stream f t).2.1 (adr.stream f t).2.2)

/-- **«small», the stream's, and the weights' bound hold of these cells BY THEIR MAKE**: they say
nothing: see the head, (3). -/
theorem cellsH_small {ns : ℕ} {tl : HTailF2} {nr nc : ℕ} (adr : HeadAdr)
    (μ : JLay ns tl nr nc → Cb.Gl.E) :
    (∀ m f t, ((cellsH adr μ).cell m f t).natAbs < 2 ^ 18) ∧
      (∀ f t, ((cellsH adr μ).stream f t).natAbs < 2 ^ 18) ∧
      ∀ k v, ((cellsH adr μ).Wh k v).natAbs ≤ 2 ^ 12 := by
  refine ⟨fun m f t => ?_, fun f t => ?_, fun k v => ?_⟩
  · have h := abs_lt.1 (intOf_small
      (matsOfE μ (adr.cell m f t).1 (adr.cell m f t).2.1 (adr.cell m f t).2.2))
    show (intOf _).natAbs < 2 ^ 18
    omega
  · have h := abs_lt.1 (intOf_small
      (matsOfE μ (adr.stream f t).1 (adr.stream f t).2.1 (adr.stream f t).2.2))
    show (intOf _).natAbs < 2 ^ 18
    omega
  · have h := abs_le.1 (intW_small (Inst.Model.Head.Hof (wOfE μ) k v))
    show (intW _).natAbs ≤ 2 ^ 12
    omega

/-- **The library's own map of the head's cells.** h, L, b: the public record's numbers of the
head's sub-proof, its layout, and what it reads of the stream's matrix. -/
def adrOf (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) : HeadAdr where
  cell := fun M φ i =>
    match M with
    | .wide => (0 + φ / (L.m / h.T) / L.k, φ % (L.m / h.T) * h.T + i, φ / (L.m / h.T) % L.k)
    | .act =>
      (h.NHf + φ / (L.mD / h.T) / L.kD, φ % (L.mD / h.T) * h.T + i, φ / (L.mD / h.T) % L.kD)
    | .row =>
      (h.NHf + 1 + φ / (L.mR / h.T) / L.kR, φ % (L.mR / h.T) * h.T + i,
        φ / (L.mR / h.T) % L.kR)
  stream := fun φ i =>
    (h.NHf + 3 + b.cell (φ / h.d) (φ % h.d) / (b.mxb / h.T) / b.kxb,
      b.cell (φ / h.d) (φ % h.d) % (b.mxb / h.T) * h.T + i,
      b.cell (φ / h.d) (φ % h.d) / (b.mxb / h.T) % b.kxb)
  iB := h.NHf + 2

section AdrOf
variable {ns : ℕ} {tl : HTailF2} {nr nc : ℕ} (h : OnBytes.Model.Head.Shape)
  (L : OnBytes.Model.Head.HL) (b : OnBytes.Model.Head.Border) (μ : JLay ns tl nr nc → Cb.Gl.E)

/-- At adrOf K6's cells are the integers of the library's Hd.cellsH. -/
theorem adrOf_wide (φ i : ℕ) : (cellsH (adrOf h L b) μ).cell .wide φ i =
    intOf ((OnBytes.Road.Hd.cellsH h L b (matsOfE μ)).hf φ i) := rfl
theorem adrOf_act (φ i : ℕ) : (cellsH (adrOf h L b) μ).cell .act φ i =
    intOf ((OnBytes.Road.Hd.cellsH h L b (matsOfE μ)).hd φ i) := rfl
theorem adrOf_row (φ i : ℕ) : (cellsH (adrOf h L b) μ).cell .row φ i =
    intOf ((OnBytes.Road.Hd.cellsH h L b (matsOfE μ)).hr φ i) := rfl
theorem adrOf_stream (φ i : ℕ) : (cellsH (adrOf h L b) μ).stream φ i =
    intOf ((OnBytes.Road.Hd.cellsH h L b (matsOfE μ)).x φ i) := rfl

end AdrOf

/-- K6's sizes and policy, of the public record's numbers of the head's sub-proof: its own
filling (Johnson/Stored/HeadSeatAt.lean), with h.ls written out as h.la - h.lt. -/
@[reducible] def sizesOf (h : OnBytes.Model.Head.Shape) : Sizes :=
  { lt := h.lt, ls := h.la - h.lt, d := h.d, MF := h.MF, KF := h.KF, epsF := h.epsF, V := h.V,
    sh := h.digSh, F := h.famF }

@[reducible] def policyOf (h : OnBytes.Model.Head.Shape) : Policy :=
  { C := h.clipC, theta := h.theta, cap := h.cap }

/-- The place of the lookup on the head's link's calls, with the record that the kind's own
parameters make in the place of the plan's. -/
def headAt (X : OnBytes.Model.Verify.Public) : Option First.Look.Place :=
  (lookAt X ((if X.p4 then 2 else 1) * X.NGr) false).bind fun x =>
    (P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x).shape.map fun h => { x with fs := h }

variable [Sizes] [Policy] [Request]

/-- **The layout of the lookup on the head's link's calls.** The state: the token that was heard. -/
noncomputable def headLay (adr : HeadAdr) (fs : OnBytes.Model.Forest.Shape) (lm first ns : ℕ)
    (tl : HTailF2)
    (nr nc : ℕ) : Cb.Fo.Lay Cb.Gl.E ℕ (JLay ns tl nr nc) where
  K := fun y μ c i =>
    letI : Token := ⟨y⟩
    rd (keyTable (cellsH adr μ) c (i / T) (i % T))
  bc := fun t c j =>
    lyCell ns tl nr nc adr.iB (FoNums.cellRC fs lm (t, c, j)).1 (FoNums.cellRC fs lm (t, c, j)).2
  mkS := fun s => lyMask ns tl nr nc (first + s)

section
variable (adr : HeadAdr) (x : First.Look.Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
  (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (Ex : Iop.ExtSpec)
  (Wp : Type)

/-- **THE CALLER OF THE LOOKUP ON THE HEAD's LINK's CALLS.** -/
@[reducible] noncomputable def headCaller : LookupCCaller where
  h := x.fs
  St₀ := ℕ
  J₀ := JLay x.ns tl nr nc
  finJ := inferInstance
  decJ := inferInstance
  L := headLay adr x.fs x.lm x.F.next x.ns tl nr nc
  Ex := Ex
  Kc := Unit
  Wp := Wp
  Sg := laySg x D rad oW
  R0 := ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩
  msg₀ := msgLay x tl D rad oW wOf nr nc

/-- K6's cells, off the tuple of messages. -/
noncomputable def headCells (m : (laySg x D rad oW).Msg) : NCells :=
  cellsH adr (msgLay x tl D rad oW wOf nr nc m)

/-- All members of the signature: each stands sent when the shift is drawn. -/
def allO : List (laySg x D rad oW).O :=
  (none :: (List.finRange (sigListCalls D rad x.link).length).map some :
    List (Option (Fin (sigListCalls D rad x.link).length)))

/-- The guest clip's array, at the token that was heard. -/
noncomputable def headClip : ℕ → (laySg x D rad oW).Msg → ℕ → Cb.Gl.E := fun y m t =>
  letI : Token := ⟨y⟩
  rd (clipAt (headCells adr x tl D rad oW wOf nr nc m).toCells (corner 0 t))

/-- The guest table's. -/
noncomputable def headTable : ℕ → (laySg x D rad oW).Msg → ℕ → Cb.Gl.E := fun y m t =>
  letI : Token := ⟨y⟩
  rd (tableAt (headCells adr x tl D rad oW wOf nr nc m).toCells (corner 0 t))

/-- **The two guests' arrays.** Each names ALL the signature's members. -/
noncomputable def headArrs :
    List (List (laySg x D rad oW).O × (ℕ → (laySg x D rad oW).Msg → ℕ → Cb.Gl.E)) :=
  [(allO x D rad oW, headClip adr x tl D rad oW wOf nr nc),
    (allO x D rad oW, headTable adr x tl D rad oW wOf nr nc)]

/-- **THE SAME WITH ITS RIDERS.** -/
@[reducible] noncomputable def headRider : LookupCRCaller :=
  riderOf (headCaller adr x tl D rad oW wOf nr nc Ex Wp)
    (tailIds lt (headArrs adr x tl D rad oW wOf nr nc))

end

/-- **The same of the public record.** Left as letters: the request; the stored table's message and
its reading, with the matrix's two sizes; the chain's record; the radius. K6's floor there is
OnBytes.Model.Head.keyFloor X.hS. -/
noncomputable def headRiderAt (X : OnBytes.Model.Verify.Public) (R : Request) (D : Sent)
    (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
    (Ex : Iop.ExtSpec) (Wp : Type) : Option LookupCRCaller :=
  (headAt X).map fun x =>
    @headRider (sizesOf X.hS) (policyOf X.hS) R
      (adrOf X.hS X.HLy (OnBytes.Model.Verify.borderOf X.y)) x X.H.tl D rad oW wOf nr nc Ex Wp

/-- **What is asked of the public data at the head's link's calls**: just what the theorems below
spend. -/
structure HeadOK (set : OnBytes.Params.Setting) (x : First.Look.Place) (floor : ℕ) : Prop where
  /-- the kind's own parameters make the plan's record -/
  shape : (P.ofPlace set false x).shape = some x.fs
  /-- there are K6's six calls -/
  six : x.fs.NC = 6
  /-- a position's bits lie in the first part of the key point -/
  tail : lt ≤ x.fs.dT
  /-- each call has room for K6's table: its columns' bits and the positions' -/
  sizes : ∀ c, c < 6 → lJ floor (callKeys c) + lt ≤ Cb.LdLkp.Port.nOf x.fs c

section
variable {set : OnBytes.Params.Setting} {adr : HeadAdr} {x : First.Look.Place} {floor : ℕ}
  {tl : HTailF2} {D : Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E}
  {nr nc : ℕ} (Ex : Iop.ExtSpec) (Wp : Type)

/-- **The library's theorem applies**, and the list of bad challenges is the plain lookup's. -/
theorem head_good (H : HeadOK set x floor) :
    ((kLookupCR [headRider adr x tl D rad oW wOf nr nc Ex Wp]).toKind.block
        (headRider adr x tl D rad oW wOf nr nc Ex Wp)).Good ∧
      TWhole.errList ((kLookupCR [headRider adr x tl D rad oW wOf nr nc Ex Wp]).ε
          (headRider adr x tl D rad oW wOf nr nc Ex Wp)) =
        Cb.Fo.forEps (Fintype.card Cb.Gl.E) x.fs := by
  obtain ⟨h₀, a, b, e⟩ := shape_made H.shape
  have hok : FoNums.ok x.fs = true := by
    rw [e]
    exact Cb.Fo.shape_ok a b
  exact tail_good (c := headCaller adr x tl D rad oW wOf nr nc Ex Wp) lt
    (headArrs adr x tl D rad oW wOf nr nc) hok H.tail

/-- **THE BASE JOINT IN FRONT OF THE BLOCK, UNFOLDED.** -/
theorem head_says (a : ℕ × Ex.Str) (w : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [headRider adr x tl D rad oW wOf nr nc Ex Wp]).A
      (headRider adr x tl D rad oW wOf nr nc Ex Wp)).relR a w) :
    (∀ k < x.fs.NC, ∀ b < 2 ^ Cb.LdLkp.Port.nOf x.fs k, ∃ u < 2 ^ Cb.LdLkp.Port.kOf x.fs k,
      (headLay adr x.fs x.lm x.F.next x.ns tl nr nc).K a.1 (msgLay x tl D rad oW wOf nr nc w.1) k
        b = ((FoNums.tauN x.fs k u : ℕ) : Cb.Gl.E)) ∧
      (headRider adr x tl D rad oW wOf nr nc Ex Wp).src w.1 a :=
  ⟨h.2, h.1.2⟩

/-- **THE KEYS' HALF**: at the token that was heard: every place of every call's table, read, is a
row of that call's table in the verifier's record: the form that K6's tie of the tables takes.
-/
theorem head_rows (H : HeadOK set x floor) (a : ℕ × Ex.Str) (w : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [headRider adr x tl D rad oW wOf nr nc Ex Wp]).A
      (headRider adr x tl D rad oW wOf nr nc Ex Wp)).relR a w) :
    letI : Token := ⟨a.1⟩
    ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
      ∃ u < 2 ^ Cb.LdLkp.Port.kOf x.fs call,
        rd (keyTable (headCells adr x tl D rad oW wOf nr nc w.1) call col t) =
          ((FoNums.tauN x.fs call u : ℕ) : Cb.Gl.E) := by
  letI : Token := ⟨a.1⟩
  intro call hc col hcol t ht
  have hT : 0 < T := Nat.pos_of_ne_zero (by
    unfold T
    exact (Nat.pow_pos (by norm_num)).ne')
  have hb : col * T + t < 2 ^ Cb.LdLkp.Port.nOf x.fs call := by
    refine lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by norm_num) (H.sizes call hc))
    rw [Nat.pow_add]
    have h1 : col * T + t < (col + 1) * T := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left ht _
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ hcol)
  obtain ⟨u, hu, e⟩ := (head_says Ex Wp a w h).1 call (by rw [H.six]; exact hc) _ hb
  refine ⟨u, hu, ?_⟩
  have e1 : (col * T + t) / T = col := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt ht, Nat.zero_add]
  have e2 : (col * T + t) % T = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  have e3 : rd (keyTable (headCells adr x tl D rad oW wOf nr nc w.1) call
      ((col * T + t) / T) ((col * T + t) % T)) = ((FoNums.tauN x.fs call u : ℕ) : Cb.Gl.E) := e
  rw [e1, e2] at e3
  exact e3

/-- **THE GUESTS' HALF**: K6's CornerGuests, at the token that was heard. -/
theorem head_guests (a : ℕ × Ex.Str) (w : (laySg x D rad oW).Msg × Wp)
    (h : ((kLookupCR [headRider adr x tl D rad oW wOf nr nc Ex Wp]).A
      (headRider adr x tl D rad oW wOf nr nc Ex Wp)).relR a w) :
    letI : Token := ⟨a.1⟩
    CornerGuests (headCells adr x tl D rad oW wOf nr nc w.1).toCells := by
  letI : Token := ⟨a.1⟩
  intro t ht
  have hs := (tail_src (c := headCaller adr x tl D rad oW wOf nr nc Ex Wp) lt
    (headArrs adr x tl D rad oW wOf nr nc) w.1 a).1 (head_says Ex Wp a w h).2
  have h1 := hs (allO x D rad oW, headClip adr x tl D rad oW wOf nr nc) List.mem_cons_self t ht
  have h2 := hs (allO x D rad oW, headTable adr x tl D rad oW wOf nr nc)
    (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)) t ht
  exact ⟨(rd_zero_iff (okE_clipAt _ _)).1 h1, (rd_zero_iff (okE_tableAt _ _)).1 h2⟩

/-- **THE RIDERS' CLAUSE BEHIND headRider's BLOCK IS: K06OutStatement's TWO SUMS ARE 0**, at the
token in the state that the block hands on. (K3RiderK6.lean's k6_tgt stands at a
FIXED token: another block.) -/
theorem head_tgt (m : (laySg x D rad oW).Msg)
    (b : TX (ℕ × Cb.Gl.E) Cb.Gl.E (Option (JLay x.ns tl nr nc)) × Ex.Str) (zt : Point)
    (hz : zt.size = lt) (h : IsTail OnBytes.Model.Reading.gl zt b.1.2.1.pt x.fs.dT) :
    letI : Token := ⟨b.1.1.1⟩
    (headRider adr x tl D rad oW wOf nr nc Ex Wp).tgt m b ↔
      (∑ t < T, eq zt t *
          clipAt (headCells adr x tl D rad oW wOf nr nc m).toCells (corner 0 t)) = 0 ∧
        (∑ t < T, eq zt t *
          tableAt (headCells adr x tl D rad oW wOf nr nc m).toCells (corner 0 t)) = 0 := by
  letI : Token := ⟨b.1.1.1⟩
  refine (tail_tgt (c := headCaller adr x tl D rad oW wOf nr nc Ex Wp) lt
    (headArrs adr x tl D rad oW wOf nr nc) m b).trans ?_
  rw [← rd_zero_iff (okE_sumTo _ _), ← rd_zero_iff (okE_sumTo _ _), rd_outSum h hz,
    rd_outSum h hz]
  constructor
  · intro g
    have hc := g (allO x D rad oW, headClip adr x tl D rad oW wOf nr nc) List.mem_cons_self
    have ht := g (allO x D rad oW, headTable adr x tl D rad oW wOf nr nc)
      (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))
    exact ⟨hc, ht⟩
  · intro g y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact g.1
    · obtain rfl := List.mem_singleton.1 hy
      exact g.2

/-- The two guests read the named messages alone: they name all. -/
theorem head_readsOnly (g : ℕ → (laySg x D rad oW).Msg → ℕ → Cb.Gl.E) :
    (tailId (headCaller adr x tl D rad oW wOf nr nc Ex Wp) lt (allO x D rad oW) g).ReadsOnly :=
  fun _ m m' h => by
    have e : m = m' := funext fun a => h a (by
      cases a with
      | none => exact List.mem_cons_self
      | some k =>
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨k, List.mem_finRange k, rfl⟩))
    rw [e]

/-! ### the reading's lemmas -/

/-- **THE CELLS' READING**: where the matrices that msg₀ reads are the casts of integer matrices
below 2^18 in size (MatsAre: paid by lay_mats_cast from the smallness test's clause), K6's cells
ARE these integers at adr's places. -/
theorem head_cells_cast (m : (laySg x D rad oW).Msg) (Mz : OnBytes.Road.Mats ℤ)
    (hM : MatsAre x tl D rad oW wOf nr nc m Mz) (hs : ∀ a r c, |Mz a r c| < 2 ^ 18) :
    (∀ M f t, (headCells adr x tl D rad oW wOf nr nc m).cell M f t =
        Mz (adr.cell M f t).1 (adr.cell M f t).2.1 (adr.cell M f t).2.2) ∧
      ∀ f t, (headCells adr x tl D rad oW wOf nr nc m).stream f t =
        Mz (adr.stream f t).1 (adr.stream f t).2.1 (adr.stream f t).2.2 := by
  have hM' : matsOfE (msgLay x tl D rad oW wOf nr nc m) = OnBytes.Road.Rows.Norms.castM Mz := hM
  refine ⟨fun M f t => ?_, fun f t => ?_⟩
  · show intOf (matsOfE (msgLay x tl D rad oW wOf nr nc m) _ _ _) = _
    rw [hM']
    exact intOf_cast (hs _ _ _)
  · show intOf (matsOfE (msgLay x tl D rad oW wOf nr nc m) _ _ _) = _
    rw [hM']
    exact intOf_cast (hs _ _ _)

/-- **THE WEIGHTS' READING**: a weight of the output matrix stands in TWO cells of the committed
matrix (two bytes: the library's Hof): where msg₀ reads these two as the casts of the index's, and
the weight is of size at most 2^12, K6's Wh IS the library's Hof of the index's matrix. -/
theorem head_wh_cast (m : (laySg x D rad oW).Msg) (Wi : Inst.Model.Mat) {k v : ℕ}
    (h1 : wOfE (msgLay x tl D rad oW wOf nr nc m) (Inst.Model.Head.oH + k) v =
      ((Wi (Inst.Model.Head.oH + k) v : ℤ) : Cb.Gl.E))
    (h2 : wOfE (msgLay x tl D rad oW wOf nr nc m) (Inst.Model.Head.oH + 5120 + k) v =
      ((Wi (Inst.Model.Head.oH + 5120 + k) v : ℤ) : Cb.Gl.E))
    (hb : |Inst.Model.Head.Hof Wi k v| ≤ 2 ^ 12) :
    (headCells adr x tl D rad oW wOf nr nc m).Wh k v = Inst.Model.Head.Hof Wi k v := by
  show intW (Inst.Model.Head.Hof (wOfE (msgLay x tl D rad oW wOf nr nc m)) k v) = _
  have e : Inst.Model.Head.Hof (wOfE (msgLay x tl D rad oW wOf nr nc m)) k v =
      ((Inst.Model.Head.Hof Wi k v : ℤ) : Cb.Gl.E) := by
    unfold Inst.Model.Head.Hof
    rw [h1, h2]
    push_cast
    rfl
  rw [e]
  exact intW_cast hb

end

#print axioms intOf_small
#print axioms intOf_cast
#print axioms intW_cast
#print axioms cellsH_small
#print axioms adrOf_stream
#print axioms head_good
#print axioms head_says
#print axioms head_rows
#print axioms head_guests
#print axioms head_tgt
#print axioms head_readsOnly
#print axioms head_cells_cast
#print axioms head_wh_cast

end VerifiableInference.Desc.Kinds.Head.Law
