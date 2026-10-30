-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerAtt.lean: THE CLOSED CALLER OF THE PROVED LOOKUP BLOCK, WITH ITS
RIDER, AT THE LOOKUP ON THE CALLS OF AN ATTENTION LINK of the proof's first chain. Definitions (with
code wherever a definition can have code), two premises of the lookup's lemma at that caller, each a
theorem, and the lemma that unfolds what the joint in front of the block then says. NO SOUNDNESS OF
ANY TEXT THAT RUNS IS CLAIMED.

Why. The library proves its lookup block knowledge sound «whoever calls it». At a made-up caller the
theorem speaks of nothing that was committed.
Johnson/Desc/First/Look/K3Caller.lean has the first
closed caller, at the lookup on the digits of a link's smallness test, without riders. This file has
the second: at the lookup on a link's CALLS, where a key is a function of many cells and where
another kind's identity rides on the lookup's point. The common definitions are those of
Johnson/Desc/First/Look/K3CallerBase.lean.

WHY ATTENTION FIRST. At a layers' link and at the head the keys hold products with the weights
(Inst/Model/FF/Trace.lean: keyVec D t tb L0 w; Johnson/Road/HeadCallLib.lean: kvOf c z np t H y),
which are committed in the stored table, not in the first chain's messages. Attention's four key
vectors read cells alone.

What each field is, and of which public data.
  h     the plan's record of the lookup on the calls, x.fs. AttOK.shape asks that it is the record
        that the kind's own parameters make (P.shape).
  St₀   Unit: neither the key vectors nor the rider's array reads the state.
  J₀    JAtt: the entries of the link's mask row; EVERY CELL BEHIND THE COMMITTED SYMBOLS of the
        smallness test's list of matrices (Cb.Pv.Tail.JCell at the record tl's sizes); one more,
        read as 0.
  L.K   the library's four vectors of looked-up values of an attention segment
        (Inst.Model.AttSeg.keyVec), at the sizes, the scales and the table functions that
        Johnson/Road/Lane5AttDef.lean makes of the verifier's plain record of the shape (dimOf,
        sclOf, tbOf), at the cells that its rule of addresses names (addrA).
  L.bc  the bits of the counts: cells of the matrix bA (number NAs + 2 of the list), at the row and
        column of FoNums.cellRC at the plan's lm.
  L.mkS the mask row's entries from the lookup's first slot on.
  Sg    Johnson.Pack.sigOf at the chain's codes and THE ORACLE MESSAGES THAT STAND SENT WHEN THE
        SHIFT IS DRAWN: the kept messages of earlier links, sent anew in the link's first prover's
        message, then the link's own of moment 0 (sigListCalls). The message from which the forms'
        values are read (a later moment's) IS NO MEMBER: so neither a key nor the rider's array can
        read it, BY TYPE.
  msg₀  a mask entry: read off the link's first message with a mask row. A CELL: THE ONE UNPACKING
        OF THE COMMITTED SYMBOLS (Cb.Pv.Tail.cellValS), the symbols read off the messages at the
        seats of the matrices' symbol arrays (symAt, after the library's symLay).
  R0    the joint that says nothing (quiet).
  ι, g, sel, f   the library's crDen (Johnson/Top/H/LookupCRModel.lean): one member: identity at3,
        «the denominator is the row's sum», on the cube (piece | head | position), at the pick
        selAtt of the key point of call 2.

LETTERS LEFT, AND WHOSE THEY ARE: D : Sent and rad, as in K3Caller.lean's head; Ex, Wp: the rule's.
S and tl are fields of the public record at an attention link (attCallerAt).

WHAT THE JOINT IN FRONT THEN SAYS (att_says). Every key of every call, computed by the library's
formulas from the cells behind the symbols that these messages hold, is a row of that call's table
in the verifier's record; and at every piece, head and position the denominator is the sum of the
row's weights. Nothing else: R0 is quiet.

Limits.
(1) addrA, keyVec, dimOf, sclOf and tbOf are the library's; that they are what THE PROGRAMS lay is
shown by no theorem: Lane5AttDef.lean: the rule of addresses «is written here by a reading of these
texts»; the relation can be what the verifier's calls are there to show only at a shape with one
shift, ldh = 7 and kFD = 16. Johnson/Road/Rows/AttCalls.lean: «that the programs lay their keys as
the library's vector of looked-up values does is not said here».
(2) seatCalls, sigListCalls and symAt are A SECOND WRITING of the programs' maps (ReqRows.addTerms,
ReqFrame.whereIs, ReqFrame.first; HostLay.lean's symLay), read off their text; no theorem ties them.
A KEPT CELL's SEAT is taken by the born array's own blocks; the program lays it by the kept
message's numbers of bits: AttReadsOK.keptSame asks that a kept message has the shape of the message
whose rows it took. THAT A KEPT MESSAGE HOLDS WHAT THE BORN MESSAGE HELD is the code switch's
promise, not said here.
(3) THE CELLS ARE cellValS: 0 WHERE A COLUMN OF SYMBOLS IS THE PACKING OF NOTHING SMALL. That the
symbols are packings of small integers (Cb.Pv.Tail.Base) is the smallness test's clause and rides
beside this block; without it the joint in front speaks of zeros there.
(4) WHERE A READING FAILS A SYMBOL OR A MASK ENTRY IS 0: AttReadsOK (seated, cellsIn, keptSame,
sampled) shuts that: premises on public data, spent by no theorem on the joints, EVALUATED NOWHERE.
(5) AttOK's fields are premises on public data: `attOKB` has them as one Bool, with a theorem
(`attOK_of_yes`, Johnson/Desc/First/Att/K05PublicB.lean).
(6) Debts of the rider that stand (Johnson/Top/H/K3HostLaw.lean): that
the verifier's form at true
reads is worth the identity (at attention it ends in no single claim and leans on the masked
sumcheck's law twice and on a batching element of attention's own); that the sent reads are the true
ones; RiderBites. R0 being quiet, the first empty use (the source rides in R0) is shut by the
definition; the second (the keys' clause gives the source) is not looked at.
(7) The words, the samples and the decoded witness: three readings that are nobody's yet, as in
K3Caller.lean's Limits (7).
(8) Nothing on the layers' links, the head, the key file.
ROUTINES IN A CONTEXT: none is named. Plain records and pure functions of the programs' side that
are named: Verify.Public, Attention.Shape, HTailF2, TMat, Forest.Shape, ReqGroup, KeptTarget,
reqGroups, keptOf, reqArray, and what K3CallerBase.lean names.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerBase
import Johnson.Desc.First.Look.Before
import Johnson.Top.H.LookupCRModel
import Johnson.Road.Lane5AttDef
import Johnson.Road.Rows.AttCalls
import OnBytes.Tie.Pv.Tail.SizeOf
import Cb.Pv.Tail.InLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr callsOf)
open Cb.Pv.Tail (JCell Syms cellValS)

/-! ## 1 What stands sent when the shift of the calls' lookup is drawn -/

/-- The kept oracle messages that are sent anew in link i's first prover's message. -/
def keptAt (D : Sent) (i : Nat) : List KeptTarget :=
  (((reqGroups D.shape)[i]?).map Params.keptOf).getD []

/-- For each of them, in their order: as what it was first sent: (link, number among its link's). -/
def bornAt (D : Sent) (i : Nat) : Array (Nat × Nat) :=
  (((reqGroups D.shape)[i]?).map (·.born)).getD #[]

/-- **The oracle messages that stand sent when the shift of link i's lookup on the calls is drawn**,
each with its radius: the kept ones, then the link's own of moment 0. -/
def sigListCalls (D : Sent) (rad : OracleShape → Nat) (i : Nat) : List (OracleShape × Nat) :=
  (keptAt D i).map (fun k => (k.shape, rad k.shape)) ++ sigList D rad i 0

/-- **The seat of an address at link i, in that list.** A cell of an array of the link's own: in its
message, behind the kept ones. A cell of an array that an earlier link sent: in the kept message
that took that message's rows, at the row and place that the born array's blocks give. -/
def seatCalls (D : Sent) (i : Nat) : Addr → Option Seat
  | .cell t r c =>
    ((D.arrayOf.getD i #[])[t]?).bind fun bn =>
      (OnBytes.reqArray D.layout bn.1 bn.2).bind fun a =>
        (laidPlace a.blocks r c).bind fun rp =>
          if bn.1 == i then some ⟨(keptAt D i).length + a.message, false, rp.1, rp.2⟩
          else ((bornAt D i).idxOf? (bn.1, a.message)).map fun k => ⟨k, false, rp.1, rp.2⟩
  | .mask j =>
    ((messagesAt D i).findIdx? fun x => x.shape.maskRows != 0).map fun m =>
      ⟨(keptAt D i).length + m, true, 0, j⟩

/-- Every address of a family has a seat, and the seat lies in its table. On public data alone. -/
def Seated (cs : Codes) (l : List (OracleShape × Nat)) (seat : Addr → Option Seat)
    (Rd : Addr → Prop) : Prop :=
  ∀ a, Rd a → ∃ s, seat a = some s ∧ s.Fits cs l

/-- What is kept from the front while a test holds is a first stretch of what the test keeps. -/
theorem filter_eq_takeWhile_append {α : Type} (p : α → Bool) :
    ∀ l : List α, ∃ r, l.filter p = l.takeWhile p ++ r
  | [] => ⟨[], rfl⟩
  | a :: l => by
    by_cases h : p a = true
    · obtain ⟨r, hr⟩ := filter_eq_takeWhile_append p l
      exact ⟨r, by
        rw [List.filter_cons_of_pos h, List.takeWhile_cons_of_pos h, hr, List.cons_append]⟩
    · exact ⟨(a :: l).filter p, by rw [List.takeWhile_cons_of_neg h, List.nil_append]⟩

theorem moment0 :
    (fun m : Params.ReqMessage => decide (m.moment ≤ 0)) = fun m => m.moment == 0 := by
  funext m
  by_cases h : m.moment = 0 <;> simp [h]

/-- **THE SIGNATURE's MESSAGES STAND IN THE LINK's FIRST PROVER's MESSAGE**, in their order, right
behind the message that carries the link before: as the list of
Johnson/Desc/First/Look/Before.lean has it (firstSend), of whose roots the block's field «before» at
the calls' lookup is made (beforeAt … false). g, link: the request's own group and link number i. -/
theorem sigCalls_firstSend (D : Sent) (rad : OracleShape → Nat) (i : Nat) (g : ReqGroup)
    (link : Params.ReqLink) (hg : (reqGroups D.shape)[i]? = some g)
    (hl : D.shape.link[i]? = some link) :
    ∃ r, (firstSend D.shape i g link.messages).map (·.shape) =
      (if 0 < i then [g.target.shape] else []) ++ (sigListCalls D rad i).map (·.1) ++ r := by
  obtain ⟨r0, hr0⟩ := filter_eq_takeWhile_append (fun m : Params.ReqMessage => m.moment == 0)
    link.messages
  have e1 : (sigListCalls D rad i).map (·.1) =
      (Params.keptOf g).map (·.shape) ++
        (link.messages.takeWhile fun m => m.moment == 0).map (·.shape) := by
    unfold sigListCalls keptAt sigList messagesAt
    rw [hg, hl, moment0]
    simp only [Option.map_some, Option.getD_some, List.map_append, List.map_map]
    rfl
  rw [e1]
  unfold firstSend
  rw [hr0]
  by_cases h0 : i = 0
  · subst h0
    exact ⟨r0.map (·.shape) ++ [(foldMaskNotice (ioppFoldShape
      ⟨D.shape.code, D.shape.maskCode, g.k, g.h⟩ {})).shape] ++ D.shape.atStart.map (·.shape), by
        simp [List.map_append, List.map_map, Function.comp_def, List.append_assoc]⟩
  · have hp : 0 < i := Nat.pos_of_ne_zero h0
    exact ⟨r0.map (·.shape) ++ [(foldMaskNotice (ioppFoldShape
      ⟨D.shape.code, D.shape.maskCode, g.k, g.h⟩ {})).shape], by
        simp [hp, h0, List.map_append, List.map_map, Function.comp_def, List.append_assoc]⟩

/-! ## 2 The entries: the mask row's, and the cells behind the committed symbols -/

/-- The smallness test's sizes at the plan's record. -/
abbrev szOf (tl : HTailF2) : Cb.Pv.Tail.Size := (OnBytes.Tie.Pv.Tail.sizeOf tl).size

/-- **The entries**: the mask row's ns; every cell of the list's matrices; one more, read as 0. -/
abbrev JAtt (ns : Nat) (tl : HTailF2) : Type := Option (Fin ns ⊕ JCell (szOf tl))

/-- The cell (matrix, row, column), where there is one. -/
def cellJ (s : Cb.Pv.Tail.Size) (a r c : Nat) : Option (JCell s) :=
  if h : a < s.NM ∧ c < s.k a ∧ r < s.m a then some ⟨⟨a, h.1⟩, ⟨c, h.2.1⟩, ⟨r, h.2.2⟩⟩ else none

/-- A cell as an entry. -/
def enCell (ns : Nat) (tl : HTailF2) (a r c : Nat) : JAtt ns tl :=
  (cellJ (szOf tl) a r c).map Sum.inr

/-- A mask entry as an entry. -/
def enMask (ns : Nat) (tl : HTailF2) (j : Nat) : JAtt ns tl := (finOf ns j).map Sum.inl

noncomputable section
open Johnson.Pack VerifiableInference.OnPublicFiles Cb.Fo Cb.Rider

section
variable (cs : Codes) (l : List (OracleShape × Nat)) (seat : Addr → Option Seat) (tl : HTailF2)

/-- **The committed symbols**, read off the messages: symbol (matrix, row of symbols, column) is
entry (row, column) of the matrix's symbol array (the library's symLay,
OnBytes/Tie/Pv/Tail/HostLay.lean). 0 WHERE THE READING FAILS. -/
def symAt (m : (sigOf cs l).Msg) : Syms Cb.Gl.E (szOf tl) := fun μ i' c =>
  (valAt cs l seat m (.cell (tl.gtTree.getD μ.val 0) i'.val c.val)).getD 0

/-- **The caller's reading msg₀.** A cell is the one unpacking of the committed symbols. -/
def msgAtt (ns : Nat) (m : (sigOf cs l).Msg) : JAtt ns tl → Cb.Gl.E
  | none => 0
  | some (.inl k) => (valAt cs l seat m (.mask k.val)).getD 0
  | some (.inr j) => cellValS (symAt cs l seat tl m) j

end

/-- **The cells of an attention segment, off the entries**: by the library's rule of addresses. -/
def rawOf (S : Attention.Shape) (ns : Nat) (tl : HTailF2) (μ : JAtt ns tl → Cb.Gl.E)
    (x : Inst.Model.AttSeg.Raw) : Cb.Gl.E :=
  μ (enCell ns tl (Road.L5.addrA S x).1 (Road.L5.addrA S x).2.1 (Road.L5.addrA S x).2.2)

/-! ## 3 The layout, the caller, the rider -/

/-- **The layout of the lookup on an attention link's calls.** -/
def attLay (S : Attention.Shape) (h : Forest.Shape) (lm first ns : Nat) (tl : HTailF2) :
    Cb.Fo.Lay Cb.Gl.E Unit (JAtt ns tl) where
  K := fun _ μ c i =>
    if hc : c < 4 then
      Inst.Model.AttSeg.keyVec (scl := Road.L5.sclOf S) (Road.L5.dimOf S) (Road.L5.tbOf S)
        (rawOf S ns tl μ) ⟨c, hc⟩ i
    else 0
  bc := fun t c j =>
    enCell ns tl (S.cf.NAs + 2) (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2
  mkS := fun s => enMask ns tl (first + s)

/-- The signature. -/
abbrev attSg (x : Place) (D : Sent) (rad : OracleShape → Nat) : Cb.Sig Cb.Gl.E :=
  sigOf D.codes (sigListCalls D rad x.link)

/-- **THE CALLER OF THE LOOKUP ON AN ATTENTION LINK's CALLS**, at a place x with the verifier's
record S of the sub-proof's shape and the plan's record tl of the link's smallness test. -/
@[reducible] def attCaller (x : Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type) : LookupCCaller where
  h := x.fs
  St₀ := Unit
  J₀ := JAtt x.ns tl
  finJ := inferInstance
  decJ := inferInstance
  L := attLay S x.fs x.lm x.F.next x.ns tl
  Ex := Ex
  Kc := Unit
  Wp := Wp
  Sg := attSg x D rad
  R0 := quiet Ex _ Wp
  msg₀ := msgAtt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl x.ns

/-- The segment's cells, off the tuple of messages. -/
def attCells (x : Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (m : (attSg x D rad).Msg) : Inst.Model.AttSeg.Raw → Cb.Gl.E :=
  rawOf S x.ns tl (msgAtt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl x.ns m)

/-- **THE SAME WITH ITS RIDER**: the library's crDen, its letter «cells» filled. -/
@[reducible] def attRider (x : Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type) : LookupCRCaller :=
  crDen (attCaller x S tl D rad Ex Wp) (Road.L5.dimOf S) (callsOf x.fs)
    fun _ m => attCells x S tl D rad m

/-- **The same of the public record**: link i of X. None where link i is no attention link. -/
def attRiderAt (X : Verify.Public) (D : Sent) (rad : OracleShape → Nat) (i : Nat)
    (Ex : Iop.ExtSpec) (Wp : Type) : Option LookupCRCaller :=
  if X.p4 = true ∧ i % 2 = 1 then
    (lookAt X i false).bind fun x =>
      (X.A[i / 2]?).map fun a => attRider x a.S a.seam.tl D rad Ex Wp
  else none

/-! ## 4 The tests on public data -/

/-- The library's condition between the lookup's record and the segment's sizes, as a test. -/
def attFitsB (S : Attention.Shape) (h : Forest.Shape) : Bool :=
  decide (FoNums.nOf h 2 = (callsOf h).a 2 ∧ (callsOf h).Dk ≤ (callsOf h).a 2 ∧
    (callsOf h).e 2 ≤ (callsOf h).sg ∧ (Road.L5.dimOf S).lW ≤ (callsOf h).a 2 ∧
    (Road.L5.dimOf S).nb ≤ 2 ^ ((callsOf h).a 2 - (Road.L5.dimOf S).lW) ∧ 1 ≤ h.v)

theorem attFits_of {S : Attention.Shape} {h : Forest.Shape} (e : attFitsB S h = true) :
    AttFits h (Road.L5.dimOf S) (callsOf h) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := of_decide_eq_true e
  exact ⟨rfl, rfl, h1, h2, h3, h4, h5, h6⟩

/-- **The addresses that the caller's reading reads**: every symbol of every matrix of the list; the
mask entries of the lookup's own scalars. -/
inductive ReadsAtt (tl : HTailF2) (h : Forest.Shape) (first : Nat) : Addr → Prop
  | sym (μ : Fin (szOf tl).NM) (i' : Fin (Alg.symRows ((szOf tl).m μ))) (c : Fin ((szOf tl).k μ)) :
      ReadsAtt tl h first (.cell (tl.gtTree.getD μ.val 0) i'.val c.val)
  | mask (s : Nat) : s < FoNums.nMasks h → ReadsAtt tl h first (.mask (first + s))

/-- **What is asked of the public data at an attention link's calls**: JUST WHAT THE THEOREMS BELOW
SPEND. Each field is a test that a program can run; none reads a message, a witness or a transcript.
(The guards of the reading, AttReadsOK, are a record of their own,
which stands below.) -/
structure AttOK (set : Params.Setting) (x : Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) : Prop where
  /-- the kind's own parameters make the plan's record -/
  shape : (P.ofPlace set false x).shape = some x.fs
  /-- there are the library's four calls -/
  four : x.fs.NC = 4
  /-- the planes' packing fits the shape -/
  planes : (Forest.planeCols x.fs x.lm).toBool = true
  /-- the library's condition between the lookup's record and the segment's sizes -/
  fits : attFitsB S x.fs = true
  /-- the lookup's mask entries are entries of the mask row -/
  masksIn : x.F.next + FoNums.nMasks x.fs ≤ x.ns

/-- **What guards the caller's READING against a silent 0**: tests on public data that no theorem on
the joints spends: without them a symbol, a mask entry or a cell that has no seat is read as 0. -/
structure AttReadsOK (x : Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) : Prop where
  /-- every message of the signature has one answer to its sample -/
  sampled : ∀ o ∈ sigListCalls D rad x.link, o.1.answers = 1
  /-- a kept message has the shape of the message whose rows it took -/
  keptSame : ∀ k (hk : k < (keptAt D x.link).length),
    (((messagesAt D ((bornAt D x.link).getD k (0, 0)).1)[((bornAt D x.link).getD k (0, 0)).2]?).map
      (·.shape)) = some ((keptAt D x.link).get ⟨k, hk⟩).shape
  /-- every address that the reading reads has a seat, and the seat lies in its table -/
  seated : Seated D.codes (sigListCalls D rad x.link) (seatCalls D x.link)
    (ReadsAtt tl x.fs x.F.next)
  /-- every valid name of a cell has a cell of the list's matrices -/
  cellsIn : ∀ r : Inst.Model.AttSeg.Raw, r.Valid (Road.L5.dimOf S) →
    (cellJ (szOf tl) (Road.L5.addrA S r).1 (Road.L5.addrA S r).2.1
      (Road.L5.addrA S r).2.2).isSome = true

/-! ## 5 Two premises of the lookup's lemma, at the caller -/

section
variable {set : Params.Setting} {x : Place} {S : Attention.Shape} {tl : HTailF2} {D : Sent}
  {rad : OracleShape → Nat} (Ex : Iop.ExtSpec) (Wp : Type)

/-- **(a) The test on the public numbers.** -/
theorem att_ok (H : AttOK set x S tl D rad) :
    OkLookupC (callersCR [attRider x S tl D rad Ex Wp]) :=
  okLookupC_of_made fun c hc => by
    obtain rfl := List.mem_singleton.1 hc
    obtain ⟨h₀, a, b, e⟩ := shape_made H.shape
    exact ⟨_, _, h₀, _, a, b, e⟩

/-- **(b) The rider's choice is lawful.** -/
theorem att_sel (H : AttOK set x S tl D rad) : SelLookupCR [attRider x S tl D rad Ex Wp] :=
  fun r hr => by
    obtain rfl := List.mem_singleton.1 hr
    exact crDen_sel _ _ _ _ (attFits_of H.fits)

/-- **So the library's theorem applies**: the lookup with the rider, at this caller, has the
property of a block over the caller's signature. -/
theorem att_good (H : AttOK set x S tl D rad) :
    ((kLookupCR [attRider x S tl D rad Ex Wp]).toKind.block (attRider x S tl D rad Ex Wp)).Good :=
  lookupCR_good _ (att_ok Ex Wp H) (att_sel Ex Wp H) _ (List.mem_singleton.2 rfl)

open Fo.Peel OnBytes.Maker OnBytes.Flat in
/-- **(c) The written rounds meet the lookup's spec**: for every list of written rounds that hold
elements alone and whose entries are those of the block's own declared rounds. -/
theorem att_meets (H : AttOK set x S tl D rad)
    (hr : (P.ofPlace set false x).entries.isSome = true) (ds : List RDT)
    (hd : ∀ d ∈ ds, Fo.Peel.Plain (toRD d))
    (he : ds.map (·.entry) = (P.ofPlace set false x).rounds.map (·.entry)) :
    List.Forall₂ MeetsT ds (Fo.specF x.fs) :=
  meets_declared H.shape (attFits_of H.fits).v1
    (by
      rw [H.four]
      decide)
    hr ds hd he

/-- **(e) The two equations on the layout** that the law on the out-statement asks. -/
theorem att_mkS (s : Nat) :
    (attCaller x S tl D rad Ex Wp).L.mkS s = enMask x.ns tl (x.F.next + s) := rfl

theorem att_bc (t k j : Nat) :
    (attCaller x S tl D rad Ex Wp).L.bc t k j =
      enCell x.ns tl (S.cf.NAs + 2) (FoNums.cellRC x.fs x.lm (t, k, j)).1
        (FoNums.cellRC x.fs x.lm (t, k, j)).2 := rfl

/-- **(f) The planes' packing**: a yes of the program's own test is the two bounds. -/
theorem att_lm (H : AttOK set x S tl D rad) : 5 ≤ x.lm ∧ x.lm ≤ x.fs.kT + 5 := by
  have h := H.planes
  unfold Forest.planeCols at h
  split at h
  · simp [Except.toBool] at h
  · rename_i hn
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hn
    exact hn

/-! ## 6 What the joint in front says -/

/-- **THE BASE JOINT IN FRONT OF THE BLOCK, UNFOLDED.** Every key of every call, computed from the
cells behind the symbols that the messages hold, is a row of that call's table in the verifier's
record; and identity at3 is 0 at every valid index: the denominator is the row's sum. -/
theorem att_says (H : AttOK set x S tl D rad) (a : Unit × Ex.Str)
    (w : (attSg x D rad).Msg × Wp) :
    ((kLookupCR [attRider x S tl D rad Ex Wp]).A (attRider x S tl D rad Ex Wp)).relR a w ↔
      (∀ k < x.fs.NC, ∀ b < 2 ^ Cb.LdLkp.Port.nOf x.fs k, ∃ u < 2 ^ Cb.LdLkp.Port.kOf x.fs k,
        (attLay S x.fs x.lm x.F.next x.ns tl).K ()
            (msgAtt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl x.ns w.1) k b =
          ((FoNums.tauN x.fs k u : ℕ) : Cb.Gl.E)) ∧
      ∀ b g i, Inst.Model.AttSeg.Idn.Valid (Road.L5.dimOf S) (.at3 b g i) →
        Inst.Model.AttSeg.idnVal (Road.L5.dimOf S) (attCells x S tl D rad w.1) (.at3 b g i) =
          0 := by
  have e := crDen_src (attCaller x S tl D rad Ex Wp) (Road.L5.dimOf S) (callsOf x.fs)
    (fun _ m => attCells x S tl D rad m) (attFits_of H.fits) w.1 a
  constructor
  · intro h
    exact ⟨h.2, e.1 h.1.2⟩
  · intro h
    exact ⟨⟨trivial, e.2 h.2⟩, h.1⟩

/-- **THE JOINT IN FRONT OF THE BLOCK, OVER THE SIGNATURE**: every oracle message of the signature
decodes, with its own sample's seed and answers, to the message that the witness names (where one
decodes to nothing no witness meets the relation: it counts as false), and the base joint holds at
these messages. -/
theorem att_src_relR
    (a : (Unit × (attSg x D rad).Smp) × (Ex.prod (attSg x D rad).ext).Str)
    (w : (attSg x D rad).Wit × Wp) :
    ((kLookupCR [attRider x S tl D rad Ex Wp]).toKind.src (attRider x S tl D rad Ex Wp)).relR a w ↔
      (∀ k, (attSg x D rad).decs a.1.2 a.2.2 k = some (w.1 k).1) ∧
        ((kLookupCR [attRider x S tl D rad Ex Wp]).A (attRider x S tl D rad Ex Wp)).relR
          (a.1.1, a.2.1) ((attSg x D rad).msgs w.1, w.2) :=
  Iff.rfl

/-- **THE CONDITION IN FRONT**: no message has a collision at its sample's seed. -/
theorem att_src_on (a : (Unit × (attSg x D rad).Smp) × (Ex.prod (attSg x D rad).ext).Str) :
    ((kLookupCR [attRider x S tl D rad Ex Wp]).toKind.src (attRider x S tl D rad Ex Wp)).on a ↔
      (attSg x D rad).CF a.1.2 a.2.2 :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-! ### at3's places of the key point: public data, with code -/

/-- The cube's dimension: (piece | head | position). -/
def attG (x : Place) (S : Attention.Shape) : Nat :=
  (callsOf x.fs).a 2 - (Road.L5.dimOf S).lW + (Road.L5.dimOf S).lg + (Road.L5.dimOf S).lT

/-- The pick: variable t of the cube ↦ a place of the key point. -/
def attSel (x : Place) (S : Attention.Shape) (t : Nat) : Nat :=
  selAtt (callsOf x.fs).Dk (callsOf x.fs).sg ((callsOf x.fs).e 2)
    ((callsOf x.fs).a 2 - (Road.L5.dimOf S).lW) t

/-- At a call below 4 the layout's key is the library's. -/
theorem attLay_K (h : Forest.Shape) (lm first ns : Nat) (μ : JAtt ns tl → Cb.Gl.E) (c : Fin 4)
    (i : Nat) :
    (attLay S h lm first ns tl).K () μ c.val i =
      Inst.Model.AttSeg.keyVec (scl := Road.L5.sclOf S) (Road.L5.dimOf S) (Road.L5.tbOf S)
        (rawOf S ns tl μ) c i := by
  show (if hc : c.val < 4 then _ else _) = _
  rw [dif_pos c.isLt]

/-- **R0 does not hold the clauses**: it holds at every statement and witness. -/
theorem att_R0_quiet (a : Unit × Ex.Str) (w : (attSg x D rad).Msg × Wp) :
    (attCaller x S tl D rad Ex Wp).R0.relR a w := trivial

/-- **A cell that the caller reads is the unpacking of the committed symbols.** -/
theorem attCells_eq (H : AttReadsOK x S tl D rad) (m : (attSg x D rad).Msg)
    (r : Inst.Model.AttSeg.Raw) (hr : r.Valid (Road.L5.dimOf S)) :
    ∃ j : JCell (szOf tl),
      cellJ (szOf tl) (Road.L5.addrA S r).1 (Road.L5.addrA S r).2.1 (Road.L5.addrA S r).2.2 =
          some j ∧
        attCells x S tl D rad m r =
          cellValS (symAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl m) j := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 (H.cellsIn r hr)
  refine ⟨j, hj, ?_⟩
  unfold attCells rawOf enCell
  rw [hj]
  rfl

end

end

#print axioms attFits_of
#print axioms att_ok
#print axioms att_sel
#print axioms att_good
#print axioms sigCalls_firstSend
#print axioms att_meets
#print axioms att_lm
#print axioms att_src_relR
#print axioms att_src_on
#print axioms att_says
#print axioms attLay_K
#print axioms attCells_eq

end VerifiableInference.Desc.First.Look
