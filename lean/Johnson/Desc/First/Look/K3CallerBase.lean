-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerBase.lean: WHAT EVERY CLOSED CALLER OF THE PROVED LOOKUP BLOCK AT A
PLACE OF THE PROOF's FIRST CHAIN SHARES: the public data beside Verify.Public, the entries of a
link, the signature of the link's own oracle messages, the reading msg₀ of the entries off a tuple
of messages, the test that every address read resolves; and the premises of the lookup's lemma that
do not hang on the kind of place. Definitions (with code wherever a definition can have code) and
small theorems. NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

Main names.
  Sent: the chain's codes, the request's shape, the layout, and link by link arrayOf. THE RECORD
    Verify.Public DOES NOT HOLD THEM; they stand in the carried record (K3CallerOwn.lean).
  Place.arrays: the link's written list of arrays with its number of slots. findJ: the entry with an
    address, WITH CODE (the library's Fo.entryOf picks by choice). findJ_sound.
  laidHolds, laidIn, laidPlace, Seat, seatOf: address ↦ seat: ReqRows.addTerms | ReqRows.row
    (OnBytes/Iop/ReqRows.lean) read backwards: the map by which the link's closing turns its one
    equation into a row on oracle messages.
  messagesAt, lastMoment, sigList: the link's own oracle messages sent up to a moment, each with its
    radius: the list at which Johnson.Pack.sigOf is the caller's signature.
  Seat.Fits, Resolves: every address of a family has an entry, a seat, and the seat lies in its
    message's table.
  readAt, valAt, msgAt (msg₀), msgAt_of, msgAt_val, inTab_iff: GENERAL in the codes, the signature's
    list l and the map «seat» from addresses to seats; seatOf and sigList are one filling.
  quiet: the joint that says nothing. noRider: the empty family of riders.
  forIn_says: AT ANY CALLER, by unfolding alone: what the joint in front of the block says.
  shape_made: a yes of P.shape is the programs' two public tests. rounds_entries, meets_declared:
    written rounds that hold elements alone and have the entries of the block's own declared rounds
    meet the lookup's spec.

Limits. seatOf, laidPlace and sigList are A SECOND WRITING of the programs' maps, read off their
text; no theorem ties them to ReqRows.addTerms, laidTensor or ReqFrame.whereIs. OWN ARRAYS ALONE: a
cell of an array that an earlier link sent has no seat here. WHERE A READING FAILS msgAt IS 0: a
caller whose tables hold 0 needs Resolves, or its clause in front holds for nothing there. Two
addresses may share a seat: not shut here. rad (the radius of a message's list) is a letter: it
must be the radius at which the sending kind promises «no collision at the sample's seed» and at
which the closing kind tests proximity.
ROUTINES IN A CONTEXT: none is named. Plain records and pure functions of the programs' side that
are named: Verify.Public, Fork, Forest.Shape, Forest.shape, Forest.pubAsk, Params.ReqShape,
ReqLayout, ReqArray, LaidBlock, ReqMessage, OracleShape, Codes, reqArray, Plan.shapeOfFork.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.LookKind
import Johnson.Desc.First.Look.LookKindAgrees
import Johnson.Top.H.LookupCRide
import Johnson.Top.H.LookupCShape
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelT
import OnBytes.Tie.Pv.Plan.PlaceShape
import Johnson.Pack.PortF
import OnBytes.Iop.ReqRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)

/-! ## 1 The public side, with code -/

/-- **What the caller reads beside Verify.Public**: plain data. -/
structure Sent where
  /-- the first chain's codes -/
  codes : Codes
  /-- the request's shape: link by link the oracle messages, by moment -/
  shape : Params.ReqShape
  /-- the layout: link by link the arrays, each with its message and its blocks -/
  layout : Params.ReqLayout
  /-- link by link, for each array of the sub-proof's list: the link that sent it, its name there -/
  arrayOf : Array (Array (Nat × String))

/-- The link's written list of arrays, with its number of slots. -/
def Place.arrays (x : Place) : Road.Rows.Shape := Tie.Pv.Plan.shapeOfFork x.base x.ns

/-- The kind's parameter «first» is the place's next slot. -/
theorem first_eq (set : Params.Setting) (digits : Bool) (x : Place) :
    (P.ofPlace set digits x).first = x.F.next := rfl

/-- k as a member of Fin n, where it is one. -/
def finOf (n k : Nat) : Option (Fin n) := if h : k < n then some ⟨k, h⟩ else none

theorem finOf_some {n k : Nat} (h : k < n) : finOf n k = some ⟨k, h⟩ := dif_pos h

/-- **The entry with an address**, or none: with code. -/
def findJ (S : Road.Rows.Shape) : Addr → Option S.J
  | .cell t r c =>
    if ht : t < S.arrays.length then
      (finOf (S.arrays.get ⟨t, ht⟩).R r).bind fun r' =>
        (finOf (S.arrays.get ⟨t, ht⟩).K c).map fun c' => Sum.inl ⟨⟨t, ht⟩, r', c'⟩
    else none
  | .mask j => (finOf S.ns j).map Sum.inr

/-- The block holds element (i, c) of its array. -/
def laidHolds (b : Params.LaidBlock) (i c : Nat) : Bool :=
  decide (b.firstI ≤ i) && decide (i < b.firstI + 2 ^ b.bitsI) &&
    decide (b.firstC ≤ c) && decide (c < b.firstC + 2 ^ b.bitsC)

/-- Where the block lays element (i, c): (row, place) in its message's table: LaidBlock's own
docstring (OnBytes/Params/Items.lean), as a function. -/
def laidIn (b : Params.LaidBlock) (i c : Nat) : Nat × Nat :=
  let x := if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
    else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)
  (b.firstRow + x / 2 ^ b.placeBits, b.firstPlace + x % 2 ^ b.placeBits)

/-- Where element (i, c) of an array lies in its message's table. None: no block holds it. -/
def laidPlace (bs : List Params.LaidBlock) (i c : Nat) : Option (Nat × Nat) :=
  (bs.find? fun b => laidHolds b i c).map fun b => laidIn b i c

/-- A seat: an entry of an oracle message of the link. -/
structure Seat where
  /-- the message's number among its link's, from 0 -/
  msg : Nat
  /-- in the mask rows' table; else in the main rows' -/
  mask : Bool
  row : Nat
  place : Nat
  deriving DecidableEq, Repr

/-- Link i's oracle messages. -/
def messagesAt (D : Sent) (i : Nat) : List Params.ReqMessage :=
  ((D.shape.link[i]?).map (·.messages)).getD []

/-- **The seat of an address at link i.** None: the list has no such array; an earlier link sent it;
the layout has no array of the name; no block holds the cell; the link has no mask row. -/
def seatOf (D : Sent) (i : Nat) : Addr → Option Seat
  | .cell t r c =>
    ((D.arrayOf.getD i #[])[t]?).bind fun bn =>
      if bn.1 == i then
        (OnBytes.reqArray D.layout i bn.2).bind fun a =>
          (laidPlace a.blocks r c).map fun rp => ⟨a.message, false, rp.1, rp.2⟩
      else none
  | .mask j =>
    ((messagesAt D i).findIdx? fun x => x.shape.maskRows != 0).map fun m => ⟨m, true, 0, j⟩

/-- The link's last moment. -/
def lastMoment (D : Sent) (i : Nat) : Nat := (((messagesAt D i).getLast?).map (·.moment)).getD 0

/-- **The link's own oracle messages sent up to a moment**, each with its radius: a first stretch of
the link's list, so that a message keeps its number. -/
def sigList (D : Sent) (rad : OracleShape → Nat) (i mom : Nat) : List (OracleShape × Nat) :=
  ((messagesAt D i).takeWhile fun m => decide (m.moment ≤ mom)).map fun m => (m.shape, rad m.shape)

/-- The seat lies in its message's table. -/
def Seat.Fits (cs : Codes) (l : List (OracleShape × Nat)) (s : Seat) : Prop :=
  ∃ hk : s.msg < l.length,
    if s.mask = true then
      s.row < (l.get ⟨s.msg, hk⟩).1.maskRows ∧
        s.place < (Johnson.Pack.pMask cs (l.get ⟨s.msg, hk⟩).1).ell
    else
      s.row < (l.get ⟨s.msg, hk⟩).1.mainRows ∧
        s.place < (Johnson.Pack.pMain cs (l.get ⟨s.msg, hk⟩).1).ell

/-- **Every address of a family has an entry, a seat, and the seat lies in its table.** On public
data alone. -/
def Resolves (S : Road.Rows.Shape) (cs : Codes) (l : List (OracleShape × Nat))
    (seat : Addr → Option Seat) (Rd : Addr → Prop) : Prop :=
  ∀ a, Rd a → (findJ S a).isSome = true ∧ ∃ s, seat a = some s ∧ s.Fits cs l

theorem findJ_sound (S : Road.Rows.Shape) :
    ∀ (a : Addr) (j : S.J), findJ S a = some j → S.addr j = a
  | .cell t r c, j, h => by
    simp only [findJ] at h
    split at h
    · rename_i ht
      obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨c', hc, h⟩ := Option.map_eq_some_iff.1 h
      unfold finOf at hr hc
      split at hr
      · split at hc
        · obtain rfl := Option.some.inj hr
          obtain rfl := Option.some.inj hc
          subst h
          rfl
        · cases hc
      · cases hr
    · cases h
  | .mask s, j, h => by
    simp only [findJ] at h
    obtain ⟨s', hs, h⟩ := Option.map_eq_some_iff.1 h
    unfold finOf at hs
    split at hs
    · obtain rfl := Option.some.inj hs
      subst h
      rfl
    · cases hs

/-! ## 2 The reading of a tuple of messages -/

noncomputable section
open Johnson.Pack VerifiableInference.OnPublicFiles Cb.Fo

/-- An entry of the main rows' table of an oracle message of shape s. -/
def jMain (cs : Codes) (s : OracleShape) (r : Fin s.mainRows) (c : Fin (pMain cs s).ell) :
    (portCode cs s).J :=
  (Sum.inl (r, c) :
    (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell))

/-- An entry of its mask rows' table. -/
def jMask (cs : Codes) (s : OracleShape) (r : Fin s.maskRows) (c : Fin (pMask cs s).ell) :
    (portCode cs s).J :=
  (Sum.inr (r, c) :
    (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell))

/-- **What a tuple of messages holds at a seat**; none where the seat lies in no table. -/
def readAt (cs : Codes) (l : List (OracleShape × Nat)) (m : (sigOf cs l).Msg) (s : Seat) :
    Option Cb.Gl.E :=
  if hk : s.msg < l.length then
    if s.mask = true then
      (finOf (l.get ⟨s.msg, hk⟩).1.maskRows s.row).bind fun r =>
        (finOf (pMask cs (l.get ⟨s.msg, hk⟩).1).ell s.place).map fun c =>
          m (⟨s.msg, hk⟩ : Fin l.length) (jMask cs (l.get ⟨s.msg, hk⟩).1 r c)
    else
      (finOf (l.get ⟨s.msg, hk⟩).1.mainRows s.row).bind fun r =>
        (finOf (pMain cs (l.get ⟨s.msg, hk⟩).1).ell s.place).map fun c =>
          m (⟨s.msg, hk⟩ : Fin l.length) (jMain cs (l.get ⟨s.msg, hk⟩).1 r c)
  else none

theorem readAt_some (cs : Codes) (l : List (OracleShape × Nat)) (s : Seat) (h : s.Fits cs l)
    (m : (sigOf cs l).Msg) : (readAt cs l m s).isSome = true := by
  obtain ⟨hk, h⟩ := h
  unfold readAt
  rw [dif_pos hk]
  split
  · rename_i hm
    rw [if_pos hm] at h
    rw [finOf_some h.1, finOf_some h.2]
    rfl
  · rename_i hm
    rw [if_neg hm] at h
    rw [finOf_some h.1, finOf_some h.2]
    rfl

section
variable (cs : Codes) (l : List (OracleShape × Nat)) (seat : Addr → Option Seat)

/-- **What the messages hold at an address.** cs: the codes. l: the signature's list. seat: where an
address lies in these messages. -/
def valAt (m : (sigOf cs l).Msg) (a : Addr) : Option Cb.Gl.E := (seat a).bind (readAt cs l m)

/-- **The caller's reading msg₀**: the entries of a written list of arrays, off the tuple of
messages. 0 AT THE ENTRY THAT IS NONE AND WHERE THE READING FAILS: Resolves shuts the second case.
-/
def msgAt (S : Road.Rows.Shape) (m : (sigOf cs l).Msg) : Option S.J → Cb.Gl.E
  | none => 0
  | some j => (valAt cs l seat m (S.addr j)).getD 0

theorem msgAt_of (S : Road.Rows.Shape) {a : Addr} {j : S.J} (h : findJ S a = some j)
    (m : (sigOf cs l).Msg) :
    msgAt cs l seat S m (findJ S a) = (valAt cs l seat m a).getD 0 := by
  rw [h]
  show (valAt cs l seat m (S.addr j)).getD 0 = _
  rw [findJ_sound S a j h]

/-- Under Resolves: the entry at a is what the messages hold at a's seat. -/
theorem msgAt_val {S : Road.Rows.Shape} {Rd : Addr → Prop} (hR : Resolves S cs l seat Rd)
    {a : Addr} (ha : Rd a) (m : (sigOf cs l).Msg) :
    valAt cs l seat m a = some (msgAt cs l seat S m (findJ S a)) := by
  obtain ⟨h1, s, h2, h3⟩ := hR a ha
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (readAt_some _ _ s h3 m)
  have e : valAt cs l seat m a = some v := by
    unfold valAt
    rw [h2]
    exact hv
  rw [msgAt_of cs l seat S hj m, e]
  rfl

/-- Under Resolves: «the entry at a is in the range table» says it of what the messages hold there.
-/
theorem inTab_iff {S : Road.Rows.Shape} {Rd : Addr → Prop} (hR : Resolves S cs l seat Rd)
    {a : Addr} (ha : Rd a) (q : Nat) (m : (sigOf cs l).Msg) :
    Cb.Rng.InTab q (msgAt cs l seat S m (findJ S a)) ↔
      ∃ v, valAt cs l seat m a = some v ∧ Cb.Rng.InTab q v := by
  rw [msgAt_val cs l seat hR ha m]
  exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨v', e', h⟩ => by
    obtain rfl := Option.some.inj e'
    exact h⟩

end

/-! ## 3 What every caller shares -/

/-- The joint that says nothing. -/
@[reducible] def quiet (Ex : Iop.ExtSpec) (M Wp : Type) : Iop.IOR.Rels Unit Unit Ex (M × Wp) :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩

/-- A caller with the empty family of riders. -/
@[reducible] def noRider (c : LookupCCaller) : LookupCRCaller :=
  ⟨c, Empty, fun e => e.elim, fun e => e.elim, fun e => e.elim⟩

/-- **What the joint in front of the block says, at any caller**: the caller's own joint, and: for
every call k and every key number b below 2^n_k there is a row u below 2^k_k of that call's table
with: the layout's key, a function of the entries that msg₀ reads off the committed messages, is the
table's row. -/
theorem forIn_says (c : LookupCCaller) (a : c.St₀ × c.Ex.Str) (w : c.Sg.Msg × c.Wp) :
    ((kLookupC [c]).A c).relR a w ↔
      c.R0.relR a w ∧ ∀ k < c.h.NC, ∀ b < 2 ^ Cb.LdLkp.Port.nOf c.h k,
        ∃ u < 2 ^ Cb.LdLkp.Port.kOf c.h k,
          c.L.K a.1 (c.msg₀ w.1) k b = ((FoNums.tauN c.h k u : ℕ) : Cb.Gl.E) :=
  Iff.rfl

/-- What a yes of P.shape is: the programs' two public tests. -/
theorem shape_made {p : P} {h : Forest.Shape} (e : p.shape = some h) :
    ∃ h₀, Forest.shape p.calls p.lid = .ok h₀ ∧ Forest.pubAsk h₀ p.pub = .ok () ∧
      h = { h₀ with pub := p.pub } := by
  rw [P.shape_older] at e
  split at e
  · rename_i h₀ hs
    split at e
    · rename_i hb
      refine ⟨h₀, hs, ?_, (Option.some.inj e).symm⟩
      cases hp : Forest.pubAsk h₀ p.pub with
      | ok u => rfl
      | error s =>
        rw [hp] at hb
        simp [Except.toBool] at hb
    · cases e
  · cases e

/-- The entries of the block's declared rounds are the planner's. -/
theorem rounds_entries (p : P) : p.rounds.map (·.entry) = p.entries.getD [] := by
  unfold P.rounds
  rw [List.map_map]
  exact List.map_id _

open Fo.Peel OnBytes.Maker OnBytes.Flat in
/-- **(c) The written rounds meet the lookup's spec**: for every list of written rounds that hold
elements alone (Plain) and whose entries are those of THE BLOCK's OWN DECLARED ROUNDS. -/
theorem meets_declared {p : P} {h : Forest.Shape} (hs : p.shape = some h) (hv : 1 ≤ h.v)
    (hN : 1 < h.NC) (hr : p.entries.isSome = true) (ds : List RDT)
    (hd : ∀ d ∈ ds, Fo.Peel.Plain (toRD d)) (he : ds.map (·.entry) = p.rounds.map (·.entry)) :
    List.Forall₂ MeetsT ds (Fo.specF h) := by
  obtain ⟨es, hes⟩ := Option.isSome_iff_exists.1 hr
  rw [rounds_entries, hes] at he
  unfold P.entries at hes
  rw [hs] at hes
  change lookEntries p.set h = some es at hes
  unfold lookEntries at hes
  split at hes
  · rename_i Pl hf
    obtain rfl := Option.some.inj hes
    have e : FoNums.several h = true := decide_eq_true hN
    refine meets_planT (s := p.set) (sc := .request) (P := Pl) h hv ?_ ds hd he
    rw [e]
    exact hf
  · cases hes

end

#print axioms findJ_sound
#print axioms readAt_some
#print axioms msgAt_of
#print axioms msgAt_val
#print axioms inTab_iff
#print axioms forIn_says
#print axioms shape_made
#print axioms rounds_entries
#print axioms meets_declared

end VerifiableInference.Desc.First.Look
