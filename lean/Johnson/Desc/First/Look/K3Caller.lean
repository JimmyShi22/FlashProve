-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3Caller.lean: THE CLOSED CALLER OF THE PROVED LOOKUP BLOCK AT A PLACE OF
THE PROOF's FIRST CHAIN: first member: the lookup on the digits of a link's smallness test, general
in the link, without riders. Definitions (with code wherever a definition can have code), the
premises of the lookup's lemma at that caller, each a theorem, and the lemma that unfolds what the
joint in front of the block then says. NO SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

Why. The library proves its lookup block knowledge sound «whoever calls it»: the caller is a record
of data (LookupCCaller, LookupCRCaller; Johnson/Top/H/LookupC.lean, LookupCRide.lean). At a made-up
caller every premise holds and the theorem speaks of nothing that was committed. Here the caller's
data are a sub-proof's own.

What each field is, and of which public data.
  h     the plan's record of the digits' lookup, tl.f9. DigOK.shape asks that it is the record that
        the kind's own parameters make (P.shape: Forest.shape, then Forest.pubAsk).
  St₀   Unit: without riders no term of the block reads the state.
  J₀    Option (x.arrays).J: every cell of the link's written list of arrays, every entry of its
        mask row (OnBytes.Road.Rows.Shape.J at Plan.shapeOfFork x.base x.ns), and one more, read as
        0.
  L     the library's layout of the digits' lookup (DgP.digL5) at the plan's tl; an address becomes
        an entry by findJ, WITH CODE (the library's Fo.entryOf picks by choice); the first slot is
        x.F.next, which is the kind's parameter first (first_eq).
  Sg    Johnson.Pack.sigOf at the chain's codes and the shapes of THE LINK's OWN ORACLE MESSAGES
        SENT BY THEN (sigList), each with a radius.
  msg₀  an entry of J₀, read off the tuple of messages: address ↦ seat (seatOf) ↦ the message's
        entry (readAt). seatOf is ReqRows.addTerms | ReqRows.row (OnBytes/Iop/ReqRows.lean) read
        backwards: the map by which the link's closing turns its one equation into a row on oracle
        messages: a cell (t, r, c) ↦ arrayOf[t] = (born, name) ↦ the layout's array ↦ its block ↦
        (message, row, place); mask j ↦ entry j of the one mask row of the link's first message that
        has a mask row.
  R0    THE JOINT THAT SAYS NOTHING (quiet): what rides beside the lookup goes by the rule of
        composition's own step for that. So R0 cannot hold the clause that the lookup is to show
        (Cb.Rider.forB_hollow's empty use is shut by the definition).
  Ex, Wp  letters: the oracles beside the block and the further witness are the rule's.
  Kc    Unit.
  ι     Empty (noRider).

LETTERS LEFT, AND WHOSE THEY ARE.
  D : Sent   the chain's codes, the request's shape, the layout, and link by link arrayOf. THE
        RECORD Verify.Public DOES NOT HOLD THEM. They are items of the first chain's parameter
        bytes and what declareLinks fills. They stand in the carried record; the condition «on» of
        the lemma must say that the record's own four are D's (OwnIs, K3CallerOwn.lean): else a
        made-up D meets all that is here.
  rad   the radius of an oracle message's list. NOT THIS FILE's: it must be the radius at
        which the sending kind promises «no collision at the sample's seed» and at which the closing
        kind tests proximity.

WHAT THE JOINT IN FRONT THEN SAYS (dig_src_relR, dig_plain), in three sentences. Every oracle
message of the link decodes, with its own sample's seed and answers, to the message that the witness
names (where one decodes to nothing, NO witness meets the relation: it counts as false). Every low
digit of the smallness test, read off that decoded message at the seat where the layout lays ZZ's
cell, is a number below 2^10, and every high digit is a number below 2^8. Nothing else is said: R0
is quiet and there is no rider.
THE CONDITION IN FRONT (dig_src_on): no oracle message of the link has a collision at the seed of
its sample (Sig.CF). THE SENDING BLOCKS' PROMISE MUST PAY IT; nothing here does.

Limits. (1) seatOf, laidPlace and sigList are A SECOND WRITING of the programs' maps, read off their
text; no theorem ties them to ReqRows.addTerms, laidTensor or ReqFrame.whereIs. (2) OWN ARRAYS
ALONE: a cell of an array that an earlier link sent has no seat here (the digits' two arrays are the
link's own, which Resolves then asks). (3) WHERE A READING FAILS msg₀ IS 0, AND 0 IS A ROW OF BOTH
DIGIT TABLES: so without Resolves (every address that the lookup reads has an entry, a seat, and the
seat lies in its message's table) the clause in front would hold for nothing. Resolves is a premise
on public data; it is shown at no value here. (4) DigOK's five fields are premises on public data:
at a real link each is a run. (5) That the messages of sigList are sent before the shift is drawn is
the block's field «before» (Before.lean) against the plan, not a theorem here. (6) sigOf's own
limits stand: one answer a message (DigOK.sampled asks it); a message without an answer is no lawful
member beyond unique decoding. By the text of Plan.takeGroup (OnBytes/Plan/ReqFrame.lean) every
message of a link, the first with the link's mask row among them, has the policy's number of
answers: so the link's mask row is sampled wherever that number is not 0 [read; no theorem]. (7) The
words of an oracle message (Sg.ext.Str), the samples (Sg.Smp) and the decoded witness (Sg.Wit) are
read off the rule's oracles, record and witness by three readings that are nobody's yet: not here.
(8) Two addresses may share a seat: not shut here. (9) Nothing on the calls' lookups, on riders, on
the key file's lookups.
ROUTINES IN A CONTEXT: none is named. Plain records and pure functions of the programs' side that
are named: Verify.Public, HTailF2, Fork, Forest.Shape, Forest.shape, Forest.pubAsk, Params.ReqShape,
ReqLayout, ReqArray, LaidBlock, ReqMessage, OracleShape, Codes, reqArray, Plan.shapeOfFork.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerBase
import Johnson.Desc.First.Look.Laid
import OnBytes.Tie.Pv.Lookup.Digits.PortEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)

/-! ## 1 The addresses that the lookup reads -/

/-- An array's entry as an address. -/
def addrOf (e : DgP.Ent3) : Addr := .cell e.1 e.2.1 e.2.2

/-- **The addresses that the digits' lookup reads**: the low and the high digits (ZZ), the bits of
the counts (BZ), the mask entries of the lookup's own scalars. -/
inductive ReadsDig (tl : HTailF2) (first : Nat) : Addr → Prop
  | low (i : DgP.Pl tl) : ReadsDig tl first (.cell tl.ix.ZZ i.2.val i.1.val)
  | high (i : DgP.Pl tl) : ReadsDig tl first (.cell tl.ix.ZZ i.2.val (tl.mz + i.1.val))
  | bit (t c j : Nat) : t < 2 ^ tl.f9.kT → c < tl.f9.NC → j < FoNums.planes →
      ReadsDig tl first (addrOf (DgP.bcP tl t c j))
  | mask (s : Nat) : s < FoNums.nMasks tl.f9 → ReadsDig tl first (.mask (first + s))

noncomputable section
open Johnson.Pack VerifiableInference.OnPublicFiles Cb.Fo

/-! ## 2 The caller -/

/-- How the digits' layout names an array's entry, and a mask entry. -/
def enOf (S : Road.Rows.Shape) (e : DgP.Ent3) : Option S.J := findJ S (addrOf e)
def mkOf (S : Road.Rows.Shape) (j : Nat) : Option S.J := findJ S (.mask j)

/-- The link's own oracle messages, all moments, each with its radius. -/
abbrev digList (x : Place) (D : Sent) (rad : OracleShape → Nat) : List (OracleShape × Nat) :=
  sigList D rad x.link (lastMoment D x.link)

/-- **The signature.** -/
abbrev digSg (x : Place) (D : Sent) (rad : OracleShape → Nat) : Cb.Sig Cb.Gl.E :=
  sigOf D.codes (digList x D rad)

/-- What the link's messages hold at an address. -/
abbrev digVal (x : Place) (D : Sent) (rad : OracleShape → Nat) (m : (digSg x D rad).Msg)
    (a : Addr) : Option Cb.Gl.E :=
  valAt D.codes (digList x D rad) (seatOf D x.link) m a

/-- **The reading msg₀.** -/
abbrev digMsg (x : Place) (D : Sent) (rad : OracleShape → Nat) (m : (digSg x D rad).Msg) :
    Option x.arrays.J → Cb.Gl.E :=
  msgAt D.codes (digList x D rad) (seatOf D x.link) x.arrays m

/-- **THE CALLER OF THE LOOKUP ON THE DIGITS**, at a place x with the plan's record tl of the link's
smallness test. -/
@[reducible] def digCaller (x : Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
    (Ex : Iop.ExtSpec) (Wp : Type) : LookupCCaller where
  h := tl.f9
  St₀ := Unit
  J₀ := Option x.arrays.J
  finJ := inferInstance
  decJ := inferInstance
  L := DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit
  Ex := Ex
  Kc := Unit
  Wp := Wp
  Sg := digSg x D rad
  R0 := quiet Ex _ Wp
  msg₀ := digMsg x D rad

/-- **The same of the public record**: link i of X. The record of the lookup inside tl is laid anew
as THE ONE THAT THE KIND's OWN PARAMETERS MAKE (P.shape), so that DigOK.shape holds by the making;
that it has the plan's own numbers is a test by a run, field by field (Forest.Shape has no decidable
equality). None where X has no such link or the programs' two public tests refuse. -/
def digCallerAt (X : Verify.Public) (D : Sent) (rad : OracleShape → Nat) (i : Nat)
    (Ex : Iop.ExtSpec) (Wp : Type) : Option LookupCCaller :=
  (lookAt X i true).bind fun x => (tlAt X i).bind fun tl =>
    (P.ofPlace (Params.settingOf X.P.frame) true x).shape.map fun h =>
      digCaller x { tl with f9 := h } D rad Ex Wp

/-! ## 3 The tests on public data -/

/-- **What is asked of the public data at a link's digits.** Each field is a test that a program can
run; none reads a message, a witness or a transcript. -/
structure DigOK (set : Params.Setting) (x : Place) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (pp : Nat) : Prop where
  /-- the kind's own parameters make the plan's record -/
  shape : (P.ofPlace set true x).shape = some tl.f9
  /-- the library's test on the smallness test's record -/
  tail : DgP.shapeTest2 tl pp = true
  /-- the planner makes the rounds -/
  rounds : (P.ofPlace set true x).entries.isSome = true
  /-- every message of the signature has one answer to its sample -/
  sampled : ∀ o ∈ digList x D rad, o.1.answers = 1
  /-- every address that the lookup reads has an entry, a seat, and the seat lies in its table -/
  resolves : Resolves x.arrays D.codes (digList x D rad) (seatOf D x.link) (ReadsDig tl x.F.next)

/-! ## 4 The premises of the lookup's lemma, at the caller -/

section
variable {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat}
  {pp : Nat} (Ex : Iop.ExtSpec) (Wp : Type)

/-- **(a) The test on the public numbers.** -/
theorem dig_ok (H : DigOK set x tl D rad pp) : OkLookupC [digCaller x tl D rad Ex Wp] :=
  okLookupC_of_made fun c hc => by
    obtain rfl := List.mem_singleton.1 hc
    obtain ⟨h₀, a, b, e⟩ := shape_made H.shape
    exact ⟨_, _, h₀, _, a, b, e⟩

theorem dig_okR (H : DigOK set x tl D rad pp) :
    OkLookupC (callersCR [noRider (digCaller x tl D rad Ex Wp)]) := dig_ok Ex Wp H

theorem dig_foOk (H : DigOK set x tl D rad pp) : FoNums.ok tl.f9 = true := by
  obtain ⟨h₀, a, b, e⟩ := shape_made H.shape
  rw [e]
  exact Cb.Fo.shape_ok a b

/-- **(b) The riders' choices**: none. -/
theorem dig_sel : SelLookupCR [noRider (digCaller x tl D rad Ex Wp)] := fun r hr => by
  obtain rfl := List.mem_singleton.1 hr
  exact fun e => Empty.elim e

/-- **(e) The two equations on the layout** that the law on the out-statement asks, at lm = 5. -/
theorem dig_mkS (s : Nat) :
    (digCaller x tl D rad Ex Wp).L.mkS s = mkOf x.arrays (x.F.next + s) := rfl

theorem dig_bc (t k j : Nat) :
    (digCaller x tl D rad Ex Wp).L.bc t k j =
      DgP.plV tl (enOf x.arrays) (FoNums.cellRC tl.f9 5 (t, k, j)).1
        (FoNums.cellRC tl.f9 5 (t, k, j)).2 :=
  DgP.digL5_cell (enOf x.arrays) (mkOf x.arrays) x.F.next Unit t k j

/-- **(f) The planes' packing**: lm = 5. -/
theorem dig_lm : 5 ≤ 5 ∧ 5 ≤ tl.f9.kT + 5 := ⟨le_refl 5, Nat.le_add_left 5 _⟩

end

open Fo.Peel OnBytes.Maker OnBytes.Flat in
/-- **(c) at the digits.** The record's v is at least 1 by the test on the public numbers; the
smallness test has two calls. -/
theorem dig_meets {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} {pp : Nat} (H : DigOK set x tl D rad pp) (ds : List RDT)
    (hd : ∀ d ∈ ds, Fo.Peel.Plain (toRD d))
    (he : ds.map (·.entry) = (P.ofPlace set true x).rounds.map (·.entry)) :
    List.Forall₂ MeetsT ds (Fo.specF tl.f9) :=
  meets_declared H.shape
    (by
      have := Cb.Fo.ok_v (dig_foOk H)
      omega)
    (by
      rw [(DgP.shape2_parts H.tail).2.1.nc]
      decide)
    H.rounds ds hd he

/-! ## 5 What the joint in front says -/

section
variable {x : Place} {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat} {pp : Nat}
  (Ex : Iop.ExtSpec) (Wp : Type)

/-- The library's unfolding at digL serves digL5: the two layouts have one K. -/
theorem forIn_dig5 {J₀ St₀ Kc M Wq : Type} {Ey : Iop.ExtSpec} (h : DgP.shapeTest2 tl pp = true)
    (en : DgP.Ent3 → J₀) (mk : Nat → J₀) (jLK : Nat) (R0 : Iop.IOR.Rels Kc St₀ Ey (M × Wq))
    (msg₀ : M → J₀ → Cb.Gl.E) :
    Cb.Fo.forIn Cb.Gl.E tl.f9 (DgP.digL5 Cb.Gl.E tl en mk jLK St₀) R0 msg₀ =
      ⟨fun a y w => R0.rel a y w ∧ DgP.DigIn tl en (msg₀ w.1),
        fun a w => R0.relR a w ∧ DgP.DigIn tl en (msg₀ w.1), R0.on, R0.core⟩ :=
  (rfl : Cb.Fo.forIn Cb.Gl.E tl.f9 (DgP.digL5 Cb.Gl.E tl en mk jLK St₀) R0 msg₀ =
    Cb.Fo.forIn Cb.Gl.E tl.f9 (DgP.digL Cb.Gl.E tl en mk jLK St₀) R0 msg₀).trans
    (DgP.forIn_dig h en mk jLK R0 msg₀)

/-- **The base joint in front, unfolded**: all digits, as msg₀ reads them, are in range. -/
theorem dig_base_relR (hT : DgP.shapeTest2 tl pp = true) (a : Unit × Ex.Str)
    (w : (digSg x D rad).Msg × Wp) :
    ((kLookupCR [noRider (digCaller x tl D rad Ex Wp)]).A
        (noRider (digCaller x tl D rad Ex Wp))).relR a w ↔
      DgP.DigIn tl (enOf x.arrays)
        (digMsg x D rad w.1) := by
  show (Cb.Fo.forIn Cb.Gl.E tl.f9 (DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next
    Unit)
    (Cb.Rider.withRider (quiet Ex _ Wp) (noRider (digCaller x tl D rad Ex Wp)).src)
    (digMsg x D rad)).relR a w ↔ _
  rw [forIn_dig5 hT]
  exact ⟨fun h => h.2, fun h => ⟨⟨trivial, fun e => Empty.elim e⟩, h⟩⟩

/-- **In plain terms**: every low digit, read off the link's messages at the seat of ZZ's cell, is a
number below 2^10, every high digit a number below 2^8. -/
theorem dig_plain
    (hR : Resolves x.arrays D.codes (digList x D rad) (seatOf D x.link) (ReadsDig tl x.F.next))
    (m : (digSg x D rad).Msg) :
    DgP.DigIn tl (enOf x.arrays) (digMsg x D rad m) ↔
      (∀ i : DgP.Pl tl, ∃ v, digVal x D rad m
          (.cell tl.ix.ZZ i.2.val i.1.val) = some v ∧ Cb.Rng.InTab (2 ^ t2D0) v) ∧
      ∀ i : DgP.Pl tl, ∃ v, digVal x D rad m
          (.cell tl.ix.ZZ i.2.val (tl.mz + i.1.val)) = some v ∧ Cb.Rng.InTab (2 ^ t2D1) v := by
  unfold DgP.DigIn
  exact and_congr (forall_congr' fun i => inTab_iff _ _ _ hR (.low i) _ m)
    (forall_congr' fun i => inTab_iff _ _ _ hR (.high i) _ m)

/-- **THE JOINT IN FRONT OF THE BLOCK, OVER THE SIGNATURE, UNFOLDED.** a: the state with the
samples, and the oracles with the messages' words. w: for each message a pair (message, encoding
randomness), and the further witness. -/
theorem dig_src_relR (hT : DgP.shapeTest2 tl pp = true)
    (a : (Unit × (digSg x D rad).Smp) × (Ex.prod (digSg x D rad).ext).Str)
    (w : (digSg x D rad).Wit × Wp) :
    ((kLookupCR [noRider (digCaller x tl D rad Ex Wp)]).toKind.src
        (noRider (digCaller x tl D rad Ex Wp))).relR a w ↔
      (∀ k, (digSg x D rad).decs a.1.2 a.2.2 k = some (w.1 k).1) ∧
        DgP.DigIn tl (enOf x.arrays)
          (digMsg x D rad ((digSg x D rad).msgs w.1)) :=
  and_congr_right fun _ =>
    dig_base_relR Ex Wp hT (a.1.1, a.2.1) ((digSg x D rad).msgs w.1, w.2)

/-- **THE CONDITION IN FRONT, UNFOLDED**: no message has a collision at its sample's seed. -/
theorem dig_src_on (a : (Unit × (digSg x D rad).Smp) × (Ex.prod (digSg x D rad).ext).Str) :
    ((kLookupCR [noRider (digCaller x tl D rad Ex Wp)]).toKind.src
        (noRider (digCaller x tl D rad Ex Wp))).on a ↔ (digSg x D rad).CF a.1.2 a.2.2 :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- **R0 does not hold the clause**: it holds at every statement and witness. -/
theorem dig_R0_quiet (a : Unit × Ex.Str) (w : (digSg x D rad).Msg × Wp) :
    (digCaller x tl D rad Ex Wp).R0.relR a w := trivial

end

end

#print axioms dig_ok
#print axioms dig_okR
#print axioms dig_foOk
#print axioms dig_sel
#print axioms dig_mkS
#print axioms dig_bc
#print axioms dig_meets
#print axioms forIn_dig5
#print axioms dig_base_relR
#print axioms dig_plain
#print axioms dig_src_relR
#print axioms dig_src_on
#print axioms dig_R0_quiet

end VerifiableInference.Desc.First.Look
