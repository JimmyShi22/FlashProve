-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Own24.lean: **K6's OWN LAW AT THE TABLE's FRAME WITH THE COMPONENTS READ
OFF THE TABLE's WITNESS BY THE READERS OF OTHER FILES: NO LETTER rd6 | comp | own ANY MORE**: the
cells are Hd.cellsH, at the public record's own shape, layout and border, at
ownQ … w 24 (Johnson/P5J/CellQ.lean: over ownOf: the small integers whose packing
the symbols are; symAt at the seats; readAt: the one accessor at the seat of
segment 24's own copy); the mask row is Law/K6ReadAt.lean's maskQ. THIS KIND's HALF OF (pin), "the
components that the rule reads are read off pinned places alone", IS A THEOREM: STATED AND PROVED.
  SeatsIn a condition on public letters alone: every place that segment k's seats name, within its
      sizes, lies inside the ranges of the segment's own copy of that message.
  ownQ_alike under SeatsNamed and SeatsIn: witnesses that read alike through the accessor
      inside the ranges have ONE ownQ at segment k.
  comp24 · readsPinnedW_24 · comp24_cells : cellsN (comp24 … w).1 = Hd.cellsH Wp.hS Wp.HLy (borderOf
      Wp.y) (ownQ … w 24). THE HEAD's SHAPE, LAYOUT AND BORDER ARE THE PUBLIC RECORD's
      OWN: were they three free letters that no premise reads,
      the sentence would be true at every shape and meant at one.
  base24 the table's "constr 4 small", its packing half (the library's Base at segment 24's symbols
      as the segment reads them): IT STANDS IN THE ITEM ON BOTH SIDES (the table's
      ctx).
  k6Own24 THE CALL: p.Own (K6On) (K6After) (meansW … comp24 … base24 …) InK6 OutK6, at the block
      blockOf Wp 24.
  k06_whole_24 Law/K06Means.lean's assembly at one record, at comp24: ⇒ Policy.HeadCl
      (Hd.npOf Wp.hS) (polOf Wp.hS) Wz x (Hd.cellsH Wp.hS Wp.HLy (borderOf Wp.y) (ownQ … w 24)). Its
      premises are that file's, to the letter.
**TWO LISTS, NOT ONE**: ms: the
members pinned in front of the piece (Fenced | SmpStays | the item's Pinned | ReadAlike) · msR: the
list that readAt searches (ownQ | maskQ | base24): AT msR := THE TABLE's OWN LIST ownQ … msR … IS
THE TABLE's ownQ, TO THE LETTER; were one letter to hold both offices, no list
could pay Fenced and the
table's GroupsSeated together at a real plan. SeatsIn says: every place that segment 24's seats
name IS SEATED in msR, BY A MEMBER THAT IS PINNED (in ms), inside its ranges: A REAL TEST ON THE
PLAN: FALSE IF s 24 NAMES A MESSAGE THAT IS SENT BEHIND K6 (then the reading must be cut to the
matrices that the head's cells lie in: NOT DONE); an empty list does not pass it where segment 24
has a symbol. The mask row's
two conditions run below a public nM.
WHAT IT DOES NOT SAY. LETTERS THAT STAY, ALL MEANT AS PUBLIC FUNCTIONS OF THE PLAN, TIED TO IT BY
NOTHING HERE: s | seat (the sizes and seats of the segments' matrices) · N | arr | ms | msR (the
plan's numbers; which message a tenant holds; the pinned members; the reader's list) · nM | pl (how
many entries the mask row has, and where they lie) · cs (the codes) · smp | decT (the frame's
samples and the stored table's decoder: A SILLY decT := none pays DecTStays and makes the item on
both sides false at every witness: the law is then the promise alone) · wh (from the stored table's
cells to the output matrix's weights). THE LETTERS UNDER "THERE IS": none in k6Own24's own text
(base24 holds the library's: "there are small integers whose packing the symbols are": pinned by
that equation, and unique by the library's baseAt_unique). THE LINK's NUMBER IS 24 IN THE BLOCK AND
IN THE READING ALIKE.
∀-LETTERS THAT NO PREMISE READS, BY DESIGN: wh (named above) · G (the frame's description of the
files: it stands in Pinned alone). SeatsNamed | SeatsIn | the mask row's two
conditions HAVE RUN AT NO PLAN. WHERE THE COMMITTED SYMBOLS ARE NO PACKING OF SMALL INTEGERS ownQ IS
0 IN THAT COLUMN (its own limit): the item "constr 4 small" (the library's Base) says that
they are one: it stands on both sides (base24); THE LAW SPENDS IT NOWHERE; whoever reads the
closed item's cells as "the committed integers" spends it. All the premises on the piece of
Law/K6OwnW.lean; K6On not inside the table's promise; the items ours; planes on neither side; NO
MEMBER. The lift to the
description's own piece is not in this file. NO
SOUNDNESS OF A PROTOCOL OR A VERIFIER.
NOT A TOP: FOR k6Own24 AND k6Own24By STAND Law/K6Cut.lean's k6OwnCut | k6OwnCutBy:
here the sizes s, the mask row's length nM and the pinned list ms are still free letters beside Wp,
and SeatsNamed is asked at every segment: three gaps by reading stand open in them; nobody calls
them as tops; what lives of this file are its definitions and the assemblies at one record.
GENERAL IN THE BLOCK: k6Own24By: the call for any block b6, of any type of claims, that meets
Law/K6Steps.lean's record K6Steps Wp b6 on after: p.Own (on) (after) ...; k6Own24, with its
statement as it was, is its instance at blockOf, K6On and K6After.

-/
import Mathlib
import Johnson.P5J.CellQ
import Johnson.Desc.Kinds.Law.K6ReadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Piece Frame Sending Mem MsgT Fenced SmpStays ErrBears kitK
    kitFs
  SeatsNamed namedOnce)
open VerifiableInference.Desc.Kinds.HeadJoin (cellsN)

variable (cs : OnBytes.Codes) {Cells Tok : Type} (arr : Nat → Nat → Nat) (ms msR : List Mem)
  (N : Numbers)
  (s : Nat → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat)

/-- Every place that segment k's seats name, within its sizes, lies inside the ranges of the
segment's own copy of that message. -/
def SeatsIn (k : Nat) : Prop :=
  ∀ (μ : Fin (s k).NM) (r c : Nat), r < Alg.symRows ((s k).m μ) → c < (s k).k μ →
    InCopy cs arr ms msR N k (seat k μ r c).1 false (seat k μ r c).2.1 (seat k μ r c).2.2

variable (Wp : OnBytes.Model.Verify.Public) (wh : Cells → Nat → Nat → Int) (nM : Nat)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **The components that K6's rule reads, off the table's witness**: by Road.Hd's map of the
head's cells AT THE PUBLIC RECORD's OWN shape, layout and border. -/
def comp24 : Wit Cells Tok MsgT → Pinned :=
  compOf Wp.hS Wp.HLy (OnBytes.Model.Verify.borderOf Wp.y)
    (fun w => P5J.ownQ cs arr msR N s seat w 24) wh (maskQ cs arr msR N 24 nM pl)

/-- **The table's "constr 4 small", its packing half**: segment 24's committed symbols, as the
witness holds them and the segment reads them, ARE the packing of small integers (the library's
Base; base_at, Johnson/P5J/CellQ.lean, says that hidAtSeat's field base is this sentence). -/
def base24 (w : Wit Cells Tok MsgT) : Prop :=
  Cb.Pv.Tail.Base (Meaning.symAt (s 24) (seat 24) (Sound.readAt cs arr msR N 24 w))

namespace Came

/-- **ownQ reads pinned places alone.** -/
theorem ownQ_alike (k : Nat) (hN : SeatsNamed arr N s seat)
    (hI : SeatsIn cs arr ms msR N s seat k) (w w' : Wit Cells Tok MsgT)
    (hA : ReadAlike cs arr ms w w') :
    P5J.ownQ cs arr msR N s seat w k = P5J.ownQ cs arr msR N s seat w' k := by
  have e : Meaning.symAt (s k) (seat k) (Sound.readAt cs arr msR N k w) =
      Meaning.symAt (s k) (seat k) (Sound.readAt cs arr msR N k w') := by
    funext μ r c
    exact readAt_alike cs arr ms msR N k _ w w' (hN k μ r.val c.val r.isLt c.isLt) hA false _ _
      (hI μ r.val c.val r.isLt c.isLt)
  unfold P5J.ownQ Meaning.ownOf
  beta_reduce
  rw [e]

/-- **This kind's half of (pin): A THEOREM.** -/
theorem readsPinnedW_24 (hN : SeatsNamed arr N s seat) (hI : SeatsIn cs arr ms msR N s seat 24)
    (hn : ∀ j, j < nM → namedOnce arr N 24 (pl j).1 = true)
    (hin : ∀ j, j < nM →
      InCopy cs arr ms msR N 24 (pl j).1 (pl j).2.1 (pl j).2.2.1 (pl j).2.2.2) :
    ReadsPinnedW cs arr ms (comp24 (Tok := Tok) cs arr msR N s seat Wp wh nM pl) :=
  readsPinnedW_comp cs arr ms _ _ _ _ wh _ (ownQ_alike cs arr ms msR N s seat 24 hN hI)
    (maskQ_alike cs arr ms msR N 24 nM pl hn hin)

/-- The library's record made of our cells is Hd.cellsH at segment 24's own integers off the
witness. -/
theorem comp24_cells (w : Wit Cells Tok MsgT) :
    cellsN (comp24 cs arr msR N s seat Wp wh nM pl w).1 =
      OnBytes.Road.Hd.cellsH Wp.hS Wp.HLy (OnBytes.Model.Verify.borderOf Wp.y)
        (P5J.ownQ cs arr msR N s seat w 24) := rfl

/-- **THE CALL, WITH NO LETTER FOR THE READING.** -/
theorem k6Own24By {Xi : Type} (G : FileDescription Xi)
    (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (decT : (Nat → Option (Nat × List UInt64)) → S → Option Cells)
    (fld : Fmt.Fld) (Fr : Frame)
    {Cl : Type} (p : Piece (_root_.Run.ckP fld) Fr S Cl (Wit Cells Tok MsgT)) (b6 : Block S Cl)
    {on after : S → Prop}
    (hst : K6Steps Wp b6 on after) (hpb : p.b = Sound.below b6) (hback : p.back = [])
    (hext : ∀ a τ w, p.ext a τ w = w) (hN : SeatsNamed arr N s seat)
    (hI : SeatsIn cs arr ms msR N s seat 24)
    (hn : ∀ j, j < nM → namedOnce arr N 24 (pl j).1 = true)
    (hin : ∀ j, j < nM →
      InCopy cs arr ms msR N 24 (pl j).1 (pl j).2.1 (pl j).2.2.1 (pl j).2.2.2)
    (hF : Fenced p.base ms) (hS : SmpStays cs smp p ms) (hD : DecTStays decT p)
    (hlog : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err) :
    p.Own (fun a => on a.1) (fun b => after b.1)
      (meansW cs G arr smp decT ms (comp24 cs arr msR N s seat Wp wh nM pl) (base24 cs arr msR N s
          seat)
        Wp Fr) InK6 OutK6 :=
  k6OwnWBy cs G arr smp decT ms _ _ Wp fld Fr p b6 hst hpb hback hext
    (readsPinnedW_24 cs arr ms msR N s seat Wp wh nM pl hN hI hn hin) hF hS hD hlog hErr

/-- The same at the block at the unit type, under K6On, with K6After behind.
    -/
theorem k6Own24 {Xi : Type} (G : FileDescription Xi)
    (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (decT : (Nat → Option (Nat × List UInt64)) → S → Option Cells)
    (fld : Fmt.Fld) (Fr : Frame)
    (p : Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)) (b6 : Block S Unit)
    (hb6 : blockOf Wp 24 = some b6) (hpb : p.b = Sound.below b6) (hback : p.back = [])
    (hext : ∀ a τ w, p.ext a τ w = w) (hN : SeatsNamed arr N s seat)
    (hI : SeatsIn cs arr ms msR N s seat 24)
    (hn : ∀ j, j < nM → namedOnce arr N 24 (pl j).1 = true)
    (hin : ∀ j, j < nM →
      InCopy cs arr ms msR N 24 (pl j).1 (pl j).2.1 (pl j).2.2.1 (pl j).2.2.2)
    (hF : Fenced p.base ms) (hS : SmpStays cs smp p ms) (hD : DecTStays decT p)
    (hlog : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs p.ds) j)) (toRDs p.ds) 0 p.err) :
    p.Own (fun a => K6On Wp a.1) (fun b => K6After Wp b.1)
      (meansW cs G arr smp decT ms (comp24 cs arr msR N s seat Wp wh nM pl) (base24 cs arr msR N s
          seat)
        Wp Fr) InK6 OutK6 :=
  k6Own24By cs arr ms msR N s seat Wp wh nM pl G smp decT fld Fr p b6
    ((k6Steps_blockOf Wp 24 b6 hb6).weaken fun _ h => h.1) hpb hback hext hN hI hn hin hF hS hD hlog
        hErr

/-- **THE ASSEMBLY AT ONE RECORD, AT SEGMENT 24's OWN INTEGERS OFF THE WITNESS**:
HeadOrdLB's middle clause at Mh := ownQ … w 24, at the public record's own shape, layout and border.
-/
theorem k06_whole_24 (s0 : S) (y : Nat) (x : Inst.Model.Instance Inst.Model.ppref)
    (Wz : Inst.Model.Mat) (tab : Nat → Nat) (w : Wit Cells Tok MsgT) (hon : K6On Wp s0)
    (hin : K6In Wp s0 (comp24 cs arr msR N s seat Wp wh nM pl w))
    (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat s0 = some y)
    (hlook : LookCallsAt Wp tab s0 y (comp24 cs arr msR N s seat Wp wh nM pl w).1)
    (hrider : RiderAt Wp s0 y (comp24 cs arr msR N s seat Wp wh nM pl w).1)
    (hsmall : ∀ m f t, ((comp24 cs arr msR N s seat Wp wh nM pl w).1.cell m f t).natAbs < 2 ^ 18)
    (hsmallS : ∀ f t, ((comp24 cs arr msR N s seat Wp wh nM pl w).1.stream f t).natAbs < 2 ^ 18)
    (hF : OnBytes.Road.Hd.FullH Wp.hS) (h8 : Wp.hS.digSh = 8) (hr : s0.rowR = x.r)
    (he : s0.rowE = x.e) (htok : ∀ t, t < 1024 → s0.tokv.getD t 0 = x.tok t) (hyx : y = x.y.val)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : wh w.cells =
      (Inst.Model.Layout.weightsOf Inst.Model.ppref Inst.Model.Layout.kRef Wz).H) :
    _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf Wp.hS) (OnBytes.Road.Hd.polOf Wp.hS) Wz x
      (OnBytes.Road.Hd.cellsH Wp.hS Wp.HLy (OnBytes.Model.Verify.borderOf Wp.y)
        (P5J.ownQ cs arr msR N s seat w 24)) := by
  unfold comp24 at hin hlook hrider hsmall hsmallS
  exact k06_whole_own Wp.HLy (OnBytes.Model.Verify.borderOf Wp.y)
    (fun w => P5J.ownQ cs arr msR N s seat w 24) wh (maskQ cs arr msR N 24 nM pl) Wp s0 y x Wz tab w
    hon
    hin hy hlook hrider hsmall hsmallS hF h8 hr he htok hyx htab hW

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.ownQ_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.readsPinnedW_24
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6Own24By
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6Own24
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06_whole_24
#check @VerifiableInference.Desc.Kinds.Head.Law.Came.k6Own24
#check @VerifiableInference.Desc.Kinds.Head.Law.Came.k06_whole_24
