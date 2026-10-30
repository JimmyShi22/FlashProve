-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Means.lean: WHAT THE KIND's LAW CONCLUDES IN FRONT MEANS, at the closed
caller of the lookup on an attention link's calls: the chain's first joint's Todo gives the
segment's own identities at every valid name, at the cells that are read off the committed symbols;
and its rider at the lookup's point.

Main names:
  `OwnMeans x S tl D rad z m`: three clauses at the cells T := attCells x S tl D rad m
    (Johnson/Desc/First/Look/K3CallerAtt.lean): the identities at1 vanish at every valid name (the
    index's cells are bits); the identities at2 vanish at every valid name (the stated maximum is
    the score at the index); denOut (dimOf S) (callsOf x.fs) z T = 0 (Cb/Pv/Att/Mean/DenStep.lean:
    the batch, at the point z, of the identities at3: "the denominator is the row's sum of the
    softmax weights").
  `K05_means`: **Todo x0 m gives OwnMeans at z := the lookup's point x0.2.1.pt.**
  `K05_todo_is`: what Todo is at these letters, exactly: the rider at the point, the two families on
    their cubes, and the join at the rule values: todo_iff_hid (Att/K05GuestHid.lean) there.
  `K05_rider_means`: THE RIDER's ROW: the base joint in front of the lookup with riders gives the
    identities at3 at every valid name. It is the second half of `att_says` (K3CallerAtt.lean),
    worded as this kind's row.
  `K05_means_bites`: Todo fails at every message one of whose valid identities at1 or at2 is not 0,
    or whose denOut at the lookup's point is not 0.
  `K05_goodIn_means`: the law at the block k5AtO (K05_goodIn_k5AtO, Att/K05KeepsSeats.lean) with
    OwnMeans at the world's part as the relation in front.

In whose letters. The first two clauses are the premises own1 and own2 of the library's att_ord_base
(Johnson/Road/Rows/AttStartBase.lean), at t := T; K05_rider_means' conclusion is its premise ridden.
The third clause is the target of the library's lookup with riders at its rider "the denominator"
(Johnson/Top/H/LookupCRModel.lean: crDen).
Premises: Attention.plan's return (for: a position has at most 16 bits); for the rider's row: AttOK.
Limits. (1) BETWEEN THE THIRD CLAUSE AND THE RIDER's ROW LIES THE LOOKUP's LAW: denOut = 0 speaks of
one point and does not give at3 at every name (Cb/G6/Rider/Model/Denom.lean: den_not_back); the step
is paid in the lookup's rounds' errors, by the lookup's files' theorem on that block, which is not
called here. (2) NO (x0, m) WITH Todo AT THESE LETTERS IS SHOWN: if there is none, K05_means is true
and empty. (3) att_ord_base also asks ht: t c = cellValS y (pl …) AT EVERY NAME c: T reads 0 at a
name whose place lies outside the sizes: it meets ht at valid names alone: the tie is not made here.
(4) "The committed symbols are the packing of small integers" is not spent: the clauses speak of the
cells as elements of the field. (5) What Todo's fourth clause (K05_todo_is: the join at the rule
values) says of the key vectors at the lookup's points is not worded here.
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05KeepsSeats
import Johnson.Desc.First.Att.K05Own
import Johnson.Desc.First.Att.K05Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Road.L5 (callsOf dimOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.OnPublicFiles (kLookupCR)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask attCells attRider
  att_says)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- **What the kind's own rounds mean**, at the cells off the committed symbols. z: the lookup's
point. -/
structure OwnMeans (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape)
    (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) (z : ℕ → Cb.Gl.E)
    (m : (attSg x D rad).Msg) : Prop where
  own1 : ∀ j b g i, (Idn.at1 j b g i).Valid (dimOf S) →
    idnVal (dimOf S) (attCells x S tl D rad m) (.at1 j b g i) = 0
  own2 : ∀ b g i, (Idn.at2 b g i).Valid (dimOf S) →
    idnVal (dimOf S) (attCells x S tl D rad m) (.at2 b g i) = 0
  rider : denOut (dimOf S) (callsOf x.fs) z (attCells x S tl D rad m) = 0

section Means
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

/-- **K05_means.** -/
theorem K05_means {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A) (ns : ℕ) (N : Nums)
    (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (m : (attSg x D rad).Msg)
    (h : ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo x0 m) :
    OwnMeans x A.S tl D rad x0.2.1.pt m :=
  ⟨own1_of_todo (closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N)
      (lT_le_16 (OnBytes.Road.L5.plan_shape hA).1) x0 m h,
    own2_of_todo (closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N) x0 m h,
    guest_at_point (closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N)
      (zcRead_hid (hidLet_meant (attBase x A.S tl D rad) (attLin0 x A.S tl D rad) ns N
        (attQ0 x A.S tl D rad Ex Wp α ns N))) x0 m h⟩

/-- **What Todo is at these letters, exactly**: todo_iff_hid (Att/K05GuestHid.lean) at the closed
caller. Against K05_means it holds one clause more: the join at the rule values. -/
theorem K05_todo_is {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A) (ns : ℕ) (N : Nums)
    (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (m : (attSg x D rad).Msg) :
    ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo x0 m ↔
      denOut (dimOf A.S) (callsOf x.fs) x0.2.1.pt (attCells x A.S tl D rad m) = 0 ∧
      (∀ i : Fin (dimOf A.S).nb, ∀ Y < 2 ^ (closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).g1,
        scoreIdnG (dimOf A.S) (attCells x A.S tl D rad m) i Y = 0) ∧
      (∀ i : Fin (dimOf A.S).nb, ∀ Y < 2 ^ (closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).g2,
        bitIdnT (dimOf A.S) (attCells x A.S tl D rad m) i Y = 0) ∧
      joinVal ((meantQ (attBase x A.S tl D rad) (attLin0 x A.S tl D rad) ns N (attQ0 x A.S tl D rad Ex Wp α ns N)).q x0)
        (KF (scl := (meantQ (attBase x A.S tl D rad) (attLin0 x A.S tl D rad) ns N (attQ0 x A.S tl D rad Ex Wp α ns N)).scl) (dimOf A.S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt)
          (rv (dimOf A.S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt) (attCells x A.S tl D rad m)))
        (((meantQ (attBase x A.S tl D rad) (attLin0 x A.S tl D rad) ns N (attQ0 x A.S tl D rad Ex Wp α ns N)).ce x0).val ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).msg m)) = 0 :=
  todo_iff_hid (hidLet_meant (attBase x A.S tl D rad) (attLin0 x A.S tl D rad) ns N
    (attQ0 x A.S tl D rad Ex Wp α ns N)) rfl (lT_le_16 (OnBytes.Road.L5.plan_shape hA).1) x0 m

/-- **The rider's row**: at the base joint in front of the lookup with riders. -/
theorem K05_rider_means {set : Params.Setting} {S : Attention.Shape} (H : AttOK set x S tl D rad)
    (a : Unit × Ex.Str) (w : (attSg x D rad).Msg × Wp)
    (h : ((kLookupCR [attRider x S tl D rad Ex Wp]).A (attRider x S tl D rad Ex Wp)).relR a w) :
    ∀ b g i, (Idn.at3 b g i).Valid (dimOf S) →
      idnVal (dimOf S) (attCells x S tl D rad w.1) (.at3 b g i) = 0 :=
  ((att_says Ex Wp H a w).1 h).2

/-- Todo is no relation that holds of every message. -/
theorem K05_means_bites {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A) (ns : ℕ) (N : Nums)
    (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (m : (attSg x D rad).Msg)
    (hbad : ¬ OwnMeans x A.S tl D rad x0.2.1.pt m) :
    ¬ ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo x0 m :=
  fun h => hbad (K05_means x tl D rad Ex Wp α hA ns N x0 m h)

open Classical in
/-- **The law at the block k5AtO, with what it means in front.** -/
theorem K05_goodIn_means {W Cl : Type} {Fr : Frame} (claim : Aff → Cl) (Wv : Verify.Public)
    (l g : ℕ) (before : List (ℕ × ℕ)) (blk : VerifiableInference.Desc.Block First.S Aff)
    (hblk : k5AtO Wv l g before = some blk) {A : Attention.Plan} (hg : Wv.A[g]? = some A)
    {set : Params.Setting} {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (on : First.S × Fr.E.Str → Prop)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl) :
    let p := parO Wv l A before
    ∀ (_ : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) a.1)
    (I : PinItem Fr seatSO base W (attSg x D rad).Msg) (_ : (attSg x D rad).Msg)
    (R' : First.S × Fr.E.Str → W → Prop)
    (_ : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own (fun a : First.S × Fr.E.Str => a.1) (fun b : First.S × Fr.E.Str => b.1) x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on I.part R')
    (_ : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w),
    (⟨blk, base, written p, [], fun _ _ w => w,
        bearErr (written p) _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)⟩ : Piece (ckP .two) Fr First.S Aff W).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => OwnMeans x A.S tl D rad (x0 a).2.1.pt (I.part w)) R' := by
  intro p hleft I m0 R' hb hR'
  exact goodIn_conseq _
    (K05_goodIn_k5AtO x tl D rad Ex Wp α claim Wv l g before blk hblk hg hA H hfs hok ns nx k j0
      base x0 yOf on gOf pl hleft I m0 R' hb hR')
    (fun _ _ _ _ _ _ _ h => h)
    (fun a _ _ w _ _ _ _ h => K05_means x tl D rad Ex Wp α hA ns _ (x0 a) (I.part w) h)

end Means

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_means
#print axioms VerifiableInference.Desc.First.Att.P.K05_todo_is
#print axioms VerifiableInference.Desc.First.Att.P.K05_rider_means
#print axioms VerifiableInference.Desc.First.Att.P.K05_means_bites
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_means
