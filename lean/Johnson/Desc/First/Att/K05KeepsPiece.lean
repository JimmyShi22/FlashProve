-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KeepsPiece.lean: K05_keepsW_all_any (Att/K05KeepsAny.lean) AT THE KIND's
OWN
PIECE of the rule of composition, at the kind's own written rounds: the seam's five premises (hyes,
hpass, hd, he, hon') are paid by Att/K05Seam.lean; the pin is brought to one premise on the relation
behind.

Main names:
  `K05_keepsW_piece`: (k5Piece … base (written p) ε).ior.red.KeepsW on (LaidBehind …) (Todo at the
    world's part) R' ε, at ε := bearErr (written p) _ (… .ch.eps Ex).
  `goodIn_iff_keepsW`: at the kind's piece, whose extractor hands the witness through, the rule's
    `Piece.GoodIn` (Johnson/Desc/Sound/GoodIn.lean) IS `KeepsW` at the piece's own errors: by
    definition.
  `K05_goodIn_piece`: so the same law at the rule's own name for what a block with a promise owes.

Premises: those of K05_keepsW_all_any that are not the seam: Attention.plan's return; BaseIs;
p.own = A.own; planOkAll = true; hJn; hscl; at each statement with "on": Room at the ledger in front
and K3Pts; BillsAllJ, at the records' first components. For the pin: an item I of the border
(PinItem: it fixes the part; the seat's lay keeps what it reads of the record; it reads the stored
table and trees below the base alone) and hR': the relation behind gives the item. None is shown in
this file or in what it imports. That GatheredAllJ is ever met at a view that the verifier accepts
is not shown. planOkAll is evaluated in no file of this tree.
WHAT IS CLOSED, AND WHAT STAYS A LETTER. Closed: the reduction, its out, recA, recB, the written
rounds, on', mOf. STILL LETTERS beside "on": x0, zx, zy, zk, yOf (functions of the statement in
front), ns0, k0, kr, j0, Q0, Jn, Ex, the seat, the frame, base, and P0, Λ0 with BaseIs: at the first
chain's seat they are meant to be readings of the record (what the lookup has heard; the lookup's
typed out-statement; the ledger's numbers): nothing here ties them; hroom and hk3 are asked of "on".
Limits: those of K05KeepsAny.lean and K05Seam.lean. That a file's written rounds at the kind's
stretch are `written p` is not shown. The statement is about the piece's own reduction: the fold of
Johnson/Desc/Block.lean at the list of this one block, behind the stage's tests: no other text of a
verifier.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05KeepsAny
import Johnson.Desc.First.Att.K05Seam
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (recOf)
open K5Law (PlanLaw)
open Cb.Pv.Att.End (EndLay JoinLay NameJ)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.Sound (Frame Piece)

variable {M0 Mg X : Type}

open Classical in
/-- **The kind's law at the kind's own piece.** -/
theorem K05_keepsW_piece {St Cl W : Type} {Fr : Frame} {P0 : OwnPar Cb.Gl.E M0 X}
    {cellJ0 : AttSeg.Raw → P0.J} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (B : BaseIs P0 A.S A.fs cellJ0)
    (hok : planOkAll cf A.S A.fs = true) (Λ0 : Lin P0 Mg) (seat : Seat St)
    (claims : List (String × (Nat → St → Except String (List Cl × St)))) (p : Par)
    (hp : p.own = A.own) (ns0 k0 : ℕ)
    (Q0 : JoinLay (closedOf P0 Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ P0.D A.S.ls A.S.cf.lmS)
    (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    (hJn : ∀ x0 m gL W, Jn x0 gL W m → ∀ kv,
      Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl W) =
        Cb.Pv.Att.End.joinVal ((meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0).q x0) kv (((meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0).ce x0).val ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).msg m)))
    (Ex : ExtSpec) (base : ℕ) (x0 : St × Fr.E.Str → X) (yOf : St × Fr.E.Str → Ex.Str)
    (zx zy : St × Fr.E.Str → Array E) (zk : St × Fr.E.Str → Array (Array E))
    (on : St × Fr.E.Str → Prop) (kr : ℕ)
    (hroom : ∀ a, on a → ∀ F, seat.ledger a.1 = some F → Room F ns0 k0 kr)
    (hk3 : ∀ a, on a → K3Pts A.fs (zx a) (zy a) (zk a) (P0.zOf (x0 a)))
    (hscl : (Q0.scl.κ 0).sh = A.S.cf.sh.getD 0 0)
    (I : PinItem Fr seat base W Mg) (m0 : Mg) (R' : St × Fr.E.Str → W → Prop)
    (hb : BillsAllJ P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S settings.lidb cf A.fs (endLay P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) cellJ0 A.S.ls A.S.cf.lmS j0) Jn
      seat p.own (fun a : St × Fr.E.Str => a.1) (fun b : St × Fr.E.Str => b.1) x0 zx zk on I.part R')
    (hR' : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w) :
    (k5Piece (W := W) (ckP .two) Fr seat claims p base (written p)
        (bearErr (written p) _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).ior.red.KeepsW
      on (LaidBehind Fr seat p base on)
      (fun a w => ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R'
      (bearErr (written p) _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_keepsW_all_any hA B hok Λ0 seat p hp ns0 k0 Q0 j0 Jn hJn Ex (written p)
    (k5Piece (W := W) (ckP .two) Fr seat claims p base (written p)
      (bearErr (written p) _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).ior.red.out
    (fun a => a.1) (fun b => b.1) x0 yOf zx zy zk on kr hroom hk3
    (fun a τ b _ h => seam_yes seat claims p base (written p) _ a τ b h)
    (fun a τ b h => seam_pass seat claims p base (written p) _ a τ b h)
    (seam_plain p) (seam_entries p) hscl I.part (mOfItem I m0) (LaidBehind Fr seat p base on) R'
    (fun a τ b ha h => seam_on' seat claims p base (written p) _ on a τ b ha h) hb
    (fun a τ b w _ h hw => seam_pin_item seat claims p base (written p) _ I m0 R' hR' a τ b w h hw)

/-- At the kind's piece `GoodIn` is `KeepsW`: the extractor hands the witness through. -/
theorem goodIn_iff_keepsW {St Cl W : Type} {Fr : Frame} (seat : Seat St)
    (claims : List (String × (Nat → St → Except String (List Cl × St)))) (p : Par) (base : ℕ)
    (ds : List RDT) (err : Err (uLT (ckP .two) ds)) (on on' : St × Fr.E.Str → Prop)
    (R R' : St × Fr.E.Str → W → Prop) :
    (k5Piece (W := W) (ckP .two) Fr seat claims p base ds err).GoodIn on on' R R' ↔
      (k5Piece (W := W) (ckP .two) Fr seat claims p base ds err).ior.red.KeepsW on on' R R' err :=
  Iff.rfl

open Classical in
/-- **The kind's law at the rule's own name for what a block with a promise owes.** -/
theorem K05_goodIn_piece {St Cl W : Type} {Fr : Frame} {P0 : OwnPar Cb.Gl.E M0 X}
    {cellJ0 : AttSeg.Raw → P0.J} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (B : BaseIs P0 A.S A.fs cellJ0)
    (hok : planOkAll cf A.S A.fs = true) (Λ0 : Lin P0 Mg) (seat : Seat St)
    (claims : List (String × (Nat → St → Except String (List Cl × St)))) (p : Par)
    (hp : p.own = A.own) (ns0 k0 : ℕ)
    (Q0 : JoinLay (closedOf P0 Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ P0.D A.S.ls A.S.cf.lmS)
    (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    (hJn : ∀ x0 m gL W, Jn x0 gL W m → ∀ kv,
      Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl W) =
        Cb.Pv.Att.End.joinVal ((meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0).q x0) kv (((meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0).ce x0).val ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).msg m)))
    (Ex : ExtSpec) (base : ℕ) (x0 : St × Fr.E.Str → X) (yOf : St × Fr.E.Str → Ex.Str)
    (zx zy : St × Fr.E.Str → Array E) (zk : St × Fr.E.Str → Array (Array E))
    (on : St × Fr.E.Str → Prop) (kr : ℕ)
    (hroom : ∀ a, on a → ∀ F, seat.ledger a.1 = some F → Room F ns0 k0 kr)
    (hk3 : ∀ a, on a → K3Pts A.fs (zx a) (zy a) (zk a) (P0.zOf (x0 a)))
    (hscl : (Q0.scl.κ 0).sh = A.S.cf.sh.getD 0 0)
    (I : PinItem Fr seat base W Mg) (m0 : Mg) (R' : St × Fr.E.Str → W → Prop)
    (hb : BillsAllJ P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S settings.lidb cf A.fs (endLay P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) cellJ0 A.S.ls A.S.cf.lmS j0) Jn
      seat p.own (fun a : St × Fr.E.Str => a.1) (fun b : St × Fr.E.Str => b.1) x0 zx zk on I.part R')
    (hR' : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w) :
    (k5Piece (W := W) (ckP .two) Fr seat claims p base (written p)
        (bearErr (written p) _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).GoodIn
      on (LaidBehind Fr seat p base on)
      (fun a w => ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R' :=
  K05_keepsW_piece hA B hok Λ0 seat claims p hp ns0 k0 Q0 j0 Jn hJn Ex base x0 yOf zx zy zk on kr
    hroom hk3 hscl I m0 R' hb hR'

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW_piece
#print axioms VerifiableInference.Desc.First.Att.P.goodIn_iff_keepsW
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_piece
