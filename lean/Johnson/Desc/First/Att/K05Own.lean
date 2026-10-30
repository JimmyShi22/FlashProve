-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Own.lean: THE LAST, THIN STEP: from K05_goodIn_piece
(Att/K05KeepsPiece.lean) to the form in which a table of borders asks a kind's law: the relation at
a border is "every item of a set holds", and the kind's piece is good from the items that it closes
to the items that it opens.

Main names:
  `goodIn_conseq`: GENERAL, for every piece: `Piece.GoodIn` (Johnson/Desc/Sound/GoodIn.lean) bears a
    smaller relation behind and a larger one in front; for both the condition in front, the piece's
    own output and the kept promise may be used.
  `K05_own_of`: at any type ι of items, any meaning `means`, any sets In and Out:
    (k5Piece …).GoodIn on (LaidBehind …) "every item of In holds" "every item of Out holds".

Premises of K05_own_of: those of K05_goodIn_piece, with the relation behind read as "every item of
Out
holds": so THREE DEBTS OF THE KIND's FILES AT A TABLE stand named: hb (BillsAllJ: the items of Out
give what is asked of the relation behind), hR' (the items of Out give the item that pins the
world's part), hIn (where the piece puts out and the items of Out hold behind: the chain's first
joint's Todo at the world's part gives every item of In in front). None is shown in this file or in
what it imports, at any table.
Limits. No table is imported: ι, means, In, Out are letters. At sets In and Out that are empty, or a
meaning that holds of nothing, the theorem is true and says nothing. The form is meant to be the one
that the table of joints' files type as what a kind's files owe:
that the two agree is not held by Lean here.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05KeepsPiece

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

/-- `GoodIn` bears a smaller relation behind and a larger one in front. -/
theorem goodIn_conseq {S Cl W : Type} {C : PQ.CK} {F : Frame} (P : Piece C F S Cl W)
    {on on' : S × F.E.Str → Prop} {R R' RA RB : S × F.E.Str → W → Prop}
    (h : P.GoodIn on on' R R')
    (hB : ∀ a τ b w, on a → P.ior.red.out a τ = some b → on' b → RB b w → R' b w)
    (hA : ∀ a τ b w, on a → P.ior.red.out a τ = some b → on' b → RB b w →
      R a (P.ext a τ w) → RA a (P.ext a τ w)) :
    P.GoodIn on on' RA RB := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun w hw =>
    hA a τ b w ha hb (hτ b hb).1 hw ((hτ b hb).2 w (hB a τ b w ha hb (hτ b hb).1 hw))⟩) (h a ha)

variable {M0 Mg X : Type}

open Classical in
/-- **The kind's law between two sets of items.** -/
theorem K05_own_of {St Cl W ι : Type} {Fr : Frame} {P0 : OwnPar Cb.Gl.E M0 X}
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
    (I : PinItem Fr seat base W Mg) (m0 : Mg)
    (means : ι → St × Fr.E.Str → W → Prop) (In Out : ι → Prop)
    (hb : BillsAllJ P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S settings.lidb cf A.fs (endLay P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) cellJ0 A.S.ls A.S.cf.lmS j0) Jn
      seat p.own (fun a : St × Fr.E.Str => a.1) (fun b : St × Fr.E.Str => b.1) x0 zx zk on I.part
      (fun b w => ∀ j, Out j → means j b w))
    (hR' : ∀ b w, (∀ j, Out j → means j b w) → I.holds (I.rc b.1) b.2 w)
    (hIn : ∀ a τ b w, on a →
      (k5Piece (W := W) (ckP .two) Fr seat claims p base (written p)
        (bearErr (written p) _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).ior.red.out a τ = some b →
      LaidBehind Fr seat p base on b → (∀ j, Out j → means j b w) →
      ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w) →
      ∀ j, In j → means j a w) :
    (k5Piece (W := W) (ckP .two) Fr seat claims p base (written p)
        (bearErr (written p) _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).GoodIn
      on (LaidBehind Fr seat p base on)
      (fun a w => ∀ j, In j → means j a w) (fun b w => ∀ j, Out j → means j b w) :=
  goodIn_conseq _
    (K05_goodIn_piece hA B hok Λ0 seat claims p hp ns0 k0 Q0 j0 Jn hJn Ex base x0 yOf zx zy zk on kr
      hroom hk3 hscl I m0 (fun b w => ∀ j, Out j → means j b w) hb hR')
    (fun _ _ _ _ _ _ _ h => h) hIn

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.goodIn_conseq
#print axioms VerifiableInference.Desc.First.Att.P.K05_own_of
