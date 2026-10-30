-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KeepsSeats.lean: THE KIND's LAW AT THE KIND's OWN PIECE, AT THE SEATS THAT
SIT, WHATEVER THE BLOCK's TEST ON THE PLAN, AND SO AT THE BLOCK k5AtO: K05_keepsW_left_seats
(Att/K05LeftSeats.lean: the form of the law at the closed caller of the lookup on an
attention link's calls, at the hearing's seat seatSO and the lookup's seat K3.seatCalls) with the
seam's five premises paid by Att/K05Seam.lean and the pin brought to one premise on the relation
behind.

Main names:
  `K05_keepsW_piece_seats`: (k5Piece … seatSO claims p base (written p) ε).ior.red.KeepsW on
    (LaidBehind …) (Todo at the world's part) R' ε. `K05_goodIn_piece_seats`: the same at the rule's
    own name Piece.GoodIn.
  `K05_goodIn_anyPlanOk`: the same of { attentionKind seatSO claims p with planOk := ok }, at every Bool ok,
    every list of runs and every type of claims: a piece's reduction reads no test on the plan.
  `parO`, `k5AtO_is`: the block k5AtO (Att/SeatO.lean) is attentionKind seatSO (runsO pA) (parO …) with one
    more test on the plan. `K05_goodIn_k5AtO`: so the law at the block k5AtO, at its own stretch.
WHICH TEXT IS MEANT. Whether a description in this library names k5AtO is not said here. The
set of lots that has run seats, in a harness file not imported here, attentionKind seatSO [] { link, piece :=
3, work, own := p.own, before } with planOk := ‹its planOk› && claimsOkAtO p, at the type Unit of
claims, with no runs: K05_goodIn_anyPlanOk holds of that block too (claims := [], ok := that Bool).

NOT HERE, BUT AT K05_keepsW_piece (Att/K05KeepsPiece.lean): the letters P0, Λ0, Q0, Jn, the
seat, zx, zy, zk, kr, ns0, k0 and the premises BaseIs, hJn, hroom, hk3, hscl: they are the closed
caller's (attBase, attLin), the seat seatSO, what the lookup has heard (gOf a), and are drawn from
hleft. WHAT IS LEFT, BY NAME. Public: hA (Attention.plan's return) · H (AttOK) · hfs · hok
(planOkAll) · hp. Letters: x, tl, D, rad, Ex, Wp, α, claim, ns, nx, k, j0, pl, base, the frame; and
three functions of the statement in front: x0 (the lookup's typed out-statement), gOf (what the
lookup has heard), yOf (idle). At each statement with "on": hleft (K3LeftOutIs: the lookup's sharp
promise: it ties gOf a to the record by heard a.1 = some (gOf a), the ledger by fork a.1 = some F',
and x0 a to the same rounds by OutTies). Of the relation behind: hb (BillsLaterJ) · I : PinItem with
hR'. NONE IS SHOWN HERE. NO MEMBER OF THE WHOLE IS SHOWN.
Limits: those of K05LeftSeats.lean, K05Seam.lean. That Wv.A[g]? is the planner's return (hg beside
hA) is shown by nobody here.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LeftSeats
import Johnson.Desc.First.Att.K05Seam
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)
open VerifiableInference.Desc.Sound (Frame Piece)

section Seats
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

open Classical in
/-- **The kind's law at the kind's own piece, at the seats that sit.** -/
theorem K05_keepsW_piece_seats {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (on : First.S × Fr.E.Str → Prop)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl)
    (hleft : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) a.1)
    (I : PinItem Fr seatSO base W (attSg x D rad).Msg) (m0 : (attSg x D rad).Msg)
    (R' : First.S × Fr.E.Str → W → Prop)
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own (fun a : First.S × Fr.E.Str => a.1) (fun b : First.S × Fr.E.Str => b.1) x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on I.part R')
    (hR' : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w) :
    (k5Piece (W := W) (ckP .two) Fr seatSO claims p base (written p)
        (bearErr (written p) _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).ior.red.KeepsW
      on (LaidBehind Fr seatSO p base on)
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R'
      (bearErr (written p) _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_keepsW_left_seats x tl D rad Ex Wp α claim hA H hfs hok p hp ns nx k j0 (written p)
    (k5Piece (W := W) (ckP .two) Fr seatSO claims p base (written p)
      (bearErr (written p) _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).ior.red.out
    (fun a => a.1) (fun b => b.1) x0 yOf on gOf pl hleft
    (fun a τ b _ h => seam_yes seatSO claims p base (written p) _ a τ b h)
    (fun a τ b h => seam_pass seatSO claims p base (written p) _ a τ b h)
    (seam_plain p) (seam_entries p) I.part (mOfItem I m0) (LaidBehind Fr seatSO p base on) R'
    (fun a τ b ha h => seam_on' seatSO claims p base (written p) _ on a τ b ha h) hb
    (fun a τ b w _ h hw => seam_pin_item seatSO claims p base (written p) _ I m0 R' hR' a τ b w h hw)

open Classical in
/-- The same at the rule's own name for what a block with a promise owes. -/
theorem K05_goodIn_piece_seats {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (on : First.S × Fr.E.Str → Prop)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl)
    (hleft : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) a.1)
    (I : PinItem Fr seatSO base W (attSg x D rad).Msg) (m0 : (attSg x D rad).Msg)
    (R' : First.S × Fr.E.Str → W → Prop)
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own (fun a : First.S × Fr.E.Str => a.1) (fun b : First.S × Fr.E.Str => b.1) x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on I.part R')
    (hR' : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w) :
    (k5Piece (W := W) (ckP .two) Fr seatSO claims p base (written p)
        (bearErr (written p) _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R' :=
  K05_keepsW_piece_seats x tl D rad Ex Wp α claim hA H hfs hok claims p hp ns nx k j0 base x0 yOf on
    gOf pl hleft I m0 R' hb hR'

open Classical in
/-- **Whatever the block's test on the plan**: a piece's reduction does not read it. -/
theorem K05_goodIn_anyPlanOk {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) (ok : Bool) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (on : First.S × Fr.E.Str → Prop)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (pl : ℕ → ℕ → JAtt x.ns tl)
    (hleft : ∀ a, on a → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script p.own) + k))) (x0 a) (gOf a) a.1)
    (I : PinItem Fr seatSO base W (attSg x D rad).Msg) (m0 : (attSg x D rad).Msg)
    (R' : First.S × Fr.E.Str → W → Prop)
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seatSO p.own (fun a : First.S × Fr.E.Str => a.1) (fun b : First.S × Fr.E.Str => b.1) x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on I.part R')
    (hR' : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w) :
    (⟨{ attentionKind seatSO claims p with planOk := ok }, base, written p, [], fun _ _ w => w,
        bearErr (written p) _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)⟩ : Piece (ckP .two) Fr First.S Ck W).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R' :=
  K05_goodIn_piece_seats x tl D rad Ex Wp α claim hA H hfs hok claims p hp ns nx k j0 base x0 yOf on
    gOf pl hleft I m0 R' hb hR'

end Seats

/-! ## Whatever the test on the plan; the block k5AtO -/

/-- The place's numbers that the first chain's description hands the kind at segment l. -/
def parO (Wv : Verify.Public) (l : ℕ) (pA : Attention.Plan) (before : List (ℕ × ℕ)) : Par :=
  { link := l, piece := 3, work := (Params.settingOf Wv.P.frame).workOf .field .request
    own := pA.own, before := before }

/-- **The block that the description lays is the kind's, with one more test on the plan.** -/
theorem k5AtO_is (Wv : Verify.Public) (l g : ℕ) (before : List (ℕ × ℕ))
    (b : VerifiableInference.Desc.Block First.S Aff) (h : k5AtO Wv l g before = some b) :
    ∃ pA, Wv.A[g]? = some pA ∧
      b = { attentionKind seatSO (runsO pA) (parO Wv l pA before) with
        planOk := (attentionKind seatSO (runsO pA) (parO Wv l pA before)).planOk && claimsOkAtO pA } := by
  unfold k5AtO at h
  cases hg : Wv.A[g]? with
  | none => rw [hg] at h; cases h
  | some pA =>
    rw [hg] at h
    exact ⟨pA, rfl, (Option.some.inj h).symm⟩

section AtO
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

open Classical in
/-- **The kind's law at the block k5AtO**, at its own stretch. -/
theorem K05_goodIn_k5AtO {W Cl : Type} {Fr : Frame} (claim : Aff → Cl) (Wv : Verify.Public)
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
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R' := by
  intro p hleft I m0 R' hb hR'
  obtain ⟨pA, hg', rfl⟩ := k5AtO_is Wv l g before blk hblk
  obtain rfl : A = pA := Option.some.inj (hg.symm.trans hg')
  exact K05_goodIn_anyPlanOk x tl D rad Ex Wp α claim _ hA H hfs hok (runsO A) p rfl ns nx k j0 base
    x0 yOf on gOf pl hleft I m0 R' hb hR'

end AtO

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW_piece_seats
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_piece_seats
#print axioms VerifiableInference.Desc.First.Att.P.k5AtO_is
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_anyPlanOk
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_k5AtO
