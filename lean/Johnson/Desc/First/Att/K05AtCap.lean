-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05AtCap.lean: TWO STEPS FROM THE KIND's PIECE TOWARDS THE PIECE THAT A RULE
OVER A DESCRIPTION's DATA TAKES: (1) the written rounds are ANY stretch ds that is plain and has the
kind's entries: not only `written p`; (2) the errors are the cap: at each round the whole number
‹the round's challenges› / 2 ^ kc (Iop/ErrCap.lean: Err.cap).

Main names:
  `goodIn_err_le`: GENERAL, for every piece: Piece.GoodIn (Johnson/Desc/Sound/GoodIn.lean) is
    monotone in the piece's errors (Doomed.mono_err, Iop/Rbr.lean).
  `K05_goodIn_anyDs`: K05_goodIn_anyPlanOk (Att/K05KeepsSeats.lean) at any ds with hd (each written
    round is plain) and he (its entries are the kind's): the seam's seam_yes, seam_pass and seam_on'
    hold at any ds. So "the data's stretch is written p" is not needed: two tests on the stretch
    are.
  `K05_goodIn_cap`: **the same at the errors Err.cap kc**, where the stretch's kinds are the
    format's and the Boolean k5Held kc on the kind's public list says yes: by K05_below_fmt
    (Att/K05Kinds.lean) and Err.le_cap_of_below_inv.
  `K05_goodIn_means_cap`: the same with OwnMeans (Att/K05Means.lean) as the relation in front.

Premises: those of K05_goodIn_anyPlanOk; hd, he; for the cap: hkind and a yes of k5Held kc. NONE IS
SHOWN HERE. k5Held is evaluated in no file of this tree. NO MEMBER OF THE WHOLE IS SHOWN.
Limits. Whether Err.cap is the text of the cap that a rule over a description takes is not held
here: no such rule is imported. The block is bare: neither guarded, nor narrowed, nor lifted over a
public part. At kc = 0 the cap is the number of a round's challenges and the statement is empty.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Means
import Johnson.Desc.First.Att.K05Kinds
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- `GoodIn` is monotone in the piece's errors. -/
theorem goodIn_err_le {S Cl W : Type} {C : PQ.CK} {F : Frame} (b : Block S Cl) (base : ℕ)
    (ds : List RDT) (back : List Fmt.RoundView) (ext : S × F.E.Str → Tr (uLT C ds) → W → W)
    {ε ε' : Err (uLT C ds)} (hle : Err.le ε ε') {on on' : S × F.E.Str → Prop}
    {R R' : S × F.E.Str → W → Prop}
    (h : (⟨b, base, ds, back, ext, ε⟩ : Piece C F S Cl W).GoodIn on on' R R') :
    (⟨b, base, ds, back, ext, ε'⟩ : Piece C F S Cl W).GoodIn on on' R R' :=
  fun a ha => Doomed.mono_err _ hle (h a ha)

section
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

open Classical in
/-- **The law at any plain stretch with the kind's entries.** -/
theorem K05_goodIn_anyDs {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) (ok : Bool) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (ds : List RDT) (hd : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = (rounds p).map (·.entry))
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
    (⟨{ attentionKind seatSO claims p with planOk := ok }, base, ds, [], fun _ _ w => w,
        bearErr ds _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)⟩ : Piece (ckP .two) Fr First.S Ck W).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R' :=
  K05_keepsW_left_seats x tl D rad Ex Wp α claim hA H hfs hok p hp ns nx k j0 ds
    (k5Piece (W := W) (ckP .two) Fr seatSO claims p base ds
      (bearErr ds _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).ior.red.out
    (fun a => a.1) (fun b => b.1) x0 yOf on gOf pl hleft
    (fun a τ b _ h => seam_yes seatSO claims p base ds _ a τ b h)
    (fun a τ b h => seam_pass seatSO claims p base ds _ a τ b h)
    hd he I.part (mOfItem I m0) (LaidBehind Fr seatSO p base on) R'
    (fun a τ b ha h => seam_on' seatSO claims p base ds _ on a τ b ha h) hb
    (fun a τ b w _ h hw => seam_pin_item seatSO claims p base ds _ I m0 R' hR' a τ b w h hw)

open Classical in
/-- **The law at the cap.** -/
theorem K05_goodIn_cap {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) (ok : Bool) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (ds : List RDT) (hd : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = (rounds p).map (·.entry))
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
    (hR' : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) (kc : ℕ)
    (hc : k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true) :
    (⟨{ attentionKind seatSO claims p with planOk := ok }, base, ds, [], fun _ _ w => w,
        Err.cap kc (uLT (ckP .two) ds)⟩ : Piece (ckP .two) Fr First.S Ck W).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (I.part w)) R' := by
  have hid := (OnBytes.Road.L5.plan_shape hA).1
  have PA := plan_all hid hok
  obtain ⟨_, _, _, _, _, _, _, U⟩ := PA.units
  have hrec : p.own = recOf (closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))) A.own.rows :=
    hp.trans (rec_of_plan hA PA.law.place (OnBytes.Road.Rows.norm_of_hid hid)
      (Nat.le_of_succ_le (OnBytes.Road.Rows.sizes_of_hid hid).lnT) U _ rfl rfl rfl)
  exact goodIn_err_le _ base ds [] _
    (Err.le_cap_of_below_inv kc _ (K05_below_fmt _ rfl A.own.rows p hrec Ex kc ds he hkind hc))
    (K05_goodIn_anyDs x tl D rad Ex Wp α claim ok hA H hfs hok claims p hp ns nx k j0 base ds hd he
      x0 yOf on gOf pl hleft I m0 R' hb hR')

open Classical in
/-- **The law at the cap, with what it means in front.** -/
theorem K05_goodIn_means_cap {W Cl Ck : Type} {Fr : Frame} (claim : Aff → Cl) (ok : Bool) {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS) (base : ℕ)
    (ds : List RDT) (hd : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = (rounds p).map (·.entry))
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
    (hR' : ∀ b w, R' b w → I.holds (I.rc b.1) b.2 w)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) (kc : ℕ)
    (hc : k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true) :
    (⟨{ attentionKind seatSO claims p with planOk := ok }, base, ds, [], fun _ _ w => w,
        Err.cap kc (uLT (ckP .two) ds)⟩ : Piece (ckP .two) Fr First.S Ck W).GoodIn
      on (LaidBehind Fr seatSO p base on)
      (fun a w => OwnMeans x A.S tl D rad (x0 a).2.1.pt (I.part w)) R' :=
  goodIn_conseq _
    (K05_goodIn_cap x tl D rad Ex Wp α claim ok hA H hfs hok claims p hp ns nx k j0 base ds hd he
      x0 yOf on gOf pl hleft I m0 R' hb hR' hkind kc hc)
    (fun _ _ _ _ _ _ _ h => h)
    (fun a _ _ w _ _ _ _ h => K05_means x tl D rad Ex Wp α hA ns _ (x0 a) (I.part w) h)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.goodIn_err_le
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_anyDs
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_cap
#print axioms VerifiableInference.Desc.First.Att.P.K05_goodIn_means_cap
