-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5HearLaw.lean: the law of kind K5, the hearing's half: the hearing is what
the
proved chain reads. Where hear x (Att/K5AttentionKind.lean) returns, the typed chain of attention's own rounds
(Cb/Pv/Att/Own.lean), on the transcript made of what the rounds hold, has as the outputs of its
sumchecks the readings of the record Heard; and each sumcheck's target reads as the scalars heard
from
which it starts.

Main names:
  `SizeP S st`: the letters S of a sumcheck have the sizes of the script's stage st.
  `OfP D riders H hh`: the typed data D are made of what was heard.
  `OutIsP`, `out_isP`: the typed output is the part's record, read: eps; the last running claim; the
    point (the challenges, then beta); the end values. The one place where PartHearLaw enters.
  `TailOfP`, `TailIsP`, `tail_isP`, `UnitsOfP`, `UnitsAreP`, `units_areP`: the six sumchecks behind
    the softmax-table units; the units.
  `hear_law`: the whole, for every reading, all letters and all data made of the lists heard.

Premises: PartHearLaw (Part/MaskedSumLaw.lean) · Sized F · in the typed data: the reading of each
beta
is other than 0 · SizeP and the riders' number: facts of the letters at a value against the plan.
Sources: what Att/K5SaidAll.lean names, and Cb/Pv/Att/Own.lean (SumL, Tail, Seen, AttOwn);
OnBytes/Tie/Pv/Att/OwnTie.lean (SumH, TailH, UnitsH); Tr.lean (plainOut, plain_ini, plain_last,
plain_vals). No routine that runs in a context is reached.
Limits: one direction, from a return (the other: Att/K5Returns.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Att.OwnTie
import Johnson.Desc.First.Att.K5SaidAll
import Johnson.Desc.Part.MaskedSumLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH SameRead SumRead plainOut plain_ini plain_last plain_vals)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends PartHearLaw)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- The letters have the stage's sizes. -/
def SizeP {X : Type} (S : SumL K M X) (st : Stage) : Prop :=
  ∃ n, st = .sum ((List.ofFn S.T.deg).map fun d => Var.plain (d + 1)) ⟨S.T.DY, n⟩

/-- The data are made of what was heard. -/
structure OfP {X : Type} {S : SumL K M X} (D : SumH ρ S) (riders : List E) (H : PscH) (hh : MaskedSum.Heard) :
    Prop where
  r : D.r = riders
  n : S.n = riders.length
  H : D.H = H
  t : D.t = hh.target

/-- The typed output is the part's record, read. -/
structure OutIsP {X : Type} (S : SumL K M X) (D : SumH ρ S) (hh : MaskedSum.Heard) : Prop where
  st : D.out.st = D.st
  eps : D.out.eps = ρ.val hh.eps
  fin : D.out.fin = ρ.val hh.claim
  ini : ∀ i : Fin S.T.nv, ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt i = ρ.val (hh.r.getD i.1 zeroE)
  last : ldPartLast S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt = ρ.val (hh.r.getLastD zeroE)
  vals : D.out.vals = D.v

theorem out_isP (law : PartHearLaw) {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage}
    {riders : List E} {H : PscH} {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (hD : OfP D riders H hh)
    (h : SumAt C st riders H hh Gf) : OutIsP S D hh := by
  obtain ⟨vs, e, F, G, used, e1, sd, _⟩ := h
  obtain ⟨n, e2⟩ := hs
  rw [e1] at e2
  injection e2 with e3 e4
  subst e3 e4
  obtain ⟨_, _, hH, ht⟩ := hD
  subst hH
  have hl : D.H.rs.map (·.1.length) = List.ofFn S.T.deg := by
    rw [sd.lens, List.map_map]
    exact List.map_id _
  have hlen : D.H.rs.length = S.T.nv := by
    have := congrArg List.length hl
    simpa using this
  refine ⟨rfl, by rw [sd.eps]; rfl, ?_, fun i => ?_, ?_, plain_vals ρ S.T D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _⟩
  · show (plainOut ρ S.T D.st D.t D.H.mu D.H.eps D.H.rs D.H.sentY D.H.beta D.b D.v).fin = _
    rw [law K ρ S.T D.st D.t D.H.mu D.H.eps D.H.rs D.H.sentY D.H.beta D.b D.v S.ok.one hl sd.lenY, sd.claim, ht]
    rfl
  · have hi : i.1 < (D.H.rs.map (·.2)).length := by rw [List.length_map, hlen]; exact i.2
    rw [sd.r, List.getD_append _ _ _ _ hi]
    refine (plain_ini ρ S.T D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _ i).trans ?_
    congr 1
    simp [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases D.H.rs[i.1]? <;> rfl
  · rw [sd.r]
    refine (plain_last ρ S.T D.st _ _ _ D.H.rs D.H.sentY D.H.beta D.b _).trans ?_
    simp

/-! ## The eleven stages behind the softmax-table units -/

/-- The tail's data are made of what was heard, and the letters have the script's sizes. -/
structure TailOfP {X : Type} {T : Tail K M X} (dt : TailH ρ T) (x : Params.AttentionRounds) (h : Heard) (L : Lists) :
    Prop where
  zE : SizeP T.sE (products x.e x.pairs)
  oE : OfP dt.dE L.ridersE L.HE h.division
  xV : dt.xV = L.xV
  zM : SizeP T.sVM (products x.valueM x.pairs)
  oM : OfP dt.dVM L.vC L.HM h.below
  zVD : SizeP T.sVD (products x.valueD x.pairs)
  oVD : OfP dt.dVD [] L.HVD h.on
  pts : dt.pts = L.pt
  nz : T.nz = L.pt.length
  mx : dt.mx = L.vM
  np : T.np = L.vM.length
  xF : dt.xF = L.xF
  zF : SizeP T.sF (products x.attained x.pairs)
  oF : OfP dt.dF [] L.HF h.atIndex
  xD : dt.xD = L.xD
  zD : SizeP T.sD (keyStage x)
  oD : OfP dt.dD [] L.HD h.key
  xH : dt.xH = L.xH
  zH : SizeP T.sH (products x.bits x.pairs)
  oH : OfP dt.dH [] L.HH h.cells

/-- The six outputs are the part's records, read; the six targets are read from what was heard. -/
structure TailIsP {X : Type} {T : Tail K M X} (dt : TailH ρ T) (x : Params.AttentionRounds) (h : Heard) (L : Lists) :
    Prop where
  iE : OutIsP T.sE dt.dE h.division
  iM : OutIsP T.sVM dt.dVM h.below
  iVD : OutIsP T.sVD dt.dVD h.on
  iF : OutIsP T.sF dt.dF h.atIndex
  iD : OutIsP T.sD dt.dD h.key
  iH : OutIsP T.sH dt.dH h.cells
  tE : ρ.val dt.dE.t = ρ.val (L.v5.getD 1 zeroE)
  tM : ρ.val dt.dVM.t = ρ.val (L.vC.getD 0 zeroE)
  tVD : ρ.val dt.dVD.t = ρ.val (L.vC.getD 1 zeroE)
  tF : ρ.val dt.dF.t = ∑ b : Fin x.pairs, ρ.val (h.om.getD b.1 zeroE) * ρ.val (L.vM.getD b.1 zeroE)
  tD : ρ.val dt.dD.t = ∑ b : Fin x.pairs, ρ.val (h.om'.getD b.1 zeroE) * ρ.val (L.HF.v.getD (2 * b.1 + 1) zeroE)
  tH : ρ.val dt.dH.t = 0

theorem tail_isP (law : PartHearLaw) {X : Type} {T : Tail K M X} (dt : TailH ρ T) {x : Params.AttentionRounds}
    {h : Heard} {G : Fork} {L : Lists} (hs : Said x h G L) (ho : TailOfP dt x h L) : TailIsP dt x h L where
  iE := out_isP law T.sE dt.dE ho.zE ho.oE hs.sE
  iM := out_isP law T.sVM dt.dVM ho.zM ho.oM hs.sM
  iVD := out_isP law T.sVD dt.dVD ho.zVD ho.oVD hs.sVD
  iF := out_isP law T.sF dt.dF ho.zF ho.oF hs.sF
  iD := out_isP law T.sD dt.dD ho.zD ho.oD hs.sD
  iH := out_isP law T.sH dt.dH ho.zH ho.oH hs.sH
  tE := by rw [ho.oE.t]; exact hs.tE K ρ
  tM := by rw [ho.oM.t]; exact hs.tM K ρ
  tVD := by rw [ho.oVD.t]; exact hs.tVD K ρ
  tF := by rw [ho.oF.t]; exact hs.tF K ρ
  tD := by rw [ho.oD.t]; exact hs.tD K ρ
  tH := by rw [ho.oH.t, hs.tH, ρ.zero]

/-! ## The softmax-table units -/

/-- The units' data are made of what was heard, and the letters have the script's sizes. -/
def UnitsOfP {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → List (Nat × Nat) →
    List (Nat × MaskedSum.Heard) → List E → List (List E × PscH) → Prop
  | [], _, [], [], _, [] => True
  | u :: us, d, p :: ps, o :: os, pre, (v7, H) :: l =>
    SizeP u (products p.1 p.2) ∧ OfP d.1 (pre ++ v7) H o.2 ∧ UnitsOfP us d.2 ps os [] l
  | _, _, _, _, _, _ => False

/-- The units' outputs are the part's records, read; each target is read as the last rider. -/
def UnitsAreP {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → List (Nat × MaskedSum.Heard) → Prop
  | [], _, [] => True
  | u :: us, d, o :: os =>
    OutIsP u d.1 o.2 ∧ ρ.val d.1.t = ρ.val (d.1.r.getD (d.1.r.length - 1) zeroE) ∧ UnitsAreP us d.2 os
  | _, _, _ => False

theorem units_areP (law : PartHearLaw) {X : Type} {G : Fork} :
    ∀ (us : List (SumL K M (Seen K X))) (d : UnitsH ρ us) (ps : List (Nat × Nat))
      (os : List (Nat × MaskedSum.Heard)) (pre : List E) (l : List (List E × PscH)),
      UnitsAt ps os pre l G → UnitsOfP us d ps os pre l → UnitsAreP us d os
  | [], _, [], [], _, [], _, _ => trivial
  | u :: us, d, p :: ps, o :: os, pre, (v7, H) :: l, ⟨a1, _, a3, a4, a5⟩, ⟨z, of, hn⟩ => by
    refine ⟨out_isP law u d.1 z of a3, ?_, units_areP law us d.2 ps os [] l a5 hn⟩
    rw [of.t, a4 K ρ, of.r, List.length_append, a1, show pre.length + 7 - 1 = pre.length + 6 by omega,
      List.getD_append_right _ _ _ _ (by omega), show pre.length + 6 - pre.length = 6 by omega]
  | [], _, [], [], _, _ :: _, _, ho => ho.elim
  | [], _, [], _ :: _, _, _, _, ho => ho.elim
  | [], _, _ :: _, _, _, _, _, ho => ho.elim
  | _ :: _, _, [], _, _, _, _, ho => ho.elim
  | _ :: _, _, _ :: _, [], _, _, _, ho => ho.elim
  | _ :: _, _, _ :: _, _ :: _, _, [], _, ho => ho.elim

/-! ## The whole -/

/-- **(H) The hearing is what the proved chain reads.** -/
theorem hear_law (law : PartHearLaw) {x : Params.AttentionRounds} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear x (F, rs, 0) = some (h, G, [], 0)) (hz : Sized F) :
    ∃ L : Lists, RoundsAre L.rounds rs ∧ Said x h G L ∧ Sized G ∧ Stays F G ∧
      ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (M X : Type) (A : AttOwn K M X) (du : UnitsH ρ A.units)
        (dt : TailH ρ A.tail), UnitsOfP A.units du x.score h.scores.toList L.planes.flatten L.units →
        TailOfP dt x h L → UnitsAreP A.units du h.scores.toList ∧ TailIsP dt x h L := by
  obtain ⟨L, used, a1, a2, a3, a4, a5⟩ := hear_said hh hz
  rw [List.append_nil] at a1
  subst a1
  exact ⟨L, a2, a3, a4, a5, fun K _ _ ρ M X A du dt hu ht =>
    ⟨units_areP law A.units du _ _ _ _ a3.units hu, tail_isP law dt a3 ht⟩⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.out_isP
#print axioms VerifiableInference.Desc.First.Att.P.tail_isP
#print axioms VerifiableInference.Desc.First.Att.P.units_areP
#print axioms VerifiableInference.Desc.First.Att.P.hear_law
