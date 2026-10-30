-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReadAs.lean: from the view of a written transcript to the typed transcript
made of what was heard.

Main names:
  `Listed`, `valsOf_listed`: a list of names has no repeats and holds the name a at the number num
    a.
  `sumOk_of`, `tailOk_of`, `unitsOk_of`: SumOk from the ties (OfP, SizeP, SumAt, ValsOf) and Listed.
  `unitsHeard_eq`, `heard_eq`: the typed data's own lists, laid as rounds, are L.rounds.
  `reads_of_view`: where the view's rounds, their digests struck, hold a list of heard rounds, the
    view's rounds read in
    the field read that list.
  `TListed`, `UListed`.
  `carry_reads`: at a written transcript whose tests of work pass and whose view holds L.rounds, for
    typed data with the
    four ties: the carry's image is the chain's joined transcript on ownTrs.

Premises of carry_reads: Said; as many written rounds as specs; no written round has an "answer"
item; the tests of
work pass; the lists of names are Listed at the numberings.
Sources: Att/K05ReadOwn.lean; Att/K05One.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ReadOwn
import Johnson.Desc.First.Att.K05One

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Pv.Att Cb.Pv.Lay Johnson.L5.Layers OnBytes OnBytes.Model OnBytes.Slice OnBytes.Flat
open OnBytes.Maker Run Fo.Peel TwV OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH unitsTrs ownTrs)
open VerifiableInference.Desc.Part

noncomputable section

variable {M X : Type}

/-- The list holds the name a at the number num a, and has no repeats. -/
def Listed {A : Type} (sh : List A) (num : A → ℕ) : Prop := sh.Nodup ∧ ∀ a, sh[num a]? = some a

theorem valsOf_listed {A : Type} {sh : List A} {num : A → ℕ} (h : Listed sh num) (l : List GE) (a : A) :
    Tw.valsOf sh l a = l.getD (num a) 0 := by
  classical
  obtain ⟨hl, ha⟩ := List.getElem?_eq_some_iff.1 (h.2 a)
  have e := h.1.idxOf_getElem (num a) hl
  rw [ha] at e
  unfold Tw.valsOf
  rw [e]

theorem sumOk_of {Y : Type} {S : SumL GE M Y} {D : SumH Reading.gl S} {riders pre : List E} {H : PscH}
    {hh : MaskedSum.Heard} {C : Aff} {st : Stage} {G : Fork} {a : Add S} {sh : List S.T.A} (o : OfP D riders H hh)
    (z : SizeP S st) (sa : SumAt C st pre H hh G) (v : ValsOf D a) (ls : Listed sh a.num) : SumOk D sh := by
  obtain ⟨n, rfl⟩ := z
  refine ⟨by rw [o.r, o.n], ?_, funext fun x => ?_⟩
  · rw [o.H, sumAt_rs sa]
    simp
  · rw [valsOf_listed ls, getD_read, v.1 x]

theorem unitsHeard_eq : ∀ (us : List (SumL GE M (Seen GE X))) (du : UnitsH Reading.gl us) (ps : List (ℕ × ℕ))
    (os : List (ℕ × MaskedSum.Heard)) (pre : List E) (l : List (List E × PscH)), UnitsOfP us du ps os pre l →
    unitsHeard us du = unitsRounds pre l
  | [], _, [], [], _, [], _ => rfl
  | _ :: us, d, _ :: ps, _ :: os, pre, (v7, H) :: l, ⟨_, o, o2⟩ => by
    show sumRounds d.1.r d.1.H ++ unitsHeard us d.2 = sumRounds (pre ++ v7) H ++ unitsRounds [] l
    rw [o.r, o.H, unitsHeard_eq us d.2 ps os [] l o2]
  | [], _, [], [], _, _ :: _, h => h.elim
  | [], _, [], _ :: _, _, _, h => h.elim
  | [], _, _ :: _, _, _, _, h => h.elim
  | _ :: _, _, [], _, _, _, h => h.elim
  | _ :: _, _, _ :: _, [], _, _, h => h.elim
  | _ :: _, _, _ :: _, _ :: _, _, [], h => h.elim

theorem heard_eq {A : AttOwn GE M X} {du : UnitsH Reading.gl A.units} {dt : TailH Reading.gl A.tail}
    {x : Params.AttentionRounds} {h : Heard} {L : Lists}
    (t1 : UnitsOfP A.units du x.score h.scores.toList L.planes.flatten L.units) (t2 : TailOfP dt x h L) :
    unitsHeard A.units du ++ tailHeard dt = L.rounds := by
  rw [unitsHeard_eq _ _ _ _ _ _ t1]
  unfold tailHeard Lists.rounds
  rw [t2.oE.r, t2.oE.H, t2.xV, t2.oM.r, t2.oM.H, t2.oVD.r, t2.oVD.H, t2.pts, t2.mx, t2.xF, t2.oF.r, t2.oF.H, t2.xD,
    t2.oD.r, t2.oD.H, t2.xH, t2.oH.r, t2.oH.H]

theorem reads_of_view : ∀ {hs : List RoundH} {rs : List Fmt.RoundView}, RoundsAre hs (rs.map noDigest) →
    List.Forall₂ Reads hs (rs.map (Fo.rdRV Reading.gl))
  | [], [], _ => .nil
  | _ :: _, r :: _, ⟨a, b⟩ => .cons
    ⟨congrArg (List.map Reading.gl.val) (holds_sent (r := noDigest r) a.1), fun l hl =>
      congrArg (List.map Reading.gl.val) (a.2 l hl).symm⟩ (reads_of_view b)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- The tail's lists of names are listed at the numberings. -/
structure TListed {T : Tail GE M X} (q : Shs T) (nm : TailNums T) : Prop where
  lE : Listed q.hE nm.nE
  lM : Listed q.hM nm.nM
  lVD : Listed q.hVD nm.nVD
  lF : Listed q.hF nm.nF
  lD : Listed q.hD nm.nD
  lH : Listed q.hH nm.nH

def UListed : (us : List (SumL GE M (Seen GE X))) → UShs us → UnitsNums us → Prop
  | [], _, _ => True
  | _ :: us, q, nm => Listed q.1.1 nm.1 ∧ UListed us q.2 nm.2

theorem tailOk_of {T : Tail GE M X} {dt : TailH Reading.gl T} {x : Params.AttentionRounds} {h : Heard} {G : Fork}
    {L : Lists} {q : Shs T} {nm : TailNums T} (nz : BetasNz Reading.gl L) (x1 : X) (hs : Said x h G L)
    (t2 : TailOfP dt x h L) (t4 : TailVals dt (tailAdd T L h nz nm x1)) (lq : TListed q nm) : TailOk dt q :=
  ⟨sumOk_of t2.oE t2.zE hs.sE t4.vE lq.lE, sumOk_of t2.oM t2.zM hs.sM t4.vM lq.lM,
    sumOk_of t2.oVD t2.zVD hs.sVD t4.vVD lq.lVD, sumOk_of t2.oF t2.zF hs.sF t4.vF lq.lF,
    sumOk_of t2.oD t2.zD hs.sD t4.vD lq.lD, sumOk_of t2.oH t2.zH hs.sH t4.vH lq.lH⟩

theorem unitsOk_of {G : Fork} : ∀ (us : List (SumL GE M (Seen GE X))) (du : UnitsH Reading.gl us)
    (ps : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (pre : List E) (l : List (List E × PscH)) (q : UShs us)
    (nm : UnitsNums us) (s : Seen GE X), UnitsAt ps os pre l G → UnitsOfP us du ps os pre l →
    UnitsVals us du (unitsAdd (ρ := Reading.gl) us nm pre l s) → UListed us q nm → UnitsOk us du q
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: us, d, _ :: ps, _ :: os, _, (_, _) :: l, q, nm, _, ⟨_, _, a3, _, a5⟩, ⟨z, o, o2⟩, ⟨v, v2⟩, ⟨l1, l2⟩ =>
    ⟨sumOk_of o z a3 v l1, unitsOk_of us d.2 ps os [] l q.2 nm.2 _ a5 o2 v2 l2⟩
  | _ :: _, _, [], _, _, _, _, _, _, _, h, _, _ => h.elim
  | _ :: _, _, _ :: _, [], _, _, _, _, _, _, h, _, _ => h.elim
  | _ :: _, _, _ :: _, _ :: _, _, [], _, _, _, _, h, _, _ => h.elim

/-- **(c).** -/
theorem carry_reads (Ex : ExtSpec) (A : AttOwn GE M X) (qu : UShs A.units) (qt : Shs A.tail)
    (nu : UnitsNums A.units) (nt : TailNums A.tail) (lu : UListed A.units qu nu) (lt : TListed qt nt) (ds : List RDT)
    (hl : ds.length = (chSp A.ch (ownRd A qu qt)).length) (hA : ∀ d ∈ ds, NoAns d.items)
    (τ : Tr (uLT (ckP .two) ds)) (hp : passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    {x : Params.AttentionRounds} {h : Heard} {G : Fork} {L : Lists} (hs : Said x h G L)
    (hr : RoundsAre L.rounds ((rvT (ckP .two) ds τ).map noDigest)) (nz : BetasNz Reading.gl L) (x0 : X)
    (du : UnitsH Reading.gl A.units) (dt : TailH Reading.gl A.tail)
    (t1 : UnitsOfP A.units du x.score h.scores.toList L.planes.flatten L.units) (t2 : TailOfP dt x h L)
    (t3 : UnitsVals A.units du (unitsAdd (ρ := Reading.gl) A.units nu L.planes.flatten L.units (x0, [])))
    (t4 : TailVals dt (tailAdd A.tail L h nz nt (OnBytes.Tie.Pv.Att.seenAfter A.units du (x0, [])))) :
    (chCarry Ex A.ch (ownRd A qu qt) ds hl).tr τ = some (A.ch.join Ex (ownTrs A du dt)) := by
  rw [chCarry_tr Ex A.ch _ ds hl hA τ hp]
  refine congrArg some (own_img Ex A qu qt du dt
    (unitsOk_of A.units du _ _ _ _ qu nu _ hs.units t1 t3 lu) (tailOk_of nz _ hs t2 t4 lt) ?_)
  rw [heard_eq t1 t2]
  exact reads_of_view hr

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.carry_reads
