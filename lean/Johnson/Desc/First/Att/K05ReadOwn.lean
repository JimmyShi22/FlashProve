-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReadOwn.lean: the reading of Att/K05Read.lean along the chain of
attention's own rounds
(Cb/Pv/Att/Own.lean: AttOwn.ch: the units, then the tail's eleven stages).

Main names:
  `drERd`, `drPtRd`: how one element, and a point of n coordinates, are made of the elements drawn.
  `SumOk`: a stage's data have the letters' numbers, and their end values are those heard, in the
    order of a list of names.
  `ChIs.stage`: a sumcheck's stage in front of a chain.
  `Shs`, `tailRd`, `tailHeard`, `TailOk`, `tail_is`: the tail. `UShs`, `unitsRd`, `unitsHeard`,
    `UnitsOk`, `units_is`: the
    units in front.
  `ownRd`, `own_img`: for all plain data that read the rounds as they were heard, the image is the
    chain's joined
    transcript on the typed transcripts made of what was heard (ownTrs).

Sources: Att/K05ReadSum.lean; OnBytes/Tie/Pv/Att/OwnTie.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ReadSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Pv.Att Cb.Pv.Lay Johnson.L5.Layers OnBytes OnBytes.Model OnBytes.Slice OnBytes.Flat
open OnBytes.Maker Run Fo.Peel TwV OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH unitsTrs ownTrs)

noncomputable section

variable {M : Type}

/-- One element. -/
def drERd : DrRd (drE GE).D where
  k := 1
  dl := fun x => [x]
  mkD := fun l => l.headD 0
  inv := fun l h => Tw.one_of_len l h

/-- A point of n coordinates. -/
def drPtRd (n : ℕ) : DrRd (drPt GE n).D where
  k := n
  dl := fun p => List.ofFn p
  mkD := fun l => fun i : Fin n => l.getD i.1 0
  inv := fun l h => Tw.ofFn_getD l n h

/-- The stage's data have the letters' numbers; their end values are those heard, in sh's order. -/
structure SumOk {X : Type} {S : SumL GE M X} (D : SumH Reading.gl S) (sh : List S.T.A) : Prop where
  r : D.r.length = S.n
  rs : D.H.rs.length = S.T.nv
  v : Tw.valsOf sh (D.H.v.map Reading.gl.val) = D.v

/-- A sumcheck's stage in front of a chain. -/
theorem ChIs.stage {X : Type} (S : SumL GE M X) (Ow : S.Nx → M → Prop) (next : Ch GE M S.Nx)
    (D : SumH Reading.gl S) (sh : List S.T.A) (nd : sh.Nodup) (ok : SumOk D sh) (rn : ChRd next) (tn : next.Trs)
    (pa pb : Rounds GE) (hp : List.Forall₂ Reads (sumRounds D.r D.H) pa) (h : ChIs next rn tn pb) :
    ChIs (S.stage Ow next) (plainRd S.T sh nd, rn) (D.tr, tn) (pa ++ pb) :=
  ⟨pa, pb, rfl, by
    show pa.length = (plainSp S.T.nv S.T.deg S.T.DY ++ [_]).length + 1
    rw [← hp.length_eq, sumRounds_length, List.length_append, plainSp_length, ok.rs]
    rfl, sum_img' D sh nd ok.r ok.rs ok.v hp, h⟩

/-! ## The tail -/

/-- The end values' names of the tail's six sumchecks, each in a list without repeats. -/
structure Shs {X : Type} (T : Tail GE M X) where
  hE : List T.sE.T.A
  nE : hE.Nodup
  hM : List T.sVM.T.A
  nM : hM.Nodup
  hVD : List T.sVD.T.A
  nVD : hVD.Nodup
  hF : List T.sF.T.A
  nF : hF.Nodup
  hD : List T.sD.T.A
  nD : hD.Nodup
  hH : List T.sH.T.A
  nH : hH.Nodup

variable {X : Type}

/-- The reader's data along the tail. -/
def tailRd (T : Tail GE M X) (q : Shs T) : ChRd T.ch :=
  (plainRd T.sE.T q.hE q.nE, (drERd, (plainRd T.sVM.T q.hM q.nM, (plainRd T.sVD.T q.hVD q.nVD, (drPtRd T.nz,
    (drERd, (plainRd T.sF.T q.hF q.nF, (drERd, (plainRd T.sD.T q.hD q.nD, (drERd,
      (plainRd T.sH.T q.hH q.nH, ())))))))))))

/-- The tail's rounds as they were heard, of the typed data's own lists. -/
def tailHeard {T : Tail GE M X} (d : TailH Reading.gl T) : List RoundH :=
  sumRounds d.dE.r d.dE.H ++ (([], some [d.xV]) :: (sumRounds d.dVM.r d.dVM.H ++ (sumRounds d.dVD.r d.dVD.H ++
    (([], some d.pts) :: (d.mx, some [d.xF]) :: (sumRounds d.dF.r d.dF.H ++ (([], some [d.xD]) ::
      (sumRounds d.dD.r d.dD.H ++ (([], some [d.xH]) :: sumRounds d.dH.r d.dH.H))))))))

structure TailOk {T : Tail GE M X} (d : TailH Reading.gl T) (q : Shs T) : Prop where
  oE : SumOk d.dE q.hE
  oM : SumOk d.dVM q.hM
  oVD : SumOk d.dVD q.hVD
  oF : SumOk d.dF q.hF
  oD : SumOk d.dD q.hD
  oH : SumOk d.dH q.hH

theorem tail_is {T : Tail GE M X} (d : TailH Reading.gl T) (q : Shs T) (ok : TailOk d q) {p : Rounds GE}
    (hp : List.Forall₂ Reads (tailHeard d) p) : ChIs T.ch (tailRd T q) d.trs p := by
  unfold tailHeard at hp
  obtain ⟨pE, p1, rfl, hE, k1⟩ := Tw.f2_split _ _ _ hp
  obtain ⟨xV, p2, hV, k2, rfl⟩ := List.forall₂_cons_left_iff.1 k1
  obtain ⟨pM, p3, rfl, hM, k3⟩ := Tw.f2_split _ _ _ k2
  obtain ⟨pVD, p4, rfl, hVD, k4⟩ := Tw.f2_split _ _ _ k3
  obtain ⟨xP, p5, hP, k5, rfl⟩ := List.forall₂_cons_left_iff.1 k4
  obtain ⟨xS, p6, hS, k6, rfl⟩ := List.forall₂_cons_left_iff.1 k5
  obtain ⟨pF, p7, rfl, hF, k7⟩ := Tw.f2_split _ _ _ k6
  obtain ⟨xD, p8, hD, k8, rfl⟩ := List.forall₂_cons_left_iff.1 k7
  obtain ⟨pD, p9, rfl, hDD, k9⟩ := Tw.f2_split _ _ _ k8
  obtain ⟨xH, pH, hH, k10, rfl⟩ := List.forall₂_cons_left_iff.1 k9
  refine ChIs.stage T.sE _ _ d.dE q.hE q.nE ok.oE _ _ _ _ hE ?_
  refine ⟨xV, _, rfl, by rw [hV.2 _ rfl]; rfl, ?_⟩
  refine ChIs.stage T.sVM _ _ d.dVM q.hM q.nM ok.oM _ _ _ _ hM ?_
  refine ChIs.stage T.sVD _ _ d.dVD q.hVD q.nVD ok.oVD _ _ _ _ hVD ?_
  refine ⟨xP, _, rfl, by rw [hP.2 _ rfl]; exact funext fun i => getD_read d.pts i.1, ?_⟩
  refine ⟨xS, _, rfl, by rw [hS.1]; exact funext fun i => getD_read d.mx i.1, by rw [hS.2 _ rfl]; rfl, ?_⟩
  refine ChIs.stage T.sF _ _ d.dF q.hF q.nF ok.oF _ _ _ _ hF ?_
  refine ⟨xD, _, rfl, by rw [hD.2 _ rfl]; rfl, ?_⟩
  refine ChIs.stage T.sD _ _ d.dD q.hD q.nD ok.oD _ _ _ _ hDD ?_
  refine ⟨xH, _, rfl, by rw [hH.2 _ rfl]; rfl, ?_⟩
  have := ChIs.stage T.sH T.sH.Out (.done _) d.dH q.hH q.nH ok.oH () () pH [] k10 rfl
  rwa [List.append_nil] at this

/-! ## The units in front -/

/-- The end values' names of the units. -/
def UShs : List (SumL GE M (Seen GE X)) → Type
  | [] => Unit
  | u :: us => {sh : List u.T.A // sh.Nodup} × UShs us

def unitsRd (tail : Ch GE M (Seen GE X)) (rt : ChRd tail) : (us : List (SumL GE M (Seen GE X))) → UShs us →
    {X' : Type} → (pr : X' → Seen GE X) → ChRd (unitsCh us pr tail)
  | [], _, _, pr => ChRd.comap tail rt pr
  | u :: us, q, _, _ => (plainRd u.T q.1.1 q.1.2, unitsRd tail rt us q.2 _)

def unitsHeard : (us : List (SumL GE M (Seen GE X))) → UnitsH Reading.gl us → List RoundH
  | [], _ => []
  | _ :: us, d => sumRounds d.1.r d.1.H ++ unitsHeard us d.2

def UnitsOk : (us : List (SumL GE M (Seen GE X))) → UnitsH Reading.gl us → UShs us → Prop
  | [], _, _ => True
  | _ :: us, d, q => SumOk d.1 q.1.1 ∧ UnitsOk us d.2 q.2

theorem units_is (tail : Ch GE M (Seen GE X)) (rt : ChRd tail) (ts : tail.Trs) (pb : Rounds GE)
    (h : ChIs tail rt ts pb) : ∀ (us : List (SumL GE M (Seen GE X))) (d : UnitsH Reading.gl us) (q : UShs us)
    {X' : Type} (pr : X' → Seen GE X), UnitsOk us d q → ∀ pa : Rounds GE,
    List.Forall₂ Reads (unitsHeard us d) pa →
    ChIs (unitsCh us pr tail) (unitsRd tail rt us q pr) (unitsTrs tail ts us d pr) (pa ++ pb)
  | [], _, _, _, pr, _, _, .nil => ChIs.comap tail rt ts pb pr h
  | u :: us, d, q, _, pr, ok, pa, hp => by
    obtain ⟨p1, p2, rfl, h1, h2⟩ := Tw.f2_split _ _ _ (show List.Forall₂ Reads
      (sumRounds d.1.r d.1.H ++ unitsHeard us d.2) pa from hp)
    have ih := units_is tail rt ts pb h us d.2 q.2
      (fun b : (_ × (Fin u.n → GE)) × u.T.our.par.Out => ((pr b.1.1).1, (pr b.1.1).2 ++ [List.ofFn b.1.2])) ok.2 p2 h2
    refine ⟨p1, p2 ++ pb, List.append_assoc _ _ _, ?_, sum_img' d.1 q.1.1 q.1.2 ok.1.r ok.1.rs ok.1.v h1, ih⟩
    show p1.length = (plainSp u.T.nv u.T.deg u.T.DY ++ [_]).length + 1
    rw [← h1.length_eq, sumRounds_length, List.length_append, plainSp_length, ok.1.rs]
    rfl

/-! ## The whole -/

/-- The reader's data along the chain of attention's own rounds. -/
def ownRd (A : AttOwn GE M X) (qu : UShs A.units) (qt : Shs A.tail) : ChRd A.ch :=
  unitsRd A.tail.ch (tailRd A.tail qt) A.units qu _

/-- **The image of the plain data is the chain's joined transcript.** -/
theorem own_img (Ex : ExtSpec) (A : AttOwn GE M X) (qu : UShs A.units) (qt : Shs A.tail)
    (du : UnitsH Reading.gl A.units) (dt : TailH Reading.gl A.tail) (hu : UnitsOk A.units du qu)
    (ht : TailOk dt qt) {p : Rounds GE} (hp : List.Forall₂ Reads (unitsHeard A.units du ++ tailHeard dt) p) :
    img _ _ (chRds Ex A.ch (ownRd A qu qt)) p = A.ch.join Ex (ownTrs A du dt) := by
  obtain ⟨pa, pb, rfl, h1, h2⟩ := Tw.f2_split _ _ _ hp
  exact img_join Ex A.ch _ _ _ (units_is A.tail.ch _ dt.trs _ (tail_is dt qt ht h2) A.units du qu _ hu pa h1)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.own_img
