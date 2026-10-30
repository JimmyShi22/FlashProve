-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Spec.lean: the specs of the reading (Att/K05Read.lean: chSp) are the
library's spEnt over the kind's
own entries. So written rounds whose entries are the kind's ROUNDS, and that send and draw elements
alone, meet them.

Main names:
  `spEnt_entry`, `plainSp_eq`, `zero_sp`, `chSp_comap`, `entries_planes`.
  `stage_spec`, `ShsLen`, `tail_spec`, `ULen`, `units_spec`, `own_spec`: stage by stage, then along
    the chain, under the
    letters' numbers against the plan (UnitsFits, TailFits) and the lists' lengths.
  `own_meets`: every written round is Plain, and the entries are those of `rounds p`: then the
    written rounds meet the
    specs (the library's meets_mapT).

Sources: OnBytes/Tie/Pv/Lookup/Forest/FoPeelT.lean, FoMeetPlan.lean; Att/K05ReadOwn.lean;
Att/K5Data.lean; Att/K5Returns.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelT
import Johnson.Desc.First.Att.K05ReadOwn
import Johnson.Desc.First.Att.K5Data
import Johnson.Desc.First.Att.K5Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Pv.Att Cb.Pv.Lay Johnson.L5.Layers OnBytes OnBytes.Model OnBytes.Slice OnBytes.Flat
open OnBytes.Maker Run Fo.Peel TwV OnBytes.Model.Road
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)

variable {M X : Type}

theorem spEnt_entry (name : String) (s k z : ℕ) :
    Fo.spEnt (MaskedSum.entry name s k z) = ⟨s, k, k != 0 && z == k⟩ := by
  unfold Fo.spEnt MaskedSum.entry
  simp

theorem plainSp_eq : ∀ (k : ℕ) (n : Fin k → ℕ) (DY : ℕ),
    plainSp k n DY = (List.ofFn n).map (fun d => (⟨d, 1, false⟩ : Tw.RSp)) ++ [⟨DY, 1, true⟩]
  | 0, _, _ => rfl
  | k + 1, n, DY => by
    rw [List.ofFn_succ]
    exact congrArg ((⟨n 0, 1, false⟩ : Tw.RSp) :: ·) (plainSp_eq k (fun i => n i.succ) DY)

/-- A sumcheck's stage. -/
theorem stage_spec {Y : Type} (S : SumL GE M Y) {st : Stage} (z : SizeP S st) (sh : List S.T.A) {vs : List Var}
    {e : Ends} (hst : st = .sum vs e) (hn : sh.length = e.n) :
    (MaskedSum.entries ⟨S.n, vs, some e⟩).map Fo.spEnt =
      (⟨S.n + 1, 1, false⟩ : Tw.RSp) :: (plainSp S.T.nv S.T.deg S.T.DY ++ [⟨sh.length, 0, false⟩]) := by
  obtain ⟨n, rfl⟩ := z
  injection hst with h1 h2
  subst h1 h2
  rw [plainSp_eq, hn]
  simp [MaskedSum.entries, spEnt_entry, Function.comp_def, Var.d]

theorem zero_sp (n : ℕ) : (n != 0 && (0 : ℕ) == n) = false := by
  cases n <;> simp

/-- The lists of names have the plan's lengths. -/
structure ShsLen {T : Tail GE M X} (q : Shs T) (x : Params.AttentionRounds) : Prop where
  lE : q.hE.length = 2 * x.pairs
  lM : q.hM.length = 2 * x.pairs
  lVD : q.hVD.length = 2 * x.pairs
  lF : q.hF.length = 2 * x.pairs
  lD : q.hD.length = x.Lam + x.pairs * x.lt
  lH : q.hH.length = 2 * x.pairs

theorem tail_spec (T : Tail GE M X) (q : Shs T) (x : Params.AttentionRounds) (hf : TailFits T x) (hq : ShsLen q x) :
    chSp T.ch (tailRd T q) = (entriesOf 0 (tailStages x)).map Fo.spEnt := by
  have eE := stage_spec T.sE hf.zE q.hE rfl hq.lE
  have eM := stage_spec T.sVM hf.zM q.hM rfl hq.lM
  have eVD := stage_spec T.sVD hf.zVD q.hVD rfl hq.lVD
  have eF := stage_spec T.sF hf.zF q.hF rfl hq.lF
  have eD := stage_spec T.sD hf.zD q.hD rfl hq.lD
  have eH := stage_spec T.sH hf.zH q.hH rfl hq.lH
  show ((⟨T.sE.n + 1, 1, false⟩ : Tw.RSp) :: (plainSp T.sE.T.nv T.sE.T.deg T.sE.T.DY ++ [⟨q.hE.length, 0, false⟩])) ++
    ([⟨0, 1, false⟩] ++
    (((⟨T.sVM.n + 1, 1, false⟩ : Tw.RSp) :: (plainSp T.sVM.T.nv T.sVM.T.deg T.sVM.T.DY ++ [⟨q.hM.length, 0, false⟩])) ++
    (((⟨T.sVD.n + 1, 1, false⟩ : Tw.RSp) :: (plainSp T.sVD.T.nv T.sVD.T.deg T.sVD.T.DY ++ [⟨q.hVD.length, 0, false⟩])) ++
    ([⟨0, T.nz, false⟩] ++ ([⟨T.np, 1, false⟩] ++
    (((⟨T.sF.n + 1, 1, false⟩ : Tw.RSp) :: (plainSp T.sF.T.nv T.sF.T.deg T.sF.T.DY ++ [⟨q.hF.length, 0, false⟩])) ++
    ([⟨0, 1, false⟩] ++
    (((⟨T.sD.n + 1, 1, false⟩ : Tw.RSp) :: (plainSp T.sD.T.nv T.sD.T.deg T.sD.T.DY ++ [⟨q.hD.length, 0, false⟩])) ++
    ([⟨0, 1, false⟩] ++
    (((⟨T.sH.n + 1, 1, false⟩ : Tw.RSp) :: (plainSp T.sH.T.nv T.sH.T.deg T.sH.T.DY ++ [⟨q.hH.length, 0, false⟩])) ++
      [])))))))))) = _
  rw [← eE, ← eM, ← eVD, ← eF, ← eD, ← eH, hf.nE, hf.nM, hf.nVD, hf.nF, hf.nD, hf.nH, hf.nz, hf.np]
  have a1 : 0 + 5 + x.lt + 2 = 5 + (x.lt + 2) := by omega
  simp only [tailStages, entriesOf, products, keyStage, List.map_append, List.map_cons, List.map_nil, a1, Nat.zero_add,
    spEnt_entry, zero_sp]
  simp [Fo.spEnt]

theorem chSp_comap : ∀ {Y : Type} (c : Ch GE M Y) (r : ChRd c) {Y' : Type} (f : Y' → Y),
    chSp (c.comap f) (ChRd.comap c r f) = chSp c r
  | _, .done _, _, _, _ => rfl
  | _, .ride _ n _ _ _ _ _ next, r, _, _ => by
    show ((⟨n + 1, 1, false⟩ : Tw.RSp) :: (r.1.sp ++ [⟨r.1.sh.length, 0, false⟩])) ++
      chSp (next.comap _) (ChRd.comap next r.2 _) = _ ++ chSp next r.2
    rw [chSp_comap next r.2 _]
  | _, .draw _ _ _ next, r, _, _ => by
    show [(⟨0, r.1.k, false⟩ : Tw.RSp)] ++ chSp (next.comap _) (ChRd.comap next r.2 _) = _ ++ chSp next r.2
    rw [chSp_comap next r.2 _]
  | _, .send n _ _ _ _ next, r, _, _ => by
    show [(⟨n, r.1.k, false⟩ : Tw.RSp)] ++ chSp (next.comap _) (ChRd.comap next r.2 _) = _ ++ chSp next r.2
    rw [chSp_comap next r.2 _]

/-- The units' lists of names have the plan's lengths. -/
def ULen : (us : List (SumL GE M (Seen GE X))) → UShs us → List (ℕ × ℕ) → Prop
  | [], _, [] => True
  | _ :: us, q, p :: ps => q.1.1.length = 2 * p.2 ∧ ULen us q.2 ps
  | _, _, _ => False

theorem units_spec (tail : Ch GE M (Seen GE X)) (rt : ChRd tail) (rest : List Stage)
    (ht : chSp tail rt = (entriesOf 0 rest).map Fo.spEnt) : ∀ (us : List (SumL GE M (Seen GE X))) (q : UShs us)
    (ps : List (ℕ × ℕ)) (k : ℕ) {X' : Type} (pr : X' → Seen GE X), UnitsFits us ps k → ULen us q ps →
    (ps = [] → k = 0) →
    chSp (unitsCh us pr tail) (unitsRd tail rt us q pr) =
      (entriesOf k ((ps.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ rest)).map Fo.spEnt
  | [], _, [], k, _, pr, _, _, hk => by
    rw [hk rfl]
    exact (chSp_comap tail rt pr).trans ht
  | u :: us, q, p :: ps, k, _, pr, ⟨z, n, fs⟩, ⟨l1, l2⟩, _ => by
    have ih := units_spec tail rt rest ht us q.2 ps 0
      (fun b : (_ × (Fin u.n → GE)) × u.T.our.par.Out => ((pr b.1.1).1, (pr b.1.1).2 ++ [List.ofFn b.1.2])) fs l2
      (fun _ => rfl)
    have e := stage_spec u z q.1.1 rfl l1
    show ((⟨u.n + 1, 1, false⟩ : Tw.RSp) :: (plainSp u.T.nv u.T.deg u.T.DY ++ [⟨q.1.1.length, 0, false⟩])) ++
      chSp (unitsCh us (fun b : (_ × (Fin u.n → GE)) × u.T.our.par.Out =>
        ((pr b.1.1).1, (pr b.1.1).2 ++ [List.ofFn b.1.2])) tail) (unitsRd tail rt us q.2 _) = _
    rw [← e, ih, n]
    show _ = (MaskedSum.entries ⟨k + 7, _, _⟩ ++ entriesOf 0 _).map Fo.spEnt
    rw [List.map_append]
    rfl
  | [], _, _ :: _, _, _, _, h, _, _ => h.elim
  | _ :: _, _, [], _, _, _, h, _, _ => h.elim

theorem entries_planes (l : List Stage) : ∀ (n k : ℕ),
    entriesOf k (List.replicate n (.scalars 3) ++ l) = entriesOf (k + 3 * n) l
  | 0, _ => rfl
  | n + 1, k => by
    show entriesOf (k + 3) (List.replicate n (.scalars 3) ++ l) = _
    rw [entries_planes l n (k + 3)]
    congr 1
    omega

/-- **The reading's specs are the specs of K5's own entries.** -/
theorem own_spec (A : AttOwn GE M X) (qu : UShs A.units) (qt : Shs A.tail) (x : Params.AttentionRounds)
    (hu : UnitsFits A.units x.score (3 * x.planeMessages)) (ht : TailFits A.tail x) (lu : ULen A.units qu x.score)
    (lt : ShsLen qt x) (hne : x.score ≠ []) :
    chSp A.ch (ownRd A qu qt) = (entriesOf 0 (script x)).map Fo.spEnt := by
  rw [script_eq, entries_planes, Nat.zero_add]
  exact units_spec A.tail.ch _ _ (tail_spec A.tail qt x ht lt) A.units qu x.score _ _ hu lu fun h => absurd h hne

/-- **(b)'s premise**: written rounds whose entries are K5's ROUNDS, and that send and draw elements
alone, meet the specs. -/
theorem own_meets (A : AttOwn GE M X) (qu : UShs A.units) (qt : Shs A.tail) (p : Par)
    (hu : UnitsFits A.units p.own.score (3 * p.own.planeMessages)) (ht : TailFits A.tail p.own)
    (lu : ULen A.units qu p.own.score) (lt : ShsLen qt p.own) (hne : p.own.score ≠ []) (ds : List RDT)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry)) :
    List.Forall₂ MeetsT ds (chSp A.ch (ownRd A qu qt)) := by
  have h := meets_mapT ds hd
  rw [he] at h
  rw [own_spec A qu qt p.own hu ht lu lt hne]
  have e : ((rounds p).map (·.entry)).map Fo.spEnt = (entriesOf 0 (script p.own)).map Fo.spEnt := by
    unfold rounds
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    show Fo.spEnt (if e.drawE == 0 then e else { e with work := p.work }) = Fo.spEnt e
    split <;> rfl
  rwa [e] at h

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.own_meets
#print axioms VerifiableInference.Desc.First.Att.P.tail_spec
