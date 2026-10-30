-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Claims.lean: the law of kind K5: the letters' claims, which Att/K05Law.lean
takes as
premises, cut in two and half paid. A claim is a pair (the target read, the public state). The state
is
the typed side's to choose: the data are made here with each state the letters' own claim's second
part,
stage by stage. What is left is the first part: the letters' claim's first part is the reading of
the
part's record's target.

Main names:
  `Target`, `State`, `claim_iff`.
  `TailNums`, `tailAdd`, `tailData`, `TailTargets`, `tail_claims`: the tail's six stages.
  `UnitsNums`, `unitsAdd`, `UnitsTargets`, `units_claims`: the softmax-table units.

Sources: what Att/K5Data.lean names.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- The letters' claim's first part is the target, read. -/
abbrev Target {X : Type} {S : SumL K M X} (D : SumH ρ S) (x : X) : Prop := (S.cl x D.rd).1 = ρ.val D.t
/-- The public state is the letters' claim's second part. -/
abbrev State {X : Type} {S : SumL K M X} (D : SumH ρ S) (x : X) : Prop := D.st = (S.cl x D.rd).2

theorem claim_iff {X : Type} {S : SumL K M X} (D : SumH ρ S) (x : X) : D.Claim x ↔ Target D x ∧ State D x := by
  unfold SumH.Claim
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, (congrArg Prod.snd h).symm⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 h2.symm

/-! ## The tail -/

/-- For each of the six sumchecks: each end value's number among those heard. -/
structure TailNums {X : Type} (T : Tail K M X) where
  nE : T.sE.T.A → Nat
  nM : T.sVM.T.A → Nat
  nVD : T.sVD.T.A → Nat
  nF : T.sF.T.A → Nat
  nD : T.sD.T.A → Nat
  nH : T.sH.T.A → Nat

section Tail
variable {X : Type} (T : Tail K M X) (L : Lists) (h : Heard) (nz : BetasNz ρ L) (nm : TailNums T) (x : X)

noncomputable def aE : Add T.sE := ⟨nm.nE, (T.sE.cl x (rd ρ T.sE.n L.ridersE)).2⟩
noncomputable def dE : SumH ρ T.sE := mkSum T.sE L.ridersE L.HE nz.bE (aE (ρ := ρ) T L nm x) h.division.target
noncomputable def y2 : T.sE.Nx × K := ((dE T L h nz nm x).nx x, ρ.val L.xV)
noncomputable def aM : Add T.sVM := ⟨nm.nM, (T.sVM.cl (y2 T L h nz nm x) (rd ρ T.sVM.n L.vC)).2⟩
noncomputable def dM : SumH ρ T.sVM := mkSum T.sVM L.vC L.HM nz.bM (aM T L h nz nm x) h.below.target
noncomputable def y3 : T.sVM.Nx := (dM T L h nz nm x).nx (y2 T L h nz nm x)
noncomputable def aVD : Add T.sVD := ⟨nm.nVD, (T.sVD.cl (y3 T L h nz nm x) (rd ρ T.sVD.n [])).2⟩
noncomputable def dVD : SumH ρ T.sVD := mkSum T.sVD [] L.HVD nz.bVD (aVD T L h nz nm x) h.on.target
noncomputable def y6 : ((T.sVD.Nx × (Fin T.nz → K)) × (Fin T.np → K)) × K :=
  ((((dVD T L h nz nm x).nx (y3 T L h nz nm x), rd ρ T.nz L.pt), rd ρ T.np L.vM), ρ.val L.xF)
noncomputable def aF : Add T.sF := ⟨nm.nF, (T.sF.cl (y6 T L h nz nm x) (rd ρ T.sF.n [])).2⟩
noncomputable def dF : SumH ρ T.sF := mkSum T.sF [] L.HF nz.bF (aF T L h nz nm x) h.atIndex.target
noncomputable def y8 : T.sF.Nx × K := ((dF T L h nz nm x).nx (y6 T L h nz nm x), ρ.val L.xD)
noncomputable def aD : Add T.sD := ⟨nm.nD, (T.sD.cl (y8 T L h nz nm x) (rd ρ T.sD.n [])).2⟩
noncomputable def dD : SumH ρ T.sD := mkSum T.sD [] L.HD nz.bD (aD T L h nz nm x) h.key.target
noncomputable def y10 : T.sD.Nx × K := ((dD T L h nz nm x).nx (y8 T L h nz nm x), ρ.val L.xH)
noncomputable def aH : Add T.sH := ⟨nm.nH, (T.sH.cl (y10 T L h nz nm x) (rd ρ T.sH.n [])).2⟩

/-- **What the typed side adds at the tail, each state the letters' own.** -/
noncomputable def tailAdd : TailAdd T :=
  ⟨aE (ρ := ρ) T L nm x, aM T L h nz nm x, aVD T L h nz nm x, aF T L h nz nm x, aD T L h nz nm x, aH T L h nz nm x⟩

/-- The tail's data. -/
noncomputable def tailData : TailH ρ T := mkTail T L h nz (tailAdd T L h nz nm x)

/-- The targets, stage by stage. -/
structure TailTargets (dt : TailH ρ T) (x : X) : Prop where
  tE : Target dt.dE x
  tM : Target dt.dVM (dt.x2 x)
  tVD : Target dt.dVD (dt.x3 x)
  tF : Target dt.dF (dt.x6 x)
  tD : Target dt.dD (dt.x8 x)
  tH : Target dt.dH (dt.x10 x)

/-- **For these data the letters' claims are the targets.** -/
theorem tail_claims : (tailData T L h nz nm x).Claims x ↔ TailTargets T (tailData T L h nz nm x) x :=
  ⟨fun c => ⟨((claim_iff _ _).1 c.cE).1, ((claim_iff _ _).1 c.cVM).1, ((claim_iff _ _).1 c.cVD).1,
      ((claim_iff _ _).1 c.cF).1, ((claim_iff _ _).1 c.cD).1, ((claim_iff _ _).1 c.cH).1⟩,
    fun t => ⟨(claim_iff _ _).2 ⟨t.tE, rfl⟩, (claim_iff _ _).2 ⟨t.tM, rfl⟩, (claim_iff _ _).2 ⟨t.tVD, rfl⟩,
      (claim_iff _ _).2 ⟨t.tF, rfl⟩, (claim_iff _ _).2 ⟨t.tD, rfl⟩, (claim_iff _ _).2 ⟨t.tH, rfl⟩⟩⟩

end Tail

/-! ## The units -/

def UnitsNums {X : Type} : List (SumL K M (Seen K X)) → Type
  | [] => Unit
  | u :: us => (u.T.A → Nat) × UnitsNums us

/-- What the typed side adds at the units, each state the letters' own. s: what the first has seen.
-/
noncomputable def unitsAdd {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsNums us → List E →
    List (List E × PscH) → Seen K X → UnitsAdd us
  | [], _, _, _, _ => ()
  | u :: us, nm, pre, l, s =>
    (⟨nm.1, (u.cl s (rd ρ u.n (pre ++ (l.headD ([], ⟨zeroE, zeroE, [], [], zeroE, []⟩)).1))).2⟩,
      unitsAdd us nm.2 [] l.tail
        (s.1, s.2 ++ [List.ofFn (rd ρ u.n (pre ++ (l.headD ([], ⟨zeroE, zeroE, [], [], zeroE, []⟩)).1))]))

def UnitsTargets {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → Seen K X → Prop
  | [], _, _ => True
  | _ :: us, d, s => Target d.1 s ∧ UnitsTargets us d.2 (s.1, s.2 ++ [List.ofFn d.1.rd])

/-- For data made of the lists with these states, the units' claims are the targets. -/
theorem units_claims {X : Type} : ∀ (us : List (SumL K M (Seen K X))) (du : UnitsH ρ us) (ps : List (Nat × Nat))
    (os : List (Nat × MaskedSum.Heard)) (pre : List E) (l : List (List E × PscH)) (nm : UnitsNums us)
    (s : Seen K X), UnitsOfP us du ps os pre l → UnitsVals us du (unitsAdd (ρ := ρ) us nm pre l s) →
    (UnitsClaims us du s ↔ UnitsTargets us du s)
  | [], _, _, _, _, _, _, _, _, _ => Iff.rfl
  | u :: us, d, p :: ps, o :: os, pre, (v7, H) :: l, nm, s, ⟨_, of, hn⟩, ⟨hv, hvs⟩ => by
    have hrd : d.1.rd = rd ρ u.n (pre ++ v7) := by
      show rd ρ u.n d.1.r = _
      rw [of.r]
    have hst : State d.1 s := by
      show d.1.st = _
      rw [hv.2, hrd]
      rfl
    have ih := units_claims us d.2 ps os [] l nm.2 (s.1, s.2 ++ [List.ofFn d.1.rd]) hn (by
      rw [hrd]
      exact hvs)
    exact and_congr ((claim_iff _ _).trans (and_iff_left hst)) ih
  | _ :: _, _, [], _, _, _, _, _, ho, _ => ho.elim
  | _ :: _, _, _ :: _, [], _, _, _, _, ho, _ => ho.elim
  | _ :: _, _, _ :: _, _ :: _, _, [], _, _, ho, _ => ho.elim

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.tail_claims
#print axioms VerifiableInference.Desc.First.Att.P.units_claims
