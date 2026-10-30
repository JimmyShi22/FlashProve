-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Data.lean: the law of kind K5 is not empty: the typed data of which
Att/K5Law.lean speaks are made here, from the lists heard, under one premise on the view and numbers
of
the plan; and the typed end values are tied to what was shown.

Main names:
  `BetasNz ρ L`: the premise on the view: the element drawn in each sumcheck's round of the further
    variable reads other than 0. The kind's text does not ask it: the part tests no beta, and the
      ledger
    takes any factor. Without it the typed data do not exist, and the law says nothing of that view.
  `Add S`: what the typed side adds at a sumcheck: each end value's number among those heard; the
    public state. `mkSum`, `mkTail`, `ValsOf`: the data; a typed end value is the reading of the one
    heard under its number.
  `TailFits`, `UnitsFits`: the letters' numbers against the plan's.
  `tail_exists`, `units_exist`, `data_exist`: the data, with their ties.
  `paid_slots`: a stage's debt is: its row is worth 0, and for each end value the map at the
    output's
    point is what its slot is worth in the ledger's world; under the places of the mask entries.

Limit: that BetasNz holds of a view which the general step accepts is not shown in this file or in
what it imports.
Sources: what Att/K5Law.lean names.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- **The premise on the view**: what is drawn «never 0» reads other than 0. -/
structure BetasNz (ρ : Reading K) (L : Lists) : Prop where
  units : ∀ u ∈ L.units, ρ.val u.2.beta ≠ 0
  bE : ρ.val L.HE.beta ≠ 0
  bM : ρ.val L.HM.beta ≠ 0
  bVD : ρ.val L.HVD.beta ≠ 0
  bF : ρ.val L.HF.beta ≠ 0
  bD : ρ.val L.HD.beta ≠ 0
  bH : ρ.val L.HH.beta ≠ 0

/-- What the typed side adds at a sumcheck. -/
structure Add {X : Type} (S : SumL K M X) where
  /-- an end value's number among those heard -/
  num : S.T.A → Nat
  st : S.T.St

/-- The data of one sumcheck. -/
def mkSum {X : Type} (S : SumL K M X) (riders : List E) (H : PscH) (hb : ρ.val H.beta ≠ 0) (a : Add S) (t : E) :
    SumH ρ S :=
  ⟨riders, H, hb, fun x => ρ.val (H.v.getD (a.num x) zeroE), a.st, t⟩

/-- The typed end values are those heard, read; the state is the one added. -/
def ValsOf {X : Type} {S : SumL K M X} (D : SumH ρ S) (a : Add S) : Prop :=
  (∀ x, D.v x = ρ.val (D.H.v.getD (a.num x) zeroE)) ∧ D.st = a.st

/-! ## The tail -/

structure TailAdd {X : Type} (T : Tail K M X) where
  aE : Add T.sE
  aM : Add T.sVM
  aVD : Add T.sVD
  aF : Add T.sF
  aD : Add T.sD
  aH : Add T.sH

def mkTail {X : Type} (T : Tail K M X) (L : Lists) (h : Heard) (nz : BetasNz ρ L) (a : TailAdd T) : TailH ρ T where
  dE := mkSum T.sE L.ridersE L.HE nz.bE a.aE h.division.target
  xV := L.xV
  dVM := mkSum T.sVM L.vC L.HM nz.bM a.aM h.below.target
  dVD := mkSum T.sVD [] L.HVD nz.bVD a.aVD h.on.target
  pts := L.pt
  mx := L.vM
  xF := L.xF
  dF := mkSum T.sF [] L.HF nz.bF a.aF h.atIndex.target
  xD := L.xD
  dD := mkSum T.sD [] L.HD nz.bD a.aD h.key.target
  xH := L.xH
  dH := mkSum T.sH [] L.HH nz.bH a.aH h.cells.target

/-- The tail's letters have the plan's numbers. -/
structure TailFits {X : Type} (T : Tail K M X) (x : Params.AttentionRounds) : Prop where
  zE : SizeP T.sE (products x.e x.pairs)
  nE : T.sE.n = 5 + (x.lt + 2)
  zM : SizeP T.sVM (products x.valueM x.pairs)
  nM : T.sVM.n = 2
  zVD : SizeP T.sVD (products x.valueD x.pairs)
  nVD : T.sVD.n = 0
  nz : T.nz = 2 * x.lgk + 2 * x.lt + 4
  np : T.np = x.pairs
  zF : SizeP T.sF (products x.attained x.pairs)
  nF : T.sF.n = 0
  zD : SizeP T.sD (keyStage x)
  nD : T.sD.n = 0
  zH : SizeP T.sH (products x.bits x.pairs)
  nH : T.sH.n = 0

structure TailVals {X : Type} {T : Tail K M X} (dt : TailH ρ T) (a : TailAdd T) : Prop where
  vE : ValsOf dt.dE a.aE
  vM : ValsOf dt.dVM a.aM
  vVD : ValsOf dt.dVD a.aVD
  vF : ValsOf dt.dF a.aF
  vD : ValsOf dt.dD a.aD
  vH : ValsOf dt.dH a.aH

theorem units_ne {G : Fork} : ∀ {ps : List (Nat × Nat)} {os : List (Nat × MaskedSum.Heard)} {pre : List E}
    {l : List (List E × PscH)}, UnitsAt ps os pre l G → ps ≠ [] → leftOf pre l = []
  | _ :: _, _ :: _, _, (_, _) :: _, _, _ => rfl
  | [], _, _, _, _, h => absurd rfl h
  | _ :: _, [], _, _, h, _ => h.elim
  | _ :: _, _ :: _, _, [], h, _ => h.elim

theorem tail_exists {X : Type} (T : Tail K M X) {x : Params.AttentionRounds} {h : Heard} {G : Fork} {L : Lists}
    (hs : Said x h G L) (hne : x.score ≠ []) (nz : BetasNz ρ L) (f : TailFits T x) (a : TailAdd T) :
    TailOfP (mkTail T L h nz a) x h L ∧ TailVals (mkTail T L h nz a) a := by
  have hE : L.ridersE.length = 5 + (x.lt + 2) := by
    unfold Lists.ridersE
    rw [units_ne hs.units hne]
    simp [hs.l5, hs.lI, hs.l2]
  exact ⟨
    { zE := f.zE, oE := ⟨rfl, by rw [f.nE, hE], rfl, rfl⟩, xV := rfl
      zM := f.zM, oM := ⟨rfl, by rw [f.nM, hs.lC], rfl, rfl⟩
      zVD := f.zVD, oVD := ⟨rfl, f.nVD, rfl, rfl⟩
      pts := rfl, nz := by rw [f.nz, hs.lPt], mx := rfl, np := by rw [f.np, hs.lM], xF := rfl
      zF := f.zF, oF := ⟨rfl, f.nF, rfl, rfl⟩, xD := rfl
      zD := f.zD, oD := ⟨rfl, f.nD, rfl, rfl⟩, xH := rfl
      zH := f.zH, oH := ⟨rfl, f.nH, rfl, rfl⟩ },
    ⟨⟨fun _ => rfl, rfl⟩, ⟨fun _ => rfl, rfl⟩, ⟨fun _ => rfl, rfl⟩, ⟨fun _ => rfl, rfl⟩, ⟨fun _ => rfl, rfl⟩,
      ⟨fun _ => rfl, rfl⟩⟩⟩

/-! ## The units -/

def UnitsAdd {X : Type} : List (SumL K M (Seen K X)) → Type
  | [] => Unit
  | u :: us => Add u × UnitsAdd us

/-- The units' letters have the plan's numbers. k: the scalars that wait in front of the first. -/
def UnitsFits {X : Type} : List (SumL K M (Seen K X)) → List (Nat × Nat) → Nat → Prop
  | [], [], _ => True
  | u :: us, p :: ps, k => SizeP u (products p.1 p.2) ∧ u.n = k + 7 ∧ UnitsFits us ps 0
  | _, _, _ => False

def UnitsVals {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → UnitsAdd us → Prop
  | [], _, _ => True
  | _ :: us, d, a => ValsOf d.1 a.1 ∧ UnitsVals us d.2 a.2

theorem units_exist {X : Type} {G : Fork} : ∀ (us : List (SumL K M (Seen K X))) (ps : List (Nat × Nat))
    (os : List (Nat × MaskedSum.Heard)) (pre : List E) (l : List (List E × PscH)), UnitsAt ps os pre l G →
    UnitsFits us ps pre.length → (∀ u ∈ l, ρ.val u.2.beta ≠ 0) → ∀ a : UnitsAdd us,
    ∃ du : UnitsH ρ us, UnitsOfP us du ps os pre l ∧ UnitsVals us du a
  | [], [], [], _, [], _, _, _, _ => ⟨(), trivial, trivial⟩
  | u :: us, p :: ps, o :: os, pre, (v7, H) :: l, ⟨a1, _, _, _, a5⟩, ⟨z, n, fs⟩, nz, a => by
    obtain ⟨du, b1, b2⟩ := units_exist us ps os [] l a5 fs (fun w hw => nz w (List.mem_cons_of_mem _ hw)) a.2
    exact ⟨(mkSum u (pre ++ v7) H (nz (v7, H) List.mem_cons_self) a.1 o.2.target, du),
      ⟨z, ⟨rfl, by rw [n, List.length_append, a1], rfl, rfl⟩, b1⟩, ⟨fun _ => rfl, rfl⟩, b2⟩
  | [], _ :: _, _, _, _, _, hf, _, _ => hf.elim
  | _ :: _, [], _, _, _, _, hf, _, _ => hf.elim
  | [], [], _ :: _, _, _, h, _, _, _ => h.elim
  | [], [], [], _, _ :: _, h, _, _, _ => h.elim
  | _ :: _, _ :: _, [], _, _, h, _, _, _ => h.elim
  | _ :: _, _ :: _, _ :: _, _, [], h, _, _, _ => h.elim

theorem planes_length {G : Fork} : ∀ {js : List Nat} {vs : List (List E)}, PlanesAt js vs G →
    vs.flatten.length = 3 * vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨a, _, c⟩ => by
    rw [List.flatten_cons, List.length_append, a, planes_length c, List.length_cons]
    omega
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **The data exist.** -/
theorem data_exist {X : Type} (A : AttOwn K M X) {p : Par} {h : Heard} {G : Fork} {L : Lists}
    (hp : planOk p = true) (hs : Said p.own h G L) (nz : BetasNz ρ L)
    (fu : UnitsFits A.units p.own.score (3 * p.own.planeMessages)) (ft : TailFits A.tail p.own)
    (au : UnitsAdd A.units) (at' : TailAdd A.tail) :
    ∃ (du : UnitsH ρ A.units) (dt : TailH ρ A.tail),
      UnitsOfP A.units du p.own.score h.scores.toList L.planes.flatten L.units ∧ TailOfP dt p.own h L ∧
      UnitsVals A.units du au ∧ TailVals dt at' := by
  have hne : p.own.score ≠ [] := by
    unfold planOk at hp
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    exact hp.1.1
  rw [← hs.nPlanes, ← planes_length hs.planes] at fu
  obtain ⟨du, a1, a2⟩ := units_exist A.units _ _ _ _ hs.units fu nz.units au
  obtain ⟨b1, b2⟩ := tail_exists A.tail hs hne nz ft at'
  exact ⟨du, _, a1, b1, a2, b2⟩

/-! ## A stage's debt, in slots -/

/-- **A stage's debt**: its row is worth 0, and each end value's slot is worth the map's value at
the output's point. -/
theorem paid_slots {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hD : OfP D riders H hh) (h : SumAt C st riders H hh Gf) (a : Add S)
    (hv : ValsOf D a) (hn : ∀ x, a.num x < H.v.length) (m : M) (mask : Nat → K) (entry : Nat → Nat → Nat → K)
    (hm : ∀ x, S.msg m (S.T.cAt x) = mask (hh.sEnd + a.num x)) (f : Aff) :
    Paid S D f (Gf.worldOf ρ mask entry) m ↔ f.value ρ (Gf.worldOf ρ mask entry) = 0 ∧
      ∀ x, S.T.map D.st (S.msg m) x (ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt) =
        (Gf.worldOf ρ mask entry).slot (hh.sEnd + a.num x) :=
  and_congr_right' (forall_congr' fun x =>
    end_slot S D hD h m x (a.num x) (hn x) mask entry (by rw [hv.1 x, hD.H]) (hm x))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.tail_exists
#print axioms VerifiableInference.Desc.First.Att.P.units_exist
#print axioms VerifiableInference.Desc.First.Att.P.data_exist
#print axioms VerifiableInference.Desc.First.Att.P.paid_slots
