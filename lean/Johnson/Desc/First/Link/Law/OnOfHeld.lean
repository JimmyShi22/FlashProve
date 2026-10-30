-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OnOfHeld.lean (kind K10): K10's OWN CONDITION IN FRONT (`K10OnS`: the field hOn of `K10Heavy`) FROM FOUR FIELDS OF THE ROWS' ASKS (`RowAsks`, Johnson/Desc/First/Close/Law/HRowAtFa.lean: the field hX of `K10Heavy`), IN THEIR OWN TEXTS, AND
WHAT IS THEN STILL LEFT. Two theorems: calls of OnOfShapes.lean and CountsOfHeld.lean (both beside this file).

Why. `OnLeft` (OnOfShapes.lean) has ten fields. Two of them (plain · gens: the two counts of the group's open rows) follow from the table's promise's own Bool `rowsHeld`, which `RowAsks` bears (rows), with its field grp and one closed test on the plan
(`coveredB`). The order and the hinge, which `onS_of_left` takes beside, ARE `RowAsks`' fields inOrder and shapes. So hOn falls to hX, the five numbers, the front, and what is closed, but for seed and plan.

What is said.
  `onLeft_of_held`: the six closed (good · agrees · kL · h0 · apart · tie) · nP = plainDue Nu O m · nG = gensDue Nu O m · grp · rows · m ∈ rowSegs O · coveredB Nu O m = true · seed · plan ⊢ `OnLeft`.
  `onS_of_held`: **front · the five · RowAsks' inOrder | shapes | grp | rows (each in that field's own text) · these ⊢ `K10OnS`.**
THE FILE DOES NOT IMPORT `RowAsks`: it restates four fields: a caller passes hX.inOrder, hX.shapes, hX.grp, hX.rows.

Limits. AN IMPLICATION. seed and plan are premises at the state. coveredB at the constant's numbers is closed:
a theorem since, under InScope and LaidAt (`covered_laid`, Johnson/LPFE1R/RowsDueAt.lean).
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OnOfShapes
import Johnson.Desc.First.Link.Law.CountsOfHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop
open IOR Prob Run KObj OnBytes.Params OnBytes.Means Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs Wit)
open VerifiableInference.Desc.First (Numbers Item rowsHeld rowSegs)
open VerifiableInference.Desc.LinkJoin (coveredB plainDue gensDue plain_of_held gens_of_held)
open VerifiableInference.Desc.LinkJoin (numBy smpDrawn smpDrawn_seed pSseed esOf esOf_nodup esOf_all
  members_of_shapes inMain_of_shapes inKept_of_shapes inMask_of_shapes sampleFits_of_shapes)

attribute [local instance] Classical.propDecidable

variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ) (seats : List (ℕ × ℕ)) (s : Sg) (e : ℕ)
  (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
  (keep : (sigOf cs lo).O → Prop) [DecidablePred keep]
  (pull : ((groupLayK cs lo s e kb hM hZ).Sh.Cin.J → GE) →
    (groupLayK cs lo s e kb hM hZ).G.C.J → GE)
  (nP nG : ℕ)

variable (fx : Fin (((groupLayK cs lo s e kb hM hZ).Sh.fold
    (SbV (groupLayK cs lo s e kb hM hZ) (Fin nP ⊕ Fin nG)) (slV (groupLayK cs lo s e kb hM hZ) pull)
    (ZV (groupLayK cs lo s e kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG)
      (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
        (esOf_all cs lo s e kb hM hZ)))).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub ((groupLayK cs lo s e kb hM hZ).sizeB keep
    (SbV (groupLayK cs lo s e kb hM hZ) (Fin nP ⊕ Fin nG)) (slV (groupLayK cs lo s e kb hM hZ) pull)
    (ZV (groupLayK cs lo s e kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG)
      (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
        (esOf_all cs lo s e kb hM hZ)))).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
  (w₁ : LdBrW (groupLayK cs lo s e kb hM hZ).G ((groupLayK cs lo s e kb hM hZ).sizeB keep
    (SbV (groupLayK cs lo s e kb hM hZ) (Fin nP ⊕ Fin nG)) (slV (groupLayK cs lo s e kb hM hZ) pull)
    (ZV (groupLayK cs lo s e kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG)
      (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
        (esOf_all cs lo s e kb hM hZ)))).kp Wp)
  (L : List (BatFoldCaller GE)) {Pz : Type}
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : VerifiableInference.Desc.First.S × F.E.Str →
    (groupLayK cs lo s e kb hM hZ).Sh.par.Cw.nat.Str) (T₀ : Statement) (L₀ : GroupLayout)

/-- **WHAT IS LEFT, WITH THE TWO COUNTS PAID OUT OF THE PROMISE's OWN Bool.** -/
theorem onLeft_of_held (a : VerifiableInference.Desc.First.S × F.E.Str) (Nu : Numbers) (O : List
    Item) (m : ℕ)
    (hP : nP = plainDue Nu O m) (hN : nG = gensDue Nu O m)
    (good : (groupLayK cs lo s e kb hM hZ).Good) (agrees : LayoutAgrees lo kb) (kL : kLay lo kb =
        s.h + s.g) (h0 : s.h = 0)
    (apart : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, numAt seats ⟨⟨lo, seat⟩, i⟩ = numAt seats ⟨⟨lo,
        seat⟩, j⟩ → i = j)
    (tie : ∀ i : Fin lo.length, memMain lo i → K1.Tie cs (lo.get i).1)
    (grp : (rdK a.1).2.1.group = Nu.groupAt m) (rows : rowsHeld Nu O a.1 = true) (hm : m ∈ rowSegs
        O) (hc : coveredB Nu O m = true)
    (seed : ∀ i : Fin lo.length, memMain lo i → ∃ (ρ : (Fin (bitsZ cs (lo.get i).1) → GE) × GEˣ) (y
        : GE), K1.SeedIs cs (lo.get i).1 a.1.st (numAt seats ⟨⟨lo, seat⟩, i⟩) ρ y)
    (plan : ∀ Gr lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → (begun (rdK a.1).2.2
        (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay → ∀ as D, pSseed cs lo
        (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩,
        i⟩) T₀ L₀ (fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) as D = pSseed cs lo (groupLayK cs lo s e kb
        hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) (begun (rdK
        a.1).2.2 (rdK a.1).2.1.group Gr) lay (fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) as D) :
    OnLeft cs lo seat seats s e kb hM hZ nP nG T₀ L₀ a :=
  ⟨good, agrees, kL, h0, apart, tie,
    fun Gr hG => by
      rw [hP]
      rw [grp] at hG
      exact plain_of_held rows hm hG hc,
    fun Gr hG => by
      rw [hN]
      rw [grp] at hG
      exact gens_of_held rows hm hG hc,
    seed, plan⟩

/-- **K10's CONDITION IN FRONT FROM THE ROWS' ASKS, THE FIVE, THE FRONT AND WHAT IS CLOSED; seed
    AND plan STAY.** -/
theorem onS_of_held (Pr : Par) (z : Pz) (a : VerifiableInference.Desc.First.S × F.E.Str) (Nu :
    Numbers) (O : List Item) (m : ℕ)
    (hP : nP = plainDue Nu O m) (hN : nG = gensDue Nu O m)
    (front : ((Cb.Pv.Bat.inJ ((groupLayK cs lo s e kb hM hZ).sizeB keep (SbV (groupLayK cs lo s e kb
        hM hZ) (Fin nP ⊕ Fin nG)) (slV (groupLayK cs lo s e kb hM hZ) pull) (ZV (groupLayK cs lo s e
        kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s e kb hM
        hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)))) A₀).keepE (groupLayK cs
        lo s e kb hM hZ).Sh.par.Cw.nat).on (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ)
        (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) keep pull (nP + (esOf cs
        lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e
        kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁ L (fun (a : Pz ×
        VerifiableInference.Desc.First.S) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀ st₀ e₀ mW z a))
    (five : (planOf (entries Pr) (rdK a.1)).k = s.h + s.g ∧ (planOf (entries Pr) (rdK a.1)).h = s.h
        ∧ (∀ Gr lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → (begun (rdK a.1).2.2
        (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay → 2 ^ lay.logEll = s.C.l ∧ 2 ^
        lay.logEllZk = s.Z.l) ∧ ((rdK a.1).2.2.codes.mask.getD (planOf (entries Pr) (rdK
        a.1)).maskCode default).ell = s.Z.l)
    (inOrder : InOrder (rdK a.1).2.2)
    (shapes : ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → ShapesAre (rdK a.1).2.2
        Gr lo kb fun i => numAt seats ⟨⟨lo, seat⟩, i⟩)
    (grp : (rdK a.1).2.1.group = Nu.groupAt m) (rows : rowsHeld Nu O a.1 = true) (hm : m ∈ rowSegs
        O) (hc : coveredB Nu O m = true)
    (good : (groupLayK cs lo s e kb hM hZ).Good) (agrees : LayoutAgrees lo kb) (kL : kLay lo kb =
        s.h + s.g) (h0 : s.h = 0)
    (apart : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, numAt seats ⟨⟨lo, seat⟩, i⟩ = numAt seats ⟨⟨lo,
        seat⟩, j⟩ → i = j)
    (tie : ∀ i : Fin lo.length, memMain lo i → K1.Tie cs (lo.get i).1)
    (seed : ∀ i : Fin lo.length, memMain lo i → ∃ (ρ : (Fin (bitsZ cs (lo.get i).1) → GE) × GEˣ) (y
        : GE), K1.SeedIs cs (lo.get i).1 a.1.st (numAt seats ⟨⟨lo, seat⟩, i⟩) ρ y)
    (plan : ∀ Gr lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → (begun (rdK a.1).2.2
        (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay → ∀ as D, pSseed cs lo
        (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩,
        i⟩) T₀ L₀ (fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) as D = pSseed cs lo (groupLayK cs lo s e kb
        hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) (begun (rdK
        a.1).2.2 (rdK a.1).2.1.group Gr) lay (fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) as D) :
    K10OnS (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo,
        seat⟩, i⟩) keep pull (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s
        e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁
        L (pSseed cs lo (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt
        seats ⟨⟨lo, seat⟩, i⟩) T₀ L₀ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) Pr (faK10 G cs lo seat
        (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩,
        i⟩) keep pull (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s e kb
        hM hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁ L
        (fun (a : Pz × VerifiableInference.Desc.First.S) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀
        st₀ e₀ mW z) a :=
  onS_of_left G cs lo seat seats s e kb hM hZ keep pull nP nG fx A₀ bC bZ w₀ w₁ L σ₀ st₀ e₀ mW T₀ L₀
      Pr z a front five inOrder shapes
    (onLeft_of_held cs lo seat seats s e kb hM hZ nP nG T₀ L₀ a Nu O m hP hN good agrees kL h0 apart
        tie grp rows hm hc seed plan)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.onLeft_of_held
#print axioms VerifiableInference.Desc.First.Close.onS_of_held
