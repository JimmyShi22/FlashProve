-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OnOfRowAsks.lean (kind K10): K10's OWN CONDITION IN FRONT (`K10OnS`: the field hOn of `K10Heavy`) FROM THE ROWS' ASKS THEMSELVES (`RowAsks`, Johnson/Desc/First/Close/Law/HRowAtFa.lean: the field hX of `K10Heavy`). A theorem: one call.

Why. OnOfHeld.lean (beside this file) restates four of `RowAsks`' fields and does not import the structure: that these are its fields, at the same group, names and numbering, has no check. Here the structure is imported and the call is made: LEAN's OWN CHECK.
A NAME: beneath HRowAtFa.lean lies Johnson/Desc/BlockSlot.lean, whose `VerifiableInference.Desc.numAt` (three numbers) takes the bare name «numAt» inside this namespace ahead of the opened `Sound.numAt` (a list of seats and a member): so here it is written `Sound.numAt`.

What is said.
  `onS_of_rowAsks`: **hX : RowAsks cs lo seat kb (groupLayK cs lo s e kb hM hZ) (namesOf … Sound.numAt seats) Nu m O (fun i => Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) a.1 · front · the five · m ∈ rowSegs O · coveredB Nu O m = true · nP | nG the plan's two counts · the six closed ·
    seed · plan ⊢ `K10OnS`.**

Limits. AN IMPLICATION. As OnOfHeld.lean's. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OnOfHeld
import Johnson.Desc.First.Close.Law.HRowAtFa

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
open VerifiableInference.Desc.LinkJoin (coveredB plainDue gensDue)
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

/-- **hOn AT ONE STATEMENT, FROM hX.** -/
theorem onS_of_rowAsks (Pr : Par) (z : Pz) (a : VerifiableInference.Desc.First.S × F.E.Str) (Nu :
    Numbers) (O : List Item) (m : ℕ)
    (hX : RowAsks cs lo seat kb (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i =>
        Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) Nu m O (fun i => Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) a.1)
    (hP : nP = plainDue Nu O m) (hN : nG = gensDue Nu O m)
    (front : ((Cb.Pv.Bat.inJ ((groupLayK cs lo s e kb hM hZ).sizeB keep (SbV (groupLayK cs lo s e kb
        hM hZ) (Fin nP ⊕ Fin nG)) (slV (groupLayK cs lo s e kb hM hZ) pull) (ZV (groupLayK cs lo s e
        kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s e kb hM
        hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)))) A₀).keepE (groupLayK cs
        lo s e kb hM hZ).Sh.par.Cw.nat).on (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ)
        (namesOf cs lo s e kb hM hZ fun i => Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) keep pull (nP +
            (esOf cs
        lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e
        kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁ L (fun (a : Pz ×
        VerifiableInference.Desc.First.S) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀ st₀ e₀ mW z a))
    (five : (planOf (entries Pr) (rdK a.1)).k = s.h + s.g ∧ (planOf (entries Pr) (rdK a.1)).h = s.h
        ∧ (∀ Gr lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → (begun (rdK a.1).2.2
        (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay → 2 ^ lay.logEll = s.C.l ∧ 2 ^
        lay.logEllZk = s.Z.l) ∧ ((rdK a.1).2.2.codes.mask.getD (planOf (entries Pr) (rdK
        a.1)).maskCode default).ell = s.Z.l)
    (hm : m ∈ rowSegs O) (hc : coveredB Nu O m = true)
    (good : (groupLayK cs lo s e kb hM hZ).Good) (agrees : LayoutAgrees lo kb) (kL : kLay lo kb =
        s.h + s.g) (h0 : s.h = 0)
    (apart : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, Sound.numAt seats ⟨⟨lo, seat⟩, i⟩ = Sound.numAt
        seats ⟨⟨lo,
        seat⟩, j⟩ → i = j)
    (tie : ∀ i : Fin lo.length, memMain lo i → K1.Tie cs (lo.get i).1)
    (seed : ∀ i : Fin lo.length, memMain lo i → ∃ (ρ : (Fin (bitsZ cs (lo.get i).1) → GE) × GEˣ) (y
        : GE), K1.SeedIs cs (lo.get i).1 a.1.st (Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) ρ y)
    (plan : ∀ Gr lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → (begun (rdK a.1).2.2
        (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay → ∀ as D, pSseed cs lo
        (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => Sound.numAt seats ⟨⟨lo,
            seat⟩,
        i⟩) T₀ L₀ (fun i => Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) as D = pSseed cs lo (groupLayK cs lo
            s e kb
        hM hZ) (namesOf cs lo s e kb hM hZ fun i => Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) (begun (rdK
        a.1).2.2 (rdK a.1).2.1.group Gr) lay (fun i => Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) as D) :
    K10OnS (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => Sound.numAt seats
        ⟨⟨lo,
        seat⟩, i⟩) keep pull (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s
        e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁
        L (pSseed cs lo (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i =>
            Sound.numAt
        seats ⟨⟨lo, seat⟩, i⟩) T₀ L₀ fun i => Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) Pr (faK10 G cs lo
            seat
        (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => Sound.numAt seats ⟨⟨lo,
            seat⟩,
        i⟩) keep pull (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s e kb
        hM hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁ L
        (fun (a : Pz × VerifiableInference.Desc.First.S) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀
        st₀ e₀ mW z) a :=
  onS_of_held G cs lo seat seats s e kb hM hZ keep pull nP nG fx A₀ bC bZ w₀ w₁ L σ₀ st₀ e₀ mW T₀ L₀
      Pr z a Nu O m hP hN front five hX.inOrder hX.shapes hX.grp hX.rows hm hc good agrees kL h0
      apart tie seed plan

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.onS_of_rowAsks
