-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TiedOfShapes.lean: THE SECOND LAYING-IN: K10On's CLAUSE
"tied" AT THE GROUP THAT THE PROGRAMS HAVE (groupLayK,
Johnson/Desc/First/Close/Law/CubeOfShapes.lean), ITS SLOTS' NAMES (namesOf) AND ITS MEMBERS' SAMPLES
AS A LIST (esOf): FIVE OF TiedOwes' TEN FIELDS (TiedLaidIn.lean: members · inMain ·
inKept · inMask · fits) FALL TO ShapesAre AND ITS COMPANIONS; FIVE STAY (plain · gens · seed · tie ·
plan). A joining.

  ShapesOwes       WHAT IS LEFT, BY NAME, at a state a, its frame's group Gr, the begun statement's
                   group Gb and layout lay: good · begunAt · ok · shapes (ShapesAre at the begun
                   statement) · shapes0 (ShapesAre in front) · agrees · apart · k · h0 · h (public
                   side) · plain · gens · seed · tie · plan
  owes_of_shapes   ShapesOwes ⊢ TiedOwes: members by members_of_shapes · inMain | inKept | inMask by
                   inMain_of_shapes | … · fits by sampleFits_of_shapes at the laid seed (four
                   other files)
  tied_of_shapes   **ShapesOwes ⊢ RowsTied at the three terms, at groupLayK**

Limits. A JOINING. EVERY FIELD OF ShapesOwes IS A PREMISE: none is shown of any state here.
ShapesAre is shown of no verifier's state. seed: seed_field ends in its text
(not joined here). No soundness statement.

-/
import Johnson.Desc.First.Link.Law.TiedLaidIn
import Johnson.Desc.First.Link.Law.SampleFitsOfShapes
import Johnson.Desc.First.Link.Law.InsideOfShapes
import Johnson.Desc.First.Link.Law.MembersOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop
open IOR Prob Run KObj OnBytes.Params OnBytes.Means Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs Wit)
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

/-- **WHAT IS LEFT OF "tied" AT THE PROGRAMS' GROUP, BY NAME.** -/
structure ShapesOwes (a : VerifiableInference.Desc.First.S × F.E.Str) (Gr Gb : Group)
    (lay : GroupLayout) : Prop where
  good : (groupLayK cs lo s e kb hM hZ).Good
  begunAt : (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr).groups[(rdK a.1).2.1.group]? = some Gb
  ok : GroupOk (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) Gb
  shapes : ShapesAre (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) Gb lo kb
    fun i => numAt seats ⟨⟨lo, seat⟩, i⟩
  shapes0 : ShapesAre (rdK a.1).2.2 Gr lo kb fun i => numAt seats ⟨⟨lo, seat⟩, i⟩
  agrees : AgreesWith lo kb lay
  apart : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo,
    numAt seats ⟨⟨lo, seat⟩, i⟩ = numAt seats ⟨⟨lo, seat⟩, j⟩ → i = j
  k : lay.k = s.h + s.g
  h0 : s.h = 0
  h : lay.h = s.h
  plain : (Gr.rows.filter (·.kind == .plain)).toList.length = nP
  gens : (Gr.rows.filter (·.kind == .generator)).toList.length = nG
  seed : ∀ i : Fin lo.length, memMain lo i →
    ∃ (ρ : (Fin (bitsZ cs (lo.get i).1) → GE) × GEˣ) (y : GE),
      K1.SeedIs cs (lo.get i).1 a.1.st (numAt seats ⟨⟨lo, seat⟩, i⟩) ρ y
  tie : ∀ i : Fin lo.length, memMain lo i → K1.Tie cs (lo.get i).1
  plan : ∀ as D, pSseed cs lo (groupLayK cs lo s e kb hM hZ)
      (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) T₀ L₀
      (fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) as D =
    pSseed cs lo (groupLayK cs lo s e kb hM hZ)
      (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩)
      (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay (fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) as D

/-- ShapesOwes gives TiedOwes. -/
theorem owes_of_shapes (z : Pz) (a : VerifiableInference.Desc.First.S × F.E.Str) (Gr Gb : Group)
    (lay : GroupLayout)
    (hl : (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay)
    (O : ShapesOwes cs lo seat seats s e kb hM hZ nP nG T₀ L₀ a Gr Gb lay) :
    TiedOwes G cs lo seat seats (groupLayK cs lo s e kb hM hZ)
      (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) keep pull nP nG
      (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ) fx A₀
      bC bZ w₀ w₁ L σ₀ st₀ e₀ mW T₀ L₀ z a Gr lay where
  plain := O.plain
  gens := O.gens
  members := members_of_shapes O.shapes0
  seed := fun x => O.seed x.1.1 x.1.2
  tie := fun x => O.tie x.1.1 x.1.2
  plan := O.plan
  inMain := fun as b x hw => inMain_of_shapes (hM := hM) hl O.shapes O.k as.1 b x hw
  inKept := fun as q x hq => inKept_of_shapes O.apart as.1 q x hq
  inMask := fun as b x hw =>
    inMask_of_shapes (hZ := hZ) O.begunAt hl O.ok O.shapes O.h as.1 b x hw
  fits := fun as => by
    obtain ⟨ρ, y, hsm, hS⟩ := smpDrawn_seed (P := Pz) cs seats (z, a.1) ⟨lo, seat⟩ as.1.1
      (O.seed as.1.1 as.1.2)
    have hσ : (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ)
        (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) keep pull
        (nP + (esOf cs lo s e kb hM hZ).length + nG)
        (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
          (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁ L
        (fun (a : Pz × VerifiableInference.Desc.First.S) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀
        st₀ e₀ mW z a).1.2 as.1.1 = (ρ, fun _ => y) := by
      show ((smpDrawn cs seats (z, a.1) ⟨lo, seat⟩ as.1.1).getD (σ₀ as.1.1)) = _
      rw [hsm]
      rfl
    obtain ⟨-, orc, zz, β, t, hx, -, -, hr, hread, -⟩ := hS
    have hro : rowOfMsg a.1.st (numAt seats ⟨⟨lo, seat⟩, as.1.1⟩) =
        K1.sampleRow (K1.Msg.of cs (lo.get as.1.1).1) (numAt seats ⟨⟨lo, seat⟩, as.1.1⟩) zz β 0
          t := by
      unfold rowOfMsg
      have hx' : a.1.st.oracles[numAt seats ⟨⟨lo, seat⟩, as.1.1⟩]? = some orc := hx
      rw [hx']
      simp [hr]
    beta_reduce
    rw [hσ, hro]
    exact sampleFits_of_shapes O.good O.begunAt hl O.ok O.shapes O.agrees O.apart O.k O.h0 as.1
      (O.tie as.1.1 as.1.2) zz β t ρ hread as.2

/-- **K10On's CLAUSE tied AT THE PROGRAMS' GROUP, FROM ShapesOwes.** -/
theorem tied_of_shapes (z : Pz) (a : VerifiableInference.Desc.First.S × F.E.Str) (Gr Gb : Group)
    (lay : GroupLayout)
    (hG : (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr)
    (hl : (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay)
    (O : ShapesOwes cs lo seat seats s e kb hM hZ nP nG T₀ L₀ a Gr Gb lay) :
    RowsTied (groupLayK cs lo s e kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG)
      (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
        (esOf_all cs lo s e kb hM hZ))
      (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩)
      (pSseed cs lo (groupLayK cs lo s e kb hM hZ)
        (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) T₀ L₀
        fun i => numAt seats ⟨⟨lo, seat⟩, i⟩)
      (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ)
        (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) keep pull
        (nP + (esOf cs lo s e kb hM hZ).length + nG)
        (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
          (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁ L
        (fun (a : Pz × VerifiableInference.Desc.First.S) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀
        st₀ e₀ mW z a).1.1.1
      (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ)
        (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) keep pull
        (nP + (esOf cs lo s e kb hM hZ).length + nG)
        (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
          (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁ L
        (fun (a : Pz × VerifiableInference.Desc.First.S) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀
        st₀ e₀ mW z a).1.2
      (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay (runRows (rdK a.1).2.2 Gr).toList :=
  tied_laid_in G cs lo seat seats _ _ keep pull nP nG _ _ _ fx A₀ bC bZ w₀ w₁ L σ₀ st₀ e₀ mW T₀ L₀ z
    a Gr lay hG hl (owes_of_shapes G cs lo seat seats s e kb hM hZ keep pull nP nG fx A₀ bC bZ w₀ w₁
      L σ₀ st₀ e₀ mW T₀ L₀ z a Gr Gb lay hl O)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.owes_of_shapes
#print axioms VerifiableInference.Desc.First.Close.tied_of_shapes
