-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/U3ValLayers.lean: WHAT THE VALUES OF "U3" (u3Vals,
Johnson/HonestTrace/U3Rows.lean) ARE AT A SEGMENT OF A GROUP OF LAYERS, WHERE THE MAKER ACCEPTS: THE
VECTOR OF READS readAt AT THE TABLES THAT THE VERIFIER's OWN MAKER OF THE WEIGHTS (funsOf) RETURNS.
The sister of head_vec (Johnson/Desc/ProofFile/Honest/K1/Law/U3ValHead.lean). Four statements and
their proofs. No definition. Public data, the challenges heard and a reader of cells as letters: no
thread, no run, no witness.

  have_ok, ask_ok   what an accepted "have_" and an accepted "ask" say
  valsAt_layers     at a segment of the layers' sort valsAt is layersVals at the built data's group
  layers_vec        where layersVals accepts, and its vec accepts the challenges heard: the group
                    has a plan hp; SV.n is the plan's number of reads; the tables are laid (x);
                    funsOf returns funs at the points that the filler makes of what was heard (WITH
                    THEIR TERMS: a tie to a verifier's state will want them); and the vector's entry
                    j, at cells C, is readAt at the plan's sizes, funs and the cells read through
                    matsOwn

Unfoldings of definitions, with layersAt_eq and layerParts_some
(Johnson/HonestTrace/U3RowsLaws.lean, Johnson/HonestTrace/ReadsLayers.lean).

Limits. That the maker accepts is a premise: proved here of no public data and no list of
challenges. Nothing ties the points or funs to a verifier's state. matsOwn is not matsOf here.
Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.HonestTrace.U3RowsLaws
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.HonestTrace (parOfMats layerParts_some u3Layers)
open OnBytes.HonestTrace.U3 (SegVals valsAt layersVals layersAt layersAt_eq placeIn have_ ask)
open OnBytes.Model.Layer (HPlan2 TableAsk TableAt layTables tableAsks funsOf)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In ptsOf namedPts)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K4 (k4LookOf)

/-- An accepted "have_": the value is there. -/
theorem have_ok {α : Type} {name : String} {o : Option α} {a : α} (h : have_ name o = .ok a) :
    o = some a := by
  cases o with
  | none => cases h
  | some b => exact congrArg some (Except.ok.inj h)

/-- An accepted "ask": the test says yes. -/
theorem ask_ok {name : String} {b : Bool} {u : Unit} (h : ask name b = .ok u) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

/-- At a segment of the layers' sort valsAt is layersVals. -/
theorem valsAt_layers (Z : Pub) (G : Ground) (cov : Head.Covered) {seg : ℕ} {SV : SegVals}
    (hv : valsAt Z G cov seg = .ok SV) {Y : OnBytes.Model.Stages.LinkH}
    (hY : G.built[seg]? = some Y) (hk : Y.kind = 0) :
    ∃ sps, spotsOf Z.cuts = some sps ∧ layersVals Z G sps seg Y.g = .ok SV := by
  unfold valsAt at hv
  obtain ⟨sps, h1, hv⟩ := bind_eq_ok hv
  obtain ⟨Y', h2, hv⟩ := bind_eq_ok hv
  obtain ⟨_, -, hv⟩ := bind_eq_ok hv
  obtain ⟨_, -, hv⟩ := bind_eq_ok hv
  obtain rfl : Y = Y' := Option.some.inj (hY.symm.trans (have_ok h2))
  exact ⟨sps, have_ok h1, by simpa [hk] using hv⟩

/-- **The layers' vector is the vector of reads at the tables that funsOf returns.** -/
theorem layers_vec (Z : Pub) (G : Ground) (sps : List Spot) (seg g : ℕ) {SV : SegVals}
    (h : layersVals Z G sps seg g = .ok SV) {hd : List Fmt.Drawn}
    {vec : Cells → ℕ → OnBytes.E} (hvec : SV.vec hd = .ok vec) :
    ∃ (hp : HPlan2) (k4 k3 : Spot × ℕ)
      (x : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ) (funs : Array HFun),
      G.W.G[g]? = some hp ∧ placeIn Z sps seg .K4 = .ok k4 ∧ placeIn Z sps seg .K3 = .ok k3 ∧
      layTables (OnBytes.Desc.First.K4.Honest.matsOf
          { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece, r0 := k4.2,
            seg := seg }) (tableAsks G.W.layers.y G.W.layers.rd g) 0 = some x ∧
      SV.n = hp.nU.getD 2 0 ∧
      funsOf G.W.layers.y
        (ptsOf { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece,
                 r0 := k4.2, seg := seg }
          { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
            look := k4LookOf G.W.layers.y.fo k3.2 } hd).fo
        (namedPts { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece,
                    r0 := k4.2, seg := seg }
          (ptsOf { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece,
                   r0 := k4.2, seg := seg }
            { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
              look := k4LookOf G.W.layers.y.fo k3.2 } hd)) x.2.1 = some funs ∧
      ∀ (C : Cells) (j : ℕ), vec C j =
        First.K8.Honest.readAt (parOfMats hp.tl.mats) funs.toList
          (cellsAtOf C (matsOwn G.W seg)) j := by
  unfold layersVals at h
  obtain ⟨hp, hhp, h⟩ := bind_eq_ok h
  obtain ⟨k4, hk4, h⟩ := bind_eq_ok h
  obtain ⟨k3, hk3, h⟩ := bind_eq_ok h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨x, hx, h⟩ := bind_eq_ok h
  obtain ⟨_, hlen, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain rfl := Except.ok.inj h
  dsimp only at hvec
  cases hl : layersAt hp.tl.mats G.W.layers.y
      (ptsOf { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece,
               r0 := k4.2, seg := seg }
        { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
          look := k4LookOf G.W.layers.y.fo k3.2 } hd).fo
      (namedPts { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece,
                  r0 := k4.2, seg := seg }
        (ptsOf { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece,
                 r0 := k4.2, seg := seg }
          { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
            look := k4LookOf G.W.layers.y.fo k3.2 } hd)) x.2.1 x.2.2 with
  | error e =>
    rw [hl] at hvec
    cases hvec
  | ok v =>
    rw [hl] at hvec
    obtain rfl := Except.ok.inj hvec
    cases hf : funsOf G.W.layers.y
        (ptsOf { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece,
                 r0 := k4.2, seg := seg }
          { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
            look := k4LookOf G.W.layers.y.fo k3.2 } hd).fo
        (namedPts { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece,
                    r0 := k4.2, seg := seg }
          (ptsOf { P := G.W.layers, hp := hp, g := g, link := seg, piece := k4.1.place.piece,
                   r0 := k4.2, seg := seg }
            { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
              look := k4LookOf G.W.layers.y.fo k3.2 } hd)) x.2.1 with
    | none =>
      unfold layersAt at hl
      rw [hf] at hl
      cases hl
    | some funs =>
      refine ⟨hp, k4, k3, x, funs, have_ok hhp, hk4, hk3, have_ok hx,
        by simpa using ask_ok hlen, hf, fun C j => ?_⟩
      show v (cellsAtOf C (matsOwn G.W seg)) j = _
      rw [layersAt_eq hl]
      unfold u3Layers
      rw [layerParts_some hf]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.have_ok
#print axioms ProofFile.Honest.K1.ask_ok
#print axioms ProofFile.Honest.K1.valsAt_layers
#print axioms ProofFile.Honest.K1.layers_vec
