-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Maps.lean: how the merge's written rounds are read as the typed rounds of
the
library's proved block for the merge (Johnson/Top/H/Merge.lean; Cb/Pv/Lay/Weights.lean).
Definitions,
and theorems with their proofs.

Main names:
  `mZ`, `m0`, `mR`, `mY`, `mV`: one map for each sort of round: the draw, the hiding polynomial's
    sum, a column bit, the further variable, the end value.
  `mergeMaps`: all of them, as the library's `Maps` (OnBytes/Flat/CarrySMaps.lean).
  `MergeDs`: what is asked of the written rounds: what each sends and draws.
  `mergeMaps_ok`: under `MergeDs` the maps are in order.

Limits. No written round is taken from a plan here. Nothing on soundness or on hiding.

-/
import OnBytes.Flat.KindsBattSend
import OnBytes.Flat.CarrySProx
import Johnson.Top.H.Merge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.OnPublicFiles (MergeCaller)

/-- The round of the draw: nothing is read of the message; one element. -/
def mZ (d : RDT) : RMap d (drawRound GE) := RMap.one (fun _ => ((), ())) id
/-- The round of the hiding polynomial's sum: one scalar; one element. -/
def m0 (d : RDT) : RMap d (pRound0 GE) := RMap.one (fun m => ((), sentT d m 0)) id
/-- A round in a column bit: two scalars; one element. -/
def mR (d : RDT) : RMap d (sRound (pfCube GE 2)) := RMap.one (fun m => ((), fun t : Fin 2 => sentT d
    m t.val)) id
/-- The round in the further variable: one scalar; one element other than 0. -/
noncomputable def mY (d : RDT) : RMap d (sRound (pDummy GE 1)) :=
  RMap.seed (fun m => ((), fun _ : Fin 1 => sentT d m 0)) 0 fun s => (⟨s.2.val, s.2.ne_zero⟩ : {x :
      GE // x ≠ 0})
/-- The round of the end value: one scalar; nothing is drawn. -/
def mV (d : RDT) : RMap d (pRoundV GE Unit) := RMap.none (fun m => ((), fun _ => sentT d m 0)) ()

/-- The rounds in the column bits, the round in the further variable, the round of the end value. -/
noncomputable def midMaps (dY dV : RDT) : (ds : List RDT) →
    Maps (ds ++ [dY, dV]) (sRounds (ldPartFmt GE ds.length (fun _ => 2) ++ [pDummy GE 1]) ++
        [pRoundV GE Unit])
  | [] => .step (mY dY) (.step (mV dV) .nil)
  | d :: ds => .step (mR d) (midMaps dY dV ds)

theorem merge_shape (G : WeightsL GE) (Ex : ExtSpec) (ds : List RDT) (hk : ds.length = G.k) :
    drawRound GE :: pRound0 GE ::
        (sRounds (ldPartFmt GE ds.length (fun _ => 2) ++ [pDummy GE 1]) ++ [pRoundV GE Unit]) =
      (G.blk (G.L.V1 Ex)).shape := by
  rw [hk]
  rfl

/-- **How the merge's written rounds are read as the proved block's typed rounds.** -/
noncomputable def mergeMaps (G : WeightsL GE) (Ex : ExtSpec) (dZ d0 : RDT) (ds : List RDT) (dY dV :
    RDT) (hk : ds.length = G.k) :
    Maps (dZ :: d0 :: (ds ++ [dY, dV])) (G.blk (G.L.V1 Ex)).shape :=
  Maps.castT (merge_shape G Ex ds hk) (.step (mZ dZ) (.step (m0 d0) (midMaps dY dV ds)))

theorem midMaps_ok (dY dV : RDT) (hY : (mY dY).OK) (hV : (mV dV).OK) :
    ∀ ds : List RDT, (∀ d ∈ ds, (mR d).OK) → (midMaps dY dV ds).OK
  | [], _ => ⟨hY, hV, trivial⟩
  | d :: ds, h => ⟨h d List.mem_cons_self, midMaps_ok dY dV hY hV ds fun d' hd' => h d'
      (List.mem_cons_of_mem _ hd')⟩

/-- What is asked of the written rounds: what each sends and draws. -/
structure MergeDs (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) : Prop where
  z : ∃ ns a, SendsDraws (toRD dZ) ns 1 0 a
  o : ∃ ns a, SendsDraws (toRD d0) ns 1 0 a
  r : ∀ d ∈ ds, ∃ ns a, SendsDraws (toRD d) ns 1 0 a
  yPlain : PlainDraws (Fmt.dsOf dY.entry dY.kind)
  yE : nE (Fmt.dsOf dY.entry dY.kind) = 0 + 1
  yP : nP (Fmt.dsOf dY.entry dY.kind) = 0
  yNZ : IsNZ (Fmt.dsOf dY.entry dY.kind) 0
  yLog : dY.entry.logN ≤ 64
  v : ∃ ns a, SendsDraws (toRD dV) ns 0 0 a

theorem mergeMaps_ok (G : WeightsL GE) (Ex : ExtSpec) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (hk : ds.length = G.k)
    (H : MergeDs dZ d0 ds dY dV) : (mergeMaps G Ex dZ d0 ds dY dV hk).OK := by
  obtain ⟨_, _, hz⟩ := H.z
  obtain ⟨_, _, ho⟩ := H.o
  obtain ⟨_, _, hv⟩ := H.v
  refine Maps.ok_castT _ ⟨RMap.one_ok _ hz Function.injective_id, RMap.one_ok _ ho
      Function.injective_id,
    midMaps_ok dY dV (RMap.seed_ok _ H.yPlain H.yE H.yP H.yNZ H.yLog ?_) (show (mV dV).OK from
        RMap.none_ok (r' := pRoundV GE Unit) _ hv ()) ds ?_⟩
  · intro s s' h
    have h1 : s.2.val = s'.2.val := congrArg Subtype.val h
    exact Prod.ext (funext fun i => i.elim0) (Units.ext h1)
  · intro d hd
    obtain ⟨_, _, hr⟩ := H.r d hd
    exact RMap.one_ok _ hr Function.injective_id

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.mergeMaps_ok
