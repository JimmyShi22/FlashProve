-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageMap.lean: a stage over one index type of pads, transported to a larger index type.
(Words of this library: lean/GLOSSARY.md.)

A part of a protocol is most easily defined over its own index type P of pads, for instance the
positions of its own pad vector. A chain of such parts has one family of pads for all. This file
transports a stage (Blocks/Stage.lean) along an injective map ip : P → P' of index types.
 * `Hon.comapP H ip`: the honest prover that uses the pad ip p where H uses the pad p. `Core.mapP`,
   `Stage.mapP`: the same block, errors, simulator and probabilities; the sets of pads with which it
   masks (U) and on which its plain parts depend (D) are the images.
 * `Cut.mapP c ip`: the relation for the honest run takes the pads through ip.
 * `Stage.Props.mapP`: `Stage.Props` is preserved. The one step with content is masked form:
   uniform pads over P' stay uniform when taken through ip (`map_unif_comp`).
 * `Core.Track.mapP`: tracking data concern the block only, so they carry over, with `OK`, `All` and
   `sum`. Rounds do not change.
-/
import Blocks.StageTrack
import Blocks.StageSide
import Blocks.StageNums
import Blocks.StageCount
import Prob.Linear
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob
open scoped ENNReal

variable {P P' E : Type}

/-- Uniform pads over P', taken through an injective ip, are uniform pads over P. -/
theorem map_unif_comp [Fintype P] [Fintype P'] [DecidableEq P] [DecidableEq P'] [AddCommGroup E]
    [Fintype E] {ip : P → P'} (hip : Function.Injective ip) :
    (unif (P' → E)).map (fun π p => π (ip p)) = unif (P → E) := by
  classical
  let φ : (P' → E) →+ (P → E) :=
    { toFun := fun π p => π (ip p), map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine map_unif_addMonoidHom φ fun π =>
    ⟨fun p' => if h : ∃ p, ip p = p' then π h.choose else 0, funext fun p => ?_⟩
  have h : ∃ q, ip q = ip p := ⟨p, rfl⟩
  show (if h : ∃ q, ip q = ip p then π h.choose else 0) = π p
  rw [dif_pos h, hip h.choose_spec]

/-- `mix` at the images, taken through an injective ip, is `mix`. -/
theorem mix_image_comp {ip : P → P'} (hip : Function.Injective ip) (U : Set P) (π σ : P' → E) :
    (fun p => mix (ip '' U) π σ (ip p)) = mix U (fun p => π (ip p)) fun p => σ (ip p) := by
  funext p
  by_cases h : p ∈ U
  · rw [mix_mem _ _ (Set.mem_image_of_mem ip h), mix_mem _ _ h]
  · rw [mix_notMem _ _ (fun hm => h ((hip.mem_set_image).mp hm)), mix_notMem _ _ h]

section Hon
variable {Xi Yi Xo Yo Ii Io : Type} {B : Block Xi Yi Xo Yo}

/-- The honest prover over the larger index type: it uses the pad ip p where H uses the pad p. -/
def Hon.comapP (H : Hon B P E Ii Io) (ip : P → P') : Hon B P' E Ii Io where
  strat := fun a π => H.strat a fun p => π (ip p)
  next := H.next
  Bad := H.Bad
  Win := H.Win

theorem Hon.tr_comapP (H : Hon B P E Ii Io) (ip : P → P') (a : Ii) (π : P' → E) (ρ : Rho B.shape) :
    (H.comapP ip).tr a π ρ = H.tr a (fun p => π (ip p)) ρ := rfl

theorem Hon.AccOn.comapP {H : Hon B P E Ii Io} {Hi : Ii → (P → E) → Xi → Yi → Prop}
    {Ho : Io → (P → E) → Xo → Yo → Prop} (h : H.AccOn Hi Ho) (ip : P → P') :
    (H.comapP ip).AccOn (fun a π x y => Hi a (fun p => π (ip p)) x y) fun a π x y =>
      Ho a (fun p => π (ip p)) x y :=
  fun a π x y ρ hi hρ => h a (fun p => π (ip p)) x y ρ hi hρ

theorem Hon.Masked.comapP [Fintype P] [Fintype P'] [DecidableEq P] [DecidableEq P']
    [AddCommGroup E] [Fintype E] {H : Hon B P E Ii Io} {V : Ii → Prop} {U D : Set P}
    {Sim : Rho B.shape → PMF (Plains B.shape)} (h : H.Masked V U D Sim)
    {ip : P → P'} (hip : Function.Injective ip) :
    (H.comapP ip).Masked V (ip '' U) (ip '' D) Sim where
  reads := fun a ρ π π' ha hρ hD =>
    h.reads a ρ _ _ ha hρ fun p hp => hD (ip p) (Set.mem_image_of_mem ip hp)
  law := fun a ρ σ ha hρ => by
    have h1 : (fun π : P' → E => ((H.comapP ip).tr a (mix (ip '' U) π σ) ρ).plains) =
        (fun π : P → E => (H.tr a (mix U π fun p => σ (ip p)) ρ).plains) ∘ fun π p => π (ip p) := by
      funext π
      show (H.tr a (fun p => mix (ip '' U) π σ (ip p)) ρ).plains = _
      rw [mix_image_comp hip]
      rfl
    rw [h1, ← PMF.map_comp, map_unif_comp hip]
    exact h.law a ρ _ ha hρ

end Hon

variable {a b : Sorts}

/-- the protocol over the larger index type of pads -/
@[reducible] def Core.mapP (S : Core P E a b) (ip : P → P') : Core P' E a b where
  B := S.B
  H := S.H.comapP ip

/-- The stage over the larger index type of pads. -/
def Stage.mapP (S : Stage P E a b) (ip : P → P') : Stage P' E a b where
  toCore := S.toCore.mapP ip
  ε := S.ε
  U := ip '' S.U
  D := ip '' S.D
  Sim := S.Sim
  pBad := S.pBad
  pWin := S.pWin

theorem Stage.toCore_mapP (S : Stage P E a b) (ip : P → P') :
    (S.mapP ip).toCore = S.toCore.mapP ip := rfl
theorem Stage.U_mapP (S : Stage P E a b) (ip : P → P') : (S.mapP ip).U = ip '' S.U := rfl
theorem Stage.D_mapP (S : Stage P E a b) (ip : P → P') : (S.mapP ip).D = ip '' S.D := rfl
theorem Stage.U_mapP_sub (S : Stage P E a b) (ip : P → P') : (S.mapP ip).U ⊆ Set.range ip :=
  Set.image_subset_range ip _
theorem Stage.D_mapP_sub (S : Stage P E a b) (ip : P → P') : (S.mapP ip).D ⊆ Set.range ip :=
  Set.image_subset_range ip _
theorem Stage.pBad_mapP (S : Stage P E a b) (ip : P → P') : (S.mapP ip).pBad = S.pBad := rfl
theorem Stage.pWin_mapP (S : Stage P E a b) (ip : P → P') : (S.mapP ip).pWin = S.pWin := rfl
theorem Stage.rounds_mapP (S : Stage P E a b) (ip : P → P') : (S.mapP ip).rounds = S.rounds := rfl
theorem Stage.below_mapP (S : Stage P E a b) (ip : P → P') (κ : ℝ≥0∞) :
    (S.mapP ip).Below κ ↔ S.Below κ := Iff.rfl

/-- the relations whose relation for the honest run takes the pads through ip -/
def Cut.mapP (c : Cut P E a) (ip : P → P') : Cut P' E a :=
  ⟨c.R, fun s π x y => c.Hn s (fun p => π (ip p)) x y, c.V⟩

/-- For injective ip, `Stage.Props` is preserved. -/
theorem Stage.Props.mapP [Fintype P] [Fintype P'] [DecidableEq P] [DecidableEq P'] [AddCommGroup E]
    [Fintype E] {S : Stage P E a b} {ca : Cut P E a} {cb : Cut P E b} (h : S.Props ca cb)
    {ip : P → P'} (hip : Function.Injective ip) :
    (S.mapP ip).Props (ca.mapP ip) (cb.mapP ip) where
  clean := h.clean
  acc := h.acc.comapP ip
  masked := h.masked.comapP hip
  keeps := h.keeps
  prBad := h.prBad
  prWin := h.prWin

section Track
variable {F : Type} [Field F] [Field E] [Algebra F E]

/-- Tracking data concern the block only. -/
def Core.Track.mapP {S : Core P E a b} {ra : Reads F E a} {rb : Reads F E b}
    (t : S.Track ra rb) (ip : P → P') : (S.mapP ip).Track ra rb := ⟨t.d, t.src⟩

theorem Core.Track.OK.mapP {S : Core P E a b} {ra : Reads F E a} {rb : Reads F E b}
    {t : S.Track ra rb} (h : t.OK) (ip : P → P') : (t.mapP ip).OK := h

omit [Field F] [Field E] [Algebra F E] in
theorem Core.Track.All.mapP {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop} {S : Core P E a b}
    {ra : Reads F E a} {rb : Reads F E b} {t : S.Track ra rb} (h : t.All Q) (ip : P → P') :
    (t.mapP ip).All Q := h

omit [Field F] [Field E] [Algebra F E] in
theorem Core.Track.sum_mapP (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ) {S : Core P E a b}
    {ra : Reads F E a} {rb : Reads F E b} (t : S.Track ra rb) (ip : P → P') :
    (t.mapP ip).sum f = t.sum f := rfl

end Track

end Blocks
