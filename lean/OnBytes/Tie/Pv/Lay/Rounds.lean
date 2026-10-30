-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lay/Rounds.lean: the rounds of the layers' product layers, joins, batches and merge
(Cb/Pv/Lay/) are the rounds that the planner lays for these stretches of a layers' sub-proof.

A typed round holds types; a plan's entry holds a name and eleven numbers. What it means that a
typed round is the round of an entry is defined in OnBytes/G4/RoundIs.lean (`EntryIs`, `ShapeIs`):
the message is as many scalars as the entry's bytes say, the challenge is drawn from the set that
the entry's two numbers of draws say, and there is no oracle position. Here this is proved, for all
sizes and for any short sumcheck, of each block's shape (Cb/Pv/Lay/Shapes.lean) and the planner's
list for its stretch (OnBytes/Tie/Pv/Lay/PlanList.lean). By `own_adds` there, these lists are parts
of what the planner's own routine lays.

Main names:
  `is_eps`, `is_var`, `is_further`, `is_values`, `is_draw`, `is_draw1`, `is_send`: the rounds, one
    by one.
  `is_psc`, `is_layer`: a sumcheck's rounds against `lPsc`; a product layer's against `lLayer`.
  `prod_rounds`, `merge_rounds`, `weights_rounds`, `wfirst_rounds`, `routed_rounds`,
    `squares_rounds`: the blocks' shapes.
  `gated_is`, `routed_is`, `weights_is`, `wfirst_is`, `squares_is`: the same against the stretches
    of a record of sizes (Params.LayerRounds), where the block's sizes are the record's.

Limits: three of an entry's eleven numbers are tied (the message's bytes, the elements drawn, how
many of them are never 0); the name, the work, the number of rows and the rest are not. Where the
planner lays no join (no coordinate to draw) the blocks with a join do not apply: `routed_is` and
`squares_is` ask that there is one.

-/
import OnBytes.G4.RoundIs
import OnBytes.Tie.Pv.Lay.PlanList
import Cb.Pv.Lay.Shapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open Iop Cb OnBytes.G4 OnBytes.Params Cb.Pv.Lay TWhole

variable {E : Type} [Field E] [Fintype E]

/-! ### The rounds, one by one -/

/-- the empty tuple -/
def unitFin0 : Unit ≃ (Fin 0 → E) := Equiv.ofUnique _ _

/-- one element as a tuple -/
def oneFin1 : E ≃ (Fin 1 → E) := (Equiv.funUnique (Fin 1) E).symm

theorem is_eps (e : Fmt.Entry) (h1 : e.msg = 24) (h2 : e.drawE = 1) (h3 : e.drawNZ = 0) :
    EntryIs E (pRound0 E) e :=
  ⟨⟨1, 1, 0⟩, ⟨⟨oneFin1⟩, ⟨oneFin1⟩, inferInstanceAs (IsEmpty Empty)⟩, h1, h2, h3⟩

theorem is_var (e : Fmt.Entry) (h1 : e.msg = 48) (h2 : e.drawE = 1) (h3 : e.drawNZ = 0) :
    EntryIs E (Johnson.L5.Layers.sRound (pfCube E 2)) e :=
  ⟨⟨2, 1, 0⟩, ⟨⟨Equiv.refl _⟩, ⟨oneFin1⟩, inferInstanceAs (IsEmpty Empty)⟩, h1, h2, h3⟩

theorem is_further (d : ℕ) (e : Fmt.Entry) (h1 : e.msg = 24 * d) (h2 : e.drawE = 1)
    (h3 : e.drawNZ = 1) : EntryIs E (Johnson.L5.Layers.sRound (pDummy E d)) e :=
  ⟨⟨d, 1, 1⟩, ⟨⟨Equiv.refl _⟩, ⟨Equiv.refl _⟩, inferInstanceAs (IsEmpty Empty)⟩, h1, h2, h3⟩

omit [Fintype E] in
theorem is_values (A : Type) [Fintype A] (e : Fmt.Entry) (h1 : e.msg = 24 * Fintype.card A)
    (h2 : e.drawE = 0) (h3 : e.drawNZ = 0) : EntryIs E (pRoundV E A) e :=
  ⟨⟨Fintype.card A, 0, 0⟩,
    ⟨⟨Equiv.arrowCongr (Fintype.equivFin A) (Equiv.refl E)⟩, ⟨unitFin0⟩,
      inferInstanceAs (IsEmpty Empty)⟩, h1, h2, h3⟩

theorem is_draw (n : ℕ) (e : Fmt.Entry) (h1 : e.msg = 0) (h2 : e.drawE = n) (h3 : e.drawNZ = 0) :
    EntryIs E (IOR.drawRound (Fin n → E)) e :=
  ⟨⟨0, n, 0⟩, ⟨⟨unitFin0⟩, ⟨Equiv.refl _⟩, inferInstanceAs (IsEmpty Empty)⟩, h1, h2, h3⟩

theorem is_draw1 (e : Fmt.Entry) (h1 : e.msg = 0) (h2 : e.drawE = 1) (h3 : e.drawNZ = 0) :
    EntryIs E (IOR.drawRound E) e :=
  ⟨⟨0, 1, 0⟩, ⟨⟨unitFin0⟩, ⟨oneFin1⟩, inferInstanceAs (IsEmpty Empty)⟩, h1, h2, h3⟩

theorem is_send (ι : Type) [Fintype ι] (e : Fmt.Entry) (h1 : e.msg = 24 * Fintype.card ι)
    (h2 : e.drawE = 1) (h3 : e.drawNZ = 0) : EntryIs E (sendRound E ι E) e :=
  ⟨⟨Fintype.card ι, 1, 0⟩,
    ⟨⟨Equiv.arrowCongr (Fintype.equivFin ι) (Equiv.refl E)⟩, ⟨oneFin1⟩,
      inferInstanceAs (IsEmpty Empty)⟩, h1, h2, h3⟩

/-! ### Lists -/

theorem rep_app {α β : Type _} {R : α → β → Prop} {a : α} {b : β} (h : R a b) {l : List α}
    {l' : List β} (hl : List.Forall₂ R l l') :
    ∀ n : ℕ, List.Forall₂ R (List.replicate n a ++ l) (List.replicate n b ++ l')
  | 0 => hl
  | n + 1 => List.Forall₂.cons h (rep_app h hl n)

theorem is_psc (w k d : ℕ) (A : Type) [Fintype A] :
    ShapeIs E (pscShape E k d A) (lPsc w 0 k d (Fintype.card A)) := by
  show List.Forall₂ (EntryIs E) _
    (eDraw "PSC epsilon" w (0 + 24) 1 :: (List.replicate k (eDraw "PSC round" w 48 1) ++
      [{ name := "PSC Y", work := w, msg := 24 * d, drawE := 1, drawNZ := 1 },
        { name := "PSC values", msg := 24 * Fintype.card A }]))
  exact List.Forall₂.cons (is_eps _ rfl rfl rfl)
    (rep_app (is_var _ rfl rfl rfl)
      (List.Forall₂.cons (is_further d _ rfl rfl rfl)
        (List.Forall₂.cons (is_values A _ rfl rfl rfl) List.Forall₂.nil)) k)

theorem is_layer (w k : ℕ) :
    ShapeIs E (pscShape E k 2 Bool ++ [IOR.drawRound E]) (lLayer w k) :=
  List.rel_append (is_psc w k 2 Bool)
    (List.Forall₂.cons (is_draw1 _ rfl rfl rfl) List.Forall₂.nil)

/-! ### The blocks -/

theorem prod_rounds (L : ProdL E) {Ex : ExtSpec} (V : ShortK L.T.par Ex) (w : ℕ) :
    ShapeIs E (L.blk V).shape (lLayer w L.k) := by
  rw [L.shape_eq V]
  exact is_layer w L.k

theorem merge_rounds (L : MergeL E) {Ex : ExtSpec} (V : ShortK L.T.par Ex) (w : ℕ) :
    ShapeIs E (L.blk V).shape (lPsc w 0 L.k 1 1) := by
  rw [L.shape_eq V]
  exact is_psc w L.k 1 Unit

theorem weights_rounds (G : WeightsL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) (w rows : ℕ) :
    ShapeIs E (G.blk V).shape (eBat w 0 rows :: lPsc w 0 G.k 1 1) := by
  rw [G.shape_eq V]
  exact List.Forall₂.cons (is_draw1 _ rfl rfl rfl) (is_psc w G.k 1 Unit)

theorem wfirst_rounds (G : WFirstL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) (w rows : ℕ) :
    ShapeIs E (G.blk V).shape (eBat w 24 rows :: lPsc w 0 G.k 1 1) := by
  rw [G.shape_eq V]
  exact List.Forall₂.cons (is_send Unit _ rfl rfl rfl) (is_psc w G.k 1 Unit)

theorem routed_rounds (G : RoutedL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) (w : ℕ) :
    ShapeIs E (G.blk V).shape (eDraw "JOIN" w 0 G.g :: lLayer w (G.g + G.k')) := by
  rw [G.shape_eq V]
  exact List.Forall₂.cons (is_draw G.g _ rfl rfl rfl) (is_layer w (G.g + G.k'))

theorem squares_rounds (G : SquaresL E) {Ex : ExtSpec} (V : ShortK G.R.L.T.par Ex) (w rows : ℕ) :
    ShapeIs E (G.blk V).shape
      (eBat w (24 * (G.ns * G.n)) rows :: eDraw "JOIN" w 0 G.g :: lLayer w (G.g + G.k')) := by
  rw [G.shape_eq V]
  refine List.Forall₂.cons (is_send (Fin G.n × Fin G.ns) _ ?_ rfl rfl)
    (List.Forall₂.cons (is_draw G.g _ rfl rfl rfl) (is_layer w (G.g + G.k')))
  show 24 * (G.ns * G.n) = 24 * Fintype.card (Fin G.n × Fin G.ns)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm G.ns G.n]

/-! ### Against the stretches of a record of sizes -/

theorem gated_is (L : ProdL E) {Ex : ExtSpec} (V : ShortK L.T.par Ex) (w : ℕ) (x : LayerRounds)
    (hk : L.k = x.ll + x.lPf + x.lt) : ShapeIs E (L.blk V).shape (gated w x) := by
  unfold gated
  rw [← hk]
  exact prod_rounds L V w

theorem routed_is (G : RoutedL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) (w : ℕ) (x : LayerRounds)
    (hr : x.routed = true) (hl : 1 < x.ll) (hg : G.g = x.ll - 1) (hk : G.k' = x.lfe + x.lt) :
    ShapeIs E (G.blk V).shape (joinRouted w x ++ routed w x) := by
  unfold joinRouted routed
  rw [if_pos hr, if_pos hl, if_pos hr, ← hg, Nat.add_assoc, ← hk]
  exact routed_rounds G V w

theorem weights_is (G : WeightsL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) (w : ℕ) (x :
    LayerRounds)
    (hf : x.firstGroup = false) (hk : G.k = x.lkW) :
    ShapeIs E (G.blk V).shape (batWeights w x ++ merge w x) := by
  unfold batWeights merge
  rw [hf, ← hk]
  exact weights_rounds G V w _

theorem wfirst_is (G : WFirstL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) (w : ℕ) (x : LayerRounds)
    (hf : x.firstGroup = true) (hk : G.k = x.lkW) :
    ShapeIs E (G.blk V).shape (batWeights w x ++ merge w x) := by
  unfold batWeights merge
  rw [hf, ← hk]
  exact wfirst_rounds G V w _

theorem squares_is (G : SquaresL E) {Ex : ExtSpec} (V : ShortK G.R.L.T.par Ex) (w : ℕ)
    (x : LayerRounds) (h0 : x.lNI ≠ 0) (hg : G.g = x.lNI) (hk : G.k' = x.lPd + x.lt)
    (hn : G.n = x.NI) (hs : G.ns = x.NS) :
    ShapeIs E (G.blk V).shape (batLimbs w x ++ joinNorms w x ++ squares w x) := by
  unfold batLimbs joinNorms squares
  rw [if_pos (by simpa using h0), ← hg, Nat.add_assoc, ← hk, ← hn, ← hs]
  exact squares_rounds G V w _

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.gated_is
#print axioms OnBytes.Tie.Pv.Lay.routed_is
#print axioms OnBytes.Tie.Pv.Lay.weights_is
#print axioms OnBytes.Tie.Pv.Lay.wfirst_is
#print axioms OnBytes.Tie.Pv.Lay.squares_is
