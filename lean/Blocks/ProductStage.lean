-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ProductStage.lean: the product layer as a stage.

Blocks/ProductBlock.lean proves soundness, completeness and masked form of a product layer. Here
they are combined in one stage (Blocks/Stage.lean): `PL.Prover.stage`, with
`PL.Prover.props_stage_a`, `props_stage_b` for the two forms of the relation after the layer, under
hypotheses, among them `PL.OrdOK` (the order of the rounds names every variable once). This needs
bounds for the withheld set (`Hon.withheld`, Blocks/BlockHon.lean): `SC.Prover.prBad_sc`,
`PL.Prover.prBad_pl`, `PL.Prover.win_pl`. The stage sends no vector. `below_stage`: a common bound
for its errors; `rounds_stage`: g + 1 rounds, under `OrdOK`.

Notation: `Stage P E a b`: a stage: the data (Blocks/Stage.lean); of its fields: `ε`: the errors,
round by round, as counts; `U`, `D`: `Set P`; `Sim`: `Rho B.shape → PMF (Plains B.shape)`; `pBad`,
`pWin`: `ℝ≥0∞`. `H.Bad`: `Set (Rho B.shape)`; `H.Win`: `Ii → Set (Rho B.shape)`: fields of `Hon`
(Blocks/BlockHon.lean). Of `L : PL E Y P N Ξ` (Blocks/ProductBlock.lean): `g`: ℕ; the number of
variables: the vectors have length 2^g; `nz`: `ℕ → Bool`; which coordinates of the next point (ζ |
ϱ̂) are rejected at 0; coordinate 0 is ζ. e: ℕ; the error count at ζ (`stage`).
-/
import Blocks.SumCheckStage
import Blocks.StageSide
import Blocks.StageNums
import Blocks.StageCount
import Iop.ViewKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob Alg
open scoped ENNReal

/-- An event that at most one value of the challenge of a round brings about has probability at most
1 / (the number of values). -/
theorem prRho_zero_le (r : Round) (P : r.Chal → Prop) (hP : ∀ c c', P c → P c' → c = c') :
    prRho (s := [r]) {ρ | P (show r.Chal × Rho [] from ρ).1} ≤
      1 / (Fintype.card r.Chal : ℝ≥0∞) := by
  have h := prRho_head_le r [] P 1 (cnt_le_one hP)
  rwa [Nat.cast_one] at h

namespace SC.Prover

variable {E Y P Ξ ι A : Type}
  [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] {S : SC E Y P Ξ ι} (H : S.Prover A)

/-- The public part of a masked sumcheck's withheld set (a flagged challenge is 0) has probability
at most n / |E|, for n variables. -/
theorem prBad_sc : ∀ l l' : List ι, prRho (H.sc l l').Bad ≤ (l.length : ℝ≥0∞) / Fintype.card E
  | [], _ => (prRho_empty _ fun _ h => h).trans (zero_le _)
  | i :: l, l' => by
      have h1 : prRho (H.round i (l ++ l')).Bad ≤ 1 / (Fintype.card E : ℝ≥0∞) :=
        prRho_zero_le (S.rd i) (fun r => S.nzv i = true ∧ r = 0) fun c c' h h' =>
          h.2.trans h'.2.symm
      refine (prRho_cyl_union_le (H.round i (l ++ l')).Bad (H.sc l l').Bad).trans
        ((add_le_add h1 (prBad_sc l l')).trans (le_of_eq ?_))
      rw [ENNReal.div_add_div_same, List.length_cons, Nat.cast_succ, add_comm]

/-- `prBad_sc`, counting the flagged variables only. -/
theorem prBad_sc_count :
    ∀ l l' : List ι, prRho (H.sc l l').Bad ≤ ((l.countP S.nzv : ℕ) : ℝ≥0∞) / Fintype.card E
  | [], _ => (prRho_empty _ fun _ h => h).trans (zero_le _)
  | i :: l, l' => by
      refine (prRho_cyl_union_le (H.round i (l ++ l')).Bad (H.sc l l').Bad).trans ?_
      by_cases hi : S.nzv i = true
      · have h1 : prRho (H.round i (l ++ l')).Bad ≤ 1 / (Fintype.card E : ℝ≥0∞) :=
          prRho_zero_le (S.rd i) (fun r => S.nzv i = true ∧ r = 0) fun c c' h h' =>
            h.2.trans h'.2.symm
        refine (add_le_add h1 (prBad_sc_count l l')).trans (le_of_eq ?_)
        rw [ENNReal.div_add_div_same, List.countP_cons_of_pos hi, Nat.cast_succ, add_comm]
      · have h1 : prRho (H.round i (l ++ l')).Bad ≤ 0 :=
          prRho_empty _ fun _ h => hi (show S.nzv i = true ∧ _ from h).1
        refine (add_le_add h1 (prBad_sc_count l l')).trans (le_of_eq ?_)
        rw [zero_add, List.countP_cons_of_neg hi]

end SC.Prover

namespace PL.Prover

variable {E Y P N Ξ A : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] {L : PL E Y P N Ξ} (H : L.Prover A)

/-- The number of the challenges of a layer that are rejected at 0: the coordinates 0, .., g of the
next point at which nz is set. -/
def nDiv (L : PL E Y P N Ξ) : ℕ := (List.range (L.g + 1)).countP L.nz

omit [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
/-- `nDiv` is g + 1, if nz is set everywhere. -/
theorem nDiv_of_all {L : PL E Y P N Ξ} (h : ∀ t, L.nz t = true) : nDiv L = L.g + 1 := by
  unfold nDiv
  rw [List.countP_eq_length.mpr fun t _ => h t, List.length_range]

omit [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
/-- `nDiv` is 0, if nz is set nowhere. -/
theorem nDiv_of_none {L : PL E Y P N Ξ} (h : ∀ t, L.nz t = false) : nDiv L = 0 := by
  unfold nDiv
  exact List.countP_eq_zero.mpr fun t _ => by rw [h t]; exact Bool.false_ne_true

omit [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
/-- `nDiv` is at most g + 1. -/
theorem nDiv_le (L : PL E Y P N Ξ) : nDiv L ≤ L.g + 1 := by
  unfold nDiv
  exact List.countP_le_length.trans (le_of_eq (List.length_range))

/-- The bound for the probability of the public part of a layer's withheld set. -/
def pBad (L : PL E Y P N Ξ) : ℝ≥0∞ := (nDiv L : ℝ≥0∞) / Fintype.card E

omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem pBad_le (L : PL E Y P N Ξ) : pBad L ≤ ((L.g : ℝ≥0∞) + 1) / Fintype.card E :=
  ENNReal.div_le_div_right (by exact_mod_cast nDiv_le L) _

omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem pBad_of_all {L : PL E Y P N Ξ} (h : ∀ t, L.nz t = true) :
    pBad L = ((L.g : ℝ≥0∞) + 1) / Fintype.card E := by
  unfold pBad
  rw [nDiv_of_all h]
  push_cast
  rfl

omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem pBad_of_none {L : PL E Y P N Ξ} (h : ∀ t, L.nz t = false) : pBad L = 0 := by
  unfold pBad
  rw [nDiv_of_none h]
  simp

omit [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
/-- The variables in their default order are the numbers below g in their order. -/
theorem vars_eq_range (g : ℕ) : vars g = List.range g :=
  List.ext_getElem (by rw [length_vars, List.length_range]) fun i h1 h2 => by simp [vars]

omit [NeZero (2 : E)] [Fintype E] [DecidableEq E] in
/-- Under `ho`, the challenges that are rejected at 0: those of the flagged rounds, and ζ if nz is
set at 0. -/
theorem nDiv_eq (ho : L.OrdOK) :
    nDiv L = L.ord.countP L.sc.nzv + (if L.nz 0 = true then 1 else 0) := by
  unfold nDiv
  rw [List.range_succ_eq_map, List.countP_cons, List.countP_map,
    List.Perm.countP_eq _ ho, vars_eq_range]
  congr 1
  refine List.countP_congr fun v hv => ?_
  show L.nz (v + 1) = true ↔ (L.nz (v + 1) && decide (v < L.g)) = true
  rw [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h, List.mem_range.mp hv⟩, fun h => h.1⟩

omit [NeZero (2 : E)] in
/-- Under `ho`, the public part of a layer's withheld set (a challenge that is rejected at 0 is 0)
has probability at most `pBad`. -/
theorem prBad_pl (ho : L.OrdOK) : prRho H.pl.Bad ≤ pBad L := by
  unfold pBad
  have h0 : prRho (∅ : Set (Rho L.init.shape)) ≤ 0 := prRho_empty _ fun _ h => h
  have h1 : prRho H.fin.Bad ≤ ((if L.nz 0 = true then 1 else 0 : ℕ) : ℝ≥0∞) / Fintype.card E := by
    by_cases hnz : L.nz 0 = true
    · rw [if_pos hnz, Nat.cast_one]
      exact prRho_zero_le (rV E) (fun ζ => L.okE ζ = false) fun c c' h h' => by
        have hz : ∀ ζ : E, L.okE ζ = false → ζ = 0 := fun ζ hζ => by
          by_contra hne
          rw [L.okE_of_ne_zero fun _ => hne] at hζ
          cases hζ
        rw [hz c h, hz c' h']
    · refine (prRho_empty _ fun ρ hρ => ?_).trans (zero_le _)
      have h3 : L.okE (show E × Rho [] from ρ).1 = false := hρ
      rw [L.okE_of_ne_zero fun h' => absurd h' hnz] at h3
      cases h3
  have h2 := H.scP.prBad_sc_count L.ord []
  refine (prRho_cyl_union_le (s := L.init.shape) ∅ ((H.scP.sc L.ord []).seq H.fin).Bad).trans ?_
  refine (add_le_add h0
      ((prRho_cyl_union_le (H.scP.sc L.ord []).Bad H.fin.Bad).trans (add_le_add h2 h1))).trans
    (le_of_eq ?_)
  rw [zero_add, ENNReal.div_add_div_same, nDiv_eq ho, Nat.cast_add]

omit [NeZero (2 : E)] in
/-- Its `Win` is empty: nothing else is withheld. -/
theorem win_pl (a : A) : H.pl.Win a = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun ρ hρ => ?_
  rcases hρ with h | h | h
  · exact h
  · have h3 : Rho.fst (s := (L.sc.sc L.ord).shape) (Rho.snd (s := L.init.shape) ρ) ∈
        (H.scP.sc L.ord []).Win (a, fun _ => 0) := h
    rw [H.scP.win_sc] at h3
    exact h3
  · exact h

/-- The protocol of the product layer. -/
def core : Core P E ⟨PLX N E Ξ, Y, A⟩ ⟨XOut N E Ξ, Y, A⟩ where
  B := L.pl
  H := H.pl

variable [Fintype P] [DecidableEq P]

/-- The product layer as a stage. e is the error count at ζ: 0 or 1 below (`props_stage_a`: 0;
`props_stage_b`: 1), by the form of the relation after the layer. (The fields: `Stage`,
Blocks/Stage.lean.) -/
def stage (e : ℕ) : Stage P E ⟨PLX N E Ξ, Y, A⟩ ⟨XOut N E Ξ, Y, A⟩ where
  toCore := H.core
  ε := L.plErr e
  U := L.pads
  D := L.pads
  Sim := simPl L
  pBad := pBad L
  pWin := 0

/-- Under the hypotheses below and 2 ≠ 0 in E: what the next two theorems share, for any Ro with
`hclean`. -/
theorem props_stage_of (ho : L.OrdOK) (T : PL.Vecs E Y Ξ) {e : ℕ} {Ro : XOut N E Ξ → Y → Prop}
    (hclean : L.pl.Clean (L.Rin T) Ro (L.plErr e)) (Inv : A → (P → E) → Ledger N E → Ξ → Y → Prop)
    (V : A → Prop) (hset : ∀ a p e0 e1, H.pt (H.set a p e0 e1) = p)
    (hInv : ∀ a p π led ξ y f w0 w1, Inv a π led ξ y →
      Inv (H.set a p (Form.val (L.proj y) w0) (Form.val (L.proj y) w1)) π (led.addProd f w0 w1) ξ y)
    (hV : ∀ a p e0 e1, V a → V (H.set a p e0 e1)) (hp : L.sc.PlacesOnceOn (vars L.g))
    (hpv : Function.Injective L.pv) (hd : Disjoint (L.sc.padsOf (vars L.g)) (Set.range L.pv)) :
    (H.stage e).Props ⟨L.Rin T, H.HIn T Inv, V⟩ ⟨Ro, H.HOut T Inv, V⟩ where
  clean := hclean
  acc := H.accOn_pl T Inv ho hset hInv
  masked := H.masked_pl ho V hp hpv hd
  keeps := fun a ρ ha => by
    show V (H.set ((H.scP.sc L.ord []).next (a, fun _ => 0) _).1 _ _ _)
    rw [SC.Prover.next_fst]
    exact hV a _ _ _ ha
  prBad := H.prBad_pl ho
  prWin := fun a _ => by
    show prRho (H.pl.Win a) ≤ 0
    rw [H.win_pl a]
    exact prRho_empty _ fun _ h => h

variable (T : PL.Vecs E Y Ξ) (Inv : A → (P → E) → Ledger N E → Ξ → Y → Prop) (V : A → Prop)

/-- `Stage.Props` of a product layer, under the hypotheses below and 2 ≠ 0 in E, with `PL.Ra` after
it: the deferred claims are true, (val v0, val v1) is the true pair. -/
theorem props_stage_a (ho : L.OrdOK) (hset : ∀ a p e0 e1, H.pt (H.set a p e0 e1) = p)
    (hInv : ∀ a p π led ξ y f w0 w1, Inv a π led ξ y →
      Inv (H.set a p (Form.val (L.proj y) w0) (Form.val (L.proj y) w1)) π (led.addProd f w0 w1) ξ y)
    (hV : ∀ a p e0 e1, V a → V (H.set a p e0 e1)) (hp : L.sc.PlacesOnceOn (vars L.g))
    (hpv : Function.Injective L.pv) (hd : Disjoint (L.sc.padsOf (vars L.g)) (Set.range L.pv)) :
    (H.stage 0).Props ⟨L.Rin T, H.HIn T Inv, V⟩ ⟨L.Ra T, H.HOut T Inv, V⟩ :=
  H.props_stage_of ho T (L.clean_pl_a T ho) Inv V hset hInv hV hp hpv hd

/-- `props_stage_a` with `PL.Rb` (and e = 1): the deferred claims are true, and the claim on the
next start form holds if no checked coordinate of the next point is 0. -/
theorem props_stage_b (ho : L.OrdOK) (hset : ∀ a p e0 e1, H.pt (H.set a p e0 e1) = p)
    (hInv : ∀ a p π led ξ y f w0 w1, Inv a π led ξ y →
      Inv (H.set a p (Form.val (L.proj y) w0) (Form.val (L.proj y) w1)) π (led.addProd f w0 w1) ξ y)
    (hV : ∀ a p e0 e1, V a → V (H.set a p e0 e1)) (hp : L.sc.PlacesOnceOn (vars L.g))
    (hpv : Function.Injective L.pv) (hd : Disjoint (L.sc.padsOf (vars L.g)) (Set.range L.pv)) :
    (H.stage 1).Props ⟨L.Rin T, H.HIn T Inv, V⟩ ⟨L.Rb T, H.HOut T Inv, V⟩ :=
  H.props_stage_of ho T (L.clean_pl_b T ho) Inv V hset hInv hV hp hpv hd

variable {F : Type} [Field F] [Algebra F E]

/-- The layer sends no vector: it exposes the same entries as its input. (_e is the argument e of
`stage`; the tracking data do not depend on it.) -/
def track (_e : ℕ) (ra : Reads F E ⟨PLX N E Ξ, Y, A⟩) :
    H.core.Track ra (Stage.readsX (XOut N E Ξ) A ra) where
  d := EncData.app (s := L.init.shape) PUnit.unit
    (EncData.app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape)
      (SC.encSc L.sc F L.ord) (REnc.none E F Bool E, PUnit.unit))
  src := fun n => .inl n

omit [Fintype P] [DecidableEq P] in
omit [NeZero (2 : E)] in
/-- Every exposed entry, and the matrix, are read after the layer as before it. -/
theorem track_ok (e : ℕ) (ra : Reads F E ⟨PLX N E Ξ, Y, A⟩) : (H.track e ra).OK :=
  ⟨fun y τ n => by
      show ra.rd ((L.sc.sc L.ord).imp y _) n = ra.rd y n
      rw [L.sc.imp_sc],
    fun y τ => by
      show ra.mat ((L.sc.sc L.ord).imp y _) = ra.mat y
      rw [L.sc.imp_sc]⟩

omit [NeZero (2 : E)] in
/-- No vector is sent, so every condition on sent vectors holds. -/
theorem all_track {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop}
    (e : ℕ) (ra : Reads F E ⟨PLX N E Ξ, Y, A⟩) : (H.track e ra).All Q :=
  EncData.All.app (s := L.init.shape) (d := PUnit.unit) trivial
    (EncData.All.app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape)
      (SC.all_encSc L.sc L.ord) ⟨fun e => e.elim, trivial⟩)

omit [NeZero (2 : E)] in
/-- No vector is sent, so every sum over sent vectors is 0. -/
theorem sum_track (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ)
    (e : ℕ) (ra : Reads F E ⟨PLX N E Ξ, Y, A⟩) : (H.track e ra).sum f = 0 := by
  show EncData.sum f _
      (EncData.app (s := L.init.shape) PUnit.unit
        (EncData.app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape)
          (SC.encSc L.sc F L.ord) (REnc.none E F Bool E, PUnit.unit))) = 0
  rw [EncData.sum_app, EncData.sum_app, SC.sum_encSc]
  rfl

omit [NeZero (2 : E)] in
/-- Under `ho`, a layer has g + 1 rounds. -/
theorem rounds_stage (ho : L.OrdOK) (e : ℕ) : (H.stage e).rounds = L.g + 1 := by
  show (L.init.shape ++ ((L.sc.sc L.ord).shape ++ L.fin.shape)).length = L.g + 1
  rw [List.length_append, List.length_append, SC.length_shape_sc, ho.length]
  exact Nat.zero_add _

omit [NeZero (2 : E)] in
/-- The errors of a layer, as probabilities (2 / |E| in each round of the sumcheck, e / |E| at ζ),
are at most κ if these are. -/
theorem below_stage {κ : ℝ≥0∞} (e : ℕ) (h2 : (2 : ℝ≥0∞) / Fintype.card E ≤ κ)
    (he : (e : ℝ≥0∞) / Fintype.card E ≤ κ) : (H.stage e).Below κ := by
  have hq0 : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqt : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h2' : ∀ i : ℕ, ((L.sc.e i + 1 : ℕ) : ℝ≥0∞) ≤ κ * Fintype.card E := fun _ => by
    show (((1 + 1 : ℕ) : ℕ) : ℝ≥0∞) ≤ _
    have := (ENNReal.div_le_iff hq0 hqt).1 h2
    exact_mod_cast this
  exact Err.Below.app (s := L.init.shape) (ε := ()) trivial
    (Err.Below.app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) (SC.below_scErr L.sc h2' L.ord)
      ⟨(ENNReal.div_le_iff hq0 hqt).1 he, trivial⟩)

end PL.Prover

end Blocks
