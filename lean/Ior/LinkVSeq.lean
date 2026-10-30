-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVSeq.lean: "a link, then a link": completeness and honest-verifier exact zero knowledge
for sets of slots with further reads (`HonestV.ExactV`, Ior/LinkV.lean).

In standard terms: a composition rule for interactive oracle reductions that run on a batch of
instances.

Proofs of `Iop.Spec.acc_seqV` and `Iop.Spec.exact_seqV` (stated in Ior/LinkV.lean), with the
simulator named (`LinkVSeq.sim`, `exactWith_seqV`).

What a link and a slot are: the head of Ior/LinkV.lean.

The simulator for a set J of slots is that of Ior/BatchSeqZkProofs.lean, with views in the place
of disclosed views:
 1. the first link's simulator once, for J, at the first parts of the ρ_j and the positions
    `firstT` (Ior/ExactSeq.lean);
 2. J': the slots of J that the first link does not withhold (a public matter). For j in J', from
    the simulated view and the given symbols: some oracles and some transcript that fit both (a
    choice); from them the explicit part that the first verifier outputs, the symbols of the
    middle implicit instance that the second simulator is given, and the rule that glues a second
    view to the first transcript. As the first link is local, these are the true ones (on the view
    of a run, under the hypotheses of `info_view`);
 3. the second link's simulator once, for J', on these data;
 4. for each slot of J: the notice (`none`: `HonestV.output`, Ior/LinkV.lean), if j is not in J',
    or the second simulator shows the notice, or `info` returns `none` at some slot of J' (then at
    every slot of J: `kern`), or `glue` returns `none`; else the two glued (Ior/ExactSeq.lean:
    `glue`) (exactly: `post`, `kern`).

Why it is exact, under the hypotheses of `exactWith_seqV`. For fixed coins of the first link, the
statements that the slots of J' hand on are in the middle relation (completeness of the first)
with one shared witness (a function of the shared witness W0, the shared coins and the shared
verifier messages, by type). The second link's property speaks of all families tied by one shared
witness. So the law of the rest is the second simulator's, and its arguments depend on the first
link's coins only through the views at `firstT`.

Limits: this file says nothing on running times; nothing on soundness. See also Limits in the head
of Ior/LinkV.lean.

Terms: lean/GLOSSARY.md.
-/
import Ior.LinkV
import Ior.BatchSeqZkProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace SStratR

theorem zip_bindR :
    ∀ {s t : Shape} {A : RoundSplits s} {B : RoundSplits t} {β γ β' γ' : Type} (S : SStratR s A β)
        (L : LStratR s A γ) (f : β → SStratR t B β') (g : β × γ → LStratR t B γ'),
      (S.bindR f).zip ((S.along L).bindR g) = Strat.bind (S.zip L) fun p => (f p.1).zip (g p)
  | [], _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _, _, (a, _), _, _, _, _, _, (m0, k0), (mj, kj), f, g =>
      congrArg (Prod.mk (a.join m0 mj)) (funext fun c => zip_bindR (k0 (a.kind.shOf c)) (kj c) f g)

end SStratR

namespace LinkVSeq
open IOR OnlineHon BatchSeqZk

section Slot
variable {X X' X'' : Type} {Ei Eo Eo' : ExtSpec} {R₁ : IOR X Ei X' Eo} {R₂ : IOR X' Eo X'' Eo'}
  {A₁ : RoundSplits R₁.shape} {A₂ : RoundSplits R₂.shape} {W0 Wj W0' Wj' W0'' Wj'' : Type}
  (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'')

theorem mem_withheld (ρ : Rho (R₁.shape ++ R₂.shape)) :
    ρ ∈ (H₁.seqV H₂).withheld ↔
    Rho.fst ρ ∈ H₁.withheld ∨ Rho.snd (s := R₁.shape) ρ ∈ H₂.withheld := by
  show ((RhoLo.fstA A₁ A₂ (Rho.lo (RoundSplits.app A₁ A₂) ρ) ∈ H₁.Bad ∨
        RhoLo.sndA A₁ A₂ (Rho.lo (RoundSplits.app A₁ A₂) ρ) ∈ H₂.Bad) ∨
      (H₁.stop0 (RhoSh.fstA A₁ A₂ (Rho.sh (RoundSplits.app A₁ A₂) ρ)) ||
          H₂.stop0 (RhoSh.sndA A₁ A₂ (Rho.sh (RoundSplits.app A₁ A₂) ρ))) = true) ↔
    (Rho.lo A₁ (Rho.fst ρ) ∈ H₁.Bad ∨ H₁.stop0 (Rho.sh A₁ (Rho.fst ρ)) = true) ∨
    (Rho.lo A₂ (Rho.snd (s := R₁.shape) ρ) ∈ H₂.Bad ∨
      H₂.stop0 (Rho.sh A₂ (Rho.snd (s := R₁.shape) ρ)) = true)
  rw [RhoLo.fstA_lo, RhoLo.sndA_lo, RhoSh.fstA_sh, RhoSh.sndA_sh, Bool.or_eq_true]
  tauto

theorem run_one (w0 : W0) (x : X) (wj : Wj) (c0 : H₁.Coin0) (d0 : H₂.Coin0) (c : H₁.Coin)
    (d : H₂.Coin) (ρ : Rho (R₁.shape ++ R₂.shape)) :
    Strat.run ((H₁.seqV H₂).one w0 x wj ((c0, d0), (c, d))) ρ =
      (Tr.app ((H₁.one w0 x wj (c0, c)).run (Rho.fst ρ)).1
          ((H₂.one ((H₁.one w0 x wj (c0, c)).run (Rho.fst ρ)).2.1
              ((H₁.one w0 x wj (c0, c)).run (Rho.fst ρ)).2.2.1
              ((H₁.one w0 x wj (c0, c)).run (Rho.fst ρ)).2.2.2 (d0, d)).run
            (Rho.snd (s := R₁.shape) ρ)).1,
        ((H₂.one ((H₁.one w0 x wj (c0, c)).run (Rho.fst ρ)).2.1
            ((H₁.one w0 x wj (c0, c)).run (Rho.fst ρ)).2.2.1
            ((H₁.one w0 x wj (c0, c)).run (Rho.fst ρ)).2.2.2 (d0, d)).run
          (Rho.snd (s := R₁.shape) ρ)).2) := by
  show Strat.run
      (SStratR.zip ((H₁.strat0 w0 c0).bindR fun w0' => H₂.strat0 w0' d0)
        (((H₁.strat0 w0 c0).along (H₁.strat w0 c0 x wj c)).bindR fun o =>
          H₂.strat o.1 d0 o.2.1 o.2.2 d)) ρ = _
  rw [SStratR.zip_bindR, Strat.run_bind]
  rfl

end Slot
end LinkVSeq

/-! ## Completeness -/

theorem acc_seqV : Spec.acc_seqV := by
  intro X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ W0 Wj W0' Wj' W0'' Wj'' H₁ H₂ Ra Rb Rc h₁ h₂ x y w c ρ hRa hρ
  obtain ⟨⟨c0, d0⟩, c, d⟩ := c
  have hρ' := fun h => hρ ((LinkVSeq.mem_withheld H₁ H₂ ρ).mpr h)
  have n1 : Rho.fst (s := R₁.shape) (t := R₂.shape) ρ ∉ H₁.withheld := fun h => hρ' (Or.inl h)
  have n2 : Rho.snd (s := R₁.shape) (t := R₂.shape) ρ ∉ H₂.withheld := fun h => hρ' (Or.inr h)
  obtain ⟨ho, hRb⟩ := h₁ x y w (c0, c) _ hRa n1
  obtain ⟨ho2, hRc⟩ := h₂ _ _ _ (d0, d) _ hRb n2
  rw [LinkVSeq.run_one]
  constructor
  · show (R₁.out x y (Tr.fst (Tr.app _ _))).bind (fun x₂ =>
        R₂.out x₂ (R₁.imp y (Tr.fst (Tr.app _ _))) (Tr.snd (s := R₁.shape) (Tr.app _ _))) = _
    rw [Tr.fst_app, Tr.snd_app, ho]
    exact ho2
  · show Rc _ (R₂.imp (R₁.imp y (Tr.fst (Tr.app _ _))) (Tr.snd (s := R₁.shape) (Tr.app _ _))) _
    rw [Tr.fst_app, Tr.snd_app]
    exact hRc

/-! ## The simulator -/

namespace LinkVSeq
open IOR OnlineHon BatchSeqZk

section Sim
variable {X X' X'' : Type} {Ei Eo Eo' : ExtSpec} (R₁ : IOR X Ei X' Eo) (R₂ : IOR X' Eo X'' Eo')
  (Wh : Set (Rho R₁.shape)) {N : ℕ}

open Classical in
/-- The slots of J that the first link does not withhold. -/
def alive (J : Finset (Fin N)) (ρs : J → Rho (R₁.shape ++ R₂.shape)) :
    Finset (Fin N) :=
  J.filter fun j => ∃ h : j ∈ J, Rho.fst (ρs ⟨j, h⟩) ∉ Wh

variable {R₁ R₂ Wh}

theorem alive_sub {J : Finset (Fin N)} {ρs : J → Rho (R₁.shape ++ R₂.shape)}
    {j : Fin N} (h : j ∈ alive R₁ R₂ Wh J ρs) : j ∈ J := by
  classical
  exact (Finset.mem_filter.mp h).1

theorem mem_alive {J : Finset (Fin N)} {ρs : J → Rho (R₁.shape ++ R₂.shape)} (j : J) :
    j.1 ∈ alive R₁ R₂ Wh J ρs ↔ Rho.fst (ρs j) ∉ Wh := by
  classical
  exact Finset.mem_filter.trans ⟨fun h => h.2.2, fun h => ⟨j.2, j.2, h⟩⟩

def up {J : Finset (Fin N)} {ρs : J → Rho (R₁.shape ++ R₂.shape)} (j : alive R₁ R₂ Wh J ρs) : J :=
  ⟨j.1, alive_sub j.2⟩

variable (R₁ R₂ Wh)

/-- What step 2 finds for one slot: the middle explicit part, the symbols for the second
simulator, the rule that glues. -/
abbrev Info : Type := X' × (Eo.Pos → Option Eo.Sym) × (Option (View R₂) → Option (View (R₁.seq R₂)))

/-- Step 2. -/
def info (x : X) (ρ : Rho (R₁.shape ++ R₂.shape))
    (T : Finset (OPos (R₁.shape ++ R₂.shape))) (a : Ei.Pos → Option Ei.Sym) (v : Option (View R₁)) :
    Option (Info R₁ R₂) :=
  v.bind fun V =>
      (pick fun z : Ei.Str × Tr R₁.shape => Ei.Fits a z.1 ∧ V.Fits (Rho.fst ρ) z.2).bind
          fun z => (R₁.out x z.1 z.2).map fun x' =>
    (x', Eo.ans (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)) (R₁.imp z.1 z.2),
      glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T z.2)

theorem info_view (hL : R₁.IsLocal) (x : X) (y : Ei.Str) (ρ : Rho (R₁.shape ++ R₂.shape))
    (T : Finset (OPos (R₁.shape ++ R₂.shape))) (τ₁ : Tr R₁.shape) (a1 : τ₁.rho = Rho.fst ρ)
    (x₂ : X') (hout : R₁.out x y τ₁ = some x₂) :
    info R₁ R₂ x ρ T (Ei.ans ((R₁.seq R₂).given ρ T) y) (some (R₁.view (firstT R₁ R₂ ρ T) τ₁)) =
      some (x₂, Eo.ans (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)) (R₁.imp y τ₁),
          glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T τ₁) := by
  obtain ⟨z, hz, hE, hV⟩ := pick_spec
    (P := fun z : Ei.Str × Tr R₁.shape =>
        Ei.Fits (Ei.ans ((R₁.seq R₂).given ρ T) y) z.1 ∧
        (R₁.view (firstT R₁ R₂ ρ T) τ₁).Fits (Rho.fst ρ) z.2)
    ⟨(y, τ₁), Ei.fits_ans _ y, a1 ▸ view_fits _ τ₁⟩
  have hr : z.2.rho = τ₁.rho := hV.1.trans a1.symm
  have h1 : R₁.out x z.1 z.2 = some x₂ := by
    rw [← hout]
    refine hL.out x z.1 y z.2 τ₁ hr hV.2.1 (fun p hp => hE.rd_eq ?_)
      (fun p hp => hV.read_eq (Or.inl (hr ▸ hp)))
    exact given_first_subset ρ T (IOR.mem_given.2 (Or.inl (hV.1 ▸ hp)))
  have h2 : Eo.ans (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)) (R₁.imp z.1 z.2) =
      Eo.ans (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)) (R₁.imp y τ₁) := by
    refine Eo.ans_congr fun e he =>
      hL.imp z.1 y z.2 τ₁ e hr hV.2.1
        (fun p hp => hE.rd_eq (srcE_subset_given he (hV.1 ▸ hp))) fun p hp => hV.read_eq ?_
    exact Or.inr (Or.inl (mem_firstT.2 (Or.inr ⟨e, he, hV.1 ▸ hp⟩)))
  have h3 : glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T z.2 =
      glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T τ₁ := by
    funext o₂
    cases o₂ with
    | none => rfl
    | some V₂ =>
        exact pick_map_congr fun τ₂ hτ₂ =>
          view_app_congr ρ T hV.1 a1 hτ₂.1 hτ₂.1 hV.2.1 rfl
            (fun p hp => hV.read_eq (a1 ▸ hp)) fun _ _ => rfl
  unfold info
  rw [Option.bind_some, hz, Option.bind_some, h1, Option.map_some, h2, h3]

open Classical in
/-- Step 4: the notice, or the two glued. -/
def post (J : Finset (Fin N)) (ρs : J → Rho (R₁.shape ++ R₂.shape))
    (g : alive R₁ R₂ Wh J ρs → Info R₁ R₂) (ds : alive R₁ R₂ Wh J ρs → Option (View R₂)) :
    J → Option (View (R₁.seq R₂)) :=
  fun j => if h : j.1 ∈ alive R₁ R₂ Wh J ρs then (g ⟨j.1, h⟩).2.2 (ds ⟨j.1, h⟩) else none

/-- Steps 2 to 4, given the simulated views of the first link. -/
def kern (S₂ : R₂.SimV N) (J : Finset (Fin N)) (xs : J → X)
    (ρs : J → Rho (R₁.shape ++ R₂.shape)) (Ts : J → Finset (OPos (R₁.shape ++ R₂.shape)))
    (as : J → Ei.Pos → Option Ei.Sym) (vs : J → Option (View R₁)) :
    PMF (J → Option (View (R₁.seq R₂))) :=
  match seqOpt fun j : alive R₁ R₂ Wh J ρs =>
      info R₁ R₂ (xs (up j)) (ρs (up j)) (Ts (up j)) (as (up j)) (vs (up j)) with
  | none => PMF.pure fun _ => none
  | some g =>
    (S₂ (alive R₁ R₂ Wh J ρs) (fun j => (g j).1) (fun j => Rho.snd (s := R₁.shape) (ρs (up j)))
        (fun j => partR R₁.shape (Ts (up j))) fun j => (g j).2.1).map
      (post R₁ R₂ Wh J ρs g)

theorem kern_of_some (S₂ : R₂.SimV N) (J : Finset (Fin N)) (xs : J → X)
    (ρs : J → Rho (R₁.shape ++ R₂.shape))
    (Ts : J → Finset (OPos (R₁.shape ++ R₂.shape))) (as : J → Ei.Pos → Option Ei.Sym)
    (vs : J → Option (View R₁)) (g : alive R₁ R₂ Wh J ρs → Info R₁ R₂)
    (h : (seqOpt fun j : alive R₁ R₂ Wh J ρs =>
        info R₁ R₂ (xs (up j)) (ρs (up j)) (Ts (up j)) (as (up j)) (vs (up j))) = some g) :
    kern R₁ R₂ Wh S₂ J xs ρs Ts as vs =
      (S₂ (alive R₁ R₂ Wh J ρs) (fun j => (g j).1) (fun j => Rho.snd (s := R₁.shape) (ρs (up j)))
          (fun j => partR R₁.shape (Ts (up j))) fun j => (g j).2.1).map
        (post R₁ R₂ Wh J ρs g) := by
  unfold kern
  rw [h]

/-- The simulator of the composition. -/
def sim (S₁ : R₁.SimV N) (S₂ : R₂.SimV N) : (R₁.seq R₂).SimV N := fun J xs ρs Ts as =>
  (S₁ J xs (fun j => Rho.fst (s := R₁.shape) (t := R₂.shape) (ρs j))
      (fun j => firstT R₁ R₂ (ρs j) (Ts j)) (fun j =>
        cut (R₁.given (Rho.fst (s := R₁.shape) (t := R₂.shape) (ρs j)) (firstT R₁ R₂ (ρs j) (Ts j)))
          (as j))).bind
    (kern R₁ R₂ Wh S₂ J xs ρs Ts as)

end Sim

/-! ## Under the hypotheses below, the simulation is exact -/

section Exact
variable {X X' X'' : Type} {Ei Eo Eo' : ExtSpec} {R₁ : IOR X Ei X' Eo} {R₂ : IOR X' Eo X'' Eo'}
  {A₁ : RoundSplits R₁.shape} {A₂ : RoundSplits R₂.shape} {W0 Wj W0' Wj' W0'' Wj'' : Type}
  (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'')

open Classical in
/-- Under the hypotheses below: the named simulator is exact, at the composed budget. -/
theorem exactWith_seqV {Ra : X → Ei.Str → W0 × Wj → Prop}
    {Rb : X' → Eo.Str → W0' × Wj' → Prop} {N : ℕ} {b₁ : BudB R₁.shape N}
    {b₂ : BudB R₂.shape N} (hL : R₁.IsLocal) (hA : H₁.AccV Ra Rb) (S₁ : R₁.SimV N)
    (hS₁ : H₁.ExactVWith N Ra b₁ S₁) (S₂ : R₂.SimV N) (hS₂ : H₂.ExactVWith N Rb b₂ S₂) :
    (H₁.seqV H₂).ExactVWith N Ra (budSeqV R₁ R₂ b₁ b₂) (sim R₁ R₂ H₁.withheld S₁ S₂) := by
  intro w0 J as ha (ρ : BRho N (R₁.shape ++ R₂.shape) (RoundSplits.app A₁ A₂)) Ts hbud
  -- what the first link's run in slot j shows
  let hh : H₁.Coin0 × (Fin N → H₁.Coin) → J → Option (View R₁) := fun c j =>
    if Rho.fst (ρ.slot j.1) ∈ H₁.withheld then none
    else
      some (R₁.view (firstT R₁ R₂ (ρ.slot j.1) (Ts j))
          ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).1)
  have hslot1 : (fun j : J => (BRho.fstA A₁ A₂ ρ).slot j.1) = fun j => Rho.fst (ρ.slot j.1) :=
    funext fun j => BRho.slot_fstA j.1 A₁ A₂ ρ
  have hlaw : S₁ J (fun j => (as j).1) (fun j => Rho.fst (ρ.slot j.1))
        (fun j => firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (fun j =>
          cut (R₁.given (Rho.fst (ρ.slot j.1)) (firstT R₁ R₂ (ρ.slot j.1) (Ts j)))
            (Ei.ans ((R₁.seq R₂).given (ρ.slot j.1) (Ts j)) (as j).2.1)) =
      (unif (H₁.Coin0 × (Fin N → H₁.Coin))).map hh := by
    have h := hS₁ w0 J as ha (BRho.fstA A₁ A₂ ρ)
      (fun j => firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (by rw [hslot1]; exact hbud.1)
    unfold HonestV.output at h
    simp only [BRho.slot_fstA] at h
    exact Eq.trans
      (congrArg _ (funext fun j => cut_ans (given_first_subset (ρ.slot j.1) (Ts j)) (as j).2.1))
      h.symm
  show _ = PMF.bind
      (S₁ J (fun j => (as j).1) (fun j => Rho.fst (ρ.slot j.1))
        (fun j => firstT R₁ R₂ (ρ.slot j.1) (Ts j)) (fun j =>
          cut (R₁.given (Rho.fst (ρ.slot j.1)) (firstT R₁ R₂ (ρ.slot j.1) (Ts j)))
            (Ei.ans ((R₁.seq R₂).given (ρ.slot j.1) (Ts j)) (as j).2.1))) _
  rw [hlaw]
  unfold HonestV.output
  refine law_split2 hh _ _ fun c => ?_
  -- the coins of the first link are fixed
  let r : J → Tr R₁.shape × W0' × X' × Wj' := fun j =>
    (H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))
  let w0' : W0' := (H₁.strat0 w0 c.1).res (BRho.shared (BRho.fstA A₁ A₂ ρ))
  let A' : J → X' × Eo.Str × Wj' := fun j => ((r j).2.2.1, R₁.imp (as j).2.1 (r j).1, (r j).2.2.2)
  have hw0 : ∀ j : J, (r j).2.1 = w0' := fun j => by
    show ((SStratR.zip (H₁.strat0 w0 c.1) (H₁.strat w0 c.1 (as j).1 (as j).2.2 (c.2 j.1))).run
        (Rho.fst (ρ.slot j.1))).2.1 = _
    rw [SStratR.res_zip, ← BRho.slot_fstA, BRho.sh_slot_shared]
  have hnw : ∀ j : J,
      j.1 ∈ alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) → Rho.fst (ρ.slot j.1) ∉ H₁.withheld :=
    fun j hj => (mem_alive j).mp hj
  have hacc : ∀ j : J, j.1 ∈ alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) →
      R₁.out (as j).1 (as j).2.1 (r j).1 = some (r j).2.2.1 ∧
      Rb (r j).2.2.1 (R₁.imp (as j).2.1 (r j).1) (w0', (r j).2.2.2) := fun j hj => by
    have h := hA (as j).1 (as j).2.1 (w0, (as j).2.2) (c.1, c.2 j.1) _ (ha j) (hnw j hj)
    refine ⟨h.1, ?_⟩
    rw [← hw0 j]
    exact h.2
  let g : alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) → Info R₁ R₂ := fun j =>
    ((A' (up j)).1,
      Eo.ans (R₂.given (Rho.snd (s := R₁.shape) (ρ.slot (up j).1)) (partR R₁.shape (Ts (up j))))
        (A' (up j)).2.1,
      glue R₁ R₂ (Rho.snd (s := R₁.shape) (ρ.slot (up j).1)) (Ts (up j)) (r (up j)).1)
  have hseq : (seqOpt fun j : alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) =>
        info R₁ R₂ (as (up j)).1 (ρ.slot (up j).1) (Ts (up j))
          (Ei.ans ((R₁.seq R₂).given (ρ.slot (up j).1) (Ts (up j))) (as (up j)).2.1)
          (hh c (up j))) = some g := by
    refine seqOpt_some _ _ fun j => ?_
    have e : hh c (up j) =
        some (R₁.view (firstT R₁ R₂ (ρ.slot (up j).1) (Ts (up j))) (r (up j)).1) :=
      if_neg (hnw (up j) j.2)
    rw [e]
    exact info_view R₁ R₂ hL _ _ _ _ _ (Strat.rho_run _ _) _ (hacc (up j) j.2).1
  refine Eq.trans ?_
    (kern_of_some R₁ R₂ H₁.withheld S₂ J (fun j => (as j).1) (fun j => ρ.slot j.1) Ts
      (fun j => Ei.ans ((R₁.seq R₂).given (ρ.slot j.1) (Ts j)) (as j).2.1) (hh c) g hseq).symm
  have hslot2 : (fun j : alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1) =>
        (BRho.sndA A₁ A₂ ρ).slot j.1) =
      fun j => Rho.snd (s := R₁.shape) (ρ.slot (up j).1) :=
    funext fun j => BRho.slot_sndA j.1 A₁ A₂ ρ
  have hQ := hS₂ w0' (alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1)) (fun j => A' (up j))
    (fun j => (hacc (up j) j.2).2) (BRho.sndA A₁ A₂ ρ) (fun j => partR R₁.shape (Ts (up j))) (by
      rw [hslot2]
      exact hbud.2 _ fun j hj => alive_sub hj)
  unfold HonestV.output at hQ
  simp only [BRho.slot_sndA] at hQ
  show _ = PMF.map _
      (S₂ _ (fun j => (A' (up j)).1) (fun j => Rho.snd (s := R₁.shape) (ρ.slot (up j).1))
        (fun j => partR R₁.shape (Ts (up j))) fun j =>
          Eo.ans (R₂.given (Rho.snd (s := R₁.shape) (ρ.slot (up j).1)) (partR R₁.shape (Ts (up j))))
            (A' (up j)).2.1)
  refine Eq.trans ?_ (congrArg (PMF.map _) hQ)
  rw [PMF.map_comp]
  refine congrArg (fun φ => PMF.map φ _) (funext fun d => funext fun j => ?_)
  by_cases hj : j.1 ∈ alive R₁ R₂ H₁.withheld J (fun j => ρ.slot j.1)
  · refine Eq.trans ?_ (dif_pos hj).symm
    show _ = glue R₁ R₂ (Rho.snd (s := R₁.shape) (ρ.slot j.1)) (Ts j) (r j).1
        (ite (Rho.snd (s := R₁.shape) (ρ.slot j.1) ∈ H₂.withheld) none (some _))
    by_cases hq : Rho.snd (s := R₁.shape) (ρ.slot j.1) ∈ H₂.withheld
    · refine (if_pos ((mem_withheld H₁ H₂ _).mpr (Or.inr hq))).trans ?_
      rw [if_pos hq]
      rfl
    · refine (if_neg fun h => ((mem_withheld H₁ H₂ _).mp h).elim (hnw j hj) hq).trans ?_
      rw [if_neg hq]
      refine Eq.trans ?_
        (glue_view (ρ.slot j.1) (Ts j) (τ₁ := (r j).1)
          (τ₂ := ((H₂.one w0' (A' j).1 (A' j).2.2 (d.1, d.2 j.1)).run
              (Rho.snd (s := R₁.shape) (ρ.slot j.1))).1)
          (Strat.rho_run _ _) (Strat.rho_run _ _)).symm
      refine congrArg some (congrArg _ ?_)
      refine (congrArg Prod.fst
        (run_one H₁ H₂ w0 (as j).1 (as j).2.2 c.1 d.1 (c.2 j.1) (d.2 j.1) (ρ.slot j.1))).trans ?_
      have e2 : ((H₁.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.1 =
          w0' := hw0 j
      show Tr.app _ _ = Tr.app _ _
      rw [e2]
  · refine Eq.trans ?_ (dif_neg hj).symm
    exact if_pos
      ((mem_withheld H₁ H₂ _).mpr (Or.inl (not_not.mp fun h => hj ((mem_alive j).mpr h))))

end Exact
end LinkVSeq

theorem exact_seqV : Spec.exact_seqV := by
  intro X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ W0 Wj W0' Wj' W0'' Wj'' H₁ H₂ Ra Rb N b₁ b₂ hL hA hE₁ hE₂
  obtain ⟨S₁, hS₁⟩ := hE₁
  obtain ⟨S₂, hS₂⟩ := hE₂
  exact ⟨_, LinkVSeq.exactWith_seqV H₁ H₂ hL hA S₁ hS₁ S₂ hS₂⟩

end Iop
