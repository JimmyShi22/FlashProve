-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/BatchSeqZkProofs.lean: "a link, then a batch IOP": completeness and honest-verifier exact
zero knowledge for sets of slots with further reads (`BIOP.Honest.Exact`, Ior/Batch.lean).

In standard terms: a composition rule for interactive oracle reductions that run on a batch of
instances.

Proofs of `Iop.Spec.acc_seqB` and `Iop.Spec.exact_seqB` (stated in Ior/BatchSeqZk.lean), with the
simulator named (`BatchSeqZk.sim`, `exactWith_seqB`).

What a link and a slot are: the head of Ior/BatchSeqZk.lean.

The simulator for a set J of slots. It is given J, the instances, the verifier messages and the
further positions T_j of the slots of J, and for each slot of J the symbols of (shared oracles,
own oracles) at the positions `given` of the composition.
 1. The link's simulator once, for J, at the first parts of the ρ_j and the positions `firstT`
    (Ior/ExactSeq.lean): the part of T_j in the link's shape, and the sources in the link's
    oracles of all that Q's simulator will be given in slot j. What it is to be given is among
    what the simulator has.
 2. J': the slots of J that the link does not withhold (a public matter). For j in J', from the
    simulated view and the given symbols: some oracles and some transcript that fit both (a
    choice), and from them the explicit part that the link's verifier outputs and the symbols of
    the new implicit instance that Q's simulator is given. As the link is local, these are the
    true ones (on the view of a run, under the hypotheses of its statement: `info_view`).
 3. Q's simulator once, for J', on these data.
 4. For each slot of J: the notice (`none`: `BIOP.Honest.output`, Ior/Batch.lean; the word:
    `IOR.Honest.output`, Ior/Honest.lean), if j is not in J', or Q's simulator shows the notice,
    or `info` returns `none` at some slot of J' (then at every slot of J: `kern`); else the two
    views glued (Ior/OnlineHonView.lean: `glue`) (exactly: `post`, `kern`).

Why it is exact, under the hypotheses of `exactWith_seqB`. For fixed coins of the link (shared and
slots'), the statements that the slots of J' hand on are in Q's relation (completeness of the
first: `hA`), with one shared witness (a function of the shared witness W0, the shared coins and
the shared verifier messages, by type) and one shared oracle (determined by that witness, by
hypothesis). So the law of the rest is Q's simulator's, and its arguments depend on the link's
coins only through the views at `firstT`. So the joint law is a bind over the law of these views,
which is the link's simulator's.

Limits: this file says nothing on running times; nothing on soundness. See also Limits in the head
of Ior/BatchSeqZk.lean.

Terms: lean/GLOSSARY.md.
-/
import Ior.BatchSeqZk
import Ior.OnlineHon
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. The verifier's randomness -/

theorem RhoLo.fstA_lo :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ρ : Rho (s ++ t)),
      RhoLo.fstA A B (Rho.lo (RoundSplits.app A B) ρ) = Rho.lo A (Rho.fst ρ)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (a, A), B, (c, ρ) => congrArg (Prod.mk (a.kind.loOf c)) (RhoLo.fstA_lo A B ρ)

theorem RhoLo.sndA_lo :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ρ : Rho (s ++ t)),
      RhoLo.sndA A B (Rho.lo (RoundSplits.app A B) ρ) = Rho.lo B (Rho.snd (s := s) ρ)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, A), B, (_, ρ) => RhoLo.sndA_lo A B ρ

theorem RhoSh.fstA_sh :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ρ : Rho (s ++ t)),
      RhoSh.fstA A B (Rho.sh (RoundSplits.app A B) ρ) = Rho.sh A (Rho.fst ρ)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (a, A), B, (c, ρ) => congrArg (Prod.mk (a.kind.shOf c)) (RhoSh.fstA_sh A B ρ)

theorem RhoSh.sndA_sh :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ρ : Rho (s ++ t)),
      RhoSh.sndA A B (Rho.sh (RoundSplits.app A B) ρ) = Rho.sh B (Rho.snd (s := s) ρ)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, A), B, (_, ρ) => RhoSh.sndA_sh A B ρ

theorem BRho.slot_fstA {N : ℕ} (j : Fin N) :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ρ : BRho N (s ++ t) (RoundSplits.app A B)),
      (BRho.fstA A B ρ).slot j = Rho.fst (ρ.slot j)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (a, A), B, (v, ρ) => congrArg (Prod.mk (a.kind.slot v j)) (BRho.slot_fstA j A B ρ)

theorem BRho.slot_sndA {N : ℕ} (j : Fin N) :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (ρ : BRho N (s ++ t) (RoundSplits.app A B)),
      (BRho.sndA A B ρ).slot j = Rho.snd (s := s) (ρ.slot j)
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, A), B, (_, ρ) => BRho.slot_sndA j A B ρ

theorem Kind.shOf_slot {N : ℕ} {C : Type} (j : Fin N) :
    ∀ (k : Kind) (v : k.All N C), k.shOf (k.slot v j) = k.allSh v
  | .sh, _ => rfl
  | .lo, _ => rfl

/-- All slots see the same shared verifier messages. -/
theorem BRho.sh_slot_shared {N : ℕ} (j : Fin N) :
    ∀ {s : Shape} {A : RoundSplits s} (ρ : BRho N s A), Rho.sh A (ρ.slot j) = BRho.shared ρ
  | [], _, _ => rfl
  | _ :: _, (a, _), (v, ρ) => by
      have h1 := Kind.shOf_slot j a.kind v
      have h2 := BRho.sh_slot_shared j ρ
      exact Prod.ext h1 h2

/-! ## 2. Strategies with results -/

namespace SStratR

theorem zip_bind :
    ∀ {s t : Shape} {A : RoundSplits s} {B : RoundSplits t} {β γ : Type} (S : SStratR s A β) (L : LStratR s A γ)
        (f : β → SStrat t B) (g : β × γ → LStrat t B),
      (S.bind f).zip ((S.along L).bind g) = Strat.bind (S.zip L) fun p => (f p.1).zip (g p)
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _, _, (a, _), _, _, _, (m0, k0), (mj, kj), f, g =>
      congrArg (Prod.mk (a.join m0 mj)) (funext fun c => zip_bind (k0 (a.kind.shOf c)) (kj c) f g)

/-- The shared part's result is a function of the shared verifier messages. -/
theorem res_zip :
    ∀ {s : Shape} {A : RoundSplits s} {β γ : Type} (S : SStratR s A β) (L : LStratR s A γ) (ρ : Rho s),
      ((S.zip L).run ρ).2.1 = S.res (Rho.sh A ρ)
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, (a, _), _, _, (_, k0), (_, kj), (c, ρ) => res_zip (k0 (a.kind.shOf c)) (kj c) ρ

end SStratR

/-! ## 3. One slot of the composition -/

namespace BatchSeqZk
open IOR OnlineHon

section Slot
variable {X X' : Type} {E0 Ej E0' Ej' : ExtSpec} {R : IOR X (E0.prod Ej) X' (E0'.prod Ej')}
  {A : RoundSplits R.shape} {Q : BIOP X' (E0'.prod Ej')} {W0 Wj W0' Wj' : Type}
  (HR : R.HonestB A W0 Wj W0' Wj') (HQ : Q.Honest W0' Wj')

theorem mem_withheld (ρ : Rho (R.shape ++ Q.ior.shape)) :
    ρ ∈ (HR.seqB HQ).withheld ↔
    Rho.fst ρ ∈ HR.withheld ∨ Rho.snd (s := R.shape) ρ ∈ HQ.withheld := by
  show ((RhoLo.fstA A Q.ann (Rho.lo (RoundSplits.app A Q.ann) ρ) ∈ HR.Bad ∨
        RhoLo.sndA A Q.ann (Rho.lo (RoundSplits.app A Q.ann) ρ) ∈ HQ.Bad) ∨
      (HR.stop0 (RhoSh.fstA A Q.ann (Rho.sh (RoundSplits.app A Q.ann) ρ)) ||
          HQ.stop0 (RhoSh.sndA A Q.ann (Rho.sh (RoundSplits.app A Q.ann) ρ))) = true) ↔
    (Rho.lo A (Rho.fst ρ) ∈ HR.Bad ∨ HR.stop0 (Rho.sh A (Rho.fst ρ)) = true) ∨
    (Rho.lo Q.ann (Rho.snd (s := R.shape) ρ) ∈ HQ.Bad ∨
      HQ.stop0 (Rho.sh Q.ann (Rho.snd (s := R.shape) ρ)) = true)
  rw [RhoLo.fstA_lo, RhoLo.sndA_lo, RhoSh.fstA_sh, RhoSh.sndA_sh, Bool.or_eq_true]
  tauto

theorem run_one (w0 : W0) (x : X) (wj : Wj) (c0R : HR.Coin0) (c0Q : HQ.Coin0) (cR : HR.Coin)
    (cQ : HQ.Coin) (ρ : Rho (R.shape ++ Q.ior.shape)) :
    (Strat.run ((HR.seqB HQ).one w0 x wj ((c0R, c0Q), (cR, cQ))) ρ).1 =
      Tr.app ((HR.one w0 x wj (c0R, cR)).run (Rho.fst ρ)).1
        ((HQ.one ((HR.one w0 x wj (c0R, cR)).run (Rho.fst ρ)).2.1
            ((HR.one w0 x wj (c0R, cR)).run (Rho.fst ρ)).2.2.1
            ((HR.one w0 x wj (c0R, cR)).run (Rho.fst ρ)).2.2.2 (c0Q, cQ)).run
          (Rho.snd (s := R.shape) ρ)).1 := by
  show (Strat.run
      (SStrat.zip ((HR.strat0 w0 c0R).bind fun w0' => HQ.strat0 w0' c0Q)
        (((HR.strat0 w0 c0R).along (HR.strat w0 c0R x wj cR)).bind fun o =>
          HQ.strat o.1 c0Q o.2.1 o.2.2 cQ)) ρ).1 = _
  rw [SStratR.zip_bind, Strat.run_bind]
  rfl

end Slot
end BatchSeqZk

/-! ## 4. Completeness -/

theorem acc_seqB : Spec.acc_seqB := by
  intro X X' E0 Ej E0' Ej' R A Q W0 Wj W0' Wj' HR HQ Ri Ro hR hQ x y w c ρ hRi hρ
  obtain ⟨⟨c0R, c0Q⟩, cR, cQ⟩ := c
  have hρ' := fun h => hρ ((BatchSeqZk.mem_withheld HR HQ ρ).mpr h)
  have h1 : Rho.fst (s := R.shape) (t := Q.ior.shape) ρ ∉ HR.withheld := fun h => hρ' (Or.inl h)
  have h2 : Rho.snd (s := R.shape) (t := Q.ior.shape) ρ ∉ HQ.withheld := fun h => hρ' (Or.inr h)
  obtain ⟨ho, hRo⟩ := hR x y w (c0R, cR) _ hRi h1
  have h3 := hQ _ _ _ (c0Q, cQ) _ hRo h2
  show ((R.seq Q.ior).out x y
      (Strat.run ((HR.seqB HQ).one w.1 x w.2 ((c0R, c0Q), (cR, cQ))) ρ).1).isSome = true
  rw [BatchSeqZk.run_one]
  show ((R.out x y (Tr.fst (Tr.app _ _))).bind fun x₂ =>
      Q.ior.out x₂ (R.imp y (Tr.fst (Tr.app _ _))) (Tr.snd (s := R.shape) (Tr.app _ _))).isSome =
    true
  rw [Tr.fst_app, Tr.snd_app, ho]
  exact h3

/-! ## 5. The simulator -/

namespace BatchSeqZk
open IOR OnlineHon

/-- A law over uniform coins from finite non-empty sets (two kinds of shared coins, two kinds of
coins for each slot): draw the first kinds; if, given these, the law over the rest is a kernel of
a function of them, the whole law is the law of that function followed by the kernel. -/
theorem law_split2 {ι C0 D0 C D V Out : Type} [Fintype ι] [DecidableEq ι] [Fintype C0] [Nonempty C0]
    [Fintype D0] [Nonempty D0] [Fintype C] [Nonempty C] [Fintype D] [Nonempty D]
    (hh : C0 × (ι → C) → V) (f : (C0 × D0) × (ι → C × D) → Out) (K : V → PMF Out)
    (h : ∀ c : C0 × (ι → C),
      (unif (D0 × (ι → D))).map (fun d => f ((c.1, d.1), fun i => (c.2 i, d.2 i))) = K (hh c)) :
    (unif ((C0 × D0) × (ι → C × D))).map f = ((unif (C0 × (ι → C))).map hh).bind K := by
  let e : (C0 × (ι → C)) × (D0 × (ι → D)) ≃ (C0 × D0) × (ι → C × D) :=
    { toFun := fun p => ((p.1.1, p.2.1), fun i => (p.1.2 i, p.2.2 i))
      invFun := fun c => ((c.1.1, fun i => (c.2 i).1), (c.1.2, fun i => (c.2 i).2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← map_unif_equiv e, PMF.map_comp]
  exact map_unif_bind_factor _ hh K h

open Classical in
/-- given symbols, cut down to a set of positions -/
def cut {E : ExtSpec} (U : Finset E.Pos) (a : E.Pos → Option E.Sym) :
    E.Pos → Option E.Sym :=
  fun p => if p ∈ U then a p else none

theorem cut_ans {E : ExtSpec} {U V : Finset E.Pos} (h : U ⊆ V) (y : E.Str) :
    cut U (E.ans V y) = E.ans U y := E.cut_ans h y

section Sim
variable {X X' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) (Q : BIOP X' Eo)
  (Wh : Set (Rho R.shape)) {N : ℕ}

open Classical in
/-- The slots of J that the link does not withhold. -/
def alive (J : Finset (Fin N)) (ρs : J → Rho (R.shape ++ Q.ior.shape)) :
    Finset (Fin N) :=
  J.filter fun j => ∃ h : j ∈ J, Rho.fst (ρs ⟨j, h⟩) ∉ Wh

variable {R Q Wh}

theorem alive_sub {J : Finset (Fin N)} {ρs : J → Rho (R.shape ++ Q.ior.shape)}
    {j : Fin N} (h : j ∈ alive R Q Wh J ρs) : j ∈ J := by
  classical
  exact (Finset.mem_filter.mp h).1

theorem mem_alive {J : Finset (Fin N)} {ρs : J → Rho (R.shape ++ Q.ior.shape)} (j : J) :
    j.1 ∈ alive R Q Wh J ρs ↔ Rho.fst (ρs j) ∉ Wh := by
  classical
  exact Finset.mem_filter.trans ⟨fun h => h.2.2, fun h => ⟨j.2, j.2, h⟩⟩

def up {J : Finset (Fin N)} {ρs : J → Rho (R.shape ++ Q.ior.shape)} (j : alive R Q Wh J ρs) : J :=
  ⟨j.1, alive_sub j.2⟩

variable (R Q Wh)

/-- Step 2: from a view of the link and the given symbols, the explicit part that the link's
verifier outputs and the symbols that Q's simulator is given. -/
def info (x : X) (ρ : Rho (R.shape ++ Q.ior.shape))
    (T : Finset (OPos (R.shape ++ Q.ior.shape)))
    (a : Ei.Pos → Option Ei.Sym) (v : Option (View R)) :
    Option (X' × (Eo.Pos → Option Eo.Sym)) :=
  v.bind fun V =>
      (pick fun z : Ei.Str × Tr R.shape => Ei.Fits a z.1 ∧ V.Fits (Rho.fst ρ) z.2).bind
          fun z => (R.out x z.1 z.2).map fun x' =>
    (x', Eo.ans (Q.ior.given (Rho.snd (s := R.shape) ρ) (partR R.shape T)) (R.imp z.1 z.2))

theorem info_view (hL : R.IsLocal) (x : X) (y : Ei.Str) (ρ : Rho (R.shape ++ Q.ior.shape))
    (T : Finset (OPos (R.shape ++ Q.ior.shape))) (τ₁ : Tr R.shape) (a1 : τ₁.rho = Rho.fst ρ)
    (x₂ : X') (hout : R.out x y τ₁ = some x₂) :
    info R Q x ρ T (Ei.ans ((R.seq Q.ior).given ρ T) y) (some (R.view (firstT R Q.ior ρ T) τ₁)) =
      some
        (x₂, Eo.ans (Q.ior.given (Rho.snd (s := R.shape) ρ) (partR R.shape T)) (R.imp y τ₁)) := by
  obtain ⟨z, hz, hE, hV⟩ := pick_spec
    (P := fun z : Ei.Str × Tr R.shape =>
        Ei.Fits (Ei.ans ((R.seq Q.ior).given ρ T) y) z.1 ∧
        (R.view (firstT R Q.ior ρ T) τ₁).Fits (Rho.fst ρ) z.2)
    ⟨(y, τ₁), Ei.fits_ans _ y, a1 ▸ view_fits _ τ₁⟩
  have hr : z.2.rho = τ₁.rho := hV.1.trans a1.symm
  have h1 : R.out x z.1 z.2 = some x₂ := by
    rw [← hout]
    refine hL.out x z.1 y z.2 τ₁ hr hV.2.1 (fun p hp => hE.rd_eq ?_)
      (fun p hp => hV.read_eq (Or.inl (hr ▸ hp)))
    exact given_first_subset ρ T (IOR.mem_given.2 (Or.inl (hV.1 ▸ hp)))
  have h2 : Eo.ans (Q.ior.given (Rho.snd (s := R.shape) ρ) (partR R.shape T)) (R.imp z.1 z.2) =
      Eo.ans (Q.ior.given (Rho.snd (s := R.shape) ρ) (partR R.shape T)) (R.imp y τ₁) := by
    refine Eo.ans_congr fun e he =>
      hL.imp z.1 y z.2 τ₁ e hr hV.2.1
        (fun p hp => hE.rd_eq (srcE_subset_given he (hV.1 ▸ hp))) fun p hp => hV.read_eq ?_
    exact Or.inr (Or.inl (mem_firstT.2 (Or.inr ⟨e, he, hV.1 ▸ hp⟩)))
  unfold info
  rw [Option.bind_some, hz, Option.bind_some, h1, Option.map_some, h2]

open Classical in
/-- Step 4: the notice, or the two views glued. -/
def post (J : Finset (Fin N)) (ρs : J → Rho (R.shape ++ Q.ior.shape))
    (Ts : J → Finset (OPos (R.shape ++ Q.ior.shape))) (as : J → Ei.Pos → Option Ei.Sym)
    (vs : J → Option (View R)) (ds : alive R Q Wh J ρs → Option (DView Q.ior.toInteractiveOracleProof)) :
    J → Option (DView (R.seq Q.ior).toInteractiveOracleProof) :=
  fun j =>
    if h : j.1 ∈ alive R Q Wh J ρs then
      (vs j).bind fun v => (ds ⟨j.1, h⟩).map fun d => glue R Q (ρs j) (Ts j) (as j) v d else none

/-- Steps 2 to 4, given the simulated views of the link. -/
def kern (SQ : Q.SimB N) (J : Finset (Fin N)) (xs : J → X)
    (ρs : J → Rho (R.shape ++ Q.ior.shape)) (Ts : J → Finset (OPos (R.shape ++ Q.ior.shape)))
    (as : J → Ei.Pos → Option Ei.Sym) (vs : J → Option (View R)) :
    PMF (J → Option (DView (R.seq Q.ior).toInteractiveOracleProof)) :=
  match seqOpt fun j : alive R Q Wh J ρs =>
      info R Q (xs (up j)) (ρs (up j)) (Ts (up j)) (as (up j)) (vs (up j)) with
  | none => PMF.pure fun _ => none
  | some g =>
    (SQ (alive R Q Wh J ρs) (fun j => (g j).1) (fun j => Rho.snd (s := R.shape) (ρs (up j)))
        (fun j => partR R.shape (Ts (up j))) fun j => (g j).2).map
      (post R Q Wh J ρs Ts as vs)

theorem kern_of_some (SQ : Q.SimB N) (J : Finset (Fin N)) (xs : J → X)
    (ρs : J → Rho (R.shape ++ Q.ior.shape)) (Ts : J → Finset (OPos (R.shape ++ Q.ior.shape)))
    (as : J → Ei.Pos → Option Ei.Sym) (vs : J → Option (View R))
    (g : alive R Q Wh J ρs → X' × (Eo.Pos → Option Eo.Sym))
    (h : (seqOpt fun j : alive R Q Wh J ρs =>
        info R Q (xs (up j)) (ρs (up j)) (Ts (up j)) (as (up j)) (vs (up j))) = some g) :
    kern R Q Wh SQ J xs ρs Ts as vs =
      (SQ (alive R Q Wh J ρs) (fun j => (g j).1) (fun j => Rho.snd (s := R.shape) (ρs (up j)))
          (fun j => partR R.shape (Ts (up j))) fun j => (g j).2).map
        (post R Q Wh J ρs Ts as vs) := by
  unfold kern
  rw [h]

end Sim

section Sim2
variable {X X' : Type} {E0 Ej E0' Ej' : ExtSpec} (R : IOR X (E0.prod Ej) X' (E0'.prod Ej'))
  (A : RoundSplits R.shape) (Q : BIOP X' (E0'.prod Ej')) (Wh : Set (Rho R.shape)) {N : ℕ}

/-- The simulator of the composition. -/
def sim (SR : R.SimL N) (SQ : Q.SimB N) : (seqB R A Q).SimB N := fun J xs ρs Ts as =>
  (SR J xs (fun j => Rho.fst (s := R.shape) (t := Q.ior.shape) (ρs j))
      (fun j => firstT R Q.ior (ρs j) (Ts j)) (fun j =>
        cut (R.given (Rho.fst (s := R.shape) (t := Q.ior.shape) (ρs j))
            (firstT R Q.ior (ρs j) (Ts j))) (as j))).bind
    (kern R Q Wh SQ J xs ρs Ts as)

end Sim2

/-! ## 6. Under the hypotheses below, the simulation is exact -/

open Classical in
theorem outputL_eq {X X' W0 Wj W0' Wj' : Type} {E0 Ej Eo : ExtSpec} {R : IOR X (E0.prod Ej) X' Eo}
    {A : RoundSplits R.shape} (H : R.HonestB A W0 Wj W0' Wj') {N : ℕ} (w0 : W0)
    (a : Fin N → Option (X × Ej.Str × Wj)) (ρ : BRho N R.shape A) (J : Finset (Fin N))
    (Ts : J → Finset (OPos R.shape)) (as : J → X × Ej.Str × Wj) (has : ∀ j : J, a j = some (as j)) :
    H.output w0 a ρ J Ts = (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j : J =>
      if ρ.slot j.1 ∈ H.withheld then none
      else
          some (R.view (Ts j)
                ((H.one w0 (as j).1 (as j).2.2 (c.1, c.2 j)).run (ρ.slot j.1)).1) := by
  unfold IOR.HonestB.output
  refine congrArg (fun φ => PMF.map φ _) (funext fun c => funext fun j => ?_)
  rw [has j]

section Exact
variable {X X' : Type} {E0 Ej E0' Ej' : ExtSpec} {R : IOR X (E0.prod Ej) X' (E0'.prod Ej')}
  {A : RoundSplits R.shape} {Q : BIOP X' (E0'.prod Ej')} {W0 Wj W0' Wj' : Type}
  (HR : R.HonestB A W0 Wj W0' Wj') (HQ : Q.Honest W0' Wj')

open Classical in
/-- Under the hypotheses below: the named simulator is exact, at the composed budget. -/
theorem exactWith_seqB {Ri : X → (E0.prod Ej).Str → W0 × Wj → Prop}
    {Ro : X' → (E0'.prod Ej').Str → W0' × Wj' → Prop} {N : ℕ} {bR : BudB R.shape N}
    {bQ : BudB Q.ior.shape N} (f : W0' → E0'.Str) (hL : R.IsLocal) (hA : HR.AccB Ri Ro)
    (hf : ∀ x y w, Ro x y w → y.1 = f w.1) (SR : R.SimL N) (hSR : HR.ExactBWith N Ri bR SR)
    (SQ : Q.SimB N) (hSQ : HQ.ExactWith N Ro bQ SQ) :
    (HR.seqB HQ).ExactWith N Ri (budSeqB R Q bR bQ) (sim R A Q HR.withheld SR SQ) := by
  intro w0 y0 a ha J as has (ρ : BRho N (R.shape ++ Q.ior.shape) (RoundSplits.app A Q.ann)) Ts hbud
  -- what the link's run in slot j shows
  let hh : HR.Coin0 × (Fin N → HR.Coin) → J → Option (View R) := fun c j =>
    if Rho.fst (ρ.slot j.1) ∈ HR.withheld then none
    else
      some (R.view (firstT R Q.ior (ρ.slot j.1) (Ts j))
          ((HR.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).1)
  have hslot1 : (fun j : J => (BRho.fstA A Q.ann ρ).slot j.1) = fun j => Rho.fst (ρ.slot j.1) :=
    funext fun j => BRho.slot_fstA j.1 A Q.ann ρ
  have hlaw : SR J (fun j => (as j).1) (fun j => Rho.fst (ρ.slot j.1))
        (fun j => firstT R Q.ior (ρ.slot j.1) (Ts j)) (fun j =>
          cut (R.given (Rho.fst (ρ.slot j.1)) (firstT R Q.ior (ρ.slot j.1) (Ts j)))
            ((E0.prod Ej).ans ((R.seq Q.ior).given (ρ.slot j.1) (Ts j)) (y0, (as j).2.1))) =
      (unif (HR.Coin0 × (Fin N → HR.Coin))).map hh := by
    have h := hSR w0 y0 a ha J as has (BRho.fstA A Q.ann ρ)
      (fun j => firstT R Q.ior (ρ.slot j.1) (Ts j)) (by rw [hslot1]; exact hbud.1)
    rw [outputL_eq HR w0 a _ J _ as has] at h
    simp only [BRho.slot_fstA] at h
    exact Eq.trans
      (congrArg _
        (funext fun j => cut_ans (given_first_subset (ρ.slot j.1) (Ts j)) (y0, (as j).2.1))) h.symm
  show _ = PMF.bind
      (SR J (fun j => (as j).1) (fun j => Rho.fst (ρ.slot j.1))
        (fun j => firstT R Q.ior (ρ.slot j.1) (Ts j)) (fun j =>
          cut (R.given (Rho.fst (ρ.slot j.1)) (firstT R Q.ior (ρ.slot j.1) (Ts j)))
            ((E0.prod Ej).ans ((R.seq Q.ior).given (ρ.slot j.1) (Ts j)) (y0, (as j).2.1)))) _
  rw [hlaw]
  refine (outputQ_eq (HR.seqB HQ) w0 y0 a ρ J Ts as has).trans ?_
  refine law_split2 hh _ _ fun c => ?_
  -- the coins of the link are fixed
  let r : J → Tr R.shape × W0' × X' × Wj' := fun j =>
    (HR.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))
  let w0' : W0' := (HR.strat0 w0 c.1).res (BRho.shared (BRho.fstA A Q.ann ρ))
  let A' : J → X' × Ej'.Str × Wj' := fun j =>
    ((r j).2.2.1, (R.imp (y0, (as j).2.1) (r j).1).2, (r j).2.2.2)
  have hw0 : ∀ j : J, (r j).2.1 = w0' := fun j => by
    show ((SStratR.zip (HR.strat0 w0 c.1) (HR.strat w0 c.1 (as j).1 (as j).2.2 (c.2 j.1))).run
        (Rho.fst (ρ.slot j.1))).2.1 = _
    rw [SStratR.res_zip, ← BRho.slot_fstA, BRho.sh_slot_shared]
  have hnw : ∀ j : J,
      j.1 ∈ alive R Q HR.withheld J (fun j => ρ.slot j.1) → Rho.fst (ρ.slot j.1) ∉ HR.withheld :=
    fun j hj => (mem_alive j).mp hj
  have hacc : ∀ j : J, j.1 ∈ alive R Q HR.withheld J (fun j => ρ.slot j.1) →
      R.out (as j).1 (y0, (as j).2.1) (r j).1 = some (r j).2.2.1 ∧
      Ro (r j).2.2.1 (R.imp (y0, (as j).2.1) (r j).1) (w0', (r j).2.2.2) := fun j hj => by
    have h := hA (as j).1 (y0, (as j).2.1) (w0, (as j).2.2) (c.1, c.2 j.1) _
      (ha j.1 (as j) (has j)) (hnw j hj)
    refine ⟨h.1, ?_⟩
    rw [← hw0 j]
    exact h.2
  have himp : ∀ j : J, j.1 ∈ alive R Q HR.withheld J (fun j => ρ.slot j.1) →
      R.imp (y0, (as j).2.1) (r j).1 = (f w0', (A' j).2.1) := fun j hj =>
    Prod.ext (hf _ _ _ (hacc j hj).2) rfl
  have hseq : (seqOpt fun j : alive R Q HR.withheld J (fun j => ρ.slot j.1) =>
        info R Q (as (up j)).1 (ρ.slot (up j).1) (Ts (up j))
          ((E0.prod Ej).ans ((R.seq Q.ior).given (ρ.slot (up j).1) (Ts (up j)))
            (y0, (as (up j)).2.1)) (hh c (up j))) =
      some fun j =>
        ((A' (up j)).1,
          (E0'.prod Ej').ans
            (Q.ior.given (Rho.snd (s := R.shape) (ρ.slot (up j).1)) (partR R.shape (Ts (up j))))
            (f w0', (A' (up j)).2.1)) := by
    refine seqOpt_some _ _ fun j => ?_
    have e : hh c (up j) =
        some (R.view (firstT R Q.ior (ρ.slot (up j).1) (Ts (up j))) (r (up j)).1) :=
      if_neg (hnw (up j) j.2)
    rw [e, ← himp (up j) j.2]
    exact info_view R Q hL _ _ _ _ _ (Strat.rho_run _ _) _ (hacc (up j) j.2).1
  refine Eq.trans ?_
    (kern_of_some R Q HR.withheld SQ J (fun j => (as j).1) (fun j => ρ.slot j.1) Ts
      (fun j => (E0.prod Ej).ans ((R.seq Q.ior).given (ρ.slot j.1) (Ts j)) (y0, (as j).2.1)) (hh c)
      _ hseq).symm
  let a' : Fin N → Option (X' × Ej'.Str × Wj') := fun j =>
    if h : j ∈ alive R Q HR.withheld J (fun j => ρ.slot j.1) then some (A' ⟨j, alive_sub h⟩)
    else none
  have hslot2 : (fun j : alive R Q HR.withheld J (fun j => ρ.slot j.1) =>
        (BRho.sndA A Q.ann ρ).slot j.1) =
      fun j => Rho.snd (s := R.shape) (ρ.slot (up j).1) :=
    funext fun j => BRho.slot_sndA j.1 A Q.ann ρ
  have hQ := hSQ w0' (f w0') a' (fun j aj h => by
      by_cases hj : j ∈ alive R Q HR.withheld J (fun j => ρ.slot j.1)
      · have h' : some (A' ⟨j, alive_sub hj⟩) = some aj := (dif_pos hj).symm.trans h
        obtain rfl := Option.some.inj h'
        have h2 := (hacc ⟨j, alive_sub hj⟩ hj).2
        rw [himp ⟨j, alive_sub hj⟩ hj] at h2
        exact h2
      · have h' : none = some aj := (dif_neg hj).symm.trans h
        cases h')
    (alive R Q HR.withheld J (fun j => ρ.slot j.1)) (fun j => A' (up j)) (fun j => dif_pos j.2)
    (BRho.sndA A Q.ann ρ) (fun j => partR R.shape (Ts (up j))) (by
      rw [hslot2]
      exact hbud.2 _ fun j hj => alive_sub hj)
  rw [outputQ_eq HQ w0' (f w0') a' (BRho.sndA A Q.ann ρ) _ _
      (fun j => A' (up j)) (fun j => dif_pos j.2)] at hQ
  simp only [BRho.slot_sndA] at hQ
  show _ = PMF.map _
      (SQ _ (fun j => (A' (up j)).1) (fun j => Rho.snd (s := R.shape) (ρ.slot (up j).1))
        (fun j => partR R.shape (Ts (up j))) fun j =>
          (E0'.prod Ej').ans
            (Q.ior.given (Rho.snd (s := R.shape) (ρ.slot (up j).1)) (partR R.shape (Ts (up j))))
            (f w0', (A' (up j)).2.1))
  refine Eq.trans ?_ (congrArg (PMF.map _) hQ)
  rw [PMF.map_comp]
  refine congrArg (fun φ => PMF.map φ _) (funext fun d => funext fun j => ?_)
  by_cases hj : j.1 ∈ alive R Q HR.withheld J (fun j => ρ.slot j.1)
  · refine Eq.trans ?_ (dif_pos hj).symm
    have e : hh c j = some (R.view (firstT R Q.ior (ρ.slot j.1) (Ts j)) (r j).1) :=
      if_neg (hnw j hj)
    beta_reduce
    rw [e]
    show _ = Option.map
        (fun d =>
          glue R Q (ρ.slot j.1) (Ts j)
            ((E0.prod Ej).ans ((R.seq Q.ior).given (ρ.slot j.1) (Ts j)) (y0, (as j).2.1))
            (R.view (firstT R Q.ior (ρ.slot j.1) (Ts j)) (r j).1) d)
        (ite (Rho.snd (s := R.shape) (ρ.slot j.1) ∈ HQ.withheld) none (some _))
    by_cases hq : Rho.snd (s := R.shape) (ρ.slot j.1) ∈ HQ.withheld
    · refine (if_pos ((mem_withheld HR HQ _).mpr (Or.inr hq))).trans ?_
      rw [if_pos hq]
      rfl
    · refine (if_neg fun h => ((mem_withheld HR HQ _).mp h).elim (hnw j hj) hq).trans ?_
      rw [if_neg hq]
      refine congrArg some ?_
      refine (congrArg _
        (run_one HR HQ w0 (as j).1 (as j).2.2 c.1 d.1 (c.2 j.1) (d.2 j.1) (ρ.slot j.1))).trans ?_
      have e2 : ((HR.one w0 (as j).1 (as j).2.2 (c.1, c.2 j.1)).run (Rho.fst (ρ.slot j.1))).2.1 =
          w0' := hw0 j
      rw [e2]
      exact dviewT_app R Q (y0, (as j).2.1) _ (ρ.slot j.1) (Ts j) _ _ (Strat.rho_run _ _)
        (Strat.rho_run _ _) _ fun p hp => (E0.prod Ej).ans_of_mem _ hp
  · refine Eq.trans ?_ (dif_neg hj).symm
    exact if_pos
      ((mem_withheld HR HQ _).mpr (Or.inl (not_not.mp fun h => hj ((mem_alive j).mpr h))))

end Exact
end BatchSeqZk

theorem exact_seqB : Spec.exact_seqB := by
  intro X X' E0 Ej E0' Ej' R A Q W0 Wj W0' Wj' HR HQ Ri Ro N bR bQ f hL hA hf hER hEQ
  obtain ⟨SR, hSR⟩ := hER
  obtain ⟨SQ, hSQ⟩ := hEQ
  exact ⟨_, BatchSeqZk.exactWith_seqB HR HQ f hL hA hf SR hSR SQ hSQ⟩

end Iop
