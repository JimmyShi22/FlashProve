-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/OnlineHon.lean: the honest side of "an IOR F in every slot, then a batch IOP Q": the
statements of Ior/Batch.lean on it, proved.

In standard terms: the honest prover's side of a composition: an interactive oracle reduction run
for each instance of a batch, then an interactive oracle proof for the whole batch.

A slot is one of the N places of a batch, each with one instance or empty. The composition is
`online F Q`, its honest side `onlineHonest` (Ior/Batch.lean).

Main names, each under the hypotheses of its statement (Ior/Batch.lean):
  `acc_online`: completeness for each slot: outside the withheld set the verifier of the
    composition accepts (`BatchHonestProver.Acc`, Iop/Batch.lean); in the proof, outside that set, F's
    verifier outputs what F's prover hands on and that statement is in Q's relation (the premise
    `HF.Acc RA RB`), and Q's verifier accepts (the premise `HQ.Acc RB`).
  `exact_online`: honest-verifier exact zero knowledge for sets of slots with further reads: for
    each slot j of J a set T_j of further positions in the oracles of its local transcript (F's
    and Q's), within the composed budget (`budOnline`) (`BIOP.ExactT`, Ior/Batch.lean).
  `hvzk_of_exactT`: for any batch IOP over one shared oracle: the exact form with further reads
    gives the form that the compiler takes (no further reads), with error |J| z.
  `hvzk_online`: the two together: honest-verifier zero knowledge of the composition in the
    compiler's form (`BatchHonestProver.HVZK`, Iop/Batch.lean).
  With the simulators named (stated in this file): `OnlineHon.exactTWith`, `OnlineHon.hvzk_bound`.

The simulator for a set J of slots (`OnlineHon.sim`) is named. It is given J, the instances, the
verifier messages and the further positions T_j of the slots of J, and the symbols of the shared
oracle at the positions `given` of the slots of J.
 1. For each slot j of J, independently: F's simulator at (x_j, the first part of ρ_j, the
    positions `furth`: the part of T_j in F's shape, and the sources, in F's oracles, of all that
    Q's simulator will be given at the second part of ρ_j and the part of T_j in Q's shape). It is
    given no symbol of the shared oracle.
 2. J' (`alive`): the slots of J whose first part of ρ_j is outside F's public bad set. For j in
    J', from the simulated view: the explicit part that F's verifier outputs, and the symbols of
    the slot's own oracles that Q's simulator is given (`info`; under `hE`, `hsE` of `info_view`
    (Ior/OnlineHonView.lean), by F's locality both are functions of x_j, ρ_j, T_j and what the
    view shows); the symbols of the shared oracle at such positions are among the given ones
    (under `hsl`: `mem_given_seq`, Ior/OnlineHonView.lean).
 3. Q's simulator once, for the set J', on these data, with the parts of the T_j in Q's shape.
 4. For each slot of J: the notice (`none`: `BIOP.outputT`, Ior/Batch.lean; the word:
    `IOR.Honest.output`, Ior/Honest.lean) if j is not in J', or Q's simulator shows the notice, or
    `info` returns `none` at some slot of J' (then at every slot of J: `kern`); else the two views
    glued (`glue`; of F's view only what the composition shows is kept) (exactly: `post`, `kern`).

Why Q's exact simulation for sets of non-empty slots is enough, though the honest prover of a slot
whose first part is withheld plays on in Q with a statement that need not be valid: the output of
Q's honest side for J' reads the vector of instances at J' only (no slot's message depends on
another slot: a fact about the types of the honest side), so Q's property is used at the vector
that is empty outside J'. This is why the composed budget asks Q's budget at every subset of J.

Limits:
Where the simulation is exact: at every ρ at which no slot of J has the first part of ρ_j in F's
secret-dependent withheld set Hid.
This file says nothing on running times; `info` takes a transcript that fits the view by choice.
It says nothing on soundness.
F is a preamble that copies the shared oracle, reads nothing of it and ties nothing to it
(hypotheses of `exact_online`).

Terms: lean/GLOSSARY.md.
-/
import Ior.OnlineHonKit
import Ior.OnlineHonView
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob Prob.Indep
open scoped ENNReal

/-! ## 1. Completeness -/

theorem acc_online : Spec.acc_online := by
  intro X Xl Wt WA W0 Wj E0 Ej F Q HF HQ ext sh inp valid RA RB hF hQ hv hsh w x c ρ hval hρ
  obtain ⟨c0, c1, c2⟩ := c
  have hρ' := fun h => hρ ((OnlineHon.mem_withheld F Q HF HQ ext sh inp w x ρ).mpr h)
  have h1 : Rho.fst (s := F.shape) (t := Q.ior.shape) ρ ∉ HF.withheld (inp w x) x := fun h =>
    hρ' (Or.inl h)
  have h2 : Rho.snd (s := F.shape) (t := Q.ior.shape) ρ ∉ HQ.withheld := fun h => hρ' (Or.inr h)
  obtain ⟨ho, hR⟩ := hF x (ext w) (inp w x) c1 _ (hv w x hval) h1
  have h3 := hQ _ _ _ (c0, c2) _ hR h2
  rw [hsh w x c1 _ hval h1] at h3
  show ((F.seq Q.ior).out x (ext w)
      (Strat.run ((onlineHonest F Q HF HQ ext sh inp).one.strat w x (c0, (c1, c2))) ρ).1).isSome =
    true
  rw [OnlineHon.run_one]
  show ((F.out x (ext w) (Tr.fst (Tr.app _ _))).bind fun x₂ =>
      Q.ior.out x₂ (F.imp (ext w) (Tr.fst (Tr.app _ _)))
        (Tr.snd (s := F.shape) (Tr.app _ _))).isSome = true
  rw [Tr.fst_app, Tr.snd_app, ho]
  exact h3

/-! ## 2. The simulator -/

namespace OnlineHon

open Classical in
/-- A family of values, if all are there. -/
def seqOpt {ι α : Type} (f : ι → Option α) : Option (ι → α) :=
  if h : ∀ i, (f i).isSome = true then some fun i => (f i).get (h i) else none

theorem seqOpt_some {ι α : Type} (f : ι → Option α) (g : ι → α) (h : ∀ i, f i = some (g i)) :
    seqOpt f = some g := by
  obtain rfl : f = fun i => some (g i) := funext h
  exact dif_pos fun _ => rfl

section Sim
variable {X Xl : Type} {E0 Ej : ExtSpec} (F : IOR X E0 Xl (E0.prod Ej)) (Q : BIOP Xl (E0.prod Ej))
  (Bad : Set (Rho F.shape)) {N : ℕ}

open Classical in
/-- The slots of J whose first part of ρ_j is outside the public bad set. -/
def alive (J : Finset (Fin N)) (ρs : J → Rho (F.shape ++ Q.ior.shape)) :
    Finset (Fin N) :=
  J.filter fun j => ∃ h : j ∈ J, Rho.fst (ρs ⟨j, h⟩) ∉ Bad

variable {F Q Bad}

theorem alive_sub {J : Finset (Fin N)} {ρs : J → Rho (F.shape ++ Q.ior.shape)}
    {j : Fin N} (h : j ∈ alive F Q Bad J ρs) : j ∈ J := by
  classical
  exact (Finset.mem_filter.mp h).1

theorem mem_alive {J : Finset (Fin N)} {ρs : J → Rho (F.shape ++ Q.ior.shape)} (j : J) :
    j.1 ∈ alive F Q Bad J ρs ↔ Rho.fst (ρs j) ∉ Bad := by
  classical
  exact Finset.mem_filter.trans ⟨fun h => h.2.2, fun h => ⟨j.2, j.2, h⟩⟩

/-- A slot of J' as a slot of J. -/
def up {J : Finset (Fin N)} {ρs : J → Rho (F.shape ++ Q.ior.shape)} (j : alive F Q Bad J ρs) : J :=
  ⟨j.1, alive_sub j.2⟩

variable (F Q Bad)

open Classical in
/-- Step 4: the notice, or the two views glued. -/
def post (J : Finset (Fin N)) (ρs : J → Rho (F.shape ++ Q.ior.shape))
    (Ts : J → Finset (OPos (F.shape ++ Q.ior.shape))) (ans : E0.Pos → Option E0.Sym)
    (vs : J → Option F.View) (ds : alive F Q Bad J ρs → Option (DView Q.ior.toInteractiveOracleProof)) :
    J → Option (DView (F.seq Q.ior).toInteractiveOracleProof) :=
  fun j =>
    if h : j.1 ∈ alive F Q Bad J ρs then
      (vs j).bind fun v => (ds ⟨j.1, h⟩).map fun d => glue F Q (ρs j) (Ts j) ans v d else none

/-- Steps 2 to 4, given the simulated views of F. -/
def kern (SQ : Q.SimB N) (J : Finset (Fin N)) (xs : J → X)
    (ρs : J → Rho (F.shape ++ Q.ior.shape)) (Ts : J → Finset (OPos (F.shape ++ Q.ior.shape)))
    (ans : E0.Pos → Option E0.Sym) (vs : J → Option F.View) :
    PMF (J → Option (DView (F.seq Q.ior).toInteractiveOracleProof)) :=
  match seqOpt fun j : alive F Q Bad J ρs =>
      info F Q (xs (up j)) (ρs (up j)) (Ts (up j)) ans (vs (up j)) with
  | none => PMF.pure fun _ => none
  | some g =>
    (SQ (alive F Q Bad J ρs) (fun j => (g j).1) (fun j => Rho.snd (s := F.shape) (ρs (up j)))
        (fun j => OPos.partR (s := F.shape) (Ts (up j))) fun j => (g j).2).map
      (post F Q Bad J ρs Ts ans vs)

/-- The simulator of the composition. -/
def sim (SF : IOR.Honest.Sim F) (SQ : Q.SimB N) :
    (online F Q).SimT N := fun J xs ρs Ts ans =>
  (pis fun j : J =>
      SF (xs j) (Rho.fst (s := F.shape) (t := Q.ior.shape) (ρs j))
        (furth F Q (ρs j) (Ts j)) fun _ => none).bind
    (kern F Q Bad SQ J xs ρs Ts ans)

end Sim

/-! ## 3. The outputs for J, when all slots of J are non-empty -/

open Classical in
theorem outputT_eq {X Wt : Type} {E : ExtSpec} (P : BIOP X E) (H : BatchHonestProver P.toBatch Wt) {N : ℕ}
    (w : Wt) (x : Fin N → Option X) (ρ : BRho N P.ior.shape P.ann) (J : Finset (Fin N))
    (Ts : J → Finset (OPos P.ior.shape)) (xs : J → X) (hxs : ∀ j : J, x j = some (xs j)) :
    P.outputT H w x ρ J Ts = (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j : J =>
      if ρ.slot j.1 ∈ H.one.withheld w (xs j) then none
      else
          some (P.ior.dviewT (Ts j) (H.ext w)
                ((H.one.strat w (xs j) (c.1, c.2 j)).run (ρ.slot j.1)).1) := by
  unfold BIOP.outputT
  refine congrArg (fun φ => PMF.map φ _) (funext fun c => funext fun j => ?_)
  rw [hxs j]

open Classical in
theorem outputQ_eq {X W0 Wj : Type} {E0 Ej : ExtSpec} {Q : BIOP X (E0.prod Ej)} (H : Q.Honest W0 Wj)
    {N : ℕ} (w0 : W0) (y0 : E0.Str) (a : Fin N → Option (X × Ej.Str × Wj))
    (ρ : BRho N Q.ior.shape Q.ann) (J : Finset (Fin N)) (Ts : J → Finset (OPos Q.ior.shape))
    (as : J → X × Ej.Str × Wj) (has : ∀ j : J, a j = some (as j)) :
    H.output w0 y0 a ρ J Ts = (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j : J =>
      if ρ.slot j.1 ∈ H.withheld then none
      else
          some (Q.ior.dviewT (Ts j) (y0, (as j).2.1)
                ((H.one w0 (as j).1 (as j).2.2 (c.1, c.2 j)).run (ρ.slot j.1)).1) := by
  unfold BIOP.Honest.output
  refine congrArg (fun φ => PMF.map φ _) (funext fun c => funext fun j => ?_)
  rw [has j]

/-! ## 4. Under the hypotheses below, the simulation is exact -/

section Exact
variable {X Xl Wt WA W0 Wj : Type} {E0 Ej : ExtSpec} (F : IOR X E0 Xl (E0.prod Ej))
  (Q : BIOP Xl (E0.prod Ej)) (HF : F.Honest WA (W0 × Wj)) (HQ : Q.Honest W0 Wj) (ext : Wt → E0.Str)
  (sh : Wt → W0) (inp : Wt → X → WA)

theorem mem_hid (w : Wt) (x : X) (ρ : Rho (F.shape ++ Q.ior.shape)) :
    ρ ∈ (onlineHonest F Q HF HQ ext sh inp).one.Hid w x ↔ Rho.fst ρ ∈ HF.Hid (inp w x) x := by
  show RhoLo.front F.shape (A' := Q.ann)
        (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann) ρ) ∈
      HF.Hid (inp w x) x ↔
    _
  rw [RhoLo.front_lo]

open Classical in
theorem sim_exact {valid : Wt → X → Prop} {RA : X → E0.Str → WA → Prop}
    {RB : Xl → (E0.prod Ej).Str → W0 × Wj → Prop} {bF : Rho F.shape → Finset (OPos F.shape) → Prop}
    {N : ℕ} {bQ : BudB Q.ior.shape N} (hL : F.IsLocal) (hF : HF.Acc RA RB) (SF : IOR.Honest.Sim F)
    (hSF : HF.ExactWith RA bF SF) (SQ : Q.SimB N) (hSQ : HQ.ExactWith N RB bQ SQ)
    (hv : ∀ w x, valid w x → RA x (ext w) (inp w x))
    (hsh : ∀ w x c ρ,
      valid w x → ρ ∉ HF.withheld (inp w x) x → ((HF.strat (inp w x) x c).run ρ).2.2.1 = sh w)
    (himp : ∀ y τ, (F.imp y τ).1 = y)
    (hsl : ∀ ρ p, F.srcE ρ (Sum.inl p) = {p} ∧ F.srcO ρ (Sum.inl p) = ∅)
    (hsE : ∀ ρ q, F.srcE ρ (Sum.inr q) = ∅) (hE : ∀ ρ, F.extReads ρ = ∅)
    (htie : ∀ ρ p, F.tie ρ p = ∅) (w : Wt) (x : Fin N → Option X) (J : Finset (Fin N)) (xs : J → X)
    (hxs : ∀ j : J, x j = some (xs j)) (hval : ∀ j : J, valid w (xs j))
    (ρ : BRho N (F.shape ++ Q.ior.shape) (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann))
    (hρ : ∀ j : J, Rho.fst (ρ.slot j.1) ∉ HF.Hid (inp w (xs j)) (xs j))
    (Ts : J → Finset (OPos (F.shape ++ Q.ior.shape)))
    (hbud : budOnline F Q bF bQ J (fun j => ρ.slot j.1) Ts) :
    (online F Q).outputT (onlineHonest F Q HF HQ ext sh inp) w x ρ J Ts =
      sim F Q HF.Bad SF SQ J xs (fun j => ρ.slot j.1) Ts
        ((online F Q).ansJ J (fun j => ρ.slot j.1) Ts (ext w)) := by
  generalize hans' : (online F Q).ansJ J (fun j => ρ.slot j.1) Ts (ext w) = ans
  have hans : ∀ (j : J) p, p ∈ (F.seq Q.ior).given (ρ.slot j.1) (Ts j) →
      ans p = some (E0.rd (ext w) p) := fun j p hp => by
    rw [← hans']
    exact if_pos ⟨j, hp⟩
  clear hans'
  -- what F's run in slot j shows
  let hvw : J → HF.Coin → Option F.View := fun j c =>
    if Rho.fst (ρ.slot j.1) ∈ HF.withheld (inp w (xs j)) (xs j) then none
    else
      some (F.view (furth F Q (ρ.slot j.1) (Ts j))
          ((HF.strat (inp w (xs j)) (xs j) c).run (Rho.fst (ρ.slot j.1))).1)
  have hlaw : ∀ j : J,
      SF (xs j) (Rho.fst (ρ.slot j.1)) (furth F Q (ρ.slot j.1) (Ts j)) (fun _ => none) =
        (unif HF.Coin).map (hvw j) := by
    intro j
    have hg : F.given (Rho.fst (ρ.slot j.1)) (furth F Q (ρ.slot j.1) (Ts j)) = ∅ := by
      unfold IOR.given
      rw [hE, Finset.empty_union]
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp hp
      rw [htie] at hq
      exact Finset.notMem_empty _ hq
    have h := hSF (xs j) (ext w) (inp w (xs j)) (hv w _ (hval j)) _ (hρ j) _ (hbud.1 j)
    have hn : E0.ans (F.given (Rho.fst (ρ.slot j.1)) (furth F Q (ρ.slot j.1) (Ts j))) (ext w) =
        fun _ => none := by
      rw [hg]
      exact funext fun p => if_neg (Finset.notMem_empty p)
    rw [← hn]
    refine h.symm.trans ?_
    unfold IOR.Honest.output
    by_cases hw : Rho.fst (ρ.slot j.1) ∈ HF.withheld (inp w (xs j)) (xs j)
    · rw [if_pos hw]
      have : hvw j = fun _ => none := funext fun c => if_pos hw
      rw [this]
      exact (PMF.map_const _ _).symm
    · rw [if_neg hw]
      exact congrArg (fun φ => PMF.map φ _) (funext fun c => (if_neg hw).symm)
  unfold sim
  rw [funext hlaw]
  refine (outputT_eq (online F Q) (onlineHonest F Q HF HQ ext sh inp) w x ρ J Ts xs hxs).trans ?_
  refine law_split J hvw _ _ fun c1 => ?_
  -- the coins of F are fixed
  let r : J → Tr F.shape × Xl × W0 × Wj := fun j =>
    (HF.strat (inp w (xs j)) (xs j) (c1 j.1)).run (Rho.fst (ρ.slot j.1))
  let A : J → Xl × Ej.Str × Wj := fun j => ((r j).2.1, (F.imp (ext w) (r j).1).2, (r j).2.2.2)
  have hnw : ∀ j : J, j.1 ∈ alive F Q HF.Bad J (fun j => ρ.slot j.1) →
      Rho.fst (ρ.slot j.1) ∉ HF.withheld (inp w (xs j)) (xs j) :=
    fun j hj h => h.elim ((mem_alive j).mp hj) (hρ j)
  have hseq : (seqOpt fun j : alive F Q HF.Bad J (fun j => ρ.slot j.1) =>
        info F Q (xs (up j)) (ρ.slot (up j).1) (Ts (up j)) ans (hvw (up j) (c1 (up j).1))) =
      some fun j =>
        ((A (up j)).1,
          (E0.prod Ej).ans
            (Q.ior.given (Rho.snd (s := F.shape) (ρ.slot (up j).1))
              (OPos.partR (s := F.shape) (Ts (up j))))
            (ext w, (A (up j)).2.1)) := by
    refine seqOpt_some _ _ fun j => ?_
    have e : hvw (up j) (c1 (up j).1) =
        some (F.view (furth F Q (ρ.slot (up j).1) (Ts (up j))) (r (up j)).1) :=
      if_neg (hnw (up j) j.2)
    rw [e]
    exact info_view F Q hL hE hsE hsl _ _ _ _ _ _ (Strat.rho_run _ _)
      (hF _ _ _ (c1 (up j).1) _ (hv w _ (hval (up j))) (hnw (up j) j.2)).1 ans (hans (up j))
  unfold kern
  rw [hseq]
  let a : Fin N → Option (Xl × Ej.Str × Wj) := fun j =>
    if h : j ∈ alive F Q HF.Bad J (fun j => ρ.slot j.1) then some (A ⟨j, alive_sub h⟩) else none
  have hslot : (fun j : alive F Q HF.Bad J (fun j => ρ.slot j.1) => (backB F.shape ρ).slot j.1) =
      fun j => Rho.snd (s := F.shape) (ρ.slot (up j).1) :=
    funext fun j => slot_backB j.1 F.shape ρ
  have hQ := hSQ (sh w) (ext w) a (fun j aj h => by
      by_cases hj : j ∈ alive F Q HF.Bad J (fun j => ρ.slot j.1)
      · have h' : some (A ⟨j, alive_sub hj⟩) = some aj := (dif_pos hj).symm.trans h
        obtain rfl := Option.some.inj h'
        have h2 :=
          (hF _ (ext w) _ (c1 j) _ (hv w _ (hval ⟨j, alive_sub hj⟩)) (hnw ⟨j, alive_sub hj⟩ hj)).2
        have e1 : F.imp (ext w) (r ⟨j, alive_sub hj⟩).1 =
            (ext w, (F.imp (ext w) (r ⟨j, alive_sub hj⟩).1).2) :=
          Prod.ext (himp _ _) rfl
        have e2 : (r ⟨j, alive_sub hj⟩).2.2 = (sh w, (r ⟨j, alive_sub hj⟩).2.2.2) :=
          Prod.ext (hsh w _ (c1 j) _ (hval ⟨j, alive_sub hj⟩) (hnw ⟨j, alive_sub hj⟩ hj)) rfl
        have h3 : RB (r ⟨j, alive_sub hj⟩).2.1
            (F.imp (ext w) (r ⟨j, alive_sub hj⟩).1) (r ⟨j, alive_sub hj⟩).2.2 := h2
        rw [e1, e2] at h3
        exact h3
      · have h' : none = some aj := (dif_neg hj).symm.trans h
        cases h')
    (alive F Q HF.Bad J (fun j => ρ.slot j.1)) (fun j => A (up j)) (fun j => dif_pos j.2)
    (backB F.shape ρ) (fun j => OPos.partR (s := F.shape) (Ts (up j))) (by
      rw [hslot]
      exact hbud.2 _ fun j hj => alive_sub hj)
  rw [outputQ_eq HQ (sh w) (ext w) a (backB F.shape ρ) _ _
      (fun j => A (up j)) (fun j => dif_pos j.2)] at hQ
  simp only [slot_backB] at hQ
  show _ = PMF.map _
      (SQ _ (fun j => (A (up j)).1) (fun j => Rho.snd (s := F.shape) (ρ.slot (up j).1))
        (fun j => OPos.partR (s := F.shape) (Ts (up j))) fun j =>
          (E0.prod Ej).ans
            (Q.ior.given (Rho.snd (s := F.shape) (ρ.slot (up j).1))
              (OPos.partR (s := F.shape) (Ts (up j))))
            (ext w, (A (up j)).2.1))
  refine Eq.trans ?_ (congrArg (PMF.map _) hQ)
  rw [PMF.map_comp]
  refine congrArg (fun φ => PMF.map φ _) (funext fun c' => funext fun j => ?_)
  by_cases hj : j.1 ∈ alive F Q HF.Bad J (fun j => ρ.slot j.1)
  · refine Eq.trans ?_ (dif_pos hj).symm
    have e : hvw j (c1 j.1) = some (F.view (furth F Q (ρ.slot j.1) (Ts j)) (r j).1) :=
      if_neg (hnw j hj)
    beta_reduce
    rw [e]
    show _ = Option.map
        (fun d =>
          glue F Q (ρ.slot j.1) (Ts j) ans (F.view (furth F Q (ρ.slot j.1) (Ts j)) (r j).1) d)
        (ite (Rho.snd (s := F.shape) (ρ.slot j.1) ∈ HQ.withheld) none (some _))
    by_cases hq : Rho.snd (s := F.shape) (ρ.slot j.1) ∈ HQ.withheld
    · refine (if_pos ((mem_withheld F Q HF HQ ext sh inp w (xs j) _).mpr (Or.inr hq))).trans ?_
      rw [if_pos hq]
      rfl
    · refine (if_neg fun h =>
        ((mem_withheld F Q HF HQ ext sh inp w (xs j) _).mp h).elim (hnw j hj) hq).trans ?_
      rw [if_neg hq]
      refine congrArg some ?_
      refine (congrArg _
        (run_one F Q HF HQ ext sh inp w (xs j) c'.1 (c1 j.1) (c'.2 j.1) (ρ.slot j.1))).trans ?_
      exact dviewT_app F Q (ext w) _ (ρ.slot j.1) (Ts j) _ _ (Strat.rho_run _ _)
        (Strat.rho_run _ _) ans (hans j)
  · refine Eq.trans ?_ (dif_neg hj).symm
    exact if_pos
      ((mem_withheld F Q HF HQ ext sh inp w (xs j) _).mpr
        (Or.inl (Or.inl (not_not.mp fun h => hj ((mem_alive j).mpr h)))))

/-- Under the hypotheses below: the named simulator is exact, at the composed budget. -/
theorem exactTWith {valid : Wt → X → Prop} {RA : X → E0.Str → WA → Prop}
    {RB : Xl → (E0.prod Ej).Str → W0 × Wj → Prop} {bF : Rho F.shape → Finset (OPos F.shape) → Prop}
    {N : ℕ} {bQ : BudB Q.ior.shape N} (hL : F.IsLocal) (hF : HF.Acc RA RB) (SF : IOR.Honest.Sim F)
    (hSF : HF.ExactWith RA bF SF) (SQ : Q.SimB N) (hSQ : HQ.ExactWith N RB bQ SQ)
    (hv : ∀ w x, valid w x → RA x (ext w) (inp w x))
    (hsh : ∀ w x c ρ,
      valid w x → ρ ∉ HF.withheld (inp w x) x → ((HF.strat (inp w x) x c).run ρ).2.2.1 = sh w)
    (himp : ∀ y τ, (F.imp y τ).1 = y)
    (hsl : ∀ ρ p, F.srcE ρ (Sum.inl p) = {p} ∧ F.srcO ρ (Sum.inl p) = ∅)
    (hsE : ∀ ρ q, F.srcE ρ (Sum.inr q) = ∅)
    (hE : ∀ ρ, F.extReads ρ = ∅) (htie : ∀ ρ p, F.tie ρ p = ∅) :
    (online F Q).ExactTWith (onlineHonest F Q HF HQ ext sh inp) N valid
      (budOnline F Q bF bQ) (sim F Q HF.Bad SF SQ) :=
  fun w x hval J xs hxs ρ hρ Ts hbud =>
    sim_exact F Q HF HQ ext sh inp hL hF SF hSF SQ hSQ hv hsh himp hsl hsE hE htie w x J xs hxs
      (fun j => hval j (xs j) (hxs j)) ρ
      (fun j h => hρ j ((mem_hid F Q HF HQ ext sh inp w (xs j) _).mpr h)) Ts hbud

end Exact

/-! ## 5. From the exact form with further reads to the compiler's form -/

section ToHvzk
variable {X Wt : Type} {E : ExtSpec} (Q : BIOP X E) (H : BatchHonestProver Q.toBatch Wt)

open Classical in
theorem given_empty (ht : Q.ior.Tied) (ρ : Rho Q.ior.shape) :
    Q.ior.given ρ ∅ = Q.ior.extReads ρ := by
  unfold IOR.given
  rw [Finset.union_empty]
  exact Finset.union_eq_left.2 (Finset.biUnion_subset.2 (ht ρ))

open Classical in
theorem dviewT_empty (ht : Q.ior.Tied) (x : X) (y : E.Str) (τ : Tr Q.ior.shape) :
    Q.ior.dviewT ∅ y τ = Q.ior.toInteractiveOracleProof.dview x y τ := by
  refine dview_ext rfl ?_ (funext fun p => ?_)
  · show E.ans (Q.ior.given τ.rho ∅) y = _
    rw [given_empty Q ht]
    rfl
  · by_cases h : p ∈ Q.ior.reads τ.rho ∨ Q.ior.blinded p = false
    · exact (if_pos (h.elim Or.inl fun h => Or.inr (Or.inr h))).trans (if_pos h).symm
    · exact (if_neg fun h' =>
          h (h'.elim Or.inl fun h' =>
              h'.elim (fun h' => absurd h' (Finset.notMem_empty p)) Or.inr)).trans (if_neg h).symm

open Classical in
theorem outputT_empty (ht : Q.ior.Tied) {N : ℕ} (w : Wt) (x : Fin N → Option X)
    (ρ : BRho N Q.ior.shape Q.ann) (J : Finset (Fin N)) :
    Q.outputT H w x ρ J (fun _ => ∅) = H.output w x ρ J := by
  unfold BIOP.outputT BatchHonestProver.output
  refine congrArg (fun φ => PMF.map φ _) (funext fun c => funext fun j => ?_)
  cases x j with
  | none => rfl
  | some xj =>
    exact congrArg (fun z => if ρ.slot j.1 ∈ H.one.withheld w xj then none else some z)
      (dviewT_empty Q ht xj _ _)

open Classical in
theorem ansJ_empty (ht : Q.ior.Tied) {N : ℕ} (J : Finset (Fin N)) (xs : J → X)
    (ρs : J → Rho Q.ior.shape) (y : E.Str) :
    Q.ansJ J ρs (fun _ => ∅) y = Q.toBatch.extAnsJ J xs ρs y := by
  funext p
  unfold BIOP.ansJ BatchInteractiveOracleProof.extAnsJ
  simp only [given_empty Q ht]
  rfl

open Classical in
/-- Under the hypotheses below: the compiler's form, with the simulator named: the simulator with
no further reads. -/
theorem hvzk_bound {N : ℕ} {valid : Wt → X → Prop} {bud : BudB Q.ior.shape N} {z : ℝ≥0∞}
    (Sim : Q.SimT N) (hS : Q.ExactTWith H N valid bud Sim) (hb : ∀ J ρs, bud J ρs fun _ => ∅)
    (ht : Q.ior.Tied) (hz : ∀ w x, valid w x → prRho (H.one.Hid w x) ≤ z) (w : Wt)
    (x : Fin N → Option X) (hval : ∀ j xj, x j = some xj → valid w xj) (J : Finset (Fin N))
    (xs : J → X) (hxs : ∀ j : J, x j = some (xs j)) :
    prBRho {ρ | H.output w x ρ J ≠
          Sim J xs (fun j => ρ.slot j.1) (fun _ => ∅)
            (Q.toBatch.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w))} ≤ J.card * z := by
  have h := pr_exists_le_mul (ι := J) (unif (BRho N Q.ior.shape Q.ann))
    (fun j ρ => ρ.slot j.1 ∈ H.one.Hid w (xs j)) z (fun j =>
      (le_of_eq (prBRho_slot j.1 (H.one.Hid w (xs j)))).trans (hz _ _ (hval j (xs j) (hxs j))))
  rw [Fintype.card_coe] at h
  refine le_trans (pr_mono _ fun ρ hρ => ?_) h
  by_contra hn
  refine hρ ?_
  rw [← outputT_empty Q H ht, ← ansJ_empty Q ht]
  exact hS w x hval J xs hxs ρ (fun j hj => hn ⟨j, hj⟩) _ (hb _ _)

end ToHvzk

end OnlineHon

theorem exact_online : Spec.exact_online := by
  intro X Xl Wt WA W0 Wj E0 Ej F Q HF HQ ext sh inp valid RA RB bF N bQ hL hF hEF hEQ hv
    hsh himp hsl hsE hE htie
  obtain ⟨SF, hSF⟩ := hEF
  obtain ⟨SQ, hSQ⟩ := hEQ
  exact ⟨OnlineHon.sim F Q HF.Bad SF SQ,
    OnlineHon.exactTWith F Q HF HQ ext sh inp hL hF SF hSF SQ hSQ hv hsh himp hsl hsE hE htie⟩

theorem hvzk_of_exactT : Spec.hvzk_of_exactT := by
  intro X Wt E Q H N valid bud z hS hb ht hz
  obtain ⟨Sim, hS⟩ := hS
  exact ⟨fun J xs ρs ans => Sim J xs ρs (fun _ => ∅) ans, OnlineHon.hvzk_bound Q H Sim hS hb ht hz⟩

/-! ## 6. Honest-verifier zero knowledge of the composition in the compiler's form -/

namespace OnlineHon
section Cor
variable {X Xl : Type} {E0 Ej : ExtSpec} (F : IOR X E0 Xl (E0.prod Ej)) (Q : BIOP Xl (E0.prod Ej))

open Classical in
/-- The verifier of the composition reads all that is tied to its positions, if Q's does and F
ties nothing. -/
theorem tied_online (htie : ∀ ρ p, F.tie ρ p = ∅) (ht : Q.ior.Tied) :
    (F.seq Q.ior).Tied := by
  intro ρ p hp e hpe
  have hsplit := OPos.elim_split (s := F.shape) p
  cases hs : OPos.split (s := F.shape) p with
  | inl q =>
      rw [hs] at hsplit
      obtain rfl : OPos.left q = p := hsplit
      rw [tie_left, htie] at hpe
      exact absurd hpe (Finset.notMem_empty e)
  | inr q =>
      rw [hs] at hsplit
      obtain rfl : OPos.right (s := F.shape) q = p := hsplit
      rw [tie_right] at hpe
      rcases Finset.mem_union.mp hpe with h | h
      · obtain ⟨u, hu, hue⟩ := Finset.mem_biUnion.mp h
        show e ∈ F.extReads (Rho.fst ρ) ∪
            (Q.ior.extReads (Rho.snd (s := F.shape) ρ)).biUnion (F.srcE (Rho.fst ρ))
        exact Finset.mem_union_right
          _ (Finset.mem_biUnion.mpr ⟨u, ht _ q ((mem_reads_right F Q ρ q).mp hp) hu, hue⟩)
      · obtain ⟨u, _, hue⟩ := Finset.mem_biUnion.mp h
        rw [htie] at hue
        exact absurd hue (Finset.notMem_empty e)

open Classical in
/-- Under `hbud`, `hb`, `ht`: the composed budget bears "no further reads". -/
theorem budOnline_empty {N : ℕ} {bF : Rho F.shape → Finset (OPos F.shape) → Prop}
    {bQ : BudB Q.ior.shape N} (hbud : ∀ ρ₁ ρ₂, bF ρ₁ ((Q.ior.extReads ρ₂).biUnion (F.srcO ρ₁)))
    (hb : ∀ J ρs, bQ J ρs fun _ => ∅) (ht : Q.ior.Tied) (J : Finset (Fin N))
    (ρs : J → Rho (F.shape ++ Q.ior.shape)) :
    budOnline F Q bF bQ J ρs fun _ => ∅ := by
  have eL : OPos.partL (s := F.shape) (t := Q.ior.shape) ∅ = ∅ := Finset.preimage_empty
  have eR : OPos.partR (s := F.shape) (t := Q.ior.shape) ∅ = ∅ := Finset.preimage_empty
  refine ⟨fun j => ?_, fun J' h => ?_⟩
  · rw [eL, eR, Finset.empty_union, given_empty Q ht]
    exact hbud _ _
  · simp only [eR]
    exact hb _ _

end Cor
end OnlineHon

theorem hvzk_online : Spec.hvzk_online := by
  intro X Xl Wt WA W0 Wj E0 Ej F Q HF HQ ext sh inp valid RA RB bud N bQ z hL hF hEF hEQ hv hsh himp
    hsl hsE hE htie hbud hb ht hz
  refine hvzk_of_exactT X Wt E0 (online F Q) (onlineHonest F Q HF HQ ext sh inp) N valid
    (budOnline F Q bud bQ) z
    (exact_online X Xl Wt WA W0 Wj E0 Ej F Q HF HQ ext sh inp valid RA RB bud N bQ hL hF hEF hEQ hv
      hsh himp hsl hsE hE htie)
    (OnlineHon.budOnline_empty F Q hbud hb ht)
    (OnlineHon.tied_online F Q htie ht) fun w x hval => ?_
  have e : (onlineHonest F Q HF HQ ext sh inp).one.Hid w x =
      Rho.cylFst Q.ior.shape (HF.Hid (inp w x) x) :=
    Set.ext fun ρ => OnlineHon.mem_hid F Q HF HQ ext sh inp w x ρ
  exact le_trans (le_of_eq ((congrArg prRho e).trans (prRho_cylFst Q.ior.shape _))) (hz w x hval)

end Iop
