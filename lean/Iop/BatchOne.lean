-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchOne.lean: sanity lemmas on the definitions of Iop/Batch.lean. (Words of this library:
lean/GLOSSARY.md.)
 1. If the positions read in the external string Π are a function of the shared challenges
    (`BatchInteractiveOracleProof.ExtShared`), a bound on the positions that one slot's verifier reads is a bound for
    a whole execution (`ReadsAtMost`), whatever N is.
 2. An ordinary IOP, taken as a protocol with slots with local rounds only, at N = 1: `JointLaw`
    (in `BatchInteractiveOracleProof.SndB`, (Snd-B)) is the condition on challenges, law (iv) (`BatchH4.VerLaw`,
    Iop/BatchSound.lean), of a state function, `ReadsAtMost` is the bound on the verifier's
    positions, HVZK for sets of slots (`BatchHonestProver.HVZK`) is HVZK (`Honest.HVZK`), `BatchHonestProver.Acc` is
    `Honest.Acc` ((Acc)).

Notation: `BatchProtocol I X` (Iop/Batch.lean): the five algorithms (I, D, Test, Link, Batch: `encodeIndex`, `decodeIndex`,
`offline`, `link`, `onlineBatch`), with the honest sides of the three protocols (`honestOfflineProver`, `honestLinkProver`, `honestOnlineBatchProver`); `Coin0`,
`Coin : Type`
(fields of `BatchHonestProver`, Iop/Batch.lean): the randomness of the shared part; the randomness of one
slot; `Bad`, `Hid`, `stop0`: fields of `BatchHonestProver` (Iop/Batch.lean): see their docstrings; `z : ℝ≥0∞`:
an argument of `BatchHonestProver.HVZK` (Iop/Batch.lean) and of `Honest.HVZK` (Iop/InteractiveOracleProof.lean).

Limits: this file does not prove that (Snd-B) is round-by-round soundness.
From part 2 on, everything is in the namespace `Iop.BatchOne`, except `BatchHonestProver.ofHonest`.
-/
import Iop.Batch
import Iop.Late

namespace Iop
open Prob
open scoped ENNReal

variable {X : Type} {E : ExtSpec}

/-! ## 1. One slot's reads and all reads -/

/-- All slots see the same shared challenges. -/
theorem BRho.sh_slot {N : ℕ} (j j' : Fin N) :
    ∀ {s : Shape} (A : RoundSplits s) (ρ : BRho N s A), Rho.sh A (ρ.slot j) = Rho.sh A (ρ.slot j')
  | [], _, _ => rfl
  | r :: s, (a, A), (v, ρ) => by
      show (a.kind.shOf (a.kind.slot v j), Rho.sh A (ρ.slot j)) =
        (a.kind.shOf (a.kind.slot v j'), Rho.sh A (ρ.slot j'))
      rw [BRho.sh_slot j j' A ρ]
      congr 1
      obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
      cases k <;> rfl

theorem BatchInteractiveOracleProof.readsAtMost_of_extShared (Q : BatchInteractiveOracleProof X E) (h4 : Q.ExtShared) {q : ℕ}
    (hq : ∀ x ρ, (Q.loc.extReads x ρ).card ≤ q) (N : ℕ) : Q.ReadsAtMost N q := by
  classical
  intro x ρ
  by_cases hne : ∃ j xj, x j = some xj
  · obtain ⟨j, xj, hj⟩ := hne
    refine le_trans (Finset.card_le_card ?_) (hq xj (ρ.slot j))
    intro p hp
    obtain ⟨j', -, hp⟩ := Finset.mem_biUnion.1 hp
    cases hj' : x j' with
    | none => rw [hj'] at hp; simp at hp
    | some xj' =>
      rw [hj'] at hp
      rw [h4 xj xj' (ρ.slot j) (ρ.slot j') (BRho.sh_slot j j' Q.ann ρ)]
      exact hp
  · have : Q.allReads x ρ = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      obtain ⟨j', -, hp⟩ := Finset.mem_biUnion.1 hp
      cases hj' : x j' with
      | none => rw [hj'] at hp; simp at hp
      | some xj' => exact hne ⟨j', xj', hj'⟩
    rw [this]; simp

/-! ## 2. One slot, local rounds only -/

namespace BatchOne

theorem BAnn.allLocal_coherent : ∀ s : Shape, (RoundSplits.allLocal s).Coherent
  | [] => trivial
  | _ :: s =>
    ⟨⟨fun _ _ => rfl, fun _ _ _ _ h => Bool.noConfusion h, fun _ _ _ _ _ => rfl⟩,
      BAnn.allLocal_coherent s⟩

/-- With one slot and local rounds only, the randomness of the batch is the randomness of the
slot. -/
def BRho.ofRho : {s : Shape} → Rho s → BRho 1 s (RoundSplits.allLocal s)
  | [], _ => ()
  | _ :: _, (c, ρ) => ((fun _ => c), BRho.ofRho ρ)

theorem BRho.slot_ofRho : ∀ {s : Shape} (ρ : Rho s), (BRho.ofRho ρ).slot 0 = ρ
  | [], _ => rfl
  | _ :: _, (c, ρ) => by
      show (c, (BRho.ofRho ρ).slot 0) = (c, ρ)
      rw [BRho.slot_ofRho ρ]

theorem BRho.ofRho_slot : ∀ {s : Shape} (ρ : BRho 1 s (RoundSplits.allLocal s)), BRho.ofRho (ρ.slot 0) = ρ
  | [], _ => rfl
  | r :: s, (v, ρ) => by
      have ih : BRho.ofRho (BRho.slot (A := RoundSplits.allLocal s) 0 ρ) = ρ := BRho.ofRho_slot (s := s) ρ
      have hv : (fun _ : Fin 1 => (v : Fin 1 → r.Chal) 0) = v := by
        funext j; rw [Subsingleton.elim j 0]
      exact Prod.ext hv ih

def BRho.equivOne (s : Shape) : BRho 1 s (RoundSplits.allLocal s) ≃ Rho s :=
  ⟨fun ρ => ρ.slot 0, BRho.ofRho, BRho.ofRho_slot, BRho.slot_ofRho⟩

theorem prBRho_one {s : Shape} (T : Set (Rho s)) :
    prBRho {ρ : BRho 1 s (RoundSplits.allLocal s) | ρ.slot 0 ∈ T} = prRho T := by
  unfold prBRho prRho
  rw [← map_unif_equiv (BRho.equivOne s), pr_map]
  rfl

/-- At one slot and local rounds only, `JointLaw` is the condition on challenges, law (iv)
(`BatchH4.VerLaw`, Iop/BatchSound.lean), of a state function: from state 0, at most as many
challenge values as the round's error count lead to state 1. -/
theorem jointLaw_one : ∀ (s : Shape) (ε : Err s) (S : PTr s → Bool),
    JointLaw 1 s (RoundSplits.allLocal s) ε (fun _ => some S) ↔
      ∀ τ : AtV s, S (.atV τ) = false → cnt (fun c : τ.round.Chal => S (τ.snoc c) = true) ≤ τ.err ε
  | [], _, _ => ⟨fun _ τ => τ.elim, fun _ => trivial⟩
  | r :: s, (e, ε), S => by
      have ih := fun (m : r.Msg) (c : r.Chal) => jointLaw_one s ε fun τ => S (PTr.cons m c τ)
      constructor
      · intro h τ
        rcases τ with m | ⟨m, c, τ⟩
        · exact (h () fun _ => m).1 0 S rfl
        · exact (ih m c).1 ((h () fun _ => m).2 fun _ => c) τ
      · intro h m0 m
        refine ⟨?_, fun v => ?_⟩
        · intro j S' hS'
          obtain rfl : S = S' := Option.some.inj hS'
          exact h (Sum.inl (m j))
        · have e1 : (fun j : Fin 1 => (some S).map fun S (τ : PTr s) =>
              S (PTr.cons ((RAnn.allLocal r).join m0 (m j)) ((RAnn.allLocal r).kind.slot v j) τ))
              = fun _ => some fun τ => S (PTr.cons (m 0) (v 0) τ) := by
            funext j; rw [Subsingleton.elim j 0]; rfl
          show JointLaw 1 s (RoundSplits.allLocal s) ε _
          rw [e1]
          exact (ih (m 0) (v 0)).2 fun τ => h (Sum.inr (m 0, v 0, τ))

theorem jointLaw_none (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s), JointLaw N s A ε (fun _ => none)
  | [], _, _ => trivial
  | r :: s, (a, A), (e, ε) => fun m0 m => by
      refine ⟨?_, fun v => jointLaw_none N s A ε⟩
      obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
      cases k
      · show cnt _ ≤ e
        rw [cnt_false]
        · exact Nat.zero_le _
        · rintro c ⟨j, S, hS, -⟩; cases hS
      · intro j S hS; cases hS

theorem readsAtMost_one_iff (Q : InteractiveOracleProof X E) (q : ℕ) :
    (BatchInteractiveOracleProof.ofProto Q).ReadsAtMost 1 q ↔ ∀ x ρ, (Q.extReads x ρ).card ≤ q := by
  classical
  constructor
  · intro h x ρ
    have := h (fun _ => some x) (BRho.ofRho ρ)
    unfold BatchInteractiveOracleProof.allReads at this
    simpa [BRho.slot_ofRho, BatchInteractiveOracleProof.ofProto] using this
  · intro h x ρ
    unfold BatchInteractiveOracleProof.allReads
    cases hx : x 0 with
    | none => simp [hx]
    | some x0 => simpa [hx] using h x0 (ρ.slot 0)

/-! ## 3. The honest prover of an ordinary IOP as the honest prover of a protocol with slots -/

/-- With local rounds only, the local challenges are all challenges. -/
def RhoLo.toRho : {s : Shape} → RhoLo s (RoundSplits.allLocal s) → Rho s
  | [], _ => ()
  | _ :: _, (c, ρ) => (c, RhoLo.toRho ρ)

theorem RhoLo.toRho_lo : ∀ {s : Shape} (ρ : Rho s), RhoLo.toRho (Rho.lo (RoundSplits.allLocal s) ρ) = ρ
  | [], _ => rfl
  | _ :: _, (c, ρ) => by
      show (c, RhoLo.toRho (Rho.lo _ ρ)) = (c, ρ)
      rw [RhoLo.toRho_lo ρ]

/-- The shared component: nothing is sent. -/
def SStrat.triv : (s : Shape) → SStrat s (RoundSplits.allLocal s)
  | [] => ()
  | _ :: s => ((), fun _ => SStrat.triv s)

def LStrat.ofStrat : {s : Shape} → Strat s Unit → LStrat s (RoundSplits.allLocal s)
  | [], _ => ()
  | _ :: _, (m, k) => (m, fun c => LStrat.ofStrat (k c))

theorem SStrat.zip_triv :
    ∀ {s : Shape} (σ : Strat s Unit), (SStrat.triv s).zip (LStrat.ofStrat σ) = σ
  | [], _ => rfl
  | r :: s, (m, k) => by
      show (m, fun c => (SStrat.triv s).zip (LStrat.ofStrat (k c))) =
        ((m, k) : r.Msg × (r.Chal → Strat s Unit))
      congr 1
      funext c
      exact SStrat.zip_triv (k c)

variable {Wt : Type}

abbrev _root_.Iop.BatchHonestProver.ofHonest {Q : InteractiveOracleProof X E} (H : Honest Q Wt) :
    BatchHonestProver (BatchInteractiveOracleProof.ofProto Q) Wt where
  Coin0 := Unit
  Coin := H.Coin
  ext := H.ext
  strat0 := fun _ _ => SStrat.triv Q.shape
  strat := fun w _ x c => LStrat.ofStrat (H.strat w x c)
  Bad := {ρ | RhoLo.toRho ρ ∈ H.Bad}
  Hid := fun w x => {ρ | RhoLo.toRho ρ ∈ H.Hid w x}
  stop0 := fun _ => false

section One
variable {Q : InteractiveOracleProof X E} (H : Honest Q Wt)

theorem ofHonest_strat (w : Wt) (x : X) (c : Unit × H.Coin) :
    (BatchHonestProver.ofHonest H).one.strat w x c = H.strat w x c.2 :=
  SStrat.zip_triv _

theorem ofHonest_withheld (w : Wt) (x : X) :
    (BatchHonestProver.ofHonest H).one.withheld w x = H.withheld w x := by
  ext ρ
  show ((RhoLo.toRho (Rho.lo _ ρ) ∈ H.Bad ∨ false = true) ∨ RhoLo.toRho (Rho.lo _ ρ) ∈ H.Hid w x) ↔
    _
  rw [RhoLo.toRho_lo, or_iff_left Bool.false_ne_true]
  rfl

theorem acc_one_iff (valid : Wt → X → Prop) : (BatchHonestProver.ofHonest H).Acc valid ↔ H.Acc valid := by
  unfold BatchHonestProver.Acc Honest.Acc
  constructor
  · intro h w x c ρ hv hρ
    have := h w x ((), c) ρ hv (by rw [ofHonest_withheld]; exact hρ)
    rwa [ofHonest_strat] at this
  · intro h w x c ρ hv hρ
    rw [ofHonest_strat]
    exact h w x c.2 ρ hv (by rwa [ofHonest_withheld] at hρ)

/-- The only slot. -/
def slot0 : ({0} : Finset (Fin 1)) := ⟨0, Finset.mem_singleton_self 0⟩

theorem eq_slot0 (j : ({0} : Finset (Fin 1))) : j = slot0 := Subsingleton.elim _ _

theorem extAnsJ_one (x : X) (ρ : Rho Q.shape) (y : E.Str) :
    (BatchInteractiveOracleProof.ofProto Q).extAnsJ ({0} : Finset (Fin 1)) (fun _ => x) (fun _ => ρ) y =
      Q.extAns x ρ y := by
  classical
  funext p
  unfold BatchInteractiveOracleProof.extAnsJ InteractiveOracleProof.extAns
  have : (∃ _j : ({0} : Finset (Fin 1)), p ∈ Q.extReads x ρ) ↔ p ∈ Q.extReads x ρ :=
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨slot0, h⟩⟩
  exact if_congr this rfl rfl

/-- The output for the only slot is the output of the ordinary IOP. -/
theorem output_one (w : Wt) (x : X) (ρ : BRho 1 Q.shape (RoundSplits.allLocal Q.shape)) :
    (BatchHonestProver.ofHonest H).output w (fun _ => some x) ρ {0} =
      (H.output w x (ρ.slot 0)).map fun o _ => o := by
  classical
  unfold BatchHonestProver.output Honest.output
  by_cases hρ : ρ.slot 0 ∈ H.withheld w x
  · rw [if_pos hρ, PMF.pure_map]
    have : (fun (c : Unit × (Fin 1 → H.Coin)) (j : ({0} : Finset (Fin 1))) =>
      (if ρ.slot j.1 ∈ (BatchHonestProver.ofHonest H).one.withheld w x then none
        else
          some ((BatchInteractiveOracleProof.ofProto Q).loc.dview x ((BatchHonestProver.ofHonest H).ext w)
              (((BatchHonestProver.ofHonest H).one.strat w x (c.1, c.2 j)).run
                (ρ.slot j.1)).1) : Option (DView Q)))
        = fun _ _ => none := by
      funext c j
      rw [eq_slot0 j, ofHonest_withheld]
      exact if_pos hρ
    show PMF.map _ _ = _
    erw [this]
    exact PMF.map_const _ _
  · rw [if_neg hρ, PMF.map_comp]
    have e : (unif H.Coin) = (unif (Unit × (Fin 1 → H.Coin))).map fun c => c.2 0 := by
      have :=
        map_unif_equiv ((Equiv.punitProd (Fin 1 → H.Coin)).trans (Equiv.funUnique (Fin 1) H.Coin))
      rw [← this]
      rfl
    rw [e, PMF.map_comp]
    congr 1
    funext c j
    rw [eq_slot0 j]
    show (if ρ.slot 0 ∈ (BatchHonestProver.ofHonest H).one.withheld w x then none else some _) = _
    rw [ofHonest_withheld]
    refine (if_neg hρ).trans ?_
    rw [ofHonest_strat]
    rfl

theorem pmf_subsingleton {α : Type} [Subsingleton α] (p q : PMF α) : p = q := by
  ext a
  have hp := p.tsum_coe
  have hq := q.tsum_coe
  rw [tsum_eq_single a fun b hb => absurd (Subsingleton.elim b a) hb] at hp hq
  rw [hp, hq]

/-- HVZK for sets of slots (`BatchHonestProver.HVZK`), at one slot with local rounds only, is HVZK
(`Honest.HVZK`). -/
theorem hvzk_one_iff (valid : Wt → X → Prop) (z : ℝ≥0∞) :
    (BatchHonestProver.ofHonest H).HVZK 1 valid z ↔ H.HVZK valid z := by
  classical
  constructor
  · rintro ⟨SimB, h⟩
    refine ⟨fun x ρ ans => (SimB {0} (fun _ => x) (fun _ => ρ) ans).map fun f => f slot0,
      fun w x hv => ?_⟩
    have hb :=
      h w (fun _ => some x) (fun j xj e => by cases e; exact hv) {0} (fun _ => x) (fun _ => rfl)
    rw [Finset.card_singleton, Nat.cast_one, one_mul] at hb
    rw [← prBRho_one]
    refine le_trans ?_ hb
    unfold prBRho
    refine pr_mono _ ?_
    intro ρ hρ heq
    refine hρ ?_
    rw [output_one] at heq
    have e1 : (fun j : ({0} : Finset (Fin 1)) => ρ.slot j.1) = fun _ => ρ.slot 0 := by
      funext j; rw [eq_slot0 j]; rfl
    rw [e1, extAnsJ_one] at heq
    have := congrArg (PMF.map fun f : ({0} : Finset (Fin 1)) → Option (DView Q) => f slot0) heq
    rw [PMF.map_comp] at this
    have hid : ((fun f : ({0} : Finset (Fin 1)) → Option (DView Q) => f slot0) ∘ fun o _ => o) =
        id := rfl
    rw [hid, PMF.map_id] at this
    exact this
  · rintro ⟨Sim, h⟩
    refine ⟨fun J xs ρs ans =>
        if hJ : (0 : Fin 1) ∈ J then
          (Sim (xs ⟨0, hJ⟩) (ρs ⟨0, hJ⟩) ans).map fun o _ => o else PMF.pure fun _ => none,
      fun w x hv J xs hxs => ?_⟩
    by_cases hJ : (0 : Fin 1) ∈ J
    · obtain rfl : J = {0} := by
        ext j; rw [Subsingleton.elim j 0]; simp [hJ]
      have hx : x = fun _ => some (xs slot0) := by
        funext j; rw [Subsingleton.elim j 0]; exact hxs slot0
      have hxs' : xs = fun _ => xs slot0 := by funext j; rw [eq_slot0 j]
      subst hx
      rw [Finset.card_singleton, Nat.cast_one, one_mul]
      refine le_trans (pr_mono _ ?_)
        (le_trans (le_of_eq (prBRho_one _)) (h w (xs slot0) (hv 0 _ rfl)))
      intro ρ hρ heq
      refine hρ ?_
      have e1 : (fun j : ({0} : Finset (Fin 1)) => ρ.slot j.1) = fun _ => ρ.slot 0 := by
        funext j; rw [eq_slot0 j]; rfl
      beta_reduce
      rw [output_one, dif_pos hJ, e1, heq]
      conv_rhs => rw [hxs']
      rw [extAnsJ_one]
    · have hE : IsEmpty J := ⟨fun j => hJ (by rw [← Subsingleton.elim j.1 0]; exact j.2)⟩
      unfold prBRho
      refine le_trans
        (pr_mono _ (fun ρ hρ => (hρ (pmf_subsingleton _ _)).elim : _ ⊆ (∅ : Set _))) ?_
      simp

end One

variable {I : Type}


end BatchOne

end Iop
