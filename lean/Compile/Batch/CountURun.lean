-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CountURun.lean: the marked queries (`Step.marked`, Rom/Defer.lean) of a run against
the challenger with the prover with free empty slots (no query for an empty slot: `proveBU`,
Compile/Batch/ProverU.lean). If `L.maxBatchSize` = 2 ^ `W.depthReq`, and if the adversary asks for one setup,
first, and then for at most n batches of at most B requests each (`GAdm`), then every run makes at
most the marked queries of one setup and of n batches of at most B requests (words of this library:
lean/GLOSSARY.md).

  `markStepU`  If `L.maxBatchSize` = 2 ^ `W.depthReq`, for a batch of at most B requests: the step of the
               challenger `VCBPG` (Compile/Batch/PubProg.lean) with the program `PpU` makes at most
               mPU W B o marked queries to o (Compile/Batch/CountU.lean).
  `countRunU`  If `L.maxBatchSize` = 2 ^ `W.depthReq`, for an adversary that asks for one setup, first, and
               then for at most n batches of at most B requests each: at the end of every run, in
               either mode (R or I, Rom/Defer.lean), the number of records of marked queries to o is
               at most Disc.mCB W p o + n * mPU W B o.

The induction on the adversary is that of `Disc.within_interactB`
(Compile/Batch/DisciplineWorld.lean), repeated because the bound of a step depends on what the
adversary is allowed to ask. The count of the setup is that of `Disc.WorldB.setup`
(Compile/Batch/WithinVCB.lean), which needs an orderly state (`TidyO`): before the setup the state
is orderly. After the setup nothing is asked of the state.

Notation: `V`, `pw`: an arbitrary type V and an arbitrary function pw : `IVK lam L → WKey lam L → V`
(the head of Compile/Batch/PubChall.lean); `i`: an element of `I`: the setup runs `Cp W WP p i`
(`VCBPG`, Compile/Batch/PubProg.lean); `ok`: a predicate on batches: in `GAdm ok A false n`
(Compile/Batch/SpecGlue.lean) each batch is allowed; `m`: a `Bool`: true is mode I, false is mode R
(`Step.run`, Rom/Defer.lean); `Option (IskH lam L × ℕ)`: the type `τ` of `VCBPG`: `none` before the
setup, then `some (k, t)` with t the token that `Step.fresh 0` returns at the end of the setup.

Limits: nothing on violations of the rules of deferred programming (Rom/Defer.lean), on ordinary
queries or on the lengths of charged tokens.
-/
import Compile.Batch.CountU
import Compile.Batch.PubProg
import Compile.Batch.WithinVCB
import Compile.Batch.DisciplineChainAll

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP Compile
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt run_bind run_fresh0)
open Compile.Disc (nEv)
open Disc

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {V : Type} (W : QueryLayout lam L) (WP : WireBP L)
  (p : Params) (pw : IVK lam L → WKey lam L → V) (i : I)

/-- If `L.maxBatchSize` = 2 ^ `W.depthReq`: the step for a batch of at most B requests makes at most mPU W B o
marked queries to each oracle o. -/
theorem markStepU (hN : L.maxBatchSize = 2 ^ W.depthReq) {B : ℕ} (s : Option (IskH lam L × ℕ))
    (b : Gen.Batch X Unit) (hb : b.pairs.length ≤ B) :
    MarkLe ((VCBPG W WP p pw (PpU W WP p) i).step s (.batch b)) (mPU W B) := by
  rcases s with _ | ⟨k, N₀⟩
  · exact trivial
  · show MarkLe
      (if hasOwn b then
        Step.fresh 0 fun t₀ =>
          (virt N₀ (t₀ + 1 - N₀) (PpU W WP p k (ownFlag b) (reqs b))).bind fun πs =>
            Step.pure (replyOfP V b πs, some (k, N₀)) else Step.pure (.inr [], some (k, N₀))) _
    split
    · intro t₀
      refine (MarkLe.bind (M₂ := fun _ => 0)
          (g := fun πs => Step.pure (replyOfP V b πs, some (k, N₀))) (fun _ => trivial)
          ((markPpU W WP p k (ownFlag b) (reqs b) hN (by simpa [reqs] using hb)).virt
            N₀ (t₀ + 1 - N₀))).mono fun o => le_rfl
    · exact trivial

variable {W WP p pw i}

/-- from steps to runs. Under the hypotheses below, for a run from any state (s, d): at its end the
number of marked queries to o (`nEv`) has grown by at most n * mPU W B o, and by mCB W p o more if
bf = false. bf is the flag of `GAdm` (Compile/Batch/SpecGlue.lean): it says whether the setup has
been made; at bf = false the hypotheses ask that s = none and that d is well-formed (`TidyO`). -/
theorem CountU.count_interact (hN : L.maxBatchSize = 2 ^ W.depthReq) {B : ℕ} (ok : Gen.Batch X Unit → Prop)
    (hok : ∀ b, ok b → b.pairs.length ≤ B) (m : Bool) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) :
    ∀ (bf : Bool) (n : ℕ) (s : Option (IskH lam L × ℕ)) (d : DSt (spec lam W.K L)), GAdm ok A bf n →
      (bf = false → s = none ∧ TidyO (rulesB W.K L lam p) d) →
      ∀ x ∈ (interact ((VCBPG W WP p pw (PpU W WP p) i).world m) A (s, d)).support,
        ∀ o, nEv x.2.2 o ≤ nEv d o + (if bf then 0 else mCB W p o) + n * mPU W B o := by
  induction A with
  | halt a =>
    intro bf n s d _ _ x hx o
    rw [interact, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    rw [Nat.add_assoc]
    exact Nat.le_add_right _ _
  | sample N k ih =>
    intro bf n s d hA hI x hx o
    rw [interact, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, _, hr⟩ := hx
    exact ih r bf n s d (hA r) hI x hr o
  | query o' q k ih =>
    intro bf n s d hA hI x hx o
    rw [interact, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hr⟩ := hx
    obtain ⟨pr, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    exact ih pr.1 bf n s _ (hA pr.1) (fun h => ⟨(hI h).1, (hI h).2.table pr.2⟩) x hr o
  | call c k ih =>
    intro bf n s d hA hI x hx o
    rw [interact, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hr⟩ := hx
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    cases c with
    | setup =>
      obtain ⟨rfl, hk⟩ := hA
      obtain ⟨rfl, ht⟩ := hI rfl
      have hz' : z ∈
          (((Cp W WP p i).bind fun o =>
              Step.fresh 0 fun t =>
                Step.pure ((.inl (pw o.1 (keyOf o.2)),
                    some (o.2, t)) : BInP V lam L × Option (IskH lam L × ℕ))).run
            m d).support := hz
      rw [run_bind, PMF.mem_support_bind_iff] at hz'
      obtain ⟨u, hu, hz'⟩ := hz'
      rw [run_fresh0] at hz'
      simp only [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hz'
      subst hz'
      have h1 := ((WorldB.setup (i := i) safeCB m d ht u hu).2 o).2
      have h2 := ih _ true n _ _ (hk _) (fun h => by cases h) x hr o
      have h3 : nEv ({ u.2 with vals := u.2.vals ++ [[]] } : DSt (spec lam W.K L)) o = nEv u.2 o :=
        rfl
      simp only [if_true, Bool.false_eq_true, if_false] at h2 ⊢
      rw [h3] at h2
      omega
    | batch b =>
      cases n with
      | zero => exact hA.elim
      | succ n =>
        obtain ⟨rfl, hb, hk⟩ := hA
        have h1 := (markStepU W WP p pw i hN s b (hok b hb)).run m d z hz o
        have h2 := ih _ true n _ _ (hk _) (fun h => by cases h) x hr o
        simp only [if_true] at h2 ⊢
        rw [Nat.succ_mul]
        omega

variable (W WP p pw i)

/-- Under the hypotheses below: every run makes at most the marked queries of one setup and of n
batches of at most B requests, in both modes. -/
theorem countRunU (hN : L.maxBatchSize = 2 ^ W.depthReq) {B : ℕ}
    (ok : Gen.Batch X Unit → Prop) (hok : ∀ b, ok b → b.pairs.length ≤ B)
    {α : Type} (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (n : ℕ)
    (m : Bool) (hA : GAdm ok A false n) :
    ∀ x ∈ (interact ((VCBPG W WP p pw (PpU W WP p) i).world m) A (none, DSt.init _)).support,
      ∀ o, nEv x.2.2 o ≤ mCB W p o + n * mPU W B o := by
  intro x hx o
  have h := CountU.count_interact
    (p := p) hN ok hok m A false n none (DSt.init _) hA (fun _ => ⟨rfl, TidyO.init⟩) x hx o
  simpa [nEv, DSt.init] using h

end Compile.Batch
