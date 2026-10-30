-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchPullProofs.lean: for good samplers (`Samplers.Good`) all properties of a record of
protocols `BatchProtocol` are preserved, with the numbers `LH.Nums.pullB`, when its challenges are computed
from other uniform strings (`Iop.Spec.pullPropsB`, Iop/BatchPull.lean). As Iop/PullProofs.lean,
whose lemmas for one slot's transcript are used. Helpers: namespace `Iop.BatchPull`. (Words of this
library: lean/GLOSSARY.md.)

Notation: `Samplers.Fib σ : Prop` (Iop/PullProofs.lean): all fibres of all samplers are within their
bounds w; `σ.w : ℕ` (a field of `Sampler`, Iop/Pull.lean): a natural number; `Samplers.Fib` asks
that it bounds the fibres; `Err.pull σ ε` (Iop/Pull.lean): each count is multiplied by the bound on
the fibres.
-/
import Iop.BatchPull
import Iop.BatchSound
import Iop.BatchOne
import Iop.PullProofs
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

namespace BatchPull

/-! ## 1. Challenges -/

theorem slot_mapAll {C D : Type} (f : C → D) {N : ℕ} (j : Fin N) :
    ∀ (k : Kind) (v : k.All N C), k.slot (k.mapAll f v) j = f (k.slot v j)
  | .sh, _ => rfl
  | .lo, _ => rfl

theorem shOf_map {C D : Type} (f : C → D) :
    ∀ (k : Kind) (c : C), k.mapSh f (k.shOf c) = k.shOf (f c)
  | .sh, _ => rfl
  | .lo, _ => rfl

theorem loOf_map {C D : Type} (f : C → D) :
    ∀ (k : Kind) (c : C), k.mapLo f (k.loOf c) = k.loOf (f c)
  | .sh, _ => rfl
  | .lo, _ => rfl

theorem slot_push {N : ℕ} (j : Fin N) :
    ∀ {s : Shape} (σ : Samplers s) {A : RoundSplits s} (ρ : BRho N (s.pull σ) (A.pull σ)),
      (BRho.push σ ρ).slot j = Rho.push σ (ρ.slot j)
  | [], _, _, _ => rfl
  | _ :: _, (σ, σs), (a, _), (v, ρ) => Prod.ext (slot_mapAll σ.φ j a.kind v) (slot_push j σs ρ)

theorem lo_push :
    ∀ {s : Shape} (σ : Samplers s) (A : RoundSplits s) (ρ : Rho (s.pull σ)),
      RhoLo.push σ (Rho.lo (A.pull σ) ρ) = Rho.lo A (Rho.push σ ρ)
  | [], _, _, _ => rfl
  | _ :: _, (σ, σs), (a, A), (c, ρ) => Prod.ext (loOf_map σ.φ a.kind c) (lo_push σs A ρ)

theorem sh_push :
    ∀ {s : Shape} (σ : Samplers s) (A : RoundSplits s) (ρ : Rho (s.pull σ)),
      RhoSh.push σ (Rho.sh (A.pull σ) ρ) = Rho.sh A (Rho.push σ ρ)
  | [], _, _, _ => rfl
  | _ :: _, (σ, σs), (a, A), (c, ρ) => Prod.ext (shOf_map σ.φ a.kind c) (sh_push σs A ρ)

/-! ## 2. Annotations -/

theorem coherent_pull :
    ∀ {s : Shape} (σ : Samplers s) {A : RoundSplits s}, A.Coherent → (A.pull σ).Coherent
  | [], _, _, _ => trivial
  | _ :: _, (_, σs), (_, _), h =>
    ⟨⟨h.1.plain_join, h.1.rd_shared, h.1.rd_own⟩, coherent_pull σs h.2⟩

theorem summary_pull :
    ∀ {s : Shape} (σ : Samplers s) (A : RoundSplits s),
      RoundSplits.summary (s.pull σ) (A.pull σ) = RoundSplits.summary s A
  | [], _, _ => rfl
  | _ :: _, (_, σs), (a, A) =>
    congrArg ((a.kind, Subsingleton a.M0, Subsingleton a.Mj) :: ·) (summary_pull σs A)

/-- The all-local annotation is carried to the all-local annotation. (By induction on the rounds: so
taking an ordinary IOP as a protocol with slots and pulling back commute, but not by definition.) -/
theorem allLocal_pull :
    ∀ {s : Shape} (σ : Samplers s), (RoundSplits.allLocal s).pull σ = RoundSplits.allLocal (s.pull σ)
  | [], _ => rfl
  | r :: s, (σ, σs) => by
      show (RAnn.allLocal (r.pull σ), (RoundSplits.allLocal s).pull σs) =
        (RAnn.allLocal (r.pull σ), RoundSplits.allLocal (Shape.pull s σs))
      rw [allLocal_pull σs]

/-! ## 3. Prefixes of transcripts -/

def pushP : {s : Shape} → (σ : Samplers s) → AtP (s.pull σ) → AtP s
  | _ :: _, (_, _), .inl _ => .inl ()
  | _ :: _, (σ, σs), .inr (m, c, τ) => .inr (m, σ.φ c, pushP σs τ)

def pushV : {s : Shape} → (σ : Samplers s) → AtV (s.pull σ) → AtV s
  | _ :: _, (_, _), .inl m => .inl m
  | _ :: _, (σ, σs), .inr (m, c, τ) => .inr (m, σ.φ c, pushV σs τ)

/-- A prefix of the pulled-back protocol's transcript, with the images of its challenges. -/
def push {s : Shape} (σ : Samplers s) : PTr (s.pull σ) → PTr s
  | .atP τ => .atP (pushP σ τ)
  | .atV τ => .atV (pushV σ τ)
  | .full τ => .full (Tr.push σ τ)

theorem push_empty : ∀ {s : Shape} (σ : Samplers s), push σ (PTr.empty (s.pull σ)) = PTr.empty s
  | [], _ => rfl
  | _ :: _, (_, _) => rfl

theorem push_cons {r : Round} {s : Shape} (σ : Sampler r) (σs : Samplers s)
    (m : r.Msg) (c : σ.Src) :
    ∀ t : PTr (s.pull σs),
      push (s := r :: s) (σ, σs) (PTr.cons (r := r.pull σ) m c t) = PTr.cons m (σ.φ c) (push σs t)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

open BatchH4 in
theorem proverLaw_pull :
    ∀ {s : Shape} (σ : Samplers s) (S : PTr s → Bool),
      ProverLaw s S → ProverLaw (s.pull σ) (fun t => S (push σ t))
  | _ :: _, (_, _), _, h, .inl _, m, h0 => h (.inl ()) m h0
  | _ :: _, (σ, σs), S, h, .inr (m', c', τ), m, h0 =>
      proverLaw_pull σs (fun t => S (PTr.cons m' (σ.φ c') t)) (h.tail m' (σ.φ c')) τ m h0

/-! ## 4. The soundness property `SndB` (Snd-B) and its late form `SndBL` (Iop/Batch.lean) -/

theorem jointLaw_pull {N : ℕ} :
    ∀ {s : Shape} {σ : Samplers s}, σ.Fib →
      ∀ (A : RoundSplits s) (ε : Err s) (St : Fin N → Option (PTr s → Bool)), JointLaw N s A ε St →
        JointLaw N (s.pull σ) (A.pull σ) (Err.pull σ ε)
          (fun j => (St j).map fun S t => S (push σ t))
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (σ, σs), hσ, (a, A), (e, ε), St, h => by
      intro (m0 : a.M0) (m : Fin N → a.Mj)
      obtain ⟨hround, hrest⟩ := h m0 m
      refine ⟨?_, fun v => ?_⟩
      · obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
        cases k
        · -- a shared round: the joint event, for one sample
          show cnt (fun c : σ.Src =>
              ∃ j S',
                (St j).map (fun S t => S (push (s := r :: s) (σ, σs) t)) = some S' ∧
                S' (.atV (Sum.inl (sp.symm (m0, m j)))) = false ∧
                S' (PTr.cons (r := r.pull σ) (sp.symm (m0, m j)) c (PTr.empty (Shape.pull s σs))) =
                  true) ≤ e * σ.w
          refine le_trans (cnt_mono ?_)
            (le_trans (cnt_comp_le σ.φ hσ.1 fun c : r.Chal =>
                ∃ j S,
                  St j = some S ∧
                  S (.atV (Sum.inl (sp.symm (m0, m j)))) = false ∧
                  S (PTr.cons (sp.symm (m0, m j)) c (PTr.empty s)) = true)
              (Nat.mul_le_mul_right _ hround))
          rintro c ⟨j, S', hS', h0, h1⟩
          obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
          refine ⟨j, S, hS, h0, ?_⟩
          have h1' : S (push (s := r :: s) (σ, σs)
                  (PTr.cons (r := r.pull σ) (sp.symm (m0, m j)) c (PTr.empty (Shape.pull s σs)))) =
              true := h1
          rw [push_cons, push_empty] at h1'
          exact h1'
        · -- a local round: each slot by itself
          intro j S' hS' h0
          obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
          show cnt (fun c : σ.Src =>
              S (push (s := r :: s) (σ, σs)
                    (PTr.cons (r := r.pull σ) (sp.symm (m0, m j))
                      c (PTr.empty (Shape.pull s σs)))) = true) ≤ e * σ.w
          refine le_trans (le_of_eq (cnt_congr fun c => ?_))
            (le_trans (cnt_comp_le σ.φ hσ.1 fun c : r.Chal =>
                S (PTr.cons (sp.symm (m0, m j)) c (PTr.empty s)) = true)
              (Nat.mul_le_mul_right _ (hround j S hS h0)))
          rw [push_cons, push_empty]
      · have ih := jointLaw_pull hσ.2 A ε _ (hrest (a.kind.mapAll σ.φ v))
        refine cast (congrArg (JointLaw N (Shape.pull s σs) (A.pull σs) (Err.pull σs ε)) ?_) ih
        funext j
        beta_reduce
        refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
        congr 1
        funext S t
        show S (PTr.cons (a.join m0 (m j)) (a.kind.slot (a.kind.mapAll σ.φ v) j) (push σs t)) =
          S (push (s := r :: s) (σ, σs)
              (PTr.cons (r := r.pull σ) (a.join m0 (m j)) (a.kind.slot v j) t))
        rw [push_cons, slot_mapAll]
        rfl

variable {X : Type} {E : ExtSpec}

theorem sndB_pull {Q : BatchInteractiveOracleProof X E} {σ : Samplers Q.loc.shape} (hσ : σ.Fib) {N : ℕ}
    {L : X → E.Str → Prop} {ε : Err Q.loc.shape} (h : Q.SndB N L ε) :
    (Q.pull σ).SndB N L (Err.pull σ ε) := by
  obtain ⟨State, h1, h2, h3, h4⟩ := h
  refine ⟨fun y x t => State y x (push σ t),
    fun y x => ?_,
    fun y x => proverLaw_pull σ (State y x) (h2 y x),
    fun y x τ hτ => h3 y x (Tr.push σ τ) hτ,
    fun y x => ?_⟩
  · show State y x (push σ (PTr.empty (Q.loc.shape.pull σ))) = true ↔ _
    rw [push_empty]
    exact h1 y x
  · refine cast (congrArg (JointLaw N (Q.loc.shape.pull σ) (Q.ann.pull σ) (Err.pull σ ε)) ?_)
      (jointLaw_pull hσ Q.ann ε _ (h4 y x))
    funext j
    cases x j <;> rfl

theorem idx_pushP : ∀ {s : Shape} (σ : Samplers s) (τ : AtP (s.pull σ)), (pushP σ τ).idx = τ.idx
  | _ :: _, (_, _), .inl _ => rfl
  | _ :: _, (_, σs), .inr (_, _, τ) => congrArg (· + 1) (idx_pushP σs τ)

theorem localTo_pull :
    ∀ {n : ℕ} {s : Shape} (σ : Samplers s) {A : RoundSplits s},
      RoundSplits.LocalTo n s A → RoundSplits.LocalTo n (s.pull σ) (A.pull σ)
  | _, [], _, _, h => by cases ‹ℕ› <;> exact False.elim h
  | 0, _ :: _, (_, _), (_, _), h => h
  | _ + 1, _ :: _, (_, σs), (_, _), h => ⟨h.1, localTo_pull σs h.2⟩

/-- If S = 0 implies S' = 0 before the prover message of round n, so it does for S, S' composed with
`push`. -/
theorem switch_pull : ∀ {s : Shape} (σ : Samplers s) (S S' : PTr s → Bool) (n : ℕ),
    (∀ τ : AtP s, n = τ.idx → S (.atP τ) = false → S' (.atP τ) = false) →
    ∀ τ : AtP (s.pull σ), n = τ.idx → S (push σ (.atP τ)) = false → S' (push σ (.atP τ)) = false
  | _ :: _, (_, _), _, _, _, h, .inl _, hn, h0 => h (.inl ()) hn h0
  | _ :: _, (σ, σs), S, S', n, h, .inr (m', c', τ), hn, h0 => by
      cases n with
      | zero => cases hn
      | succ n =>
        exact switch_pull σs (fun t => S (PTr.cons m' (σ.φ c') t))
          (fun t => S' (PTr.cons m' (σ.φ c') t)) n
          (fun τ₁ h₁ => h (.inr (m', σ.φ c', τ₁)) (congrArg (· + 1) h₁)) τ (Nat.succ.inj hn) h0

theorem sndBL_pull {Q : BatchInteractiveOracleProof X E} {σ : Samplers Q.loc.shape} (hσ : σ.Fib)
    {N : ℕ} {early : X → X} {late : Option ℕ} {L : X → E.Str → Prop}
    {ε : Err Q.loc.shape} (h : Q.SndBL N early late L ε) :
    (Q.pull σ).SndBL N early late L (Err.pull σ ε) := by
  obtain ⟨h0, State, h1, h2, hsw, h3, h4⟩ := h
  refine ⟨fun n hn => ⟨(h0 n hn).1, localTo_pull σ (h0 n hn).2⟩,
    fun y x t => State y x (push σ t),
    fun y x hL => ?_,
    fun y x => proverLaw_pull σ (State y x) (h2 y x),
    fun y x τ hL hn => ?_,
    fun y x τ hL hτ => h3 y x (Tr.push σ τ) hL hτ,
    fun y x => ?_⟩
  · show State y (early x) (push σ (PTr.empty (Q.loc.shape.pull σ))) = false
    rw [push_empty]
    exact h1 y x hL
  · exact switch_pull σ (State y (early x)) (State y x) τ.idx
      (fun τ₁ h₁ => hsw y x τ₁ hL (by rw [hn, h₁])) τ rfl
  · refine cast (congrArg (JointLaw N (Q.loc.shape.pull σ) (Q.ann.pull σ) (Err.pull σ ε)) ?_)
      (jointLaw_pull hσ Q.ann ε _ (h4 y x))
    funext j
    cases x j <;> rfl

/-! ## 5. Positions read in the external string -/

theorem allReads_pull (Q : BatchInteractiveOracleProof X E) (σ : Samplers Q.loc.shape) {N : ℕ} (x : Fin N → Option X)
    (ρ : BRho N (Q.loc.shape.pull σ) (Q.ann.pull σ)) :
    (Q.pull σ).allReads x ρ = Q.allReads x (BRho.push σ ρ) := by
  classical
  unfold BatchInteractiveOracleProof.allReads
  refine Finset.biUnion_congr rfl fun j _ => ?_
  cases x j with
  | none => rfl
  | some xj =>
    show Q.loc.extReads xj (Rho.push σ (ρ.slot j)) = Q.loc.extReads xj ((BRho.push σ ρ).slot j)
    rw [slot_push]

theorem readsAtMost_pull {Q : BatchInteractiveOracleProof X E} (σ : Samplers Q.loc.shape)
    {N q : ℕ} (h : Q.ReadsAtMost N q) : (Q.pull σ).ReadsAtMost N q :=
  fun x ρ => by rw [allReads_pull]; exact h x _

theorem extShared_pull {Q : BatchInteractiveOracleProof X E} (σ : Samplers Q.loc.shape) (h : Q.ExtShared) :
    (Q.pull σ).ExtShared :=
  fun x x' ρ ρ' hρ =>
    h x x' (Rho.push σ ρ) (Rho.push σ ρ')
      (by rw [← sh_push, ← sh_push]; exact congrArg (RhoSh.push σ) hρ)

/-! ## 6. One slot of the honest prover -/

theorem zip_pull : ∀ {s : Shape} (σ : Samplers s) {A : RoundSplits s} (a : SStrat s A) (b : LStrat s A),
    (SStrat.pull σ a).zip (LStrat.pull σ b) = Strat.pull σ (a.zip b)
  | [], _, _, _, _ => rfl
  | r :: s, (σ, σs), (an, A), (m0, k0), (mj, kj) => by
      show (an.join m0 mj,
          fun c : σ.Src =>
            (SStrat.pull σs (k0 (an.kind.mapSh σ.φ (an.kind.shOf c)))).zip
              (LStrat.pull σs (kj (σ.φ c)))) =
        ((an.join m0 mj,
          fun c : σ.Src => Strat.pull σs ((k0 (an.kind.shOf (σ.φ c))).zip (kj (σ.φ c)))) :
          r.Msg × (σ.Src → Strat (Shape.pull s σs) Unit))
      congr 1
      funext c
      rw [shOf_map, zip_pull]

variable {Wt : Type}

theorem one_strat_pull {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (σ : Samplers Q.loc.shape) (w : Wt)
    (x : X) (c : H.Coin0 × H.Coin) :
    (H.pull σ).one.strat w x c = Strat.pull σ (H.one.strat w x c) := zip_pull σ _ _

theorem mem_one_withheld_pull {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (σ : Samplers Q.loc.shape)
    (w : Wt) (x : X) (ρ : Rho (Q.loc.shape.pull σ)) :
    ρ ∈ (H.pull σ).one.withheld w x ↔ Rho.push σ ρ ∈ H.one.withheld w x := by
  show ((RhoLo.push σ (Rho.lo (Q.ann.pull σ) ρ) ∈ H.Bad ∨
        H.stop0 (RhoSh.push σ (Rho.sh (Q.ann.pull σ) ρ)) = true) ∨
      RhoLo.push σ (Rho.lo (Q.ann.pull σ) ρ) ∈ H.Hid w x) ↔
    ((Rho.lo Q.ann (Rho.push σ ρ) ∈ H.Bad ∨ H.stop0 (Rho.sh Q.ann (Rho.push σ ρ)) = true) ∨
      Rho.lo Q.ann (Rho.push σ ρ) ∈ H.Hid w x)
  rw [lo_push, sh_push]

theorem acc_pull {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} {valid : Wt → X → Prop}
    (h : H.Acc valid) (σ : Samplers Q.loc.shape) : (H.pull σ).Acc valid := by
  intro w x c ρ hv hρ
  show Q.loc.accept x (H.ext w) (Tr.push σ (((H.pull σ).one.strat w x c).run ρ).1) = true
  rw [one_strat_pull]
  exact (congrArg (Q.loc.accept x (H.ext w)) (Strat.run_pull σ (H.one.strat w x c) ρ)).trans
    (h w x c (Rho.push σ ρ) hv fun hm => hρ ((mem_one_withheld_pull H σ w x ρ).2 hm))

theorem prRho_one_withheld_pull {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt)
    {σ : Samplers Q.loc.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K) (w : Wt) (x : X)
    {p : ℝ≥0∞} (h : prRho (H.one.withheld w x) ≤ p) :
    prRho ((H.pull σ).one.withheld w x) ≤ K * p := by
  have e : (H.pull σ).one.withheld w x = {ρ | Rho.push σ ρ ∈ H.one.withheld w x} :=
    Set.ext fun ρ => mem_one_withheld_pull H σ w x ρ
  rw [e]
  exact (prRho_preimage_le hσ (H.one.withheld w x)).trans (by gcongr)

/-! ## 7. Counting: the whole verifier randomness of a batch -/

/-- w for one sample, w^N for N samples -/
def pw : Kind → ℕ → ℕ → ℕ
  | .sh, _, w => w
  | .lo, N, w => w ^ N

/-- The product of the bounds on the fibres, one factor for each sample. -/
def WB (N : ℕ) : {s : Shape} → Samplers s → RoundSplits s → ℕ
  | [], _, _ => 1
  | _ :: _, (σ, σs), (a, A) => pw a.kind N σ.w * WB N σs A

theorem cnt_mapAll_le {U C : Type} [Fintype U] [Fintype C] (φ : U → C) {w : ℕ}
    (hw : ∀ c, cnt (fun a => φ a = c) ≤ w) (N : ℕ) :
    ∀ (k : Kind) (v : k.All N C), cnt (fun v' : k.All N U => k.mapAll φ v' = v) ≤ pw k N w
  | .sh, v => hw v
  | .lo, v => by
      classical
      have e : cnt (fun v' : Fin N → U => (fun j => φ (v' j)) = v) =
          ∏ j : Fin N, cnt (fun a => φ a = v j) := by
        rw [← cnt_forall_pi (A := fun _ : Fin N => U) fun j a => φ a = v j]
        exact cnt_congr fun v' => funext_iff
      show cnt (fun v' : Fin N → U => (fun j => φ (v' j)) = v) ≤ w ^ N
      rw [e]
      refine le_trans (Finset.prod_le_prod' fun j _ => hw (v j)) (le_of_eq ?_)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_All (N : ℕ) (C : Type) [Fintype C] :
    ∀ k : Kind, Fintype.card (k.All N C) = pw k N (Fintype.card C)
  | .sh => rfl
  | .lo => by
      show Fintype.card (Fin N → C) = Fintype.card C ^ N
      rw [Fintype.card_fun, Fintype.card_fin]

theorem card_cons (N : ℕ) (r : Round) (s : Shape) (a : RAnn r) (A : RoundSplits s) :
    Fintype.card (BRho N (r :: s) (a, A)) =
      pw a.kind N (Fintype.card r.Chal) * Fintype.card (BRho N s A) := by
  rw [← card_All]
  exact Fintype.card_prod _ _

theorem cnt_push_le (N : ℕ) :
    ∀ {s : Shape} {σ : Samplers s}, σ.Fib →
      ∀ (A : RoundSplits s) (ρ : BRho N s A),
        cnt (fun ρ' : BRho N (s.pull σ) (A.pull σ) => BRho.push σ ρ' = ρ) ≤ WB N σ A
  | [], _, _, _, _ =>
    (cnt_le_card _).trans
      (le_of_eq (Fintype.card_eq_nat_card.trans (Nat.card_unique : Nat.card Unit = 1)))
  | r :: s, (σ, σs), h, (a, A), (v, ρ) => by
      have h1 := cnt_and_prod (fun v' : a.kind.All N σ.Src => a.kind.mapAll σ.φ v' = v)
        (fun ρ' : BRho N (Shape.pull s σs) (A.pull σs) => BRho.push σs ρ' = ρ)
      have h2 : cnt (fun ρ' : BRho N
            (Shape.pull (r :: s) (σ, σs)) (RoundSplits.pull (s := r :: s) (σ, σs) (a, A)) =>
              BRho.push (s := r :: s) (σ, σs) ρ' = (v, ρ)) =
          cnt (fun x : a.kind.All N σ.Src × BRho N (Shape.pull s σs) (A.pull σs) =>
            a.kind.mapAll σ.φ x.1 = v ∧ BRho.push σs x.2 = ρ) :=
        cnt_congr (C := a.kind.All N σ.Src × BRho N (Shape.pull s σs) (A.pull σs))
          fun x => Prod.mk.injEq _ _ _ _ ▸ Iff.rfl
      rw [h2, h1]
      exact Nat.mul_le_mul (cnt_mapAll_le σ.φ h.1 N a.kind v) (cnt_push_le N h.2 A ρ)

/-- If every fibre of φ has at most w elements, the source set has at most |C| w elements. -/
theorem card_src_le {U C : Type} [Fintype U] [Fintype C] (φ : U → C) {w : ℕ}
    (hw : ∀ c, cnt (fun a => φ a = c) ≤ w) :
    Fintype.card U ≤ Fintype.card C * w := by
  have h := cnt_comp_le φ hw fun _ => True
  rwa [cnt_true, cnt_true] at h

theorem round_le {N : ℕ} (hN : 0 < N) (w c u : ℕ) (hu : 0 < u) (hcov : u ≤ c * w)
    {K K' : ℝ≥0∞} (hK : (w : ℝ≥0∞) * c * K' ≤ K * u) :
    ∀ k : Kind, ((pw k N w : ℕ) : ℝ≥0∞) * (pw k N c : ℕ) * K' ^ N ≤ K ^ N * (pw k N u : ℕ)
  | .lo => by
      show ((w ^ N : ℕ) : ℝ≥0∞) * ((c ^ N : ℕ) : ℝ≥0∞) * K' ^ N ≤ K ^ N * ((u ^ N : ℕ) : ℝ≥0∞)
      push_cast
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      exact pow_le_pow_left₀ (zero_le _) hK N
  | .sh => by
      show (w : ℝ≥0∞) * c * K' ^ N ≤ K ^ N * u
      have hu0 : (u : ℝ≥0∞) ≠ 0 := by exact_mod_cast hu.ne'
      have hut : (u : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top u
      have hle : K' ≤ K := by
        have h1 : (u : ℝ≥0∞) * K' ≤ u * K := by
          calc (u : ℝ≥0∞) * K' ≤ ((c * w : ℕ) : ℝ≥0∞) * K' := by gcongr
            _ = (w : ℝ≥0∞) * c * K' := by push_cast; ring
            _ ≤ K * u := hK
            _ = u * K := mul_comm _ _
        exact (ENNReal.mul_le_mul_iff_right hu0 hut).1 h1
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      calc (w : ℝ≥0∞) * c * K' ^ (n + 1) = (w * c * K') * K' ^ n := by rw [pow_succ]; ring
        _ ≤ (K * u) * K ^ n := mul_le_mul' hK (pow_le_pow_left₀ (zero_le _) hle n)
        _ = K ^ (n + 1) * u := by rw [pow_succ]; ring

theorem WB_mul_card_le {N : ℕ} (hN : 0 < N) :
    ∀ {s : Shape} {σ : Samplers s} {κ K : ℝ≥0∞}, σ.Good κ K →
      ∀ A : RoundSplits s, (WB N σ A : ℝ≥0∞) * Fintype.card (BRho N s A) ≤
        K ^ N * Fintype.card (BRho N (s.pull σ) (A.pull σ))
  | [], _, _, K, h, _ => by
      have e : Fintype.card (BRho N [] PUnit.unit) = 1 :=
        Fintype.card_eq_nat_card.trans (Nat.card_unique : Nat.card Unit = 1)
      show ((1 : ℕ) : ℝ≥0∞) * Fintype.card (BRho N [] PUnit.unit) ≤
        K ^ N * Fintype.card (BRho N [] PUnit.unit)
      rw [e]
      simpa using one_le_pow₀ (show (1 : ℝ≥0∞) ≤ K from h)
  | r :: s, (σ, σs), κ, K, h, (a, A) => by
      obtain ⟨K', h', hK⟩ := h.2.2
      have ih := WB_mul_card_le hN h' A
      have hr := round_le hN σ.w (Fintype.card r.Chal) (Fintype.card σ.Src) Fintype.card_pos
        (card_src_le σ.φ h.1) hK a.kind
      have e1 := card_cons N r s a A
      have e2 : Fintype.card
            (BRho N (Shape.pull (r :: s) (σ, σs)) (RoundSplits.pull (s := r :: s) (σ, σs) (a, A))) =
          pw a.kind N (Fintype.card σ.Src) * Fintype.card (BRho N (Shape.pull s σs) (A.pull σs)) :=
        card_cons N (r.pull σ) (Shape.pull s σs) (a.pull σ) (A.pull σs)
      rw [e1, e2]
      show ((pw a.kind N σ.w * WB N σs A : ℕ) : ℝ≥0∞) * _ ≤ _
      push_cast
      calc
        ((pw a.kind N σ.w : ℕ) : ℝ≥0∞) * (WB N σs A : ℕ) *
              ((pw a.kind N (Fintype.card r.Chal) : ℕ) * (Fintype.card (BRho N s A) : ℕ)) =
            (pw a.kind N σ.w : ℕ) * (pw a.kind N (Fintype.card r.Chal) : ℕ) *
              ((WB N σs A : ℕ) * (Fintype.card (BRho N s A) : ℕ)) := by ring
        _ ≤ (pw a.kind N σ.w : ℕ) * (pw a.kind N (Fintype.card r.Chal) : ℕ) *
              (K' ^ N * (Fintype.card (BRho N (Shape.pull s σs) (A.pull σs)) : ℕ)) :=
            mul_le_mul' le_rfl ih
        _ = (pw a.kind N σ.w : ℕ) * (pw a.kind N (Fintype.card r.Chal) : ℕ) * K' ^ N *
              (Fintype.card (BRho N (Shape.pull s σs) (A.pull σs)) : ℕ) := by ring
        _ ≤ K ^ N * (pw a.kind N (Fintype.card σ.Src) : ℕ) *
              (Fintype.card (BRho N (Shape.pull s σs) (A.pull σs)) : ℕ) :=
          mul_le_mul' hr le_rfl
        _ = K ^ N * ((pw a.kind N (Fintype.card σ.Src) : ℕ) *
                (Fintype.card (BRho N (Shape.pull s σs) (A.pull σs)) : ℕ)) := by ring

/-- If 0 < N, for good samplers: the preimage of a set of values of a batch's verifier randomness
has at most K^N times its probability. -/
theorem prBRho_preimage_le {N : ℕ} (hN : 0 < N) {s : Shape} {σ : Samplers s} {κ K : ℝ≥0∞}
    (h : σ.Good κ K) {A : RoundSplits s} (S : Set (BRho N s A)) :
    prBRho {ρ : BRho N (s.pull σ) (A.pull σ) | BRho.push σ ρ ∈ S} ≤ K ^ N * prBRho S :=
  pr_preimage_le_mul (BRho.push σ) (cnt_push_le N h.fib A) (WB_mul_card_le hN h A) S

/-! ## 8. Honest-verifier zero knowledge for sets of slots -/

variable {X : Type} {E : ExtSpec} {Wt : Type}

open Classical in
/-- What one slot contributes to the output: nothing for an empty slot, the notice, or the disclosed
view. (See `BatchHonestProver.output`, Iop/Batch.lean.) -/
def slotOut {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (w : Wt) (ox : Option X)
    (ρ : Rho Q.loc.shape) (c : H.Coin0 × H.Coin) : Option (DView Q.loc) :=
  match ox with
  | none => none
  | some xj =>
    if ρ ∈ H.one.withheld w xj then none
    else some (Q.loc.dview xj (H.ext w) ((H.one.strat w xj c).run ρ).1)

theorem output_eq {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {N : ℕ} (w : Wt) (x : Fin N → Option X)
    (ρ : BRho N Q.loc.shape Q.ann) (J : Finset (Fin N)) :
    H.output w x ρ J =
      (unif (H.Coin0 × (Fin N → H.Coin))).map fun c =>
        fun j : J => slotOut H w (x j) (ρ.slot j.1) (c.1, c.2 j) := rfl

theorem slotOut_pull {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (σ : Samplers Q.loc.shape) (w : Wt)
    (ox : Option X) (ρ : Rho (Q.loc.shape.pull σ)) (c : H.Coin0 × H.Coin) :
    slotOut (H.pull σ) w ox ρ c = (slotOut H w ox (Rho.push σ ρ) c).map (DView.pull σ) := by
  classical
  cases ox with
  | none => rfl
  | some xj =>
    by_cases h : Rho.push σ ρ ∈ H.one.withheld w xj
    · have e1 : slotOut (H.pull σ) w (some xj) ρ c = none :=
        if_pos ((mem_one_withheld_pull H σ w xj ρ).2 h)
      have e2 : slotOut H w (some xj) (Rho.push σ ρ) c = none := if_pos h
      rw [e1, e2]
      rfl
    · have e1 : slotOut (H.pull σ) w (some xj) ρ c
          = some ((Q.loc.pull σ).dview xj (H.ext w) (((H.pull σ).one.strat w xj c).run ρ).1) :=
        if_neg fun hm => h ((mem_one_withheld_pull H σ w xj ρ).1 hm)
      have e2 : slotOut H w (some xj) (Rho.push σ ρ) c =
          some (Q.loc.dview xj (H.ext w) ((H.one.strat w xj c).run (Rho.push σ ρ)).1) := if_neg h
      rw [e1, e2, one_strat_pull, InteractiveOracleProof.dview_pull]
      exact congrArg (fun t => some (DView.pull σ (Q.loc.dview xj (H.ext w) t)))
        (Strat.run_pull σ (H.one.strat w xj c) ρ)

/-- The output for J at ρ is the image of the output for J at the pushed ρ. -/
theorem output_pull {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) (σ : Samplers Q.loc.shape)
    {N : ℕ} (w : Wt) (x : Fin N → Option X)
    (ρ : BRho N (Q.loc.shape.pull σ) (Q.ann.pull σ)) (J : Finset (Fin N)) :
    (H.pull σ).output w x ρ J =
      (H.output w x (BRho.push σ ρ) J).map fun f j => (f j).map (DView.pull σ) := by
  rw [output_eq, output_eq, PMF.map_comp]
  refine congrArg (fun g => PMF.map g (unif (H.Coin0 × (Fin N → H.Coin)))) ?_
  funext c j
  show slotOut (H.pull σ) w (x j) (ρ.slot j.1) (c.1, c.2 j) =
    (slotOut H w (x j) ((BRho.push σ ρ).slot j.1) (c.1, c.2 j)).map (DView.pull σ)
  rw [slotOut_pull, slot_push]
  rfl

/-- For good samplers, HVZK for sets of slots in the exact form (`BatchHonestProver.HVZK`) is preserved, with
the factor K^N. -/
theorem hvzk_pull {Q : BatchInteractiveOracleProof X E} {H : BatchHonestProver Q Wt} {N : ℕ} {valid : Wt → X → Prop} {z : ℝ≥0∞}
    (h : H.HVZK N valid z) {σ : Samplers Q.loc.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K) :
    (H.pull σ).HVZK N valid (K ^ N * z) := by
  obtain ⟨Sim, hS⟩ := h
  refine ⟨fun J xs ρs a =>
      (Sim J xs (fun j => Rho.push σ (ρs j)) a).map fun f j => (f j).map (DView.pull σ),
    fun w x hv J xs hxs => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- no slot: the output is the empty function
    haveI : IsEmpty J := ⟨fun j => j.1.elim0⟩
    unfold prBRho
    refine le_trans
      (pr_mono _ (fun ρ hρ => (hρ (BatchOne.pmf_subsingleton _ _)).elim : _ ⊆ (∅ : Set _))) ?_
    simp
  · have hb : K ^ N *
          prBRho {ρ | H.output w x ρ J ≠
              Sim J xs (fun j => ρ.slot j.1) (Q.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w))} ≤
        J.card * (K ^ N * z) := by
      calc _ ≤ K ^ N * (J.card * z) := by gcongr; exact hS w x hv J xs hxs
        _ = J.card * (K ^ N * z) := by ring
    refine le_trans (le_trans (pr_mono _ ?_) (prBRho_preimage_le hN hσ _)) hb
    intro ρ hρ heq
    apply hρ
    rw [output_pull, heq]
    have e : (fun j : J => (BRho.push σ ρ).slot j.1) = fun j : J => Rho.push σ (ρ.slot j.1) :=
      funext fun j => slot_push j.1 σ ρ
    rw [e]
    rfl

end BatchPull

/-! ## 9. The record of protocols -/

open BatchPull in
/-- For good samplers: `BatchProtocol.Props` is preserved, with the numbers `LH.Nums.pullB`. -/
theorem pullPropsB : Spec.pullPropsB := by
  intro I X L Ryes Rno M σT σL σB κ K hT hL hB h
  exact
    { sub := h.sub
      wired := ⟨h.wired.dec_enc, h.wired.extT, h.wired.extL, h.wired.extB⟩
      sound :=
        ⟨let ⟨ε, hb, hs⟩ := h.sound.sndT; ⟨Err.pull σT ε, hb.pull hT, hs.pull hT.fib⟩,
         let ⟨ε, hb, hs⟩ := h.sound.sndL; ⟨Err.pull σL ε, hb.pull hL, hs.pull hL.fib⟩,
         let ⟨ε, hb, hs⟩ := h.sound.sndB; ⟨Err.pull σB ε, hb.pull hB, sndBL_pull hB.fib hs⟩⟩
      reads :=
        ⟨fun x ρ => h.reads.cntT x (Rho.push σT ρ), fun x ρ => h.reads.cntLp x (Rho.push σL ρ),
         fun x ρ => h.reads.cntLc x (Rho.push σL ρ), readsAtMost_pull σB h.reads.cntB, h.reads.hidE⟩
      hidden := ⟨h.hidden.hidT.pull hT, h.hidden.hidL.pull hL, hvzk_pull h.hidden.hidB hB⟩
      complete :=
        ⟨h.complete.accT.pull σT, h.complete.accL.pull σL, acc_pull h.complete.accB σB,
         fun w x => L.honestOfflineProver.prRho_withheld_pull hT w x (h.complete.prT w x),
         fun w x => L.honestLinkProver.prRho_withheld_pull hL w x (h.complete.prL w x),
         fun w x hv => prRho_one_withheld_pull L.honestOnlineBatchProver hB w x (h.complete.prB w x hv)⟩
      localT := h.localT.pull σT
      localL := h.localL.pull σL
      localB := h.localB.pull σB
      cohB := coherent_pull σB h.cohB
      pointT := h.pointT.map (Shape.IsPoint.pull σT)
      pointL := h.pointL.map (Shape.IsPoint.pull σL)
      pointB := h.pointB.map (Shape.IsPoint.pull σB) }

end Iop
