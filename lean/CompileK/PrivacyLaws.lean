-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/PrivacyLaws.lean: the chain "object with honest-verifier zero knowledge as a whole, then
the compiler" for a wider class of simulators: any index-free laws of the three kinds of runs.

Definitions, statements, proofs.
CompileK/PrivacyWhole.lean and CompileK/WholePull.lean take HVZKWhole
for the named simulator simWhole L Sm i₀: encodings of a fixed index, and a triple Sm of run
simulators, each of which is handed the encodings at the verifier's positions only (exactly:
`kerOf`). A simulator of the whole object need not have that form.
Nothing in the two proofs uses the form.

Main names:
  `SimLaws L`, `SimLaws.sim`: a simulator given by arbitrary laws of what is shown of the three
    kinds of runs, and symbols in the place of an encoded index, as functions of "encoding
    randomness" that it draws when asked. By type no index; of a session: J and the instances of J.
    simWhole is the case `simLawsOf`.
  `simBKOf W p Vl`: the compiled simulator around such laws: the term simBKGr of
    Compile/Batch/SpecPubGr.lean with the game of the star at these laws (`simBKGr_eq`: by
    definition).
  `privacyLaws : Spec.privacyLaws`: under the hypotheses of its statement, HVZKWhole L Ryes
    (starBounds L leaves s1) Vl.sim z ⇒ index privacy of argBKE with simBKOf W p Vl and ζ =
    zetaWhole p hb z.
  `KerLaws L`, `KerLaws.toLaws`, `KerLaws.pull`: laws in kernel form: the verifier's randomness of
    a run is uniform, what else is shown has a law that depends on it; the kernels at the pushed
    verifier messages. simWhole is the case `kerOf`.
  `hvzk_pull_ker : Spec.hvzk_pull_ker`: under the hypotheses of its statement, HVZKWhole is kept
    when verifier messages are made by samplers, for simulators in kernel form; the factor of
    CompileK/WholePull.lean.
  `simulatorKOf D V`: the compiled simulator around laws in kernel form
    (`simulatorK_eq`: simulatorK D Sm is the case kerOf).



Limits: this is still not "for every Hiop.Simulator". privacyLaws asks that the simulator keep
"encoding randomness" as the real side does and answer each run by a law that depends on it alone
(no other memory between runs); hvzk_pull_ker asks moreover that the verifier's randomness of each
simulated run be uniform, which is what "honest-verifier" suggests but the type Hiop.Simulator does
not force. The limits in the headers of these two files and of CompileK/WholePullMain.lean hold too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.WholePullMain

set_option autoImplicit false

noncomputable section

namespace Hiop
open Prob Iop Rom Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type}

/-! ## Part 1. Simulators that are given by laws of the three kinds of runs -/

/-- Index-free laws: what is shown of the three kinds of runs, and the symbols in the place of an
encoded index, as functions of "encoding randomness". No index occurs; of a session: J and the
instances of J. -/
structure SimLaws (L : BatchProtocol I X) where
  T  : L.EncodingRandomness → PMF (Sess L.offline)
  Lk : L.EncodingRandomness → L.EncodingRandomness → PMF (Sess L.link)
  B  : L.EncodingRandomness → (J : Finset (Fin L.maxBatchSize)) → (J → X) → PMF (BSess L.onlineBatch J)
  y  : L.EncodingRandomness → Fin L.wordLength → L.Symbol

variable {L : BatchProtocol I X}

/-- The simulator: it draws the randomness in the place of each encoded index when that is asked
for, and answers each request by the law of the run. -/
def SimLaws.sim (V : SimLaws L) : Simulator L where
  σ := ℕ × (ℕ → L.EncodingRandomness)
  off := (unif L.EncodingRandomness).bind fun r => (V.T r).map fun a => (a, (0, fun _ => r))
  fresh := fun s =>
    (unif L.EncodingRandomness).bind fun r =>
      (V.Lk (s.2 0) r).map fun a => (a, (s.1 + 1, Function.update s.2 (s.1 + 1) r))
  session := fun s e J xs => (V.B (s.2 e) J xs).map fun a => (a, s)
  read := fun s e p => PMF.pure (V.y (s.2 e) p, s)

def SimLaws.laws (V : SimLaws L) : Laws L := ⟨V.T, V.Lk, fun r J xs _ => V.B r J xs, V.y⟩

theorem SimLaws.host_eq (V : SimLaws L) : V.sim.host = V.laws.host := rfl

/-- the laws of the simulator simWhole -/
def simLawsOf (L : BatchProtocol I X) (Sm : Sims L) (i₀ : I) : SimLaws L where
  T := fun r => simSess L.offline Sm.T () (L.encodeIndex i₀ r)
  Lk := fun r r' => simSess L.link Sm.Lk () (L.encodeIndex i₀ r, L.encodeIndex i₀ r')
  B := fun r J xs => simBsess L.onlineBatch Sm.B J xs (L.encodeIndex i₀ r)
  y := fun r p => L.encodeIndex i₀ r p

theorem simWhole_eq (L : BatchProtocol I X) (Sm : Sims L) (i₀ : I) :
    simWhole L Sm i₀ = (simLawsOf L Sm i₀).sim := rfl

/-- the game of the star with these laws -/
def SimLaws.world (V : SimLaws L) (S : OSpec) (m : ℕ) : World S (LifeOutB X) (LifeInB L) :=
  StarWB V.T V.Lk (fun r J xs _ => V.B r J xs) S m

theorem simWorldB_eq (S : OSpec) (L : BatchProtocol I X) (m : ℕ) (Sm : Sims L) (i₀ : I) :
    simWorldB S L m Sm i₀ = (simLawsOf L Sm i₀).world S m := rfl

/-- The lifetime statement of the star from honest-verifier zero knowledge of the whole object, for
a simulator given by any index-free laws. (not all hypotheses are named here: see the statement
below) -/
theorem Star.lifeStar_of_laws (S : OSpec) (L : BatchProtocol I X) (Ryes : I → X → Prop) (m s1 : ℕ)
    (V : SimLaws L) (z : ℝ≥0∞) (h : HVZKWhole L Ryes (Star.starBounds L m s1) V.sim z) (i : I)
    (α : Type) (B : Adv S (LifeOutB X) (LifeInB L) α) (n : ℕ)
    (hB : LifeAdmB (Ryes i) s1 B (fun _ => 0) false n) :
    tv ((interact (LifeB S L m i) B (none, Table.empty S)).map Prod.fst)
        ((interact (V.world S m) B (none, Table.empty S)).map Prod.fst) ≤ z := by
  unfold LifeB SimLaws.world
  rw [Star.run_pre _ _ _ (fun s e p => PMF.pure (L.encodeIndex i (s.2 e) p, s)) B _ _ n hB,
    Star.run_pre _ _ _ (fun s e p => PMF.pure (V.y (s.2 e) p, s)) B _ _ n hB, ← Star.realHost_eq]
  exact h i α _ fun a => Star.adm_pre B _ n a hB

end Hiop

namespace Compile.Batch
open Iop Rom Prob ZKCP Compile.GenMap Compile.GenPub Hiop
open Compile.GlueB (GCall SCall GAdm asW realW simOf viaCP Close)
open Compile.BatchLife (LifeOutB LifeInB LifeB LifeAdmB Sims simWorldB)
open scoped ENNReal

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## Part 2. The compiled simulator around any such laws; index privacy -/

/-- The compiled simulator around index-free laws of the three runs: simBPGr
(Compile/Batch/SpecPubGr.lean) with the game of the star at these laws. -/
def simBPOf [Inhabited V] (W : QueryLayout lam L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vl : SimLaws L) :
    Gen.Simulator (spec lam W.K L) Unit V X (Prf lam L) :=
  simOf Unit ((WrBP W p pw (Vl.world _ p.leaves)).pre (ghost W))
    (iniBP W p pw _ (none, Table.empty _))

def simBKOf (W : QueryLayout lam L) (p : Params) (Vl : SimLaws L) :
    Gen.Simulator (spec lam W.K L) Unit (IVKK lam L) X (PrfK lam L) :=
  pushSim stripK (simBPOf W p (fun v key => (v, linksOf key)) Vl)

theorem simBKGr_eq (W : QueryLayout lam L) (p : Params) (Sm : Sims L) (i₀ : I) :
    simBKGr W p Sm i₀ = simBKOf W p (simLawsOf L Sm i₀) := rfl

theorem closePubLaws (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    (Ryes Rno : I → X → Prop) (hsub : ∀ i x, Ryes i x → Rno i x) (hwd : L.Wired)
    (hC : L.onlineBatch.ann.Coherent) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt)
    (Vl : SimLaws L) (z : ℝ≥0∞)
    (hz : HVZKWhole L Ryes (Hiop.Star.starBounds L p.leaves p.s1) Vl.sim z) (B : ℕ) (hB : B ≤ L.maxBatchSize)
    {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B hb) :
    Close (relPair Ryes Rno hsub) (argBPGT W WP p pw (PpU W WP p) Vf) B
      (asW Unit (WrBP W p pw (Vl.world _ p.leaves)))
      (iniBP W p pw _ (none, Table.empty _)) (zetaWhole p hb z) := by
  intro i α A t n hA hP
  refine le_trans
    (tv_triangle _
      ((interact (asW Unit (WrBP W p pw (LifeB _ L p.leaves i))) A
        (iniBP W p pw _ (none, Table.empty _))).map Prod.fst) _)
    (add_le_add
      (realToWrBPUTOf W WP p pw Vf i hwd hC hF hW hG hWP B hB hh _ (fun b hb => hb.1) A t n hA hP)
      ?_)
  have hBeq : ∀ (G : LifeWB W) (s : G.σ),
      (interact (asW Unit (WrBP W p pw G)) A (iniBP W p pw G s)).map Prod.fst =
        (interact G ((wrapGP W p pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) (PpW W p)).adv
              A (none, LSt.init _)) s).map Prod.fst :=
    fun G s =>
      interact_adv (wrapGP W p pw (fun sT ls => CpW W p sT (ls.take (p.M + 1))) (PpW W p)) G A _ s
  rw [hBeq, hBeq]
  exact Hiop.Star.lifeStar_of_laws _ L Ryes p.leaves p.s1 Vl z hz i α _ n
    (lifeAdmB_wrapGP W p pw _ _ (Ryes i) A n
      (gAdm_mono (fun b hb => ⟨hb.1.trans hB, hb.2⟩) A false n hP))

theorem privacyPubLaws [Inhabited V] (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (pw : IVK lam L → WKey lam L → V) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    (Ryes Rno : I → X → Prop) (hsub : ∀ i x, Ryes i x → Rno i x) (hwd : L.Wired)
    (hC : L.onlineBatch.ann.Coherent) (hW : W.OKG) (hG : GrFitPB W) (hWP : WP.OK) (hF : L.onlineBatch.ann.Fmt)
    (Vl : SimLaws L) (z : ℝ≥0∞)
    (hz : HVZKWhole L Ryes (Hiop.Star.starBounds L p.leaves p.s1) Vl.sim z) (B : ℕ) (hB : B ≤ L.maxBatchSize)
    {hb : ℕ → ℕ → ℝ≥0∞} (hh : HopU W p B hb) :
    Gen.HasIndexPrivacyWith (relPair Ryes Rno hsub) (argBPG W WP p pw (PpU W WP p) Vf) B
      (simBPOf W p pw Vl) (zetaWhole p hb z) := by
  refine GlueB.gluePrivacyWith _ _ _ _ Unit _ _ _ _ _ _
    ((WrBP W p pw (Vl.world _ p.leaves)).pre (ghost W)) (iniBP W p pw _ (none, Table.empty _)) _
    (Rom.viaConsistent _ _ _ _ _ (ghostPerm I X lam L W) _ (consistent_wrapBP _)) ?_
  rw [argBPG_via W WP p pw (PpU W WP p) Vf hW (routedF_PpU W WP p hW)]
  exact GlueB.closeVia _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ghostPerm I X lam L W)
    (closePubLaws W WP p pw Vf Ryes Rno hsub hwd hC hW hG hWP hF Vl z hz B hB hh)

/-- the statement of `privacyLaws` -/
def Spec.privacyLaws : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Prop) (hsub : ∀ i x, Ryes i x → Rno i x),
    L.Wired → L.onlineBatch.ann.Coherent → L.onlineBatch.ann.Fmt → W.OKG → GrFitPB W → WP.OK →
    ∀ (Vl : SimLaws L) (z : ℝ≥0∞),
      HVZKWhole L Ryes (Hiop.Star.starBounds L p.leaves p.s1) Vl.sim z →
      ∀ (B : ℕ), B ≤ L.maxBatchSize →
        ∀ hb : ℕ → ℕ → ℝ≥0∞, HopU W p B hb →
          Gen.HasIndexPrivacyWith (relPair Ryes Rno hsub) (argBKE W WP p) B
            (simBKOf W p Vl) (zetaWhole p hb z)

/-- Index privacy of the compiled argument from honest-verifier zero knowledge of the whole object,
for a simulator given by any index-free laws of the three runs. (not all hypotheses are named here:
see `Spec.privacyLaws`) -/
theorem privacyLaws : Spec.privacyLaws :=
  fun _ _ _ _ W WP p Ryes Rno hsub hwd hC hF hW hG hWP Vl z hz B hB _ hh =>
    GenMap.privacyWith (via_KE W WP p)
      _ (privacyPubLaws W WP p _ _ Ryes Rno hsub hwd hC hW hG hWP hF Vl z hz B hB hh)

end Compile.Batch

/-! ## Part 3. Laws in the form "uniform verifier randomness, then a kernel"; through the samplers
-/

namespace Hiop
open Prob Iop Rom Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {L : BatchProtocol I X}

/-- Index-free laws in kernel form: the verifier's randomness of a run is uniform; what else is
shown of the run has a law that depends on it (for a session: on the verifier messages of the slots
shown). -/
structure KerLaws (L : BatchProtocol I X) where
  kT : L.EncodingRandomness → Rho L.offline.shape → PMF (Option (DView L.offline))
  kL : L.EncodingRandomness → L.EncodingRandomness → Rho L.link.shape → PMF (Option (DView L.link))
  kB : L.EncodingRandomness → (J : Finset (Fin L.maxBatchSize)) → (J → X) →
    (J → Rho L.onlineBatch.loc.shape) → PMF (J → Option (DView L.onlineBatch.loc))
  y  : L.EncodingRandomness → Fin L.wordLength → L.Symbol

def KerLaws.toLaws (V : KerLaws L) : SimLaws L where
  T := fun r => (unif (Rho L.offline.shape)).bind fun ρ => (V.kT r ρ).map fun o => (ρ, o)
  Lk := fun r r' => (unif (Rho L.link.shape)).bind fun ρ => (V.kL r r' ρ).map fun o => (ρ, o)
  B := fun r J xs =>
    (unif (BRho L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann)).bind fun ρ =>
      (V.kB r J xs (Pull.vis _ _ J ρ)).map fun o => (Pull.vis _ _ J ρ, o)
  y := V.y

/-- the kernels of simWhole -/
def kerOf (L : BatchProtocol I X) (Sm : Sims L) (i₀ : I) : KerLaws L where
  kT := fun r ρ => Sm.T () ρ (L.offline.extAns () ρ (L.encodeIndex i₀ r))
  kL := fun r r' ρ => Sm.Lk () ρ (L.link.extAns () ρ (L.encodeIndex i₀ r, L.encodeIndex i₀ r'))
  kB := fun r J xs ρs => Sm.B J xs ρs (L.onlineBatch.extAnsJ J xs ρs (L.encodeIndex i₀ r))
  y := fun r p => L.encodeIndex i₀ r p

theorem kerOf_toLaws (L : BatchProtocol I X) (Sm : Sims L) (i₀ : I) :
    (kerOf L Sm i₀).toLaws = simLawsOf L Sm i₀ := rfl

/-- the kernels at the pushed verifier messages, their outputs carried over -/
def KerLaws.pull (V : KerLaws L) (σT : Samplers L.offline.shape)
    (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape) : KerLaws (L.pull σT σL σB) where
  kT := fun r ρ' => (V.kT r (Rho.push σT ρ')).map (Option.map (DView.pull σT))
  kL := fun r r' ρ' => (V.kL r r' (Rho.push σL ρ')).map (Option.map (DView.pull σL))
  kB := fun r J xs ρs' =>
    (V.kB r J xs fun j => Rho.push σB (ρs' j)).map fun f j => (f j).map (DView.pull σB)
  y := V.y

namespace Spec

/-- Honest-verifier zero knowledge of the whole object through the samplers, for a simulator given
by any laws in kernel form. (not all hypotheses are named here: see the statement below) -/
def hvzk_pull_ker : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape)
      (σB : Samplers L.onlineBatch.loc.shape) (κ KT KL KB : ℝ≥0∞),
    σT.Good κ KT → σL.Good κ KL → σB.Good κ KB → KT ≠ ⊤ → 1 ≤ KL → KL ≠ ⊤ →
    1 ≤ KB → KB ≠ ⊤ → 0 < L.maxBatchSize →
    ∀ (Ryes : I → X → Prop) (B : Bounds) (V : KerLaws L) (z : ℝ≥0∞),
      HVZKWhole L Ryes B V.toLaws.sim z →
      HVZKWhole (L.pull σT σL σB) Ryes B (V.pull σT σL σB).toLaws.sim
        (Pull.factor B L.maxBatchSize KT KL KB * z)

end Spec

open Pull in
theorem hvzk_pull_ker : Spec.hvzk_pull_ker := by
  intro I X L σT σL σB κ KT KL KB hT hL hB hTt hL1 hLt hB1 hBt hN Ryes B V z hz i α E' hE'
  have gT : ∀ r,
      Adapts (V.toLaws.laws.T r) ((V.pull σT σL σB).toLaws.laws.T r)
        (adaptQ L.offline σT KT) KT := fun r => by
    have h := adapts_run hTt (den_rho (Q := L.offline) hT) (V.kT r) (Option.map (DView.pull σT))
    have e : (V.pull σT σL σB).toLaws.laws.T r =
        (unif (Rho (L.offline.shape.pull σT))).bind fun ρ' =>
          (V.kT r (Rho.push σT ρ')).map fun o => (ρ', o.map (DView.pull σT)) := by
      show ((unif (Rho (L.offline.shape.pull σT))).bind fun ρ' =>
          ((V.kT r (Rho.push σT ρ')).map (Option.map (DView.pull σT))).map fun o => (ρ', o)) = _
      exact congrArg _ (funext fun ρ' => PMF.map_comp _ _ _)
    rw [e]
    exact h
  have gL : ∀ r r',
      Adapts (V.toLaws.laws.Lk r r') ((V.pull σT σL σB).toLaws.laws.Lk r r')
        (adaptQ L.link σL KL) KL := fun r r' => by
    have h := adapts_run hLt (den_rho (Q := L.link) hL) (V.kL r r') (Option.map (DView.pull σL))
    have e : (V.pull σT σL σB).toLaws.laws.Lk r r' =
        (unif (Rho (L.link.shape.pull σL))).bind fun ρ' =>
          (V.kL r r' (Rho.push σL ρ')).map fun o => (ρ', o.map (DView.pull σL)) := by
      show ((unif (Rho (L.link.shape.pull σL))).bind fun ρ' =>
          ((V.kL r r' (Rho.push σL ρ')).map (Option.map (DView.pull σL))).map fun o => (ρ', o)) = _
      exact congrArg _ (funext fun ρ' => PMF.map_comp _ _ _)
    rw [e]
    exact h
  have gB : ∀ r J xs rest,
      Adapts (V.toLaws.laws.B r J xs rest) ((V.pull σT σL σB).toLaws.laws.B r J xs rest)
        (adaptB L.onlineBatch σB (KB ^ L.maxBatchSize) J) (KB ^ L.maxBatchSize) := fun r J xs _ => by
    have h := adapts_of_vis (Q := L.onlineBatch) hN hB hBt J (V.kB r J xs)
    have e : (V.pull σT σL σB).toLaws.laws.B r J xs (fun _ => none) = (unif (BRho L.maxBatchSize (L.onlineBatch.loc.shape.pull σB) (L.onlineBatch.ann.pull σB))).bind fun ρ' =>
        (V.kB r J xs (vis _ _ J (BRho.push σB ρ'))).map fun o =>
            (vis _ _ J ρ', fun j => (o j).map (DView.pull σB)) := by
      show ((unif (BRho L.maxBatchSize (L.onlineBatch.loc.shape.pull σB) (L.onlineBatch.ann.pull σB))).bind fun ρ' =>
          ((V.kB r J xs fun j => Rho.push σB (vis _ _ J ρ' j)).map fun f j =>
              (f j).map (DView.pull σB)).map
            fun o => (vis _ _ J ρ', o)) = _
      refine congrArg _ (funext fun ρ' => ?_)
      rw [vis_push (Q := L.onlineBatch)]
      exact PMF.map_comp _ _ _
    exact e ▸ h
  have h := tv_view_pull (AdT := adaptQ L.offline σT KT) (AdL := adaptQ L.link σL KL)
    (AdB := fun J => adaptB L.onlineBatch σB (KB ^ L.maxBatchSize) J) (KT := KT) (KL := KL) (KB := KB ^ L.maxBatchSize)
    (realLaws L i) V.toLaws.laws (realLaws (L.pull σT σL σB) i) (V.pull σT σL σB).toLaws.laws
    hL1 hLt (one_le_pow₀ hB1) (ENNReal.pow_ne_top hBt)
    (fun r => adapts_sess L.honestOfflineProver hT hTt (i, r) ()) (fun r r' => adapts_sess L.honestLinkProver hL hLt (i, r, r') ())
    (fun r J xs rest => adapts_bsess L.honestOnlineBatchProver hN hB hBt (i, r) (vec J xs rest) J)
    (fun _ _ => rfl) gT gL gB (fun _ _ => rfl)
    E' B.nenc B.total (fun u => by
      have := runsLe_of_adm (E' u) 0 _ _ (hE' u) (Nat.zero_le _)
      rwa [Nat.sub_zero, left_zero] at this)
  have hadm : ∀ u,
      (trE (adaptQ L.offline σT KT) (adaptQ L.link σL KL) (fun J => adaptB L.onlineBatch σB (KB ^ L.maxBatchSize) J) KL
          (KB ^ L.maxBatchSize) E' B.nenc B.total u).Adm
        B (Ryes i) 0 (fun _ => 0) fun _ => 0 := by
    intro u
    unfold trE
    intro o
    cases o with
    | none => trivial
    | some u' => exact adm_tr _ _ _ _ (E' u') _ _ _ _ _ (hE' u')
  exact h.trans (mul_le_mul_right (hz i (Option α) _ hadm) _)

end Hiop

/-! ## Part 4. The compiler's theorem for such simulators -/

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw Hiop
open scoped ENNReal

variable {I X : Type} {L₀ : BatchProtocol I X} {lam : ℕ}

/-- The simulator around index-free laws in kernel form of the interface before the blocks -/
def simulatorKOf (D : DataK L₀ lam) (V : KerLaws L₀) :
    Gen.Simulator (spec lam D.W.K D.L) Unit (IVKK lam D.L) X (PrfK lam D.L) :=
  simBKOf D.W D.p
    (V.pull (Samplers.ofDraws _ D.dr.T) (Samplers.ofDraws _ D.dr.Lk)
      (Samplers.ofDraws _ D.dr.B)).toLaws

theorem simulatorK_eq (D : DataK L₀ lam) (Sm : Compile.BatchLife.Sims L₀) :
    simulatorK D Sm = simulatorKOf D (kerOf L₀ Sm D.i₀) := rfl

end Compile.Batch
