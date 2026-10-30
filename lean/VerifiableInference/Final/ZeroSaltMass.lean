-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/ZeroSaltMass.lean: the chance that the honest side's offline or online run has a first salt in a given set.

1.  WHAT IS CLAIMED: at every honest side, over the committer's and the prover's coins, under every hash function: the key's offline proof
    and the online proof have a first salt in Zs with chance at most that read off each run's coins. At honestSide that is 2^-sFS for each
    run, for any provers and settings, where Zs holds at most one string of sFS bits.
2.  WHY: at the salt of 32 zero bytes the byte parser refuses the honest proof, so completeness pays this mass (CompleteUpTo.lean;
    Johnson/CompletenessAndZeroKnowledge/UndoUpToOfBut.lean).
3.  HOW: Small g Q ε c: on the paths that the oracles g answer, the program c ends with Q only behind a set of branches of one sample that has
    chance at most ε.
-/
import VerifiableInference.Final.CompileHandsNoProof
import Johnson.CompletenessAndZeroKnowledge.BadExp
import OnBytes.Prover.Nonces

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.FrontRoad OnBytes.PublicAt VerifiableInference.OnPublicFiles ZKCP.PublicRead
open AtPublicFiles.Bridge (pickAll pickAll_ok winR winK winJ)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- By hand: instance search times out here. -/
local instance finSuccNonempty (n : ℕ) : Nonempty (Fin (n + 1)) := ⟨0⟩
local instance bitsNonempty (n : ℕ) : Nonempty (Fin n → Bool) := ⟨fun _ => false⟩

/-! ## 1 Few paths -/

section Small
variable {S : OSpec} {α β : Type}

theorem Ends.mono {Q Q' : α → Prop} (h : ∀ a, Q a → Q' a) : ∀ c : Rom.OComp S α, Ends Q c → Ends Q' c
  | .pure a, e => h a e
  | .query _ _ k, e => fun r => Ends.mono h (k r) (e r)
  | .sample _ k, e => fun r => Ends.mono h (k r) (e r)

/-- Every path on which the oracles answer as g does ends in a value with Q. -/
def EndsAt (g : Fam S) (Q : α → Prop) : Rom.OComp S α → Prop
  | .pure a => Q a
  | .query o q k => EndsAt g Q (k (g o q))
  | .sample _ k => ∀ r, EndsAt g Q (k r)

theorem Ends.at (g : Fam S) {Q : α → Prop} : ∀ c : Rom.OComp S α, Ends Q c → EndsAt g Q c
  | .pure _, h => h
  | .query o q k, h => Ends.at g (k (g o q)) (h _)
  | .sample _ k, h => fun r => Ends.at g (k r) (h r)

theorem EndsAt.bind {g : Fam S} {Q' : α → Prop} {Q : β → Prop} {f : α → Rom.OComp S β} (hf : ∀ a, Q' a → EndsAt g Q (f a)) :
    ∀ c : Rom.OComp S α, EndsAt g Q' c → EndsAt g Q (c.bind f)
  | .pure a, h => hf a h
  | .query o q k, h => EndsAt.bind hf (k (g o q)) h
  | .sample _ k, h => fun r => EndsAt.bind hf (k r) (h r)

theorem EndsAt.mono {g : Fam S} {Q Q' : α → Prop} (h : ∀ a, Q a → Q' a) : ∀ c : Rom.OComp S α, EndsAt g Q c → EndsAt g Q' c
  | .pure a, e => h a e
  | .query o q k, e => EndsAt.mono h (k (g o q)) e
  | .sample _ k, e => fun r => EndsAt.mono h (k r) (e r)

/-- A program without coins ends at its value. -/
theorem endsAt_of_det {g : Fam S} {Q : α → Prop} : ∀ c : Rom.OComp S α, c.NoCoin → Q (c.det g) → EndsAt g Q c
  | .pure _, _, h => h
  | .query o q k, hc, h => endsAt_of_det (k (g o q)) (hc _) h
  | .sample _ _, hc, _ => hc.elim

/-- On the paths that g answers, a path ends with Q only behind branches of one sample that have chance at most ε. -/
inductive Small (g : Fam S) (Q : α → Prop) (ε : ℝ≥0∞) : Rom.OComp S α → Prop
  | none {c : Rom.OComp S α} (h : EndsAt g (fun a => ¬ Q a) c) : Small g Q ε c
  | query {o : S.ι} {q : S.Dom o} {k : S.Rng o → Rom.OComp S α} (h : Small g Q ε (k (g o q))) :
      Small g Q ε (.query o q k)
  | sample {n : ℕ} {k : Fin (n + 1) → Rom.OComp S α} (h : ∀ r, Small g Q ε (k r)) :
      Small g Q ε (.sample n k)
  | few {n : ℕ} {k : Fin (n + 1) → Rom.OComp S α} (B : Set (Fin (n + 1))) (hB : pr (unif (Fin (n + 1))) B ≤ ε)
      (h : ∀ r, r ∉ B → EndsAt g (fun a => ¬ Q a) (k r)) : Small g Q ε (.sample n k)

/-- A smaller event has no more chance. -/
theorem Small.weaken {g : Fam S} {Q Q' : α → Prop} {ε : ℝ≥0∞} {c : Rom.OComp S α} (hq : ∀ a, Q a → Q' a)
    (h : Small g Q' ε c) : Small g Q ε c := by
  induction h with
  | none e => exact .none (EndsAt.mono (fun a ha hq' => ha (hq a hq')) _ e)
  | query _ ih => exact .query ih
  | sample _ ih => exact .sample ih
  | few B hB e => exact .few B hB fun r hr => EndsAt.mono (fun a ha hq' => ha (hq a hq')) _ (e r hr)

/-- Behind a program: at every value of the program. -/
theorem Small.behind {g : Fam S} {Q : β → Prop} {ε : ℝ≥0∞} {f : α → Rom.OComp S β} (h : ∀ a, Small g Q ε (f a)) :
    ∀ c : Rom.OComp S α, Small g Q ε (c.bind f)
  | .pure a => h a
  | .query o q k => .query (Small.behind h (k (g o q)))
  | .sample _ k => .sample fun r => Small.behind h (k r)

/-- In front of a program that keeps the event out where it was out. -/
theorem Small.before {g : Fam S} {Q : α → Prop} {Q' : β → Prop} {ε : ℝ≥0∞} {f : α → Rom.OComp S β} {c : Rom.OComp S α}
    (hf : ∀ a, ¬ Q a → EndsAt g (fun b => ¬ Q' b) (f a)) (h : Small g Q ε c) : Small g Q' ε (c.bind f) := by
  induction h with
  | none e => exact .none (EndsAt.bind hf _ e)
  | query _ ih => exact .query ih
  | sample _ ih => exact .sample ih
  | few B hB e => exact .few B hB fun r hr => EndsAt.bind hf _ (e r hr)

end Small

section OneHash
variable {S : OSpec} {lam : ℕ} {α : Type}

/-- One hash function as the family of the oracle over it. -/
def hashFam (f : ZKCP.Oracle lam) : Fam (rom lam) := fun _ q => f q

/-- The family of typed oracles that an encoding reads off one hash function. -/
def famOver (m : OracleCoding S lam) (f : ZKCP.Oracle lam) : Fam S :=
  fun o q => (m.rng o).symm fun i => f (m.code o q i)

theorem askAll_endsAt (f : ZKCP.Oracle lam) {Q : α → Prop} : ∀ (n : ℕ) (pts : Fin n → List Bool)
    (k : (Fin n → Fin lam → Bool) → Rom.OComp (rom lam) α), EndsAt (hashFam f) Q (k fun i => f (pts i)) →
      EndsAt (hashFam f) Q ((askAll lam n pts).bind k)
  | 0, pts, k, h => by
    have e : (fun i : Fin 0 => f (pts i)) = fun i => i.elim0 := funext fun i => i.elim0
    rw [e] at h
    exact h
  | n + 1, pts, k, h => by
    show EndsAt (hashFam f) Q (((askAll lam n fun i => pts i.succ).bind fun rest =>
      .pure (Fin.cons (α := fun _ => Fin lam → Bool) (f (pts 0)) rest)).bind k)
    rw [OComp.bind_assoc]
    refine askAll_endsAt f n _ _ ?_
    have e : (Fin.cons (α := fun _ => Fin lam → Bool) (f (pts 0)) fun i => f (pts i.succ)) = fun i => f (pts i) :=
      funext fun i => Fin.cases rfl (fun _ => rfl) i
    show EndsAt (hashFam f) Q (k (Fin.cons (α := fun _ => Fin lam → Bool) (f (pts 0)) fun i => f (pts i.succ)))
    rw [e]
    exact h

theorem askAll_small (f : ZKCP.Oracle lam) {Q : α → Prop} {ε : ℝ≥0∞} : ∀ (n : ℕ) (pts : Fin n → List Bool)
    (k : (Fin n → Fin lam → Bool) → Rom.OComp (rom lam) α), Small (hashFam f) Q ε (k fun i => f (pts i)) →
      Small (hashFam f) Q ε ((askAll lam n pts).bind k)
  | 0, pts, k, h => by
    have e : (fun i : Fin 0 => f (pts i)) = fun i => i.elim0 := funext fun i => i.elim0
    rw [e] at h
    exact h
  | n + 1, pts, k, h => by
    refine .query ?_
    show Small (hashFam f) Q ε (((askAll lam n fun i => pts i.succ).bind fun rest =>
      .pure (Fin.cons (α := fun _ => Fin lam → Bool) (f (pts 0)) rest)).bind k)
    rw [OComp.bind_assoc]
    refine askAll_small f n _ _ ?_
    have e : (Fin.cons (α := fun _ => Fin lam → Bool) (f (pts 0)) fun i => f (pts i.succ)) = fun i => f (pts i) :=
      funext fun i => Fin.cases rfl (fun _ => rfl) i
    show Small (hashFam f) Q ε (k (Fin.cons (α := fun _ => Fin lam → Bool) (f (pts 0)) fun i => f (pts i.succ)))
    rw [e]
    exact h

theorem EndsAt.overOne (m : OracleCoding S lam) (f : ZKCP.Oracle lam) {Q : α → Prop} :
    ∀ c : Rom.OComp S α, EndsAt (famOver m f) Q c → EndsAt (hashFam f) Q (c.overOne m)
  | .pure _, h => h
  | .sample _ k, h => fun r => EndsAt.overOne m f (k r) (h r)
  | .query o q k, h => askAll_endsAt f _ _ _ (EndsAt.overOne m f (k (famOver m f o q)) h)

theorem Small.overOne (m : OracleCoding S lam) (f : ZKCP.Oracle lam) {Q : α → Prop} {ε : ℝ≥0∞} {c : Rom.OComp S α}
    (h : Small (famOver m f) Q ε c) : Small (hashFam f) Q ε (c.overOne m) := by
  induction h with
  | none e => exact .none (EndsAt.overOne m f _ e)
  | @query o q k _ ih => exact askAll_small f _ _ _ ih
  | sample _ ih => exact .sample ih
  | few B hB e => exact .few B hB fun r hr => EndsAt.overOne m f _ (e r hr)

theorem prob_zero_of_endsAt {Q : α → Prop} (f : ZKCP.Oracle lam) : ∀ c : Rom.OComp (rom lam) α,
    EndsAt (hashFam f) (fun a => ¬ Q a) c → ZKCP.prob ((Rom.ofRom c).run f) {a | Q a} = 0
  | .pure a, h => (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 (Set.disjoint_left.2 fun b hb hq => by
      have e : b = a := (PMF.mem_support_pure_iff _ _).1 hb
      exact h (e ▸ hq))
  | .query _ q k, h => prob_zero_of_endsAt f (k (f q)) h
  | .sample n k, h => by
    show ZKCP.prob ((unif (Fin (n + 1))).bind fun r => (Rom.ofRom (k r)).run f) _ = 0
    rw [ZKCP.prob_bind]
    refine le_antisymm (le_trans (ZKCP.expect_le_on_support _ fun r _ => ?_)
      (le_of_eq (ZKCP.expect_const _ 0))) (zero_le _)
    exact le_of_eq (prob_zero_of_endsAt f (k r) (h r))

/-- **The chance of the event, under the hash function f.** -/
theorem Small.prob_le {f : ZKCP.Oracle lam} {Q : α → Prop} {ε : ℝ≥0∞} {c : Rom.OComp (rom lam) α}
    (h : Small (hashFam f) Q ε c) : ZKCP.prob ((Rom.ofRom c).run f) {a | Q a} ≤ ε := by
  induction h with
  | none e => exact (prob_zero_of_endsAt f _ e).trans_le (zero_le _)
  | query _ ih => exact ih
  | @sample n k _ ih =>
    show ZKCP.prob ((unif (Fin (n + 1))).bind fun r => (Rom.ofRom (k r)).run f) _ ≤ ε
    rw [ZKCP.prob_bind]
    exact le_trans (ZKCP.expect_le_on_support _ fun r _ => ih r) (le_of_eq (ZKCP.expect_const _ _))
  | @few n k B hB e =>
    show ZKCP.prob ((unif (Fin (n + 1))).bind fun r => (Rom.ofRom (k r)).run f) _ ≤ ε
    rw [ZKCP.prob_bind]
    refine le_trans ?_ hB
    unfold ZKCP.expect pr
    rw [PMF.toOuterMeasure_apply]
    refine ENNReal.tsum_le_tsum fun r => ?_
    beta_reduce
    by_cases hr : r ∈ B
    · rw [Set.indicator_of_mem hr]
      exact mul_le_of_le_one_right' (ZKCP.prob_le_one _ _)
    · rw [prob_zero_of_endsAt f _ (e r hr), mul_zero]
      exact zero_le _

end OneHash

/-! ## 2 The first salt of a compiled run is its coins' -/

section Typed
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
  (h : HonestSide lam L Bd aT aL)

/-- What a run shows stands in its result. -/
theorem shown_some {P' : Type} {s : Shape} {stop : Rho s → Bool} {r : Res (P' × Tr s)} {p : P'}
    (e : shown stop r = some p) : ∃ τ, r = .ok (p, τ) := by
  cases r with
  | ok a =>
    have e' : (if stop a.2.rho then none else some a.1) = some p := e
    split at e'
    · cases e'
    · obtain ⟨a₁, a₂⟩ := a
      cases e'
      exact ⟨a₂, rfl⟩
  | noFormat => cases e
  | ranOut _ => cases e

/-- A compiled run's first salt is its coins'. -/
theorem ends_proveX_salt {K : ℕ} {L' : BatchProtocolWithLeafBody I X} (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L')
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L') (cap : ℕ → ℕ) :
    Ends (fun r : Res (OneProtocolProof lam Q × Tr Q.loc.shape) => ∀ π τ, r = .ok (π, τ) → π.salt = co.salt)
      (proveX t Q wq embS embP xin cms x y xt σ co cap) := by
  refine Ends.bind (Q' := fun _ => True) (fun r _ => ?_) _ (ends_true _)
  intro π τ e
  cases r with
  | ok z =>
    cases e
    rfl
  | noFormat => cases e
  | ranOut _ => cases e

/-- The key's offline proof, if it is shown, has the salt of its coins. -/
theorem ends_commitAt_salt (i : I) (d : DrawC lam L Bd aT aL h.KT h.KL) :
    Ends (fun k => ∀ p, k.1.piT = some p → p.salt = d.co.salt) (commitAt W S cA h i d) := by
  refine Ends.bind (Q' := fun _ => True) (fun t₁ _ => ?_) _ (ends_true _)
  refine Ends.bind (Q' := fun _ => True) (fun ts _ => ?_) _ (ends_true _)
  refine Ends.bind (Q' := fun a => ∀ π τ, a = .ok (π, τ) → π.salt = (h.dressT (h.rvT d.κ) d.co).salt)
    (fun a ha => ?_) _ (ends_proveX_salt _ _ _ _ _ _ _ _ _ _ _ _ _)
  refine Ends.bind (Q' := fun _ => True) (fun ls _ => ?_) _ (ends_true _)
  intro p hp
  obtain ⟨τ, e⟩ := shown_some hp
  exact ha p τ e

/-- The online proof, if it holds a string, has the salt of its coins. -/
theorem ends_proveAt_salt (isk : Isk lam L Bd aT aL) (x : X) (d : DrawP lam L Bd aT aL h.KB) :
    Ends (fun π => ∀ p, π.piB = some p → p.salt = d.co.salt) (proveAt W cA r₀ h isk x d) := by
  unfold proveAt
  split
  · intro p hp
    cases hp
  · refine Ends.bind (Q' := fun a => ∀ π τ, a = .ok (π, τ) → π.salt = (h.dressB (h.rvB d.κ) d.co).salt)
      (fun a ha => ?_) _ (ends_proveX_salt _ _ _ _ _ _ _ _ _ _ _ _ _)
    intro p hp
    obtain ⟨τ, e⟩ := shown_some hp
    exact ha p τ e

/-- **The committer**: the key's offline proof has a first salt in Zs with chance at most that of Zs among the run's coins. -/
theorem small_commitW_salt (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (i : I) (Zs : Set Bits) {ε : ℝ≥0∞}
    (hB : pr (unif (Fin (h.coT.n + 1))) {e | (h.coT.e e).salt ∈ Zs} ≤ ε) :
    Small g (fun k => ∃ p, k.1.piT = some p ∧ p.salt ∈ Zs) ε (commitW W S cA h i) := by
  show Small g _ ε (.sample h.ri.n fun a => .sample h.sl.n fun b => .sample h.kT.n fun c => .sample h.coT.n fun e =>
    ((coinsCopies W h (h.M + 1)).bind fun ds =>
      (.pure ⟨h.ri.e a, h.sl.e b, h.kT.e c, h.coT.e e, ds⟩ : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) _)).bind fun d =>
        commitAt W S cA h i d)
  refine .sample fun a => .sample fun b => .sample fun c => .few _ hB fun e he => ?_
  refine Ends.at g _ (Ends.bind (Q' := fun d : DrawC lam L Bd aT aL h.KT h.KL => d.co = h.coT.e e) (fun d hd => ?_) _ ?_)
  · refine Ends.mono (fun k hk => ?_) _ (ends_commitAt_salt W S cA h i d)
    rintro ⟨p, hp, hz⟩
    refine he ?_
    show (h.coT.e e).salt ∈ Zs
    rw [← hd, ← hk p hp]
    exact hz
  · refine Ends.bind (Q' := fun _ => True) (fun ds _ => ?_) _ (ends_true _)
    exact rfl

/-- **The prover**: the online proof has a first salt in Zs with chance at most that of Zs among the run's coins. -/
theorem small_proveW_salt (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (isk : Isk lam L Bd aT aL) (x : X)
    (Zs : Set Bits) {ε : ℝ≥0∞} (hB : pr (unif (Fin (h.coB.n + 1))) {e | (h.coB.e e).salt ∈ Zs} ≤ ε) :
    Small g (fun πs => ∃ p, (ZKCP.Special.head1 πs).piB = some p ∧ p.salt ∈ Zs) ε
      (proveW W cA r₀ h isk [(x, ())]) := by
  show Small g _ ε (.sample h.M fun j => .sample h.kB.n fun c => .sample h.coB.n fun e =>
    (proveAt W cA r₀ h isk x ⟨j.val, h.kB.e c, h.coB.e e⟩).bind fun π =>
      (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof lam L) [(x, ())])))
  refine .sample fun j => .sample fun c => .few _ hB fun e he => ?_
  refine Ends.at g _ (Ends.bind (Q' := fun π : RequestProof lam L => ∀ p, π.piB = some p → p.salt = (h.coB.e e).salt)
    (fun π hπ => ?_) _ (ends_proveAt_salt W cA r₀ h isk x ⟨j.val, h.kB.e c, h.coB.e e⟩))
  rintro ⟨p, hp, hz⟩
  refine he ?_
  show (h.coB.e e).salt ∈ Zs
  rw [← hπ p hp]
  exact hz

end Typed

/-! ## 3 Over one hash function -/

section Front
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)

/-- The event on the key's offline string and the online string, with two reasons on each. -/
def EitherBad (PT₁ PT₂ : OneProtocolProof 256 (batTC R.protocol R.offlineRoundSplits) → Prop) (PB₁ PB₂ : OneProtocolProof 256 R.protocol.onlineBatch → Prop)
    (k : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) (π : RequestProof 256 R.protocol) : Prop :=
  (∃ a, k.piT = some a ∧ (PT₁ a ∨ PT₂ a)) ∨ ∃ b, π.piB = some b ∧ (PB₁ b ∨ PB₂ b)

theorem prob_readOne_C (i : R.Index) {Qk : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → Prop} {ε : ℝ≥0∞} (f : ZKCP.Oracle 256)
    (hs : ∀ d, Small (famOver (T.m d) f) (fun k : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits => Qk k.1) ε
      (commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i)) :
    ZKCP.prob (((readOne T h).C i).run f) {keys | Qk keys.1.2} ≤ ε := by
  refine Small.prob_le (c := T.Pub.bind fun d => ((toldAt T h d).C i).bind fun k => Rom.OComp.pure (k.1, (d, k.2))) ?_
  refine Small.behind (fun d => ?_) _
  show Small _ _ ε ((((commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i).overOne (T.m d)).bind fun k =>
    Rom.OComp.pure ((T.part d, k.1), k.2)).bind fun k => Rom.OComp.pure (k.1, (d, k.2)))
  refine Small.before (Q := fun k : KeyT R × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits => Qk k.1.2) (fun k hk => ?_) ?_
  · exact hk
  · refine Small.before (Q := fun k : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits => Qk k.1)
      (fun k hk => ?_) (Small.overOne _ f (hs d))
    exact hk

theorem prob_readOne_P (d : T.D) (isk : Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (x : R.Instance) {Qp : RequestProof 256 R.protocol → Prop} {ε : ℝ≥0∞}
    (f : ZKCP.Oracle 256)
    (hs : Small (famOver (T.m d) f) (fun πs : ZKCP.Gen.Slots (RequestProof 256 R.protocol) [(x, ())] => Qp (ZKCP.Special.head1 πs)) ε
      (proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk [(x, ())])) :
    ZKCP.prob (((readOne T h).P (d, isk) x ()).run f) {π | Qp π} ≤ ε := by
  refine Small.prob_le (c := ((proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk [(x, ())]).overOne (T.m d)).bind fun πs =>
    Rom.OComp.pure (ZKCP.Special.head1 πs)) ?_
  refine Small.before (Q := fun πs : ZKCP.Gen.Slots (RequestProof 256 R.protocol) [(x, ())] => Qp (ZKCP.Special.head1 πs))
    (fun πs hπ => ?_) (Small.overOne _ f hs)
  exact hπ

theorem prob_four {α : Type} (p : PMF α) {A B C D E : Set α} {a b c d : ℝ≥0∞} (ha : ZKCP.prob p A ≤ a)
    (hb : ZKCP.prob p B ≤ b) (hc : ZKCP.prob p C ≤ c) (hd : ZKCP.prob p D ≤ d) (h : E ⊆ (A ∪ B) ∪ (C ∪ D)) :
    ZKCP.prob p E ≤ (a + b) + (c + d) :=
  le_trans (MeasureTheory.measure_mono h) (le_trans (MeasureTheory.measure_union_le _ _) (add_le_add
    (le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ha hb))
    (le_trans (MeasureTheory.measure_union_le _ _) (add_le_add hc hd))))

/-- **The mass of the event**, over the honest side's coins. -/
theorem eitherBad_mass (i : R.Index) (x : R.Instance) (PT₁ PT₂ : OneProtocolProof 256 (batTC R.protocol R.offlineRoundSplits) → Prop) (PB₁ PB₂ : OneProtocolProof 256 R.protocol.onlineBatch → Prop)
    {εT₁ εT₂ εB₁ εB₂ : ℝ≥0∞}
    (hT₁ : ∀ g d, Small g (fun k => ∃ a, k.1.piT = some a ∧ PT₁ a) εT₁ (commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i))
    (hT₂ : ∀ g d, Small g (fun k => ∃ a, k.1.piT = some a ∧ PT₂ a) εT₂ (commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i))
    (hB₁ : ∀ g d isk, Small g (fun πs => ∃ b, (ZKCP.Special.head1 πs).piB = some b ∧ PB₁ b) εB₁
      (proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk [(x, ())]))
    (hB₂ : ∀ g d isk, Small g (fun πs => ∃ b, (ZKCP.Special.head1 πs).piB = some b ∧ PB₂ b) εB₂
      (proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk [(x, ())])) :
    ZKCP.Pr (badExp (readOne T h) i x ()) (fun _ => {o | EitherBad PT₁ PT₂ PB₁ PB₂ o.1.1.2 o.2}) ≤
      (εT₁ + εT₂) + (εB₁ + εB₂) := by
  have hp : ∀ f, ZKCP.PrCoins f (badExp (readOne T h) i x ()) {o | EitherBad PT₁ PT₂ PB₁ PB₂ o.1.1.2 o.2} ≤
      (εT₁ + εT₂) + (εB₁ + εB₂) := fun f => by
    have keyPart : ∀ (P' : OneProtocolProof 256 (batTC R.protocol R.offlineRoundSplits) → Prop) (ε : ℝ≥0∞),
        (∀ g d, Small g (fun k => ∃ a, k.1.piT = some a ∧ P' a) ε (commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i)) →
        ZKCP.prob ((badExp (readOne T h) i x ()).run f) {o | o.1 ∈ {keys | ∃ a, keys.1.2.piT = some a ∧ P' a}} ≤ ε :=
      fun P' ε hs => by
        rw [prob_badExp_keys]
        exact prob_readOne_C T h i (Qk := fun k => ∃ a, k.piT = some a ∧ P' a) f fun d => hs _ d
    have proofPart : ∀ (P' : OneProtocolProof 256 R.protocol.onlineBatch → Prop) (ε : ℝ≥0∞),
        (∀ g d isk, Small g (fun πs => ∃ b, (ZKCP.Special.head1 πs).piB = some b ∧ P' b) ε
          (proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk [(x, ())])) →
        ZKCP.prob ((badExp (readOne T h) i x ()).run f) {o | o.2 ∈ {π | ∃ b, π.piB = some b ∧ P' b}} ≤ ε :=
      fun P' ε hs => prob_badExp_proof _ _ _ _ f _ fun keys =>
        prob_readOne_P T h keys.2.1 keys.2.2 x (Qp := fun π => ∃ b, π.piB = some b ∧ P' b) f (hs _ _ _)
    refine prob_four _ (keyPart _ _ hT₁) (keyPart _ _ hT₂) (proofPart _ _ hB₁) (proofPart _ _ hB₂) fun o ho => ?_
    rcases ho with ⟨a, ha, h1 | h2⟩ | ⟨b, hb, h1 | h2⟩
    · exact Or.inl (Or.inl ⟨a, ha, h1⟩)
    · exact Or.inl (Or.inr ⟨a, ha, h2⟩)
    · exact Or.inr (Or.inl ⟨b, hb, h1⟩)
    · exact Or.inr (Or.inr ⟨b, hb, h2⟩)
  calc ZKCP.Pr (badExp (readOne T h) i x ()) (fun _ => {o | EitherBad PT₁ PT₂ PB₁ PB₂ o.1.1.2 o.2})
      ≤ ∫⁻ _, ((εT₁ + εT₂) + (εB₁ + εB₂)) ∂(ZKCP.U 256) := MeasureTheory.lintegral_mono hp
    _ = (εT₁ + εT₂) + (εB₁ + εB₂) := by
      rw [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]

end Front

/-! ## 4 At honestSide -/

variable {I₀ X₀ : Type} {L₀ : HolographicProtocol I₀ X₀}

/-- At abstract types, so that nothing unfolds. -/
theorem pr_fst_le {A Bq : Type} [Fintype A] [Nonempty A] [Fintype Bq] [Nonempty Bq] (P : A → Prop)
    (hP : ∀ a b, P a → P b → a = b) : pr (unif (A × Bq)) {u | P u.1} ≤ (Fintype.card A : ℝ≥0∞)⁻¹ := by
  have h1 : cnt P ≤ 1 := cnt_le_one hP
  have hB0 : (Fintype.card Bq : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hBt : (Fintype.card Bq : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hA0 : (Fintype.card A : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hAt : (Fintype.card A : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [pr_unif_eq (fun u : A × Bq => P u.1), cnt_fst P, Fintype.card_prod]
  push_cast
  rw [ENNReal.div_le_iff (mul_ne_zero hA0 hB0) (ENNReal.mul_ne_top hAt hBt), ← mul_assoc,
    ENNReal.inv_mul_cancel hA0 hAt, one_mul]
  calc (cnt P : ℝ≥0∞) * Fintype.card Bq ≤ 1 * Fintype.card Bq := by
        gcongr
        exact_mod_cast h1
    _ = Fintype.card Bq := one_mul _

theorem pr_enum_eq {β : Type} [Fintype β] [Nonempty β] (E : Enum β) (hE : E.OK) (P : β → Prop) :
    pr (unif (Fin (E.n + 1))) {e | P (E.e e)} = pr (unif β) {u | P u} := by
  rw [← map_unif_of_bijective hE, pr_map]
  rfl

theorem card_bits (n : ℕ) : (Fintype.card (Fin n → Bool) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  rfl

theorem pr_enum_first {Bq : Type} [Fintype Bq] [Nonempty Bq] (n : ℕ) (E : Enum ((Fin n → Bool) × Bq)) (hE : E.OK)
    (Zs : Set Bits) (hZ : ∀ a b : Fin n → Bool, List.ofFn a ∈ Zs → List.ofFn b ∈ Zs → a = b) :
    pr (unif (Fin (E.n + 1))) {e | List.ofFn (E.e e).1 ∈ Zs} ≤ ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  refine le_trans (le_of_eq (pr_enum_eq E hE fun u => List.ofFn u.1 ∈ Zs)) ?_
  rw [← card_bits]
  exact pr_fst_le (fun a : Fin n → Bool => List.ofFn a ∈ Zs) hZ

/-- The coins of a compiled run have a first salt in Zs with chance at most 2^-sFS, where the enumeration lists each member once. -/
theorem pr_coinsPre_salt {I' X' : Type} {lam : ℕ} {L' : BatchProtocolWithLeafBody I' X'} (nR nK nJ sFS ℓ ℓr dq : ℕ) (pad : Body L') (slot : ℕ)
    (fill : Bits) (E : Enum (RunBits lam nR nK nJ sFS ℓ ℓr dq)) (hE : E.OK) (Zs : Set Bits)
    (hZ : ∀ a b : Fin sFS → Bool, List.ofFn a ∈ Zs → List.ofFn b ∈ Zs → a = b) :
    pr (unif (Fin ((coinsPre (L := L') nR nK nJ sFS ℓ ℓr dq pad slot fill E).n + 1)))
        {e | ((coinsPre (L := L') nR nK nJ sFS ℓ ℓr dq pad slot fill E).e e).salt ∈ Zs} ≤ ((2 : ℝ≥0∞) ^ sFS)⁻¹ :=
  pr_enum_first sFS E hE Zs hZ

/-- **At the compiler's own honest side**, for any provers and settings: the offline run. -/
theorem honestSide_salt_offline {offlineRoundMarks : RoundSplits L₀.offline.shape} {linkRoundMarks : RoundSplits L₀.link.shape}
    (w : HashLayout L₀ offlineRoundMarks linkRoundMarks) (provers : HonestProvers L₀) (s : CompiledSettings w provers) (Zs : Set Bits)
    (hZ : ∀ a b : Fin w.compilerParameters.sFS → Bool, List.ofFn a ∈ Zs → List.ofFn b ∈ Zs → a = b) :
    pr (unif (Fin ((honestSide w provers s).coT.n + 1))) {e | ((honestSide w provers s).coT.e e).salt ∈ Zs} ≤
      ((2 : ℝ≥0∞) ^ w.compilerParameters.sFS)⁻¹ :=
  pr_coinsPre_salt (L' := typedOracleCarrier L₀ w.LeafBody offlineRoundMarks linkRoundMarks) (winR (L := L₀))
    (winK w.queryLayout) (winJ w.queryLayout) w.compilerParameters.sFS s.coinNumbers.ℓ s.coinNumbers.ℓr
    w.queryLayout.depthReqT s.coinNumbers.padT s.coinNumbers.slotT s.windowFiller (pickAll _) (pickAll_ok _) Zs hZ

/-- The online run. -/
theorem honestSide_salt_online {offlineRoundMarks : RoundSplits L₀.offline.shape} {linkRoundMarks : RoundSplits L₀.link.shape}
    (w : HashLayout L₀ offlineRoundMarks linkRoundMarks) (provers : HonestProvers L₀) (s : CompiledSettings w provers) (Zs : Set Bits)
    (hZ : ∀ a b : Fin w.compilerParameters.sFS → Bool, List.ofFn a ∈ Zs → List.ofFn b ∈ Zs → a = b) :
    pr (unif (Fin ((honestSide w provers s).coB.n + 1))) {e | ((honestSide w provers s).coB.e e).salt ∈ Zs} ≤
      ((2 : ℝ≥0∞) ^ w.compilerParameters.sFS)⁻¹ :=
  pr_coinsPre_salt (L' := typedOracleCarrier L₀ w.LeafBody offlineRoundMarks linkRoundMarks) (winR (L := L₀))
    (winK w.queryLayout) (winJ w.queryLayout) w.compilerParameters.sFS s.coinNumbers.ℓ s.coinNumbers.ℓr
    w.queryLayout.depthReq s.coinNumbers.padB s.coinNumbers.slotB s.windowFiller (pickAll _) (pickAll_ok _) Zs hZ

/-! ## 5 What the strings' plain parts read -/

/-- What a run shows stands in its result, at messages at which it does not stop. -/
theorem shown_some_stop {P' : Type} {s : Shape} {stop : Rho s → Bool} {r : Res (P' × Tr s)} {p : P'}
    (e : shown stop r = some p) : ∃ τ, r = .ok (p, τ) ∧ stop τ.rho = false := by
  cases r with
  | ok a =>
    have e' : (if stop a.2.rho then none else some a.1) = some p := e
    split at e'
    · cases e'
    · rename_i hf
      obtain ⟨a₁, a₂⟩ := a
      cases e'
      exact ⟨a₂, rfl, by simpa using hf⟩
  | noFormat => cases e
  | ranOut _ => cases e

/-- Under every oracle, what a compiled run returns holds the plain parts of a transcript that is the strategy's run but for nonces. -/
theorem endsAt_proveX {K : ℕ} {L' : BatchProtocolWithLeafBody I₀ X₀} (t : Tag) {Y : Type} {E : ExtSpec} {lam : ℕ} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (xin : Y → Option X₀)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L')
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L') (cap : ℕ → ℕ) (g : Fam (typedOracleFamily lam K L')) :
    EndsAt g (fun r : Res (OneProtocolProof lam Q × Tr Q.loc.shape) => ∀ π τ, r = .ok (π, τ) →
        PutsLe cap 0 Q.loc.shape Q.ann wq.sh (σ.run τ.rho).1 τ ∧ π.plains = τ.plains)
      (proveX t Q wq embS embP xin cms x y xt σ co cap) := by
  refine endsAt_of_det _ (noCoin_proveX t Q wq embS embP xin cms x y xt σ co cap) fun π τ e => ?_
  refine ⟨proveX_putsLe t Q wq embS embP xin cms x y xt σ co cap g π τ e, ?_⟩
  obtain ⟨z, -, rfl, rfl⟩ := (proveX_ok_iff t Q wq embS embP xin cms x y xt σ co cap g π τ).1 e
  rfl

section Reads
variable {offlineRoundMarks : RoundSplits L₀.offline.shape} {linkRoundMarks : RoundSplits L₀.link.shape}
    (w : HashLayout L₀ offlineRoundMarks linkRoundMarks) (provers : HonestProvers L₀) (s : CompiledSettings w provers)

/-- **The settings' readers do not read nonces**: two transcripts that are one but for nonces read alike. At the format: law_cuts. -/
structure ReadsThroughNonces : Prop where
  offline : ∀ (cap : ℕ → ℕ) (τ τ' : Tr L₀.offline.shape),
    PutsLe cap 0 L₀.offline.shape offlineRoundMarks (wTC w.queryLayout).sh τ τ' →
      s.readOffline τ'.plains = s.readOffline τ.plains
  online : ∀ (cap : ℕ → ℕ) (τ τ' : Tr L₀.onlineBatch.loc.shape),
    PutsLe cap 0 L₀.onlineBatch.loc.shape L₀.onlineBatch.ann (wBC w.queryLayout).sh τ τ' →
      s.readOnline τ'.plains = s.readOnline τ.plains

variable {w provers s}

/-- **The key's offline string, if it is shown, reads the values that the coin fixes.** -/
theorem endsAt_commitAt_read (g : Fam (typedOracleFamily 256 w.queryLayout.K (typedOracleCarrier L₀ w.LeafBody offlineRoundMarks linkRoundMarks)))
    (hRun : RunValuesAreSent w provers s fun _ => True) (hN : ReadsThroughNonces w provers s) (i : I₀)
    (d : DrawC 256 L₀ w.LeafBody offlineRoundMarks linkRoundMarks
      (honestSide w provers s).side.KT (honestSide w provers s).side.KL) :
    EndsAt g (fun k => ∀ a, k.1.piT = some a → s.readOffline a.plains = s.runValuesOffline d.κ)
      (commitAt w.queryLayout w.seedQueries w.answerCode (honestSide w provers s).side i d) := by
  refine EndsAt.bind (Q' := fun _ => True) (fun t₁ _ => ?_) _ (Ends.at g _ (ends_true _))
  refine EndsAt.bind (Q' := fun _ => True) (fun ts _ => ?_) _ (Ends.at g _ (ends_true _))
  refine EndsAt.bind (fun a ha => ?_) _ (endsAt_proveX _ _ _ _ _ _ _ _ _ _ _ _ _ g)
  refine EndsAt.bind (Q' := fun _ => True) (fun ls _ => ?_) _ (Ends.at g _ (ends_true _))
  intro p hp
  obtain ⟨τ, e, hstop⟩ := shown_some_stop hp
  obtain ⟨h1, h2⟩ := ha p τ e
  refine (congrArg s.readOffline h2).trans ((hN.offline _ _ _ h1).trans ?_)
  refine hRun.T i t₁.r t₁.seed d.κ τ.rho trivial fun hin => ?_
  have ht : (honestSide w provers s).side.st.stopT i t₁.r t₁.seed τ.rho = true := @decide_eq_true _ (_) hin
  rw [hstop] at ht
  cases ht

/-- **The online string, if it holds one, reads the values that the coin fixes.** -/
theorem endsAt_proveAt_read (g : Fam (typedOracleFamily 256 w.queryLayout.K (typedOracleCarrier L₀ w.LeafBody offlineRoundMarks linkRoundMarks)))
    (hRun : RunValuesAreSent w provers s fun _ => True) (hN : ReadsThroughNonces w provers s)
    (isk : Isk 256 L₀ w.LeafBody offlineRoundMarks linkRoundMarks) (x : X₀)
    (d : DrawP 256 L₀ w.LeafBody offlineRoundMarks linkRoundMarks (honestSide w provers s).side.KB) :
    EndsAt g (fun π => ∀ b, π.piB = some b → s.readOnline b.plains = s.runValuesOnline d.κ)
      (proveAt w.queryLayout w.answerCode w.fixedSample (honestSide w provers s).side isk x d) := by
  unfold proveAt
  split
  · intro b hb
    cases hb
  · rename_i t _
    refine EndsAt.bind (fun a ha => ?_) _ (endsAt_proveX _ _ _ _ _ _ _ _ _ _ _ _ _ g)
    intro p hp
    obtain ⟨τ, e, hstop⟩ := shown_some_stop hp
    obtain ⟨h1, h2⟩ := ha p τ e
    refine (congrArg s.readOnline h2).trans ((hN.online _ _ _ h1).trans ?_)
    refine hRun.B isk.i t.r t.seed _ x d.κ τ.rho trivial fun hin => ?_
    have ht : (honestSide w provers s).side.st.stopB isk.i t.r t.seed x _ τ.rho = true := @decide_eq_true _ (_) hin
    rw [hstop] at ht
    cases ht

/-- **The committer**: the key's offline string reads a value in BadValue with chance at most that of the coins. -/
theorem small_commitW_read (g : Fam (typedOracleFamily 256 w.queryLayout.K (typedOracleCarrier L₀ w.LeafBody offlineRoundMarks linkRoundMarks)))
    (hRun : RunValuesAreSent w provers s fun _ => True) (hN : ReadsThroughNonces w provers s) (i : I₀)
    (BadValue : s.RunValues → Prop) {ε : ℝ≥0∞}
    (hB : pr (unif provers.offlineProver.Coin) {κ | BadValue (s.runValuesOffline κ)} ≤ ε) :
    Small g (fun k => ∃ a, k.1.piT = some a ∧ BadValue (s.readOffline a.plains)) ε
      (commitW w.queryLayout w.seedQueries w.answerCode (honestSide w provers s).side i) := by
  have hB' : pr (unif (Fin ((honestSide w provers s).side.kT.n + 1)))
      {c | BadValue (s.runValuesOffline ((honestSide w provers s).side.kT.e c))} ≤ ε :=
    le_trans (le_of_eq (pr_enum_eq _ (pickAll_ok _) fun κ => BadValue (s.runValuesOffline κ))) hB
  show Small g _ ε (.sample _ fun a => .sample _ fun b => .sample _ fun c => .sample _ fun e =>
    ((coinsCopies w.queryLayout (honestSide w provers s).side ((honestSide w provers s).side.M + 1)).bind fun ds =>
      (.pure ⟨(honestSide w provers s).side.ri.e a, (honestSide w provers s).side.sl.e b,
        (honestSide w provers s).side.kT.e c, (honestSide w provers s).side.coT.e e, ds⟩ :
          TypedOracleComputation 256 w.queryLayout.K (typedOracleCarrier L₀ w.LeafBody offlineRoundMarks linkRoundMarks) _)).bind fun d =>
        commitAt w.queryLayout w.seedQueries w.answerCode (honestSide w provers s).side i d)
  refine .sample fun a => .sample fun b => .few _ hB' fun c hc e => ?_
  refine EndsAt.bind (Q' := fun d : DrawC 256 L₀ w.LeafBody offlineRoundMarks linkRoundMarks
      (honestSide w provers s).side.KT (honestSide w provers s).side.KL =>
      d.κ = (honestSide w provers s).side.kT.e c) (fun d hd => ?_) _ ?_
  · refine EndsAt.mono (fun k hk => ?_) _ (endsAt_commitAt_read g hRun hN i d)
    rintro ⟨p, hp, hz⟩
    refine hc ?_
    show BadValue (s.runValuesOffline ((honestSide w provers s).side.kT.e c))
    rw [← hd, ← hk p hp]
    exact hz
  · refine Ends.at g _ (Ends.bind (Q' := fun _ => True) (fun ds _ => ?_) _ (ends_true _))
    exact rfl

/-- **The prover**: the online string reads a value in BadValue with chance at most that of the coins. -/
theorem small_proveW_read (g : Fam (typedOracleFamily 256 w.queryLayout.K (typedOracleCarrier L₀ w.LeafBody offlineRoundMarks linkRoundMarks)))
    (hRun : RunValuesAreSent w provers s fun _ => True) (hN : ReadsThroughNonces w provers s)
    (isk : Isk 256 L₀ w.LeafBody offlineRoundMarks linkRoundMarks) (x : X₀)
    (BadValue : s.RunValues → Prop) {ε : ℝ≥0∞}
    (hB : pr (unif provers.onlineProver.Coin) {κ | BadValue (s.runValuesOnline κ)} ≤ ε) :
    Small g (fun πs => ∃ b, (ZKCP.Special.head1 πs).piB = some b ∧ BadValue (s.readOnline b.plains)) ε
      (proveW w.queryLayout w.answerCode w.fixedSample (honestSide w provers s).side isk [(x, ())]) := by
  have hB' : pr (unif (Fin ((honestSide w provers s).side.kB.n + 1)))
      {c | BadValue (s.runValuesOnline ((honestSide w provers s).side.kB.e c))} ≤ ε :=
    le_trans (le_of_eq (pr_enum_eq _ (pickAll_ok _) fun κ => BadValue (s.runValuesOnline κ))) hB
  show Small g _ ε (.sample _ fun j => .sample _ fun c => .sample _ fun e =>
    (proveAt w.queryLayout w.answerCode w.fixedSample (honestSide w provers s).side isk x
      ⟨j.val, (honestSide w provers s).side.kB.e c, (honestSide w provers s).side.coB.e e⟩).bind fun π =>
      (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof 256 L₀) [(x, ())])))
  refine .sample fun j => .few _ hB' fun c hc e => ?_
  refine EndsAt.bind (fun π hπ => ?_) _ (endsAt_proveAt_read g hRun hN isk x
    ⟨j.val, (honestSide w provers s).side.kB.e c, (honestSide w provers s).side.coB.e e⟩)
  rintro ⟨p, hp, hz⟩
  refine hc ?_
  show BadValue (s.runValuesOnline ((honestSide w provers s).side.kB.e c))
  rw [← hπ p hp]
  exact hz

end Reads

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.Small.prob_le
#print axioms VerifiableInference.Compilation.small_commitW_salt
#print axioms VerifiableInference.Compilation.small_proveW_salt
#print axioms VerifiableInference.Compilation.eitherBad_mass
#print axioms VerifiableInference.Compilation.pr_coinsPre_salt
#print axioms VerifiableInference.Compilation.honestSide_salt_offline
#print axioms VerifiableInference.Compilation.honestSide_salt_online
#print axioms VerifiableInference.Compilation.endsAt_commitAt_read
#print axioms VerifiableInference.Compilation.endsAt_proveAt_read
#print axioms VerifiableInference.Compilation.small_commitW_read
#print axioms VerifiableInference.Compilation.small_proveW_read
