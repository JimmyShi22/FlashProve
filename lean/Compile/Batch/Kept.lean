-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/Kept.lean: a bound, on every path, on the Fiat-Shamir queries of the committer and
  the lazy prover of the scheme with a seed, a cache and pruned Merkle paths, not counting failed
  attempts that are not the last (weight `wKept`). Proofs of the statements of
  Compile/Batch/SpecKept.lean, whose header says what they say and what they do not (words of this
  library: lean/GLOSSARY.md).
  For `W.OKG`, if the seed's oracle is `other`:
    `keptP`              the prover on a batch b has weight at most `kPU L b.length`. The levels
                         above the cached one, the randomness of the encoding and the openings query
                         no Fiat-Shamir oracle (Compile/Batch/MeanSeed.lean): what is left is the
                         chains of one batch
    `keptC`              the committer has weight at most `kCB L p`. Making samples from small ones
                         and deriving them from the seed adds queries to `other` only; the cache
                         queries no Fiat-Shamir oracle
    `kSum_le`, `keptLe`  the sanity lemma: a round is counted in at most one of `kSlot`, `kShared`
    `nbPos_one`          the table "1 everywhere" satisfies `NbPos`
                         (Compile/Batch/SpecOneCall.lean); it serves only to state the records
                         `RuleLoop`, `RuleSh` of Compile/Batch/OneCallCostL.lean,
                         Compile/Batch/OneCallCostR.lean

  Notation: `SWk c m P`: `SWV` (Compile/CostV.lean) at the weight `pre (wKept W)`: on every path the
  weights of the queries, each at its own answer, add up to at most m, and the result has the
  property P; `T1`: the property that always holds (`fun _ => True`); `wKept W`
  (Compile/Batch/SpecKept.lean): the weight: at `fb t`, 0 for a failed attempt that is not the last,
  else 1; at every other oracle 0; in Compile/Batch/SpecKept.lean, natural numbers: `kSlot`: the
  searches of one slot with a request, in the rounds that are left: one for each local round;
  `kShared`: the shared searches: one for the joining round and for each of the shared rounds after
  it up to the next local round; `kProve1`: one execution with one slot; `kPU L n`: one batch with n
  requests; `kCB L p`: the committer; `.first`: a `PhK` (Compile/Batch/NeedCostP.lean): where the
  chains are, without tokens; attempt: a proof-of-work attempt; failed and not the last: `failsAt`
  (Compile/Batch/SpecOneCall.lean); the lazy prover: that of `argPL`
  (Compile/Batch/SeedLazyDefs.lean).
-/
import Compile.Batch.KeptWalk
import Compile.Batch.MeanSeedC
import Compile.CostPostV

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.Need (PhK)
namespace Kept
open Compile.CostP (SWV)
open Compile.Batch.Need (PhK phK full)
open Compile.Batch.OneCall
  (pre RuleSh swv_eachM swv_eachM_all costV_realQ_pre ruleSh_T ruleSh_L ruleSh_B)
open Compile.Batch.CompleteUnif (OnlyQ NotFb)
open Seed

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L}

local notation "T1" => fun _ => True
local notation "SWk" => SWV (S := spec lam W.K L) (sp := split lam W.K L) (pre (wKept W))

/-- An algorithm that queries no Fiat-Shamir oracle has weight 0. -/
theorem costV_zero {α : Type} {c : TypedOracleComputation lam W.K L α}
    (h : ∀ t, OnlyQ (S := spec lam W.K L) (NotFb t) c) : c.CostBoundV (wKept W) 0 := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact fun r => ih r fun t => h t r
  | query o q k ih =>
    refine fun r => ⟨0, le_of_eq ?_, ih r fun t => (h t).2 r⟩
    have ho : ∀ t, o ≠ OracleName.fb t := fun t => (h t).1
    cases o with
    | fb t => exact absurd rfl (ho t)
    | _ => rfl

theorem nbPosSh_one {K : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam K s A) (i : ℕ), NbPosSh (fun _ => 1) s A Ws i
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (_, Ws), i => ⟨fun _ => le_rfl, nbPosSh_one s A Ws (i + 1)⟩

theorem nbPos_one (W : QueryLayout lam L) : NbPos W nb1 :=
  ⟨nbPosSh_one _ _ _ 0, nbPosSh_one _ _ _ 0, nbPosSh_one _ _ _ 0⟩

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam W.K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (w : Wt)

theorem nf_initSlot (c0 : H.Coin0) (x : Option Y) :
    NoFbS (initSlot (lam := lam) (K := W.K) (L := L) sFS Q H wp w c0 x) :=
  (nf_drawT wp.coin).bind fun _ _ => trivial

theorem k_initSlotU (c0 : H.Coin0) (x : Option Y) :
    SWk (initSlotU sFS Q H wp w c0 x) 0 fun z => full z = x.isSome := by
  cases x with
  | none => exact rfl
  | some x => exact fun _ _ => rfl

/-- The first part of an execution of `proveBU` (no query for an empty slot), under `RuleSh`. -/
theorem k_chainsU (cms : List (Dig lam))
    (hR : RuleSh W nb1 t Q.loc.shape Q.ann wq.sh embP 0) (xs : List (Option Y)) :
    SWk (chainsU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs)
      (kShared Q.loc.shape Q.ann .first +
        (xs.map Option.isSome).count true * kSlot Q.loc.shape Q.ann .first) T1 := by
  unfold chainsU
  refine SWV.bind' (k_zero (nf_drawT wp.coin0))
    (fun c0 _ =>
      SWV.bind' (swv_eachM Option.isSome full 0
          (fun a => (k_initSlotU sFS Q H wp w c0 a).mono (fun _ h => h) (Nat.zero_le _)) xs)
        (fun zs hz =>
          SWV.bind' (k_chainTU sMT t _ _ depthReq _ _ _ embS embP 0 .first _ zs _
              (xs.map Option.isSome) hR hz)
            (m' := 0) (fun out _ => trivial) (Nat.le_refl _)) (Nat.le_refl _)) (le_of_eq ?_)
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.add_zero]
  rfl

variable (trees : List (TreeH lam))

theorem nf_openE {K : ℕ} {σ : Type} (tr : TreeH lam) (j : ℕ) (a : σ) :
    NoFbS (openE (K := K) (L := L) tr j a) := by
  unfold openE
  cases tr.salts.getD j none with
  | none => trivial
  | some x => exact fun _ => trivial

theorem nf_opensExtB {K : ℕ} {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ ps, NoFbS (opensExtB (K := K) (L := L) we y trees isRead ps)
  | [] => trivial
  | q :: ps => (nf_opensExtB we y trees isRead ps).bind fun f => by
      show NoFbS (if isRead q then _ else _)
      cases isRead q
      · trivial
      · exact (nf_openE _ _ _).bind fun _ => trivial

theorem nf_finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam W.K (Y × H.Coin)) :
    NoFbS (finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) := by
  unfold finishSlot
  dsimp only
  split_ifs
  · trivial
  · exact fun vs =>
      (nf_opensB _ _ _ _ _ _ _).bind fun f => (nf_opensExtB _ _ _ _ _).bind fun _ => trivial

theorem nf_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam W.K (Y × H.Coin))),
      NoFbS (finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs)
  | _, [] => trivial
  | j, acc :: zs => NoFbS.bind (by
      cases acc.x with
      | none => trivial
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        show NoFbS (if fl j then _ else _)
        cases fl j
        · trivial
        · exact nf_finishSlot Q H wq wp w trees c0 a0 j x cj acc) fun _ => (nf_finishAll fl c0 a0 (j + 1) zs).bind fun _ => trivial

/-- One execution of `proveB` (an empty slot is hashed like any other), under `RuleSh`. -/
theorem k_proveB (hR : RuleSh W nb1 t Q.loc.shape Q.ann wq.sh embP 0)
    (fl : ℕ → Bool) (xs : List (Option Y)) :
    SWk (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs)
      (kShared Q.loc.shape Q.ann .first + xs.length * kSlot Q.loc.shape Q.ann .first) T1 := by
  unfold proveB
  refine SWV.bind' (k_zero (nf_drawT wp.coin0))
    (fun c0 _ =>
      SWV.bind' (swv_eachM_all 0 (fun a => k_zero (nf_initSlot sFS Q H wp w c0 a)) xs)
        (fun zs hz =>
          SWV.bind' (k_chainT sMT t _ _ depthReq _ _ _ embS embP 0 .first _ zs _ xs.length hR hz)
            (m' := 0) (fun out _ => k_zero (nf_finishAll Q H wq wp w trees fl c0 out.2 0 out.1))
            (Nat.le_refl _)) (Nat.le_refl _)) (le_of_eq ?_)
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.add_zero]
  rfl

end Prove

/-! ## The lazy prover -/

section Schemes
variable (W) (WP : WireBP L) (p : Params) (hW : W.OKG)
include hW

theorem costV_chainsU (cms : List (Dig lam)) (wt : I × L.EncodingRandomness) (σ : Equiv.Perm (Fin L.maxBatchSize))
    (xs : List X) (vs : List Bits) :
    (eraseR (chainsU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
          (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq cms wt (slotsOfReq σ xs))
        vs).CostBoundV
      (wKept W) (kPU L xs.length) :=
  (costV_realQ_pre (wKept W) _ _
      ((k_chainsU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq wt cms
        (ruleSh_B hW (nbPos_one W)) (slotsOfReq σ xs)).erase vs)).mono
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Need.count_slotsOfReq σ xs)) _)

/-! ## The committer of Compile/Batch/Star.lean -/

theorem k_proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) :
    SWk (proveT W WP p tree i r) (kProve1 (BatchInteractiveOracleProof.ofProto L.offline)) T1 :=
  SWV.bind' (k_proveB p.sMT p.sFS Tag.test _ _ W.T WP.T _ _ _ W.depthReq _ _ (ruleSh_T hW (nbPos_one W)) _ [some ()]) (m' := 0) (fun _ _ => trivial) (le_of_eq (by
    show _ + 1 * _ + 0 = _
    rw [Nat.one_mul, Nat.add_zero]
    rfl))

theorem k_proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    SWk (proveLk W WP p root tree i r₀ r) (kProve1 (BatchInteractiveOracleProof.ofProto L.link)) T1 :=
  SWV.bind' (k_proveB p.sMT p.sFS Tag.link _ _ W.Lk WP.Lk _ _ _ W.depthReq _ _ (ruleSh_L hW (nbPos_one W)) _ [some ()]) (m' := 0) (fun _ _ => trivial) (le_of_eq (by
    show _ + 1 * _ + 0 = _
    rw [Nat.one_mul, Nat.add_zero]
    rfl))

theorem k_leavesC (i : I) (root : Node lam L) :
    ∀ n, SWk (leavesC W WP p i root n) (n * kProve1 (BatchInteractiveOracleProof.ofProto L.link)) T1
  | 0 => trivial
  | n + 1 =>
    SWV.bind' (k_zero (nf_nodeP' W WP p i))
      (m' := kProve1 (BatchInteractiveOracleProof.ofProto L.link) + n * kProve1 (BatchInteractiveOracleProof.ofProto L.link))
      (fun nd _ =>
        SWV.bind' (k_proveLk W WP p hW _ _ _ _ _)
          (fun _ _ => SWV.bind' (k_leavesC i root n) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _))
          (Nat.le_refl _))
      (le_of_eq (by rw [Nat.succ_mul]; omega))

theorem k_Cp (i : I) : SWk (Cp W WP p i) (kCB L p) T1 :=
  SWV.bind' (k_zero (nf_nodeP' W WP p i))
    (m' := kProve1 (BatchInteractiveOracleProof.ofProto L.offline) + (p.M + 1) * kProve1 (BatchInteractiveOracleProof.ofProto L.link))
    (fun root _ =>
      SWV.bind' (k_proveT W WP p hW _ _ _)
        (fun _ _ =>
          SWV.bind' (k_leavesC W WP p hW i root (p.M + 1)) (m' := 0)
            (fun _ _ => trivial) (Nat.le_refl _)) (Nat.le_refl _))
    (le_of_eq (Nat.zero_add _))

/-- the committer C of Compile/Batch/Star.lean, for `W.OKG` -/
theorem costV_C (i : I) : (C W WP p i).CostBoundV (wKept W) (kCB L p) :=
  costV_realQ_pre (wKept W) _ _ (((k_Cp W WP p hW i).erase []).map _)

end Schemes

end Kept

open Kept Seed MeanSeed MeanSeedC

/-- The bound on the lazy prover's weight `wKept` (`Spec.keptP`). -/
theorem keptP : Spec.keptP := by
  intro I X lam L W WP p bk σ ℓ no hW hσ kc b
  refine OComp.CostBoundV.map ?_ _
  intro j
  show (PLat W WP p bk σ ℓ no kc b j.val).CostBoundV (wKept W) _
  unfold PLat
  cases kc.2[j.val]? with
  | none => exact trivial
  | some st =>
    refine (OComp.CostBoundV.bind (t := kPU L b.length) (fun hi => ?_)
        (costV_zero fun t => onlyQ_levelsV W t (W.depth - ℓ) st.2)).mono
      (le_of_eq (Nat.zero_add _))
    split_ifs
    · refine (OComp.CostBoundV.bind (t := kPU L b.length) (fun ra => ?_)
          (costV_zero fun t =>
            onlyQ_derived W bk σ hσ t (nf_drawT (lam := lam) (K := W.K) (L := L) WP.ri) []
              kc.1.2 (off W WP p bk.m j.val))).mono
        (le_of_eq (Nat.zero_add _))
      intro z
      have hch := costV_chainsU W WP p hW [st.1] (kc.1.1, ra.1) (WP.perm.e z) (b.map Prod.fst) []
      rw [List.length_map] at hch
      refine (OComp.CostBoundV.bind (t := 0) (fun o => ?_) hch).mono (le_of_eq (Nat.add_zero _))
      refine costV_zero fun t =>
        CompleteUnif.OnlyQ.bind
          (onlyQ_finishAllL t L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _
            (fun q => onlyQ_opL W WP p bk σ hσ t ℓ kc.1 j.val ra.1 st.2 hi q) _ _ _ _ _ _)
          fun oπ => ?_
      cases oπ <;> trivial
    · exact trivial

/-- The bound on the committer's weight `wKept` (`Spec.keptC`). -/
theorem keptC : Spec.keptC := by
  intro I X lam L W WP p bk σ ℓ no hW hσ i
  refine OComp.CostBoundV.map ?_ _
  show OComp.CostBoundV (wKept W)
    (((argP W WP p bk σ).C i).bind fun o =>
      (cacheOf W WP p bk σ ℓ o.2).bind fun c => OComp.pure (o.1, (o.2, c))) _
  refine (OComp.CostBoundV.bind (t := 0)
      (fun o =>
        OComp.CostBoundV.map (costV_zero fun t => onlyQ_cacheFrom W WP p bk σ hσ t ℓ o.2 _) _)
      ?_).mono
    (le_of_eq (Nat.add_zero _))
  intro s
  refine OComp.CostBoundV.map ?_ _
  have hw : Compile.Seed.Wt bk.m (off W WP p bk.m (p.M + 1) + 0)
      ((argOf WP p (faceKE W WP p)).C i) :=
    (wt_C W WP p bk.m i).bind fun _ => .pure _
  have hc : OComp.CAV (wKept W) ((argOf WP p (faceKE W WP p)).C i) (kCB L p) (fun _ => True) :=
    (OComp.CAV.ofCost (costV_C W WP p hW i)).map _ fun _ _ => trivial
  have hu : ∀ j r, wKept W σ.o (σ.pt s j) r ≤ 0 := fun j r => by
    have e : ∀ (o : OracleName) (q : domOf lam L o) (r : rngOf lam W.K o),
        o = OracleName.other → wKept W o q r = 0 :=
      fun o q r h => by subst h; rfl
    exact le_of_eq (e _ _ _ hσ)
  exact ((OComp.CAV.derive σ s hu (hw.tosses_blocks bk) _ 0
    (OComp.CAV.blocks bk _ _ hc)).cost).mono (by omega)

namespace Kept

/-- a round is local or shared: it is in at most one of the two sums -/
theorem kSum_le : ∀ (s : Shape) (A : RoundSplits s) (ph : PhK), kShared s A ph + kSlot s A ph ≤ s.length
  | [], _, _ => le_rfl
  | r :: s, (a, A), ph => by
      by_cases hk : a.kind = .lo
      · rw [kShared_lo a A hk, kSlot_lo a A hk, List.length_cons]
        have := kSum_le s A ph.afterLo
        omega
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        rw [List.length_cons]
        cases ph with
        | loc => rw [kShared_join a A hk', kSlot_join a A hk']; have := kSum_le s A .shr; omega
        | shr => rw [kShared_shr a A hk', kSlot_sh a A hk' _ (.inr (.inl rfl))]; have := kSum_le s A .shr; omega
        | first => rw [kShared_none a A hk' _ (.inl rfl), kSlot_sh a A hk' _ (.inl rfl)]; have := kSum_le s A .first; omega
        | aft => rw [kShared_none a A hk' _ (.inr rfl), kSlot_sh a A hk' _ (.inr (.inr rfl))]; have := kSum_le s A .aft; omega

end Kept

theorem keptLe : Spec.keptLe := fun I X L p n => by
  have hB := Kept.kSum_le L.onlineBatch.loc.shape L.onlineBatch.ann .first
  have hT : kProve1 (BatchInteractiveOracleProof.ofProto L.offline) ≤ L.offline.shape.length := Kept.kSum_le _ _ .first
  have hL : kProve1 (BatchInteractiveOracleProof.ofProto L.link) ≤ L.link.shape.length := Kept.kSum_le _ _ .first
  refine ⟨?_, Nat.add_le_add hT (Nat.mul_le_mul_left _ hL)⟩
  unfold kPU
  calc
    _ ≤ L.onlineBatch.loc.shape.length + n * L.onlineBatch.loc.shape.length :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

end Compile.Batch
