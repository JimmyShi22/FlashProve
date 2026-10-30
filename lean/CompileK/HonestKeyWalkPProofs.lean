-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyWalkPProofs.lean: the proofs of CompileK/HonestKeyWalkP.lean: a walk over the
program of the honest prover with free empty slots, for a price on oracle names.

The head of CompileK/HonestKeyWalkP.lean says what the statements say and what they do not. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
The calculus and the pieces are those of CompileK/HonestKeyWalkProofs.lean (`HkSW u`; `HkNoEv`; the
lemmas hkw_*). This file adds the pieces that tell a slot with a request from an empty one (`full`,
Compile/Batch/NeedCostP.lean).

Main names:
  `hkw_eachMU`: under `hf`, doing something in each slot: only the slots with a request are charged.
  `hkw_reqTU`: the request tree: a leaf query for each request, at most cs.length − 1 inner
    vertices.
  `hkw_chainTU`: all chains of a batch; the analogue of `swv_chainTU`
    (Compile/Batch/OneCallCostR.lean), step for step, with the counts replaced, without its
    hypotheses `TW` and `RuleSh` and without what the chains return.
  `hkw_proveBU` to `hk_costV_PU`: one execution and the prover's program; the analogues of
    `swv_proveBU` to `costV_PU` (Compile/Batch/OneCallCostS.lean), without their hypotheses. In
    `hk_costV_PU` the ghost names are written back.

Terms: lean/GLOSSARY.md.
-/
import CompileK.HonestKeyWalkP
import CompileK.HonestKeyWalkProofs

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.CostP (SWV)
open Compile.Batch.Need (phK phK_afterLo full full_hear map_full_hear)
open Compile.Batch.OneCall (cPUW costV_realQ_pre)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (u : OracleName → ℕ)

theorem hkw_eachMU {σ τ : Type} {f : σ → St lam K L τ} (g : σ → Bool) (g' : τ → Bool) (c : ℕ)
    (hf : ∀ a, HkSW u (f a) (if g a then c else 0) fun b => g' b = g a) :
    ∀ l : List σ, HkSW u (eachM f l) ((l.map g).count true * c) fun l' => l'.map g' = l.map g
  | [] => rfl
  | a :: t =>
      SWV.bind' (hf a) (m' := (t.map g).count true * c) (fun b hb => SWV.bind' (hkw_eachMU g g' c hf t) (m' := 0) (fun r hr => by
        show (b :: r).map g' = (a :: t).map g
        rw [List.map_cons, List.map_cons, hb, hr]) le_rfl) (by
        rw [List.map_cons, List.count_cons]
        cases g a
        · simp
        · simp [Nat.add_mul, Nat.add_comm])

theorem hkw_rleavesTU :
    ∀ l : List (Option Tok),
      HkSW u (rleavesTU (lam := lam) (K := K) (L := L) l)
        ((l.map Option.isSome).count true * u .rleaf) fun r => r.length = l.length
  | [] => rfl
  | some c :: t =>
      SWV.bind' (hkw_rleafT u c) (m' := (t.map Option.isSome).count true * u .rleaf) (fun d _ => SWV.bind' (hkw_rleavesTU t) (m' := 0) (fun r hr => by
        show (d :: r).length = (some c :: t).length
        rw [List.length_cons, List.length_cons, hr]) le_rfl) (by
        simp only [List.map_cons, Option.isSome_some, List.count_cons_self]
        rw [Nat.succ_mul]
        omega)
  | none :: t => fun d =>
      SWV.bind' (hkw_rleavesTU t) (m' := 0) (fun r hr => by
        show (d :: r).length = (none :: t).length
        rw [List.length_cons, List.length_cons, hr]) (by simp)

theorem hkw_reqTU (depthReq : ℕ) (cs : List (Option Tok)) :
    HkSW u (reqTU (lam := lam) (K := K) (L := L) depthReq cs)
      ((cs.map Option.isSome).count true * u .rleaf + (cs.length - 1) * u .rnode) (fun _ => True) :=
  SWV.bind' (hkw_rleavesTU u cs) (m' := (cs.length - 1) * u .rnode)
    (fun ls hl =>
      SWV.bind' (hkw_levelsM u (hkw_rnodeT u) depthReq ls) (m' := 0)
        (fun _ _ => trivial) (by rw [hl]; exact le_rfl)) le_rfl

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

section One
variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
  (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

theorem hkw_slotJoinF (z : SlotSt lam K Y (r :: s)) :
    HkSW u (slotJoin sMT t a w emb plJ i z) (hkTr u w.depthJ + u (.g t)) fun z' =>
      full z' = full z := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotJoin]
  exact hkw_withTree u sMT _ _ _ (n := u (.g t) + 0) fun _ => hkw_gT u t i _ _ _ fun _ => rfl

theorem hkw_slotJoinU (z : SlotSt lam K Y (r :: s)) :
    HkSW u (slotJoinU sMT t a w emb plJ i z)
      (if full z then hkTr u w.depthJ + u (.g t) else 0) fun z' => full z' = full z := by
  cases hx : z.2.x with
  | none =>
    rw [Need.slotJoinU_none sMT t a w emb plJ i hx]
    exact rfl
  | some y =>
    have hf : full z = true := by unfold full; rw [hx]; rfl
    rw [Need.slotJoinU_some sMT t a w emb plJ i hx, hf, if_pos rfl]
    exact (hkw_slotJoinF u sMT t a w emb plJ i z).mono (fun _ h => h.trans hf) le_rfl

theorem hkw_joinMU :
    ∀ zs : List (SlotSt lam K Y (r :: s)),
      HkSW u (joinMU sMT t a w emb plJ i zs)
        ((zs.map full).count true * (hkTr u w.depthJ + u (.g t)))
        fun o => o.1.map full = zs.map full ∧ o.2.map Option.isSome = zs.map full
  | [] => ⟨rfl, rfl⟩
  | z :: zs =>
      SWV.bind' (hkw_slotJoinU u sMT t a w emb plJ i z) (m' := (zs.map full).count true * (hkTr u w.depthJ + u (.g t))) (fun z' hz' => SWV.bind' (hkw_joinMU zs) (m' := 0) (fun o ho => by
        show (z' :: o.1).map full = (z :: zs).map full ∧
          ((z'.2.x.map fun _ => z'.2.c) :: o.2).map Option.isSome = (z :: zs).map full
        rw [List.map_cons, List.map_cons, List.map_cons, ho.1, ho.2, hz', Option.isSome_map]
        exact ⟨rfl, by rw [← hz']; rfl⟩) le_rfl) (by
        rw [List.map_cons, List.count_cons]
        cases full z
        · simp
        · simp [Nat.add_mul, Nat.add_comm])

theorem hkw_slotLoF (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    HkSW u (slotLo sMT t cms xin a w emb plJ i ph z)
      (hkTr u w.depthJ + triesOf w.grJ * u (.fb t)) fun z' => full z' = full z := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotLo]
  exact hkw_withTree u sMT _ _ _ (n := triesOf w.grJ * u (.fb t) + 0) fun _ =>
    hkw_fbSlotG u _ _ t i cms _ ph _ _ _ _ _ fun _ _ _ _ => rfl

theorem hkw_slotLoU (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    HkSW u (slotLoU sMT t cms xin a w emb plJ i ph z)
      (if full z then hkTr u w.depthJ + triesOf w.grJ * u (.fb t) else 0)
      fun z' => full z' = full z := by
  cases hx : z.2.x with
  | none =>
    rw [Need.slotLoU_none sMT t cms xin a w emb plJ i ph hx]
    exact rfl
  | some y =>
    have hf : full z = true := by unfold full; rw [hx]; rfl
    rw [Need.slotLoU_some sMT t cms xin a w emb plJ i ph hx, hf, if_pos rfl]
    exact (hkw_slotLoF u sMT t cms xin a w emb plJ i ph z).mono (fun _ h => h.trans hf) le_rfl

end One

variable (depthReq : ℕ)

/-- All chains of a batch with free empty slots. fl: which slots hold a request. -/
theorem hkw_chainTU :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (fl : List Bool),
      zs.map full = fl →
      HkSW u (chainTU sMT t cms xin depthReq s A Ws embS embP i ph σ0 zs a0)
        (hkShared u t fl.length s A Ws (phK ph) + fl.count true * hkSlot u t s A Ws (phK ph))
        (fun _ => True)
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, Ws), embS, embP, i, ph, (m0, k0), zs, a0, fl, hz => by
      by_cases hk : a.kind = .lo
      · rw [Need.chainTU_lo sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk ph,
          hkShared_lo u t fl.length a A w Ws hk, hkSlot_lo u t a A w Ws hk, ← phK_afterLo]
        refine SWV.bind'
          (hkw_eachMU u full full (hkTr u w.depthJ + triesOf w.grJ * u (.fb t))
            (fun z => hkw_slotLoU u sMT t cms xin a w _ _ i ph z) zs)
          (fun zs' hz' => hkw_chainTU s A Ws _ _ (i + 1) _ _ zs' _ fl (hz'.trans hz)) (le_of_eq ?_)
        rw [hz]
        ring
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [Need.chainTU_join sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk']
          show HkSW u _
            (hkShared u t fl.length (r :: s) (a, A) (w, Ws) .loc +
              fl.count true * hkSlot u t (r :: s) (a, A) (w, Ws) .loc) (fun _ => True)
          rw [hkShared_join u t fl.length a A w Ws hk', hkSlot_join u t a A w Ws hk']
          refine SWV.bind' (hkw_joinMU u sMT t a w _ _ i zs)
            (m' := (fl.count true * u .rleaf + (fl.length - 1) * u .rnode) +
                (hkTr u w.depth0 +
                  (triesOf w.gr0 * u (.fb t) +
                    (hkShared u t fl.length s A Ws .shr + fl.count true * hkSlot u t s A Ws .shr))))
            (fun o ho => ?_) (le_of_eq ?_)
          · have e1 : o.2.map Option.isSome = fl := ho.2.trans hz
            have e2 : o.2.length = fl.length := by rw [← e1, List.length_map]
            have hq := hkw_reqTU (K := K) (L := L) (lam := lam) u depthReq o.2
            rw [e1, e2] at hq
            exact SWV.bind' hq
              (fun rq _ =>
                hkw_tree0 u sMT a w _ m0 fun tr0 =>
                  hkw_fbG u _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
                    hkw_chainTU s A Ws _ _ (i + 1) (.shr tl) _ _ _ fl
                      ((map_full_hear w bl true o.1).trans (ho.1.trans hz))) le_rfl
          · rw [hz]
            generalize fl.length - 1 = q
            ring
        | shr tk0 =>
          rw [Need.chainTU_shr sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk' tk0]
          show HkSW u _
            (hkShared u t fl.length (r :: s) (a, A) (w, Ws) .shr +
              fl.count true * hkSlot u t (r :: s) (a, A) (w, Ws) .shr) (fun _ => True)
          rw [hkShared_shr u t fl.length a A w Ws hk',
            hkSlot_sh u t a A w Ws hk' _ (.inr (.inl rfl))]
          exact (hkw_tree0 u sMT a w _ m0
              (n := triesOf w.gr0 * u (.fb t) +
                  (hkShared u t fl.length s A Ws .shr + fl.count true * hkSlot u t s A Ws .shr))
              fun tr0 =>
                hkw_fbG u _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
                  hkw_chainTU s A Ws _ _ (i + 1) (.shr tl) _ _ _ fl
                    ((map_full_hear w bl false zs).trans hz)).mono
            (fun _ h => h) (le_of_eq (by ring))
        | first =>
          rw [Need.chainTU_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inl rfl)]
          show HkSW u _
            (hkShared u t fl.length (r :: s) (a, A) (w, Ws) .first +
              fl.count true * hkSlot u t (r :: s) (a, A) (w, Ws) .first) (fun _ => True)
          rw [hkShared_none u t fl.length a A w Ws hk' _ (.inl rfl),
            hkSlot_sh u t a A w Ws hk' _ (.inl rfl)]
          exact hkw_chainTU s A Ws _ _ (i + 1) .first _ _ _
            fl ((map_full_hear w _ false zs).trans hz)
        | aft =>
          rw [Need.chainTU_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inr rfl)]
          show HkSW u _
            (hkShared u t fl.length (r :: s) (a, A) (w, Ws) .aft +
              fl.count true * hkSlot u t (r :: s) (a, A) (w, Ws) .aft) (fun _ => True)
          rw [hkShared_none u t fl.length a A w Ws hk' _ (.inr rfl),
            hkSlot_sh u t a A w Ws hk' _ (.inr (.inr rfl))]
          exact hkw_chainTU s A Ws _ _ (i + 1) .aft _ _ _ fl ((map_full_hear w _ false zs).trans hz)

end Rounds

/-! ### One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

/-- The start of a slot costs nothing, and the slot holds a request exactly if it was given one. -/
theorem hkw_initSlotU (c0 : H.Coin0) :
    ∀ x : Option Y, HkSW u (initSlotU (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x)
      0 fun z => full z = x.isSome
  | some _ => fun _ _ => rfl
  | none => rfl

theorem hkw_proveBU (fl : ℕ → Bool) (xs : List (Option Y)) :
    HkSW u (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs)
      (hkShared u t xs.length Q.loc.shape Q.ann wq.sh .first +
        (xs.map Option.isSome).count true * hkSlot u t Q.loc.shape Q.ann wq.sh .first)
      (fun _ => True) := by
  unfold proveBU
  refine SWV.bind' (hkw_zero u (hkn_drawT wp.coin0))
    (fun c0 _ =>
      SWV.bind' (hkw_eachMU u Option.isSome full 0
          (fun a => (hkw_initSlotU u sFS Q H wp w c0 a).mono (fun _ h => h) (Nat.zero_le _)) xs)
        (fun zs hz =>
          SWV.bind' (hkw_chainTU u sMT t _ _ depthReq _ _ _ embS embP 0 .first _ zs _
              (xs.map Option.isSome) hz)
            (m' := 0)
            (fun out _ => hkw_zero u (hkn_finishAll Q H wq wp trees w fl c0 out.2 0 out.1)) le_rfl)
        le_rfl) (le_of_eq ?_)
  rw [List.length_map, Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.add_zero]
  rfl

end Prove

/-! ### The prover's program -/

section Star
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

theorem hkw_PpJU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    HkSW u (PpJU W WP p k fr xs j σ) (hkPro W u xs.length) (fun _ => True) := by
  unfold PpJU
  cases k.leaves[j]? with
  | none => trivial
  | some lf =>
    refine SWV.bind'
      (hkw_proveBU u p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _ _ W.depthReq _ _ _ _)
      (m' := 0) (fun _ _ => trivial) ?_
    rw [Need.length_slotsOfReq, Nat.add_zero]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Need.count_slotsOfReq σ xs)) _

theorem hkw_PpU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) :
    HkSW u (PpU W WP p k fr xs) (hkPro W u xs.length) (fun _ => True) :=
  fun j =>
    SWV.bind' (hkw_zero u (hkn_drawT WP.perm))
      (fun σ _ => hkw_PpJU u W WP p k fr xs j.val σ) (le_of_eq (Nat.zero_add _))

/-- The prover, the ghost names written back. -/
theorem hk_costV_PU (k : ISK lam L) (b : List (X × Unit)) :
    (PU W WP p k b).CostBoundV (fun o _ _ => u o) (hkPro W u b.length) := by
  have h := (hkw_PpU u W WP p k.1 (fun _ => true) (b.map Prod.fst)).erase k.2
  rw [List.length_map] at h
  exact costV_realQ_pre (fun o _ _ => u o) _ _
    ((h.map _).weight fun o _ _ => by cases o <;> exact le_rfl)

end Star

/-! ## The statements -/

theorem honestKey_costP : Spec.honestKey_costP := fun _ _ _ _ W WP p u k b =>
  (hk_costV_PU u W WP p k b).toCost fun _ _ _ => le_rfl

theorem honestKey_typedP : Spec.honestKey_typedP := fun I X lam L W WP p k b =>
  hk_query_of_cost (honestKey_costP I X lam L W WP p (fun _ => 1) k b)

theorem honestKey_stringsP : Spec.honestKey_stringsP := fun I X lam L W WP p Wn m k b hl => by
  have e : m.blocks = blk W.K := funext fun o => honestKey_blocks I X L lam W.K m hl o
  have h := honestKey_costP I X lam L W WP p (blk W.K) k (Gen.forgetW b)
  rw [show (Gen.forgetW b).length = b.length from List.length_map _, ← e] at h
  have h1 : (PKE W WP p k (Gen.forgetW b)).CostBound m.blocks (hkPro W m.blocks b.length + 0) :=
    OComp.CostBound.bind (t := 0) (fun _ => OComp.CostBound.pure _ 0) h
  have h2 : ((Gen.withW Wn (argBKE W WP p)).P k b).CostBound
      m.blocks (hkPro W m.blocks b.length + 0 + 0) :=
    OComp.CostBound.bind (t := 0) (fun _ => OComp.CostBound.pure _ 0) h1
  have h3 := queryBound_overOne_of_cost m _ _ h2
  rw [e] at h3
  exact h3

theorem honestKey_sumP : Spec.honestKey_sumP := fun _ _ _ _ W n => by
  unfold hkPro cPUW
  rw [hkSlot_one .onl _ _ _ 0, hkShared_one .onl _ _ _ _ 0]

end Compile.Batch
