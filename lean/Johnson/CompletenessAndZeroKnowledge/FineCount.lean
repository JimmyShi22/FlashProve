-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/FineCount.lean: HOW MANY HASH QUERIES THE HONEST SIDE OF slotSystem ASKS, oracle by oracle.
An answer of a Fiat-Shamir oracle has K + 1 hash blocks, any other answer at most one
(blocks_le_costW). The step to one hash function, overOne, asks every block of every answer, so a try
of a search costs K + 1 hash queries, failed or not, and a query to a tree costs one. chainW is chainN
(Johnson/Prover/Law/Count.lean) at these weights; commitF and proveF are commitN and proveN
(Johnson/WholeKey/Work.lean) at them.

Upper bounds on every path, with chainN's looseness: every round counts both components' Fiat-Shamir
numbers. Nothing here is a goal. chainF (Johnson/Prover/Law/CountF.lean) is another count: it charges a
failed try one call, and holds of the third exit, overOneF, at which compile's committer and prover stand.
-/
import Johnson.Prover.Law.CountF
import Johnson.FrontRoad.Blocks
import Johnson.WholeKey.Work
import Johnson.CompletenessAndZeroKnowledge.SlotBudget

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile.GenPub (AllOut)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName
local notation "FsAns₂" => TypedOracleCompiler.Compile.Batch.FsAns
local notation "OC₂" => TypedOracleCompiler.Compile.Batch.TypedOracleComputation

/-- What a query costs in hash queries at most: K + 1 at a Fiat-Shamir oracle, else one. -/
def costW (K : ℕ) : ON₂ → ℕ
  | .fb _ => K + 1
  | .fbw _ _ => K + 1
  | _ => 1

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The weight of a query, whatever the answer. -/
abbrev wtW (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : (o : ON₂) → domOf lam L o → rngOf lam K o → ℕ :=
  fun o _ _ => costW K o

/-- For every coding, no answer has more blocks than costW says. -/
theorem blocks_le_costW (m : OracleCoding (typedOracleFamily lam K L) lam) (hl : 0 < lam) (o : ON₂) :
    m.blocks o ≤ costW K o := by
  have one : ∀ o' : ON₂, ((typedOracleFamily lam K L).Rng o' ≃ (Fin lam → Bool)) → m.blocks o' ≤ 1 :=
    fun o' e => le_of_eq (m.blocks_eq_one hl o' e)
  cases o with
  | leaf => exact one _ (Equiv.refl _)
  | node => exact one _ (Equiv.refl _)
  | rleaf => exact one _ (Equiv.refl _)
  | rnode => exact one _ (Equiv.refl _)
  | g t => exact one _ (Equiv.refl _)
  | other => exact one _ (Equiv.refl _)
  | fb t => exact OnBytes.FrontRoad.blocks_le m hl _
  | fbw t k => exact OnBytes.FrontRoad.blocks_le m hl _
  | ann =>
    have e : Unit ≃ (Fin (m.blocks OracleName.ann) → Fin lam → Bool) := m.rng OracleName.ann
    have h0 : m.blocks OracleName.ann = 0 := OnBytes.FrontRoad.blocks_of_card hl e (by simp)
    rw [h0]
    exact Nat.zero_le _

theorem small_W : Small (lam := lam) (L := L) fun o q => ∀ r, wtW lam K L o q r ≤ 1 :=
  ⟨fun _ _ => le_refl 1, fun _ _ => le_refl 1, fun _ _ => le_refl 1, fun _ _ => le_refl 1⟩

theorem cost_of_smallW {α : Type} {c : OC₂ lam K L α} {t : ℕ} (h : c.QueryBound t)
    (ha : c.AsksIn fun o q => ∀ r, wtW lam K L o q r ≤ 1) : c.CostBoundR (wtW lam K L) t :=
  OComp.CostBoundR.of_queryBound h ha

/-- A Fiat-Shamir query in hash queries, every try whole. B: the blocks of an answer. -/
def fsW {C P : Type} (B : ℕ) : Option (GrW C P) → ℕ → ℕ
  | none, _ => B
  | some _, n => (n + 1) * B

/-- chainN at the weights. -/
def chainW : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | [], _, _, _, _, _ => 0
  | _ :: s, (_, A), (w, W), cap, i, p =>
      treesN w.depthJ + treesN w.depth0 + (2 + p) +
        (fsW (K + 1) w.grJ (cap i) + fsW (K + 1) w.gr0 (cap i)) + chainW s A W cap (i + 1) p

section Search
variable {C P : Type} (chal : (Fin K → Dig lam) → C) (t : Tag) (qOf : P → FbIn lam L t)

theorem costW_searchO (gr : GrW C P) (α : P) :
    ∀ fuel n : ℕ, (searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qOf β)) α fuel
      n).CostBoundR (wtW lam K L) (fuel * (K + 1))
  | 0, _ => trivial
  | fuel + 1, n => by
    show (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) (qOf (gr.put n α)) fun a =>
      if gr.ok (chal a.1) then OComp.pure (some (gr.put n α, a))
      else searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qOf β)) α fuel
        (n + 1)).CostBoundR (wtW lam K L) ((fuel + 1) * (K + 1))
    intro r
    refine ⟨fuel * (K + 1), ?_, ?_⟩
    · show (fuel + 1) * (K + 1) = (K + 1) + fuel * (K + 1)
      ring
    · by_cases hk : gr.ok (chal r.1) = true
      · simp only [if_pos hk]
        trivial
      · simp only [if_neg hk]
        exact costW_searchO gr α fuel (n + 1)

theorem costW_fsO (gr : Option (GrW C P)) (cap : ℕ) (α : P) :
    (fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qOf β)) α).CostBoundR
      (wtW lam K L) (fsW (K + 1) gr cap) := by
  cases gr with
  | none =>
    show (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) (qOf α) fun a =>
      OComp.pure (some (α, a))).CostBoundR (wtW lam K L) (K + 1)
    intro r
    exact ⟨0, rfl, trivial⟩
  | some g => exact costW_searchO chal t qOf g α (cap + 1) 0

end Search

/-- **The chain in hash queries, every try whole.** -/
theorem costW_chainO (t : Tag) (cms : List (Dig lam)) (x : Option X) (co : Coins lam L)
    (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      (chainO t cms x co cap s A W embS embP i ph σ).CostBoundR (wtW lam K L)
        (chainW s A W cap i co.path.length)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k) => by
    have sm := small_W (lam := lam) (K := K) (L := L)
    have tail : ∀ {β : Type} (ph' σ') (f : Res (OutP lam L s) → OC₂ lam K L β),
        (∀ r, (f r).CostBoundR (wtW lam K L) 0) →
        ((chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          ph' σ').bind f).CostBoundR (wtW lam K L)
            (chainW s A W cap (i + 1) co.path.length + 0) :=
      fun ph' σ' f hf =>
        OComp.CostBoundR.bind hf (costW_chainO t cms x co cap s A W _ _ _ ph' σ')
    have one : ∀ (o : ON₂) (q : domOf lam L o), (∀ r, wtW lam K L o q r ≤ 1) →
        (askTypedOracle (L := L) (K := K) o q).CostBoundR (wtW lam K L) 1 := fun o q h =>
      cost_of_smallW (queryBound_askV o q) ⟨h, fun _ => trivial⟩
    simp only [chainO]
    generalize actOf cms (x.map L.early) co.salt a.kind ph = act
    cases act with
    | none => trivial
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          exact (OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind
              (costBound_onFs _ _ _ fun _ => tail _ _ _ (by intro _; trivial))
              (costW_fsO w.chal t _ w.grJ (cap i) _))
            (cost_of_smallW (queryBound_treesO _ _ _ _ _ _ _)
              (asksIn_treesO sm _ _ _ _ _ _ _))).mono (by
                show _ ≤ treesN w.depthJ + treesN w.depth0 + (2 + co.path.length) +
                  (fsW (K + 1) w.grJ (cap i) + fsW (K + 1) w.gr0 (cap i)) +
                    chainW s A W cap (i + 1) co.path.length
                omega)
        | false =>
          exact (OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind
              (costBound_onFs _ _ _ fun _ => tail _ _ _ (by intro _; trivial))
              (costW_fsO w.chal t _ w.gr0 (cap i) _))
            (cost_of_smallW (queryBound_treesO _ _ _ _ _ _ _)
              (asksIn_treesO sm _ _ _ _ _ _ _))).mono (by
                show _ ≤ treesN w.depthJ + treesN w.depth0 + (2 + co.path.length) +
                  (fsW (K + 1) w.grJ (cap i) + fsW (K + 1) w.gr0 (cap i)) +
                    chainW s A W cap (i + 1) co.path.length
                omega)
      | join ρ =>
        exact (OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind (fun _ =>
            OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind (fun _ =>
            OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind
              (costBound_onFs _ _ _ fun _ => tail _ _ _ (by intro _; trivial))
              (costW_fsO w.chal t _ w.gr0 (cap i) _))
            (cost_of_smallW (queryBound_climbO _ _ _) (asksIn_climbO sm _ _ _)))
            (one _ _ fun _ => le_refl 1)) (one _ _ fun _ => le_refl 1))
            (cost_of_smallW (queryBound_treesO _ _ _ _ _ _ _)
              (asksIn_treesO sm _ _ _ _ _ _ _)))
            (cost_of_smallW (queryBound_treesO _ _ _ _ _ _ _)
              (asksIn_treesO sm _ _ _ _ _ _ _))).mono (by
                show _ ≤ treesN w.depthJ + treesN w.depth0 + (2 + co.path.length) +
                  (fsW (K + 1) w.grJ (cap i) + fsW (K + 1) w.gr0 (cap i)) +
                    chainW s A W cap (i + 1) co.path.length
                omega)

/-- The compiled prover of one slot. -/
theorem costW_proveX (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ) :
    (proveX t Q wq embS embP xin cms x y xt σ co cap).CostBoundR (wtW lam K L)
      (chainW Q.loc.shape Q.ann wq.sh cap 0 co.path.length) :=
  (OComp.CostBoundR.bind (t := 0) (by intro _; trivial)
    (costW_chainO t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ)).mono
    (by omega)

end OnBytes.Prover

namespace Rom

/-- Weights that bound the blocks of every answer bound the hash queries of the first exit. -/
theorem queryBound_overOne_of_costR {S : OSpec} {lam : ℕ} {α : Type} (m : OracleCoding S lam)
    (v : S.ι → ℕ) (hv : ∀ o, m.blocks o ≤ v o) (c : OComp S α) :
    ∀ t, c.CostBoundR (fun o _ _ => v o) t → (c.overOne m).QueryBound t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    intro t h
    obtain ⟨t', rfl, -⟩ := h ((m.rng o).symm fun _ _ => false)
    exact ((queryBound_askAll (lam := lam) (m.blocks o) (m.code o q)).bind
      (g := fun bs => (k ((m.rng o).symm bs)).overOne m) fun bs => ih _ t' (by
        obtain ⟨t'', e, hk⟩ := h ((m.rng o).symm bs)
        have e' : v o + t' = v o + t'' := e
        have : t' = t'' := by omega
        rw [this]
        exact hk)).mono (Nat.add_le_add_right (hv o) _)

end Rom

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover
open _root_.Compile.GenPub (AllOut)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

/-- One table: its tree, its seed's two whole answers. -/
def tabW : ℕ := 2 * 2 ^ W.depth + (2 * (W.K + 1) + 0)

/-- One link run. -/
def linkW : ℕ := chainW L.link.shape aL (wLC W).sh h.capL 0 W.depthReqL + 0

/-- **The committer's hash queries.** -/
def commitF : ℕ :=
  tabW W + ((h.M + 1) * tabW W +
    (chainW L.offline.shape aT (wTC W).sh h.capT 0 W.depthReqT + ((h.M + 1) * linkW W h + 0)))

/-- **The prover's hash queries.** -/
def proveF : ℕ := chainW L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB 0 W.depthReq + 0

/-- The weights of the scheme's oracles. -/
local notation "wt" => wtW lam W.K (typedOracleCarrier L Bd aT aL)

theorem costR_bindOut {S' : OSpec} {α β : Type} {w : (o : S'.ι) → S'.Dom o → S'.Rng o → ℕ}
    {P : α → Prop} {g : α → OComp S' β} {t : ℕ} (hg : ∀ a, P a → (g a).CostBoundR w t) :
    ∀ c : OComp S' α, c.QueryBound 0 → AllOut P c → (c.bind g).CostBoundR w t
  | .pure a, _, hc => hg a hc
  | .sample _ k, h0, hc => fun r => costR_bindOut hg (k r) (h0 r) (hc r)
  | .query _ _ _, h0, _ => h0.elim

theorem costW_seedsO (cm : Dig lam) : (seedsO W S cm).CostBoundR wt (2 * (W.K + 1)) := fun _ =>
  ⟨W.K + 1, by show 2 * (W.K + 1) = (W.K + 1) + (W.K + 1); omega, fun _ => ⟨0, rfl, trivial⟩⟩

theorem costW_committerTreeKeptByProver (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeKeptByProver W b₀ y salt).CostBoundR wt (2 * 2 ^ W.depth) :=
  cost_of_smallW (queryBound_committerTreeKeptByProver W b₀ y salt) (asksIn_treeO small_W _ _)

theorem costW_tabO (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    (tabO W S b₀ i r s).CostBoundR wt (tabW W) := by
  show (tabO W S b₀ i r s).CostBoundR wt (2 * 2 ^ W.depth + (2 * (W.K + 1) + 0))
  exact OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind (t := 0) (by intro _; trivial)
    (costW_seedsO W S _)) (costW_committerTreeKeptByProver W b₀ _ _)

theorem costW_tabsO (i : I) : ∀ ds : List (DrawCopy lam L Bd aT aL h.KL),
    (tabsO W S h i ds).CostBoundR wt (ds.length * tabW W)
  | [] => trivial
  | d :: ds => by
    have e : (d :: ds).length * tabW W = tabW W + (ds.length * tabW W + 0) := by
      rw [List.length_cons, Nat.succ_mul]
      omega
    rw [e]
    exact OComp.CostBoundR.bind (fun _ =>
      OComp.CostBoundR.bind (by intro _; trivial) (costW_tabsO i ds))
      (costW_tabO W S h.b₀ i d.r _)

theorem costW_linkO (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (d : DrawCopy lam L Bd aT aL h.KL)
    (hd : d.co.path.length = W.depthReqL) :
    (linkO W cA h i t₁ t₂ d).CostBoundR wt (linkW W h) := by
  have q := costW_proveX Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
    (cmsLA cA t₁.tree.root t₂.tree.root (L.recOf i t₁.r t₁.seed).2 (L.recOf i t₂.r t₂.seed).2)
    (L.recOf i t₁.r t₁.seed, L.recOf i t₂.r t₂.seed) (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r)
    (fun k => if k = 0 then t₁.tree else t₂.tree)
    (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) d.κ) (h.dressL (h.rvL d.κ) d.co) h.capL
  have e : (h.dressL (h.rvL d.κ) d.co).path.length = W.depthReqL := hd
  rw [e] at q
  exact OComp.CostBoundR.bind (by intro _; trivial) q

theorem costW_linksO (i : I) (t₁ : TabK lam L Bd aT aL) :
    ∀ l : List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL),
      (∀ a ∈ l, a.1.co.path.length = W.depthReqL) →
      (linksO W cA h i t₁ l).CostBoundR wt (l.length * linkW W h)
  | [], _ => trivial
  | a :: l, hl => by
    have e : (a :: l).length * linkW W h = linkW W h + (l.length * linkW W h + 0) := by
      rw [List.length_cons, Nat.succ_mul]
      omega
    rw [e]
    exact OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind (by intro _; trivial)
      (costW_linksO i t₁ l fun b hb => hl b (List.mem_cons_of_mem _ hb)))
      (costW_linkO W cA h i t₁ a.2 a.1 (hl a (List.mem_cons_self ..)))

theorem costW_commitAt (i : I) (d : DrawC lam L Bd aT aL h.KT h.KL) (hd : FitC W h d) :
    (commitAt W S cA h i d).CostBoundR wt (commitF W h) := by
  refine OComp.CostBoundR.bind (fun t₁ => ?_) (costW_tabO W S h.b₀ i d.r _)
  have q2 := costW_tabsO W S h i d.copies
  rw [hd.2.1] at q2
  refine OComp.CostBoundR.bind (fun ts => ?_) q2
  have q3 := costW_proveX Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
    (cmsTA cA t₁.tree.root (L.recOf i t₁.r t₁.seed).2) (L.recOf i t₁.r t₁.seed) (L.encodeIndex i t₁.r)
    (fun _ => t₁.tree) (h.st.T i t₁.r t₁.seed d.κ) (h.dressT (h.rvT d.κ) d.co) h.capT
  have e3 : (h.dressT (h.rvT d.κ) d.co).path.length = W.depthReqT := hd.1
  rw [e3] at q3
  refine OComp.CostBoundR.bind (fun a => ?_) q3
  have q4 := costW_linksO W cA h i t₁ (d.copies.zip ts) fun b hb =>
    hd.2.2 b.1 (List.of_mem_zip (a := b.1) (b := b.2) hb).1
  have hlen : (d.copies.zip ts).length * linkW W h ≤ (h.M + 1) * linkW W h := by
    refine Nat.mul_le_mul_right _ ?_
    rw [List.length_zip, hd.2.1]
    exact Nat.min_le_left _ _
  exact OComp.CostBoundR.bind (by intro _; trivial) (q4.mono hlen)

/-- **The committer, in hash queries, on every path.** -/
theorem costW_commitW (hp : PathsFit W h) (i : I) :
    (commitW W S cA h i).CostBoundR wt (commitF W h) :=
  costR_bindOut (fun d hd => costW_commitAt W S cA h i d hd) _ (queryBound_coinsC W h)
    (allOut_coinsC W h hp)

theorem costW_proveAt (isk : Isk lam L Bd aT aL) (x : X) (d : DrawP lam L Bd aT aL h.KB)
    (hd : d.co.path.length = W.depthReq) :
    (proveAt W cA r₀ h isk x d).CostBoundR wt (proveF W h) := by
  unfold proveAt
  cases isk.copies[d.j]? with
  | none => trivial
  | some t =>
    have q := costW_proveX Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀)
      (cmsBA cA t.tree.root (L.recOf isk.i t.r t.seed).2) (x, L.recOf isk.i t.r t.seed)
      (L.encodeIndex isk.i t.r) (fun _ => t.tree) (h.st.B isk.i t.r t.seed x (h.nm d.j) d.κ)
      (h.dressB (h.rvB d.κ) d.co) h.capB
    have e : (h.dressB (h.rvB d.κ) d.co).path.length = W.depthReq := hd
    rw [e] at q
    exact OComp.CostBoundR.bind (by intro _; trivial) q

/-- **The prover, in hash queries, on every path.** -/
theorem costW_proveW (hp : PathsFit W h) (isk : Isk lam L Bd aT aL) :
    ∀ b : List (X × Unit), (proveW W cA r₀ h isk b).CostBoundR wt (proveF W h)
  | [] => trivial
  | [(x, _)] =>
    costR_bindOut (P := fun d : DrawP lam L Bd aT aL h.KB => d.co.path.length = W.depthReq)
      (fun d hd => (OComp.CostBoundR.bind (t := 0) (by intro _; trivial)
        (costW_proveAt W cA r₀ h isk x d hd)).mono (by omega)) _
      (fun _ _ _ => trivial) (fun _ _ e => hp.B e)
  | _ :: _ :: _ => trivial

end OnBytes.WholeKey

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead VerifierAndGoals
open VerifiableInference.AtEveryRequest (WithinBudget)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Read
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {J K' P' : Type} (idx : J → R.Index) (x₀ : R.Instance)
  (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
  (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
  (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool)

/-- queryBound_frontKC with the count over one hash function as a letter. -/
theorem queryBound_frontKC_over (q₀ C : ℕ) (hq : T.Pub.QueryBound q₀)
    (hC : ∀ d i, ((commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i).overOne (T.m d)).QueryBound C) (w : J) :
    ((frontArgK T h idx x₀ κ ϖ Vf).C w).QueryBound (q₀ + C + 1) := by
  have hG : ((readTold T h).C (idx w)).QueryBound (q₀ + (C + 0 + 0)) :=
    hq.bind fun d =>
      OComp.QueryBound.bind
        (OComp.QueryBound.bind (hC d (idx w)) fun _ => trivial)
        fun _ => trivial
  exact ZKCP.OComp.QueryBound.bind _ 1
    (fun keys => ZKCP.OComp.QueryBound.mapO _ _ 1 (ZKCP.queryBound_keyDigest _ _)) _ _
    (queryBound_oneOf_C (readTold T h) (idx w) hG)

/-- queryBound_frontKP with the count over one hash function as a letter. -/
theorem queryBound_frontKP_over (C : ℕ)
    (hP : ∀ d isk b, ((proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk b).overOne (T.m d)).QueryBound C)
    (isk : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))
    (x' : List Token × List Token) :
    ((frontArgK T h idx x₀ κ ϖ Vf).P isk x' ()).QueryBound C := by
  have hG : ((readTold T h).P isk.2 [(instOf R x₀ x', ())]).QueryBound C :=
    hP isk.2.1 isk.2.2 [(instOf R x₀ x', ())]
  exact ZKCP.OComp.QueryBound.mapO _ _ _
    (queryBound_oneOf_P (readTold T h) isk.2 (instOf R x₀ x') () hG)

end Read

/-- The count with NC and NP already in hash queries: no query to sample; the committer: the public
reading, NC, one for the ID; the prover: the committer again, NP. -/
def slotBudgetFine (q₀ NC NP : ℕ) : ℕ := 2 * (q₀ + NC + 1) + NP

section Slot
variable (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)
  (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
  (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : Parser D Z Form)
  (encF : TypedProof (D.F Z) (D.P Z) → Form) (bound : ℕ)

/-- **The honest side of slotSystem, oracle by oracle.** NC and NP count HASH queries: a tree query
one, a Fiat-Shamir query or try K + 1. -/
theorem slotSystem_withinBudget_fine {q₀ NC NP : ℕ} (hq : T.Pub.QueryBound q₀)
    (hp : ∀ d, PathsFit (D.input Z c₀ m₀).queryLayout (h d))
    (hC : ∀ d, commitF (D.input Z c₀ m₀).queryLayout (h d) ≤ NC)
    (hP : ∀ d, proveF (D.input Z c₀ m₀).queryLayout (h d) ≤ NP) :
    WithinBudget (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound)
      (slotBudgetFine q₀ NC NP) := by
  have hv := fun d => blocks_le_costW (T.m d) (by norm_num)
  have hC' : ∀ w, ((frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).C w).QueryBound
      (q₀ + NC + 1) := fun w =>
    queryBound_frontKC_over T h idx x₀ _ _ _ q₀ NC hq
      (fun d i => queryBound_overOne_of_costR (T.m d) _ (hv d) _ _
        ((costW_commitW _ _ _ _ (hp d) i).mono (hC d))) w
  have hP' : ∀ isk x', ((frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).P isk x' ()).QueryBound
      NP := fun isk x' =>
    queryBound_frontKP_over T h idx x₀ _ _ _ NP
      (fun d isk b => queryBound_overOne_of_costR (T.m d) _ (hv d) _ _
        ((costW_proveW _ _ _ _ (hp d) isk b).mono (hP d))) isk x'
  refine ⟨0, q₀ + NC + 1, (q₀ + NC + 1) + NP, le_of_eq ?_, fun _ => trivial,
    fun w coins => ?_, fun w coins prompt output => ?_⟩
  · unfold slotBudgetFine
    ring
  · exact queryBound_deterministicOf _ _
      (ZKCP.OComp.QueryBound.mapO _ _ _ (ZKCP.OComp.QueryBound.withCoins _ _ _ (hC' w)))
  · exact (RandomizedAlgorithm.queryBound_ofUpload _ _).2
      (ZKCP.queryBound_P_coinsFirst _ bound w coins (prompt, output) () _ _ (hC' w)
        fun isk => hP' isk _)

end Slot

end OnBytes.FrontRoad

#print axioms OnBytes.Prover.blocks_le_costW
#print axioms OnBytes.Prover.costW_chainO
#print axioms Rom.queryBound_overOne_of_costR
#print axioms OnBytes.WholeKey.costW_commitW
#print axioms OnBytes.WholeKey.costW_proveW
#print axioms OnBytes.FrontRoad.slotSystem_withinBudget_fine
