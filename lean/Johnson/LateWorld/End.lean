-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/End.lean: THE HONEST SIDE THAT LAYS LATE IS CLOSE TO THE REDUCTION AROUND THE REAL
GAME: Spec.lateToWrap (Johnson/LateWorld/SpecWrap.lean), FROM ITS PARTS.

This file states no goal of the release. The parts that are proved in other files are hypotheses
here, each a named statement; Johnson/LateWorld/Whole.lean puts their proofs in.

The way.
  1. lateW to lateC, the same with a counter for each copy: Prob.pOver (M + 1) s1 n
     (late_to_count, Johnson/LateWorld/Count.lean; Rom/Overrun.lean is called there).
  2. lateC against the reduction around the game. The adversary's first move is the setup, from
     empty tables. Both setups are "phase1, then a rest" with ONE phase1 (Spec.lateNormal,
     Spec.setupNormal). Where all seeds that phase1 gives lie in Gs, the two rests agree under the
     map of states, and lead into the invariant (contW_good); from there on the two challengers give
     the same law of output (after_setup, Johnson/LateWorld/Batch.lean). So the distance is at most
     the probability that phase1 gives a seed outside Gs: (M + 2) · δ (Spec.phaseBad).

Main names (namespace OnBytes.LateWorld).
  Spec.phaseLen, Spec.phaseCoins   two facts on what phase1 can give.
  drawRs_eq      the honest side's draws of encoding randomness are uniform.
  contW_good     the reduction's rest, where all seeds lie in Gs.
  outW, outC     the law of an adversary's output against the two challengers, with the states'
                 types written out (outW_call, outC_call, replyC_setup: unfoldings).
  rest_eq        the two rests, each followed by the adversary.
  lateToWrap_of  THE STATEMENT from its parts.

Limits. lateToWrap_of has eleven hypotheses and proves nothing without them. For adversaries whose
first move is the setup. outW and outC are devices of the proof and stand in no statement on the
scheme.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Good

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry OnBytes.WrapLaws
open _root_.Compile.GlueB (GCall GIn GAdm asW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- phase1 gives M + 1 copies' coins and M + 1 copies' tables. -/
def Spec.phaseLen : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (h : HonestSide lam L Bd aT aL) (T : Tb W),
    ∀ ω ∈ (phase1 W S h T).support, ω.d.copies.length = h.M + 1 ∧ ω.os.length = h.M + 1

/-- The coins of compiled runs that phase1 gives are members of the enumerations. -/
def Spec.phaseCoins : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (h : HonestSide lam L Bd aT aL) (T : Tb W),
    ∀ ω ∈ (phase1 W S h T).support,
      (∃ n, ω.d.co = h.coT.e n) ∧ ∀ d' ∈ ω.d.copies, ∃ n, d'.co = h.coL.e n

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  {cA : L.OutOfDomainAnswer → List (Dig lam)} (r₀ : L.Rec) {a : AtRecs lam L Bd aT aL} {Gs : L.OutOfDomainSeed → Prop}
  (s1 : ℕ) (i : I)

theorem drawRs_eq (hri : a.ri.OK) : ∀ n : ℕ, drawRs a.side n = drawU L n
  | 0 => rfl
  | n + 1 => by
    rw [drawRs, drawU, drawRs_eq hri n]
    exact bind_enum (β := L.EncodingRandomness) a.ri hri fun r => (drawU L n).bind fun rs => PMF.pure (r :: rs)

/-! ## The reduction's rest, where all seeds lie in Gs -/

theorem contW_good (hT : Spec.testBranch) (hLk : Spec.linksW) (hGT : Spec.gameTabsGood)
    (hK : Spec.stAfterKeeps) (hC : Spec.stAfterCopies) (hO : Spec.stAfterOod) {ok : I → Prop}
    {δ : ℝ≥0∞} (hP : PremLate W S cA a ok Gs δ) (hi : ok i) (ω : Om W a.side)
    (hl1 : ω.d.copies.length = a.M + 1) (hl2 : ω.os.length = a.M + 1)
    (hcT : ω.d.co.path.length = W.depthReqT)
    (hcL : ∀ d' ∈ ω.d.copies, d'.co.path.length = W.depthReqL) (hg₁ : Gs ω.o₁.2)
    (hgs : ∀ x ∈ ω.os, Gs x.2) (Tg : Tb W) :
    contW W cA r₀ a Gs s1 i ω (none, Tg) =
      (unif L.EncodingRandomness).bind fun r₁ => (drawU L ω.os.length).bind fun rs =>
        (contAt W cA a.side i ω r₁ rs).map fun o =>
          ((.inl o.1.1, (o.2, some (mkTs i rs ω.os))),
            (some (0 + ω.os.length, linksUsed usedT 1 (a.M + 1),
              stAfter (0, fun _ => (r₁, ω.o₁.2)) rs ω.os), Tg)) := by
  unfold contW
  rw [game_start r₀ s1 i Tg ω.o₁.2 hg₁, PMF.bind_map]
  refine congrArg _ (funext fun r₁ => ?_)
  show (gameTabs W r₀ a Gs s1 i ω.os
    (some (0, Hiop.UsedR.zero, (0, fun _ => (r₁, ω.o₁.2))), Tg)).bind _ = _
  rw [hGT I X lam L Bd aT aL W r₀ a Gs s1 i ω.os 0 Hiop.UsedR.zero (0, fun _ => (r₁, ω.o₁.2)) Tg
    hgs (by omega), PMF.bind_map]
  refine Rom.bind_congr_support _ fun rs hrs => ?_
  have hrl := drawU_len _ rs hrs
  have htl := mkTs_len i rs ω.os hrl
  have hzl : (ω.d.copies.zip (mkTs i rs ω.os)).length = a.M + 1 := by
    rw [List.length_zip, hl1, htl, hl2, Nat.min_self]
  show runG W r₀ a Gs s1 i (restA W cA r₀ a.side ω.d ω.T (some ⟨ω.o₁.1, L.recOf i r₁ ω.o₁.2⟩)
    (some (mkTs i rs ω.os)))
    (some (0 + ω.os.length, Hiop.UsedR.zero, stAfter (0, fun _ => (r₁, ω.o₁.2)) rs ω.os), Tg) = _
  rw [restA_good r₀ s1 i hT hLk hP hi ω.d ω.T ω.o₁.1 r₁ ω.o₁.2 (mkTs i rs ω.os)
    (0 + ω.os.length) (stAfter (0, fun _ => (r₁, ω.o₁.2)) rs ω.os) Tg
    (hK I X lam L Bd aT aL rs ω.os (0, fun _ => (r₁, ω.o₁.2)) 0 (Nat.le_refl 0)) hcT
    (by rw [hzl, hl2]; omega)
    (fun k x hx => by
      obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.1 hx
      exact ⟨hO I X lam L Bd aT aL i rs ω.os (0, fun _ => (r₁, ω.o₁.2)) k x.2 h2,
        hcL x.1 (List.mem_of_getElem? h1)⟩)]
  have hm1 : ((ω.d.copies.zip (mkTs i rs ω.os)).map fun x => x.1.co) =
      ω.d.copies.map fun d => d.co := by
    have e : ((ω.d.copies.zip (mkTs i rs ω.os)).map Prod.fst).map (fun d => d.co) =
        (ω.d.copies.zip (mkTs i rs ω.os)).map fun x => x.1.co := by
      rw [List.map_map]
      rfl
    rw [← e, List.map_fst_zip (by rw [hl1, htl, hl2])]
  have hm2 : ((ω.d.copies.zip (mkTs i rs ω.os)).map fun x => x.2) = mkTs i rs ω.os :=
    List.map_snd_zip (by rw [hl1, htl, hl2])
  have hc' : realCopies W a i (stAfter (0, fun _ => (r₁, ω.o₁.2)) rs ω.os).2 1 (mkTs i rs ω.os) =
      realTabs W a.b₀ i rs ω.os := hC I X lam L Bd aT aL W a i rs ω.os (0, fun _ => (r₁, ω.o₁.2))
  rw [hm1, hm2, hc', hzl]
  unfold contAt
  simp only [PMF.map_bind, PMF.pure_map]
  rfl

/-! ## The law of an adversary's output, with the states' types written out -/

section Out
variable {α : Type}

variable (W S cA a Gs) in
/-- Against the reduction around the real game. -/
def outW (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
    (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (s : StWG W) : PMF α :=
  (interact (wrapG W S cA r₀ a Gs s1 i) A s).map Prod.fst

variable (W S cA) in
/-- Against the honest side that lays late and counts. -/
def outC (h : HonestSide lam L Bd aT aL) (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
    (GCall X Unit) (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (s : StC W h) : PMF α :=
  (interact (lateC W S cA r₀ h s1 i) A s).map Prod.fst

theorem outW_call (c : GCall X Unit) (k : GIn (FullKey lam L aT aL) (RequestProof lam L) →
    Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
      (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (s : StWG W) :
    outW W S cA r₀ a Gs s1 i (.call c k) s =
      (repW W S cA r₀ a Gs s1 i s c).bind fun p => outW W S cA r₀ a Gs s1 i (k p.1) p.2 :=
  PMF.map_bind _ _ _

theorem outC_call (h : HonestSide lam L Bd aT aL) (c : GCall X Unit)
    (k : GIn (FullKey lam L aT aL) (RequestProof lam L) →
      Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
        (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (s : StC W h) :
    outC W S cA r₀ s1 i h (.call c k) s =
      (replyC W S cA r₀ h s1 i s c (oneOwn c s.1.1)).bind fun p =>
        outC W S cA r₀ s1 i h (k p.1) p.2 :=
  PMF.map_bind _ _ _

/-- The setup of the honest side that counts, from a state without a key. -/
theorem replyC_setup (h : HonestSide lam L Bd aT aL) (T : Tb W) (ct : Fin (h.M + 1) → ℕ) :
    replyC W S cA r₀ h s1 i ((none, T), ct) .setup none =
      (lateCommit W S cA h i T).map fun o => (.inl o.1.1, ((some o.1.2, o.2), ct)) :=
  map_map_eq _ _ _ _ fun _ => rfl

end Out

/-! ## The two rests, each followed by the adversary -/

theorem rest_eq (hT : Spec.testBranch) (hLk : Spec.linksW) (hGT : Spec.gameTabsGood)
    (hK : Spec.stAfterKeeps) (hC : Spec.stAfterCopies) (hO : Spec.stAfterOod) {ok : I → Prop}
    {δ : ℝ≥0∞} (hP : PremLate W S cA a ok Gs δ) (hi : ok i) {α : Type}
    {okb : ZKCP.Gen.Batch X Unit → Prop} (hok : ∀ b, okb b → b.length ≤ 1)
    (k : GIn (FullKey lam L aT aL) (RequestProof lam L) →
      Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
        (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ) (hk : ∀ x, GAdm okb (k x) true n)
    (ω : Om W a.side) (hl1 : ω.d.copies.length = a.M + 1) (hl2 : ω.os.length = a.M + 1)
    (hcT : ω.d.co.path.length = W.depthReqT)
    (hcL : ∀ d' ∈ ω.d.copies, d'.co.path.length = W.depthReqL) (hg₁ : Gs ω.o₁.2)
    (hgs : ∀ x ∈ ω.os, Gs x.2) (Tg : Tb W) :
    ((contC W cA a.side i ω).bind fun o =>
        outC W S cA r₀ s1 i a.side (k (.inl o.1.1)) ((some o.1.2, o.2), fun _ => 0)) =
      (contW W cA r₀ a Gs s1 i ω (none, Tg)).bind fun z =>
        outW W S cA r₀ a Gs s1 i (k z.1.1) (z.1.2, z.2) := by
  rw [contW_good r₀ s1 i hT hLk hGT hK hC hO hP hi ω hl1 hl2 hcT hcL hg₁ hgs Tg]
  unfold contC
  have hen : ((unif (Fin (a.side.ri.n + 1))).bind fun a' =>
      (drawU L ω.os.length).bind fun rs => contAt W cA a.side i ω (a.side.ri.e a') rs) =
      (unif L.EncodingRandomness).bind fun r₁ =>
        (drawU L ω.os.length).bind fun rs => contAt W cA a.side i ω r₁ rs :=
    bind_enum (β := L.EncodingRandomness) a.ri hP.ri fun r₁ =>
      (drawU L ω.os.length).bind fun rs => contAt W cA a.side i ω r₁ rs
  rw [drawRs_eq hP.ri, hen]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine congrArg _ (funext fun r₁ => ?_)
  refine Rom.bind_congr_support _ fun rs hrs => ?_
  have hrl := drawU_len _ rs hrs
  have htl := mkTs_len i rs ω.os hrl
  unfold contAt
  simp only [PMF.bind_bind, PMF.pure_bind]
  refine congrArg _ (funext fun o₃ => congrArg _ (funext fun o₄ => ?_))
  have hinv : InvG W a i ((o₄.2, some (mkTs i rs ω.os)),
      (some (0 + ω.os.length, linksUsed usedT 1 (a.M + 1),
        stAfter (0, fun _ => (r₁, ω.o₁.2)) rs ω.os), Tg)) :=
    ⟨o₄.2, mkTs i rs ω.os, 0 + ω.os.length, _, _, Tg, rfl, htl.trans hl2, by rw [htl]; omega,
      fun e t ht => by
        have h := hO I X lam L Bd aT aL i rs ω.os (0, fun _ => (r₁, ω.o₁.2)) e t ht
        have e1 : ((0, fun _ => (r₁, ω.o₁.2)) : StH L).1 + 1 + e = e + 1 := by
          show 0 + 1 + e = e + 1
          omega
        rwa [e1] at h⟩
  have hafter := after_setup r₀ s1 i hP hi hok (k (.inl ⟨ω.o₁.1.root, L.recOf i r₁ ω.o₁.2, o₃.1,
    o₄.1⟩)) n (hk _) _ hinv
  refine Eq.trans ?_ hafter.symm
  show outC W S cA r₀ s1 i a.side _ _ = outC W S cA r₀ s1 i a.side _ _
  refine congrArg _ (Prod.ext (Prod.ext ?_ rfl) ?_)
  · show some (⟨i, realTabs W a.b₀ i rs ω.os⟩ : Isk lam L Bd aT aL) =
      some ⟨i, realCopies W a i (stAfter (0, fun _ => (r₁, ω.o₁.2)) rs ω.os).2 1 (mkTs i rs ω.os)⟩
    rw [show realCopies W a i (stAfter (0, fun _ => (r₁, ω.o₁.2)) rs ω.os).2 1 (mkTs i rs ω.os) =
      realTabs W a.b₀ i rs ω.os from hC I X lam L Bd aT aL W a i rs ω.os (0, fun _ => (r₁, ω.o₁.2))]
  · funext j
    show 0 = (linksUsed usedT 1 (a.M + 1)).sess (j.val + 1)
    rw [linksUsed_sess]
    rfl

/-! ## The statement from its parts -/

/-- **THE STATEMENT, from its parts.** -/
theorem lateToWrap_of (hN : Spec.lateNormal) (hB : Spec.phaseBad) (hLen : Spec.phaseLen)
    (hCo : Spec.phaseCoins) (hSN : Spec.setupNormal) (hT : Spec.testBranch) (hLk : Spec.linksW)
    (hGT : Spec.gameTabsGood) (hK : Spec.stAfterKeeps) (hC : Spec.stAfterCopies)
    (hO : Spec.stAfterOod) : Spec.lateToWrap := by
  intro I X lam L Bd aT aL W S cA r₀ a ok Gs δ s1 i hP hi α okb k n hok hA
  have hk : ∀ x, GAdm okb (k x) true n := hA.2
  refine (tv_triangle _ (outC W S cA r₀ s1 i a.side (.call .setup k)
    ((none, Table.empty _), fun _ => 0)) _).trans
    (add_le_add (late_to_count W S cA r₀ a.side s1 i (.call .setup k) false n hA
      (none, Table.empty _)) ?_)
  show tv (outC W S cA r₀ s1 i a.side (.call .setup k) ((none, Table.empty _), fun _ => 0))
    (outW W S cA r₀ a Gs s1 i (.call .setup k) ((Table.empty _, none), (none, Table.empty _))) ≤ _
  have eC : outC W S cA r₀ s1 i a.side (.call .setup k) ((none, Table.empty _), fun _ => 0) =
      (phase1 W S a.side (Table.empty _)).bind fun ω => (contC W cA a.side i ω).bind fun o =>
        outC W S cA r₀ s1 i a.side (k (.inl o.1.1)) ((some o.1.2, o.2), fun _ => 0) := by
    rw [outC_call]
    show (replyC W S cA r₀ a.side s1 i ((none, Table.empty _), fun _ => 0) .setup none).bind _ = _
    rw [replyC_setup, hN I X lam L Bd aT aL W S cA a.side i (Table.empty _), PMF.bind_map,
      PMF.bind_bind]
    rfl
  have eW : outW W S cA r₀ a Gs s1 i (.call .setup k)
      ((Table.empty _, none), (none, Table.empty _)) =
      (phase1 W S a.side (Table.empty _)).bind fun ω =>
        (contW W cA r₀ a Gs s1 i ω (none, Table.empty _)).bind fun z =>
          outW W S cA r₀ a Gs s1 i (k z.1.1) (z.1.2, z.2) := by
    rw [outW_call, repW_setup]
    show ((runG W r₀ a Gs s1 i (setupA W S cA r₀ a.side (Table.empty _))
      (none, Table.empty _)).map _).bind _ = _
    rw [hSN I X lam L Bd aT aL W S cA r₀ a Gs s1 i (Table.empty _) (none, Table.empty _),
      PMF.bind_map, PMF.bind_bind]
    rfl
  rw [eC, eW]
  refine (tv_bind_right_le_add _ _ _ {ω | ¬ Gs ω.o₁.2 ∨ ∃ x ∈ ω.os, ¬ Gs x.2} (z := 0)
    fun ω hω hgood => ?_).trans ?_
  · have hg : Gs ω.o₁.2 ∧ ∀ x ∈ ω.os, Gs x.2 := by
      by_contra hn
      refine hgood ?_
      by_cases h1 : Gs ω.o₁.2
      · refine Or.inr ?_
        by_contra h2
        exact hn ⟨h1, fun x hx => by
          by_contra h3
          exact h2 ⟨x, hx, h3⟩⟩
      · exact Or.inl h1
    obtain ⟨hl1, hl2⟩ := hLen I X lam L Bd aT aL W S a.side (Table.empty _) ω hω
    obtain ⟨⟨nT, hnT⟩, hcs⟩ := hCo I X lam L Bd aT aL W S a.side (Table.empty _) ω hω
    rw [rest_eq r₀ s1 i hT hLk hGT hK hC hO hP hi hok k n hk ω hl1 hl2
      (by rw [hnT]; exact hP.pathT nT)
      (fun d' hd' => by
        obtain ⟨nL, hnL⟩ := hcs d' hd'
        rw [hnL]
        exact hP.pathL nL) hg.1 hg.2 (Table.empty _), tv_self]
  · rw [add_zero]
    exact hB I X lam L Bd aT aL W S a.side Gs δ (Table.empty _) hP.seeds (seedsIn_empty W S Gs)

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.contW_good
#print axioms OnBytes.LateWorld.rest_eq
#print axioms OnBytes.LateWorld.lateToWrap_of
