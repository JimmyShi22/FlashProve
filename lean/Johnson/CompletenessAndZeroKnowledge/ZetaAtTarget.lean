-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/ZetaAtTarget.lean: the error term zetaW of the statement of index privacy
(Johnson/WholeKey/Zeta.lean) at one copy, 688,127 requests and 2 ^ 64 + 1 queries, finer than boundZ
(E2E/ZetaAtCaps.lean).

Why finer. boundZ charges every one of the 9 + CT + CL + CB counted oracle names with the count of
the name that has most queries, and takes 2 ^ 39 for the leaves of a session. Here the leaves' name,
the eight other names and the names of further tries are counted apart, at the exact numbers of
the written data.

What this file has (namespace AtPublicFiles.ZetaAt.Target).
  cost_fine          for arbitrary parameters: the hash term of zetaW in three classes of names.
  Fine r             nine numbers of the parameters, and the tests.
  fine_description   Fine at the verifier's parameters at Z, for Z in scope with a live description.
  zeta_target_256    at most 2 ^ -143 plus the weighted sum of the seven error numbers, with at least
                     256 free bits in a leaf's salt.
  zeta_target_304    at most 2 ^ -157 plus the same sum, with at least 304 free bits.

Limits. Arithmetic on a written expression. Nothing here says that a prover exists at these letters,
or what the seven error numbers are. Search limits of at most 2 ^ 40. t is the number at which
zetaW is read, at most 2 ^ 64 + 1: the statement on the scheme with the commitment alone reads
zetaW at one query more than the adversary asks, so this serves at most 2 ^ 64 hash queries.
-/
import E2E.ZetaCaps
import E2E.ZetaTriesAtInput
import Johnson.WholeKey.ZetaSplit
import Johnson.Goal.Conditions.KeyDepthAtThe
import Johnson.Goal.Numbers.DepthAtThe

set_option autoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.ZetaAt.Target
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.ZetaAt
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open LPFD.Full (sBG sTG saltG)
open OnBytes.Slice (frS frZ)
open Johnson.G (dKeyFull dProofFull lenE writtenKFull_eq writtenPFull_eq)

local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName
local notation "Lf" => TypedOracleCompiler.Compile.Batch.OracleName.leaf

theorem sum_union_le {ι : Type} [DecidableEq ι] (s t : Finset ι) (f : ι → ℝ≥0∞) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter]
  exact le_self_add

theorem mul_div_nat (k x : ℕ) (d : ℝ≥0∞) :
    (k : ℝ≥0∞) * ((x : ℝ≥0∞) / d) = ((k * x : ℕ) : ℝ≥0∞) / d := by
  rw [Nat.cast_mul k x, mul_div_assoc]

/-- One term of the sum of costTotal. -/
theorem term_le (m e l A B b : ℕ) (hm : m ≤ A) (he : e ≤ B) (hl : b ≤ l) :
    (m : ℝ≥0∞) * (e + m : ℕ) / 2 ^ l ≤ ((A * (B + A) : ℕ) : ℝ≥0∞) / 2 ^ b := by
  refine ENNReal.div_le_div ?_ (pow_le_pow_right₀ (by norm_num) hl)
  have : m * (e + m) ≤ A * (B + A) := Nat.mul_le_mul hm (Nat.add_le_add he hm)
  exact_mod_cast this

section
variable {lam K : ℕ}

/-- A further try's count is at most the tests of the wiring. -/
theorem nLater_le_cnt (cap : ℕ → ℕ) (j : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ), nLater s A W cap i j ≤ cnt s A W
  | [], _, _, _ => Nat.le_refl _
  | _ :: s, (a, A), (w, W), i => by
    show (if roundHasTest a w = true ∧ j + 1 ≤ cap i then 1 else 0) + nLater s A W cap (i + 1) j ≤
      cntR w + cnt s A W
    have ih := nLater_le_cnt cap j s A W (i + 1)
    have h1 : (if roundHasTest a w = true ∧ j + 1 ≤ cap i then 1 else 0) ≤ cntR w := by
      split
      · rename_i h
        have h0 := h.1
        unfold roundHasTest at h0
        unfold cntR
        split at h0 <;> simp [h0]
      · exact Nat.zero_le _
    omega
end

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (p : Params) (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) (u : NumsW)

/-- **The hash term of zetaW in three classes of names**: the leaves' name; the eight other names
of the nine; the names of further tries, which have no queries without a secret. -/
theorem cost_fine (t n Al Ab A2 CT CL CB b : ℕ) (hT : ∀ i, a.capT i ≤ CT) (hL : ∀ i, a.capL i ≤ CL)
    (hB : ∀ i, a.capB i ≤ CB) (hb1 : b ≤ c.ℓ) (hb2 : 256 ≤ p.sFS) (hb3 : 256 ≤ lam)
    (hl : mW W a n .leaf ≤ Al)
    (h8 : ∀ o ∈ nine.erase Lf, mW W a n o ≤ Ab)
    (h2 : ∀ tg j, mW W a n (.fbw tg j) ≤ A2) (h2b : A2 ≤ Ab) :
    Rom.costTotal (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (eW W S a n) (mW W a n)
        (bitsW (lam := lam) p c) (osW W a) t ≤
      ((t * Al + Al * (0 + Al) : ℕ) : ℝ≥0∞) / 2 ^ b +
        ((t * Ab + 8 * (Ab * (2 * (a.M + 2) + Ab)) + (CT + CL + CB) * (A2 * (0 + A2)) : ℕ) :
          ℝ≥0∞) / 2 ^ 256 := by
  set e := eW W S a n with he
  set m := mW W a n with hm
  set ℓ := bitsW (lam := lam) p c with hℓ
  have b256 : ∀ o, o ≠ Lf → 256 ≤ ℓ o := by
    intro o ho
    cases o <;> first
      | exact absurd rfl ho
      | exact hb3
      | exact le_min hb2 hb3
  have e0 : ∀ tg j, e (.fbw tg j) = 0 := fun _ _ => rfl
  have eB : ∀ o ∈ nine.erase Lf, e o ≤ 2 * (a.M + 2) := by
    intro o ho
    have ho' := (Finset.mem_erase.1 ho).2
    simp only [nine, Finset.mem_insert, Finset.mem_singleton] at ho'
    rcases ho' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.zero_le _
      | (show (if _ then 2 * (a.M + 2) else 0) ≤ _
         split
         · exact Nat.le_refl _
         · exact Nat.zero_le _)
  -- the supremum
  have hsup : (osW W a).sup (fun o => (m o : ℝ≥0∞) / 2 ^ ℓ o) ≤
      (Al : ℝ≥0∞) / 2 ^ b + (Ab : ℝ≥0∞) / 2 ^ 256 := by
    refine Finset.sup_le fun o ho => ?_
    by_cases ol : o = Lf
    · subst ol
      refine le_trans (ENNReal.div_le_div (by exact_mod_cast hl)
        (pow_le_pow_right₀ (by norm_num) hb1)) le_self_add
    · have hmo : m o ≤ Ab := by
        rcases osW_mem W a ho with h | ⟨tg, j, rfl⟩
        · exact h8 o (Finset.mem_erase.2 ⟨ol, h⟩)
        · exact (h2 tg j).trans h2b
      refine le_trans (ENNReal.div_le_div (by exact_mod_cast hmo)
        (pow_le_pow_right₀ (by norm_num) (b256 o ol))) le_add_self
  -- the sum
  let f : ON₂ → ℝ≥0∞ := fun o => (m o : ℝ≥0∞) * (e o + m o : ℕ) / 2 ^ ℓ o
  have hnine : ∑ o ∈ nine, f o ≤ ((Al * (0 + Al) : ℕ) : ℝ≥0∞) / 2 ^ b +
      ((8 * (Ab * (2 * (a.M + 2) + Ab)) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [← Finset.add_sum_erase nine f (by decide : Lf ∈ nine)]
    refine add_le_add (term_le _ _ _ _ _ _ hl (Nat.zero_le _) hb1) ?_
    have hc : (nine.erase Lf).card ≤ 8 := by decide
    calc ∑ o ∈ nine.erase Lf, f o
        ≤ ∑ _o ∈ nine.erase Lf, ((Ab * (2 * (a.M + 2) + Ab) : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
          Finset.sum_le_sum fun o ho => term_le _ _ _ _ _ _ (h8 o ho) (eB o ho)
            (b256 o (Finset.ne_of_mem_erase ho))
      _ = ((nine.erase Lf).card : ℝ≥0∞) *
            (((Ab * (2 * (a.M + 2) + Ab) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((8 : ℕ) : ℝ≥0∞) * (((Ab * (2 * (a.M + 2) + Ab) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
          gcongr
      _ = ((8 * (Ab * (2 * (a.M + 2) + Ab)) : ℕ) : ℝ≥0∞) / 2 ^ 256 := mul_div_nat _ _ _
  have hlater : ∀ (tg : Tag) (k C : ℕ), k ≤ C →
      ∑ o ∈ laterNames tg k, f o ≤ ((C * (A2 * (0 + A2)) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    intro tg k C hk
    calc ∑ o ∈ laterNames tg k, f o
        ≤ ∑ _o ∈ laterNames tg k, ((A2 * (0 + A2) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          refine Finset.sum_le_sum fun o ho => ?_
          obtain ⟨j, rfl⟩ := later_mem ho
          exact term_le _ _ _ _ _ _ (h2 tg j) (le_of_eq (e0 tg j)) (b256 _ (by simp))
      _ = ((laterNames tg k).card : ℝ≥0∞) * (((A2 * (0 + A2) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C : ℝ≥0∞) * (((A2 * (0 + A2) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
          gcongr
          exact_mod_cast (later_card tg k).trans hk
      _ = ((C * (A2 * (0 + A2)) : ℕ) : ℝ≥0∞) / 2 ^ 256 := mul_div_nat _ _ _
  have hsum : ∑ o ∈ osW W a, f o ≤ ((Al * (0 + Al) : ℕ) : ℝ≥0∞) / 2 ^ b +
      ((8 * (Ab * (2 * (a.M + 2) + Ab)) + (CT + CL + CB) * (A2 * (0 + A2)) : ℕ) : ℝ≥0∞) /
        2 ^ 256 := by
    have u1 := sum_union_le (nine ∪ laterNames .test (maxCap L.offline.shape aT (wTC W).sh a.capT 0) ∪
      laterNames .link (maxCap L.link.shape aL (wLC W).sh a.capL 0))
      (laterNames .onl (maxCap L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh a.capB 0)) f
    have u2 := sum_union_le (nine ∪ laterNames .test (maxCap L.offline.shape aT (wTC W).sh a.capT 0))
      (laterNames .link (maxCap L.link.shape aL (wLC W).sh a.capL 0)) f
    have u3 := sum_union_le nine (laterNames .test (maxCap L.offline.shape aT (wTC W).sh a.capT 0)) f
    have l1 := hlater .test _ CT (maxCap_le hT L.offline.shape aT (wTC W).sh 0)
    have l2 := hlater .link _ CL (maxCap_le hL L.link.shape aL (wLC W).sh 0)
    have l3 := hlater .onl _ CB (maxCap_le hB L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh 0)
    have e1 : osW W a = nine ∪ laterNames .test (maxCap L.offline.shape aT (wTC W).sh a.capT 0) ∪
        laterNames .link (maxCap L.link.shape aL (wLC W).sh a.capL 0) ∪
        laterNames .onl (maxCap L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh a.capB 0) := rfl
    rw [e1]
    refine u1.trans ((add_le_add (u2.trans (add_le_add (u3.trans (add_le_add hnine l1)) l2))
      l3).trans (le_of_eq ?_))
    simp only [Nat.cast_add, Nat.cast_mul, ENNReal.add_div, add_mul]
    ring
  unfold Rom.costTotal
  refine (add_le_add (mul_le_mul_left' hsup _) hsum).trans (le_of_eq ?_)
  simp only [Nat.cast_add, Nat.cast_mul, ENNReal.add_div, mul_add, mul_div_assoc]
  ring

/-- **zetaW with its seven error numbers apart**, at no more requests than one copy's sessions. -/
theorem zeta_fine (t n Al Ab A2 CT CL CB b : ℕ) (hn : n ≤ u.s1) (hT : ∀ i, a.capT i ≤ CT)
    (hL : ∀ i, a.capL i ≤ CL) (hB : ∀ i, a.capB i ≤ CB) (hb1 : b ≤ c.ℓ) (hb2 : 256 ≤ p.sFS)
    (hb3 : 256 ≤ lam) (hl : mW W a n .leaf ≤ Al)
    (h8 : ∀ o ∈ nine.erase Lf, mW W a n o ≤ Ab)
    (h2 : ∀ tg j, mW W a n (.fbw tg j) ≤ A2) (h2b : A2 ≤ Ab) :
    zetaW W S p a c u t n ≤
      (((t * Al + Al * (0 + Al) : ℕ) : ℝ≥0∞) / 2 ^ b +
        ((t * Ab + 8 * (Ab * (2 * (a.M + 2) + Ab)) + (CT + CL + CB) * (A2 * (0 + A2)) : ℕ) :
          ℝ≥0∞) / 2 ^ 256) +
      ((u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
          (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
          ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ) := by
  rw [zetaW_split W S p a c u t n]
  refine add_le_add ?_ le_rfl
  unfold zetaW
  rw [pOver_zero _ _ _ hn]
  have hc := cost_fine W S p a c t n Al Ab A2 CT CL CB b hT hL hB hb1 hb2 hb3 hl h8 h2 h2b
  simpa only [mul_zero, add_zero, zero_add] using hc

/-! ## The numbers at the written data -/

set_option maxRecDepth 1000000 in
theorem leaves_keyExact : leavesW dKeyFull = 33988608 :=
  leavesE_whole dKeyFull ▸ (by decide +kernel :
    leavesE (leavesE (leavesE 0 dKeyFull.ds₁) dKeyFull.ds₂) dKeyFull.ds₃ = 33988608)

set_option maxRecDepth 1000000 in
theorem leaves_proofExact : leavesW dProofFull = 670449664 :=
  leavesE_whole dProofFull ▸ (by decide +kernel :
    leavesE (leavesE (leavesE 0 dProofFull.ds₁) dProofFull.ds₂) dProofFull.ds₃ = 670449664)

theorem rounds_of (D : OnBytes.Maker.WholeD) (l₁ l₂ l₃ : ℕ) (h₁ : lenE 0 D.ds₁ = l₁)
    (h₂ : lenE 0 D.ds₂ = l₂) (h₃ : lenE 0 D.ds₃ = l₃) :
    roundsW D = 1 + (l₁ + (1 + (l₂ + (1 + l₃)))) := by
  have a1 := Johnson.G.lenE_eq D.ds₁ 0
  have a2 := Johnson.G.lenE_eq D.ds₂ 0
  have a3 := Johnson.G.lenE_eq D.ds₃ 0
  unfold roundsW
  omega

set_option maxRecDepth 1000000 in
theorem rounds_keyExact : roundsW dKeyFull = 18951 :=
  rounds_of dKeyFull 18850 68 30 Johnson.G.len_keyFull.1 Johnson.G.len_keyFull.2.1
    Johnson.G.len_keyFull.2.2

set_option maxRecDepth 1000000 in
theorem rounds_proofExact : roundsW dProofFull = 48393 :=
  rounds_of dProofFull 48292 68 30 Johnson.G.len_proofFull.1 Johnson.G.len_proofFull.2.1
    Johnson.G.len_proofFull.2.2

/-- **The numbers at which zetaW is read**: the leaves of the three wirings; the rounds; the depths of
the request trees; the tree over an encoded index; the two lengths of salts, and the tests. -/
structure Fine (r : InnerCompilerInput) : Prop where
  depth : r.queryLayout.depth = 32
  sFS : 256 ≤ r.compilerParameters.sFS
  lvT : lv r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh ≤ 33988608
  lvL : lv r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh ≤ 19030016
  lvB : lv r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh ≤ 670449664
  rT : r.protocol.offline.shape.length ≤ 18951
  rL : r.protocol.link.shape.length ≤ 42
  rB : r.protocol.onlineBatch.loc.shape.length ≤ 48393
  qT : r.queryLayout.depthReqT ≤ 0
  qL : r.queryLayout.depthReqL ≤ 0
  qB : r.queryLayout.depthReq ≤ 6
  nT : cnt r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh ≤ 19
  nL : cnt r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh ≤ 6
  nB : cnt r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh ≤ 46

theorem fine_atFiles (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256)) :
    Fine (VerifiableInference.OnPublicFiles.innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) := by
  have tr := tries_atFiles Z scope c₀ m₀
  have lv3 := lv_fullD (dataAtFiles flashProveData Z).A
    (OnBytes.Flat.relationsAndEncodingOfClaims (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E)
    (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
    PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀
    (dataAtFiles flashProveData Z).G.z₀.2 (sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (saltG (dataAtFiles flashProveData Z).G) (dataAtFiles flashProveData Z).P
    (LPFD.Full.KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) (sTG (dataAtFiles flashProveData Z).G).logLeaves
  have rd3 := rounds_fullD (dataAtFiles flashProveData Z).A
    (OnBytes.Flat.relationsAndEncodingOfClaims (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E)
    (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
    PV.EntryFive.dsF PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀
    (dataAtFiles flashProveData Z).G.z₀.2 (sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (saltG (dataAtFiles flashProveData Z).G) (dataAtFiles flashProveData Z).P
  have hK : leavesW (dataAtFiles flashProveData Z).DK = 33988608 ∧ roundsW (dataAtFiles flashProveData Z).DK = 18951 := by
    constructor
    · show leavesW ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) = _
      rw [AtPublicFiles.Reads.key_data Z scope live, writtenKFull_eq]
      exact leaves_keyExact
    · show roundsW ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) = _
      rw [AtPublicFiles.Reads.key_data Z scope live, writtenKFull_eq]
      exact rounds_keyExact
  have hP : leavesW (dataAtFiles flashProveData Z).DP = 670449664 ∧ roundsW (dataAtFiles flashProveData Z).DP = 48393 := by
    constructor
    · show leavesW ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) = _
      rw [AtPublicFiles.Reads.proof_data Z scope live, writtenPFull_eq]
      exact leaves_proofExact
    · show roundsW ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) = _
      rw [AtPublicFiles.Reads.proof_data Z scope live, writtenPFull_eq]
      exact rounds_proofExact
  exact
    { depth := Johnson.G.fr_a
      sFS := Nat.le_refl 256
      lvT := le_of_eq (lv3.1.trans hK.1)
      lvL := le_of_eq (lv3.2.1.trans leaves_link)
      lvB := le_of_eq (lv3.2.2.trans hP.1)
      rT := le_of_eq (rd3.1.trans hK.2)
      rL := le_of_eq (rd3.2.1.trans (by rw [rounds_link]))
      rB := le_of_eq (rd3.2.2.trans hP.2)
      qT := le_of_eq (FlashProve.depthReqT_the Z live c₀ m₀)
      qL := Nat.le_refl _
      qB := show (sBG (dataAtFiles flashProveData Z).G).logLeaves ≤ _ from
        le_of_eq (FlashProve.depth_the Z scope live)
      nT := tr.nT
      nL := tr.nL
      nB := tr.nB }

/-- **At the verifier's parameters at Z**, for Z in scope with a live description. -/
theorem fine_description (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      Fine ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), Fine (D.input Z c m))
    fun c m => fine_atFiles Z scope live c m

/-! ## The error at the target -/

/-- The leaves' count at the target. -/
def targetAl : ℕ := 2 * 2 ^ 32 + 33988608 + 19030016 + 688127 * 670449664
/-- The largest count at a name of 256 bits at the target. -/
def targetAb : ℕ := 688127 * 48393
/-- The largest count at the name of a further try at the target. -/
def targetA2 : ℕ := 688127 * 46

/-- The bound at the target, for b free bits, as one number over 2 ^ b and one over 2 ^ 256. -/
theorem zeta_target (r : InnerCompilerInput) (h : Fine r) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (c : CoinNums r.LeafBody) (u : NumsW) (t n b : ℕ) (hM : a.M = 0) (ht : t ≤ 2 ^ 64 + 1)
    (hn : n ≤ u.s1) (hn' : n ≤ 688127) (hT : ∀ i, a.capT i ≤ 2 ^ 40) (hL : ∀ i, a.capL i ≤ 2 ^ 40)
    (hB : ∀ i, a.capB i ≤ 2 ^ 40) (hb : b ≤ c.ℓ) :
    zetaW r.queryLayout r.seedQueries r.compilerParameters a c u t n ≤
      ((((2 ^ 64 + 1) * targetAl + targetAl * (0 + targetAl) : ℕ) : ℝ≥0∞) / 2 ^ b +
        (((2 ^ 64 + 1) * targetAb + 8 * (targetAb * (2 * (0 + 2) + targetAb)) +
            (2 ^ 40 + 2 ^ 40 + 2 ^ 40) * (targetA2 * (0 + targetA2)) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
          (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
          ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ) := by
  have lvB' := Nat.mul_le_mul hn' (le_of_eq_of_le (runLeaves_eq _ _ _) h.lvB)
  have rB' := Nat.mul_le_mul hn' h.rB
  have qB' := Nat.mul_le_mul hn' h.qB
  have hl : mW r.queryLayout a n Lf ≤ targetAl := by
    show allLeaves r.queryLayout a n ≤ _
    unfold allLeaves targetAl
    rw [hM, h.depth]
    have l1 := le_of_eq_of_le (runLeaves_eq _ _ _) h.lvT
    have l2 := le_of_eq_of_le (runLeaves_eq _ _ _) h.lvL
    norm_num at l1 l2 lvB' ⊢
    omega
  have h8 : ∀ o ∈ nine.erase Lf, mW r.queryLayout a n o ≤ targetAb := by
    intro o ho
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 ho
    have r1 := h.rT
    have r2 := h.rL
    have q1 := h.qT
    have q2 := h.qL
    simp only [nine, Finset.mem_insert, Finset.mem_singleton] at hmem
    unfold targetAb
    norm_num at rB' qB' ⊢
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · show 1 + (a.M + 1) + n ≤ _
      omega
    · show r.queryLayout.depthReqT + (a.M + 1) * r.queryLayout.depthReqL + n * r.queryLayout.depthReq ≤ _
      rw [hM]
      omega
    · show 1 ≤ _
      omega
    · show a.M + 1 ≤ _
      omega
    · show n ≤ _
      omega
    · show r.protocol.offline.shape.length ≤ _
      omega
    · show (a.M + 1) * r.protocol.link.shape.length ≤ _
      rw [hM]
      omega
    · show n * r.protocol.onlineBatch.loc.shape.length ≤ _
      omega
  have h2 : ∀ tg j, mW r.queryLayout a n (.fbw tg j) ≤ targetA2 := by
    intro tg j
    unfold targetA2
    cases tg with
    | test =>
      have := (nLater_le_cnt a.capT j r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh 0).trans h.nT
      show nLater _ _ _ _ _ _ ≤ _
      omega
    | link =>
      have := (nLater_le_cnt a.capL j r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh 0).trans h.nL
      show (a.M + 1) * nLater _ _ _ _ _ _ ≤ _
      rw [hM]
      omega
    | onl =>
      have := Nat.mul_le_mul hn'
        ((nLater_le_cnt a.capB j r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh 0).trans h.nB)
      exact this
  have h2b : targetA2 ≤ targetAb := by
    unfold targetA2 targetAb
    norm_num
  have main := zeta_fine r.queryLayout r.seedQueries r.compilerParameters a c u t n targetAl targetAb targetA2 (2 ^ 40) (2 ^ 40) (2 ^ 40)
    b hn hT hL hB hb h.sFS (Nat.le_refl 256) hl h8 h2 h2b
  rw [hM] at main
  refine main.trans ?_
  have s1 : ((t * targetAl + targetAl * (0 + targetAl) : ℕ) : ℝ≥0∞) ≤
      (((2 ^ 64 + 1) * targetAl + targetAl * (0 + targetAl) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_right _ ht) _
  have s2 : ((t * targetAb + 8 * (targetAb * (2 * (0 + 2) + targetAb)) +
        (2 ^ 40 + 2 ^ 40 + 2 ^ 40) * (targetA2 * (0 + targetA2)) : ℕ) : ℝ≥0∞) ≤
      (((2 ^ 64 + 1) * targetAb + 8 * (targetAb * (2 * (0 + 2) + targetAb)) +
        (2 ^ 40 + 2 ^ 40 + 2 ^ 40) * (targetA2 * (0 + targetA2)) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ ht) _) _
  rw [hM]
  gcongr

/-- x / 2 ^ k is x · 2 ^ j over 2 ^ (k + j). -/
theorem div_shift (x k j : ℕ) : (x : ℝ≥0∞) / 2 ^ k = ((x * 2 ^ j : ℕ) : ℝ≥0∞) / 2 ^ (k + j) := by
  rw [pow_add, Nat.cast_mul]
  push_cast
  rw [ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)]

/-- **256 free bits: the hash term and the tail at most 2 ^ -143.** -/
theorem zeta_target_256 (r : InnerCompilerInput) (h : Fine r) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (c : CoinNums r.LeafBody) (u : NumsW) (t n : ℕ) (hM : a.M = 0) (ht : t ≤ 2 ^ 64 + 1)
    (hn : n ≤ u.s1) (hn' : n ≤ 688127) (hT : ∀ i, a.capT i ≤ 2 ^ 40) (hL : ∀ i, a.capL i ≤ 2 ^ 40)
    (hB : ∀ i, a.capB i ≤ 2 ^ 40) (hb : 256 ≤ c.ℓ) :
    zetaW r.queryLayout r.seedQueries r.compilerParameters a c u t n ≤ (2⁻¹ : ℝ≥0∞) ^ 143 +
      ((u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
          (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
          ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ) := by
  refine (zeta_target r h a c u t n 256 hM ht hn hn' hT hL hB hb).trans ?_
  gcongr
  rw [← ENNReal.add_div, ← Nat.cast_add]
  have e : (256 : ℕ) = 113 + 143 := by norm_num
  rw [e]
  refine div_pow_le _ 113 143 ?_
  unfold targetAl targetAb targetA2
  norm_num

/-- **304 free bits or more: at most 2 ^ -157.** -/
theorem zeta_target_304 (r : InnerCompilerInput) (h : Fine r) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (c : CoinNums r.LeafBody) (u : NumsW) (t n : ℕ) (hM : a.M = 0) (ht : t ≤ 2 ^ 64 + 1)
    (hn : n ≤ u.s1) (hn' : n ≤ 688127) (hT : ∀ i, a.capT i ≤ 2 ^ 40) (hL : ∀ i, a.capL i ≤ 2 ^ 40)
    (hB : ∀ i, a.capB i ≤ 2 ^ 40) (hb : 304 ≤ c.ℓ) :
    zetaW r.queryLayout r.seedQueries r.compilerParameters a c u t n ≤ (2⁻¹ : ℝ≥0∞) ^ 157 +
      ((u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
          (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
          ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ) := by
  refine (zeta_target r h a c u t n 304 hM ht hn hn' hT hL hB hb).trans ?_
  gcongr
  rw [div_shift _ 256 48]
  have e0 : (256 + 48 : ℕ) = 304 := by norm_num
  rw [e0, ← ENNReal.add_div, ← Nat.cast_add]
  have e : (304 : ℕ) = 147 + 157 := by norm_num
  rw [e]
  refine div_pow_le _ 147 157 ?_
  unfold targetAl targetAb targetA2
  norm_num

/-- **At the verifier's parameters at Z**, for Z in scope with a live description: one copy, at most
688,127 requests, at most 2 ^ 64 queries, search limits of at most 2 ^ 40. -/
theorem zeta_target_description (Z : PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (cd : VerifiableInference.Digest)
    (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More)
    (a : AtRecs 256 ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).protocol
      ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).LeafBody
      ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).offlineRoundSplits
      ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).linkRoundSplits)
    (c : CoinNums ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).LeafBody) (u : NumsW) (t n : ℕ)
    (hM : a.M = 0) (ht : t ≤ 2 ^ 64 + 1) (hn : n ≤ u.s1) (hn' : n ≤ 688127)
    (hT : ∀ i, a.capT i ≤ 2 ^ 40) (hL : ∀ i, a.capL i ≤ 2 ^ 40) (hB : ∀ i, a.capB i ≤ 2 ^ 40) :
    (256 ≤ c.ℓ → zetaW ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).queryLayout
        ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).seedQueries
        ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).compilerParameters a c u t n ≤ (2⁻¹ : ℝ≥0∞) ^ 143 +
      ((u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
          (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
          ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ)) ∧
    (304 ≤ c.ℓ → zetaW ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).queryLayout
        ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).seedQueries
        ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z cd m).compilerParameters a c u t n ≤ (2⁻¹ : ℝ≥0∞) ^ 157 +
      ((u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
          (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
          ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ)) :=
  ⟨fun hb => zeta_target_256 _ (fine_description Z scope live cd m) a c u t n hM ht hn hn' hT hL hB hb,
    fun hb => zeta_target_304 _ (fine_description Z scope live cd m) a c u t n hM ht hn hn' hT hL hB hb⟩

end AtPublicFiles.ZetaAt.Target

#print axioms AtPublicFiles.ZetaAt.Target.cost_fine
#print axioms AtPublicFiles.ZetaAt.Target.zeta_target_256
#print axioms AtPublicFiles.ZetaAt.Target.zeta_target_304
#print axioms AtPublicFiles.ZetaAt.Target.zeta_target_description
