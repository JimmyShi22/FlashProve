-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/Bridge.lean: FROM THE COUNTS OF THE TOKEN PROGRAMS TO THE COUNTS THAT THE ERROR
OF THE STATEMENT IS WRITTEN WITH. A state that is within the first is within the second.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

Two sets of counts. Johnson/TokenSide/Counts.lean (eAllT, mAllT, with the rules' bits bitsOfT and
the oracles osAllT) counts what the token programs do, and the programs are shown to stay within it
(Spec.withinTwin, Johnson/TokenRules/Spec.lean; proved in Johnson/TokenRules/Closed.lean).
Johnson/WholeKey/Zeta.lean (eW, mW, bitsW, osW) is what the error of the statement of index privacy
is written with; it names no token program. Here:
  m_le, e_le      oracle by oracle the first counts are at most the second, at the honest side of
                  the statement (AtRecs.side) and if the depths of the three request trees are the
                  wire's. They differ at g and in the request tree alone, where the second counts
                  one joining round for each run whether the protocol has a shared round or not.
  mW_zero         outside osW the second count allows no marked evaluation. (osW has, tag by tag,
                  the names below the largest cap of a round WITH a test; osAllT has more names.)
  bits_eq         on osW the two lower bounds on a charged token's length agree.
  within_zeta     so DSt.Within (Rom/Defer.lean) goes over. That an evaluation's oracle lies in osW
                  comes from the count: where the count is 0 there is no evaluation.
  Spec.withinZeta, withinZeta_of   every run against the challenger ends within the counts of the
                  statement's error, from Spec.withinTwin.

-/
import Johnson.TokenRules.Spec
import Johnson.WholeKey.Zeta

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

section Run
variable {lam K : ℕ}

theorem cLeaves_eq : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
    cLeaves s A W = WholeKey.runLeaves s A W
  | [], _, _ => rfl
  | _ :: s, (_, A), (w, W) => by
      rw [cLeaves, WholeKey.runLeaves, cLeaves_eq s A W]
      omega

theorem cTry_eq (k : ℕ) (cap : ℕ → ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ),
    cTry k cap s A W i = WholeKey.nLater s A W cap i k
  | [], _, _, _ => rfl
  | _ :: s, (a, A), (w, W), i => by
      have hc : (TokenSide.hasTest w = true ∧ k < cap i) ↔
          (WholeKey.roundHasTest a w = true ∧ k + 1 ≤ cap i) := Iff.rfl
      rw [cTry, WholeKey.nLater, cTry_eq k cap s A W (i + 1), if_congr hc rfl rfl]

theorem joinsT_le_one : ∀ (s : Shape) (A : RoundSplits s), joinsT s A ≤ 1
  | [], _ => Nat.zero_le _
  | _ :: s, (a, A) => by
      rw [joinsT]
      split
      · exact le_rfl
      · exact joinsT_le_one s A

theorem nLater_zero (cap : ℕ → ℕ) (j : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (i : ℕ), WholeKey.maxCap s A W cap i ≤ j → WholeKey.nLater s A W cap i j = 0
  | [], _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), i, h => by
      rw [WholeKey.maxCap] at h
      have h0 : ¬ (WholeKey.roundHasTest a w = true ∧ j + 1 ≤ cap i) := fun hc => by
        have h1 := le_trans (le_max_left _ _) h
        rw [if_pos hc.1] at h1
        omega
      rw [WholeKey.nLater, if_neg h0, nLater_zero cap j s A W (i + 1)
        (le_trans (le_max_right _ _) h)]

end Run

section Scheme
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (p : Params) (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd)
  (tl : TokLen lam (typedOracleCarrier L Bd aT aL) a.side.KT a.side.KL a.side.KB)

theorem m_le (hT : tl.T.dq = W.depthReqT) (hL : tl.Lk.dq = W.depthReqL) (hB : tl.B.dq = W.depthReq)
    (n : ℕ) (o : OracleName) : mAllT W a.side tl n o ≤ mW W a n o := by
  have jT := joinsT_le_one L.offline.shape aT
  have jL := joinsT_le_one L.link.shape aL
  have jB := joinsT_le_one L.onlineBatch.loc.shape L.onlineBatch.ann
  have jL' := Nat.mul_le_mul_left (a.M + 1) jL
  have jB' := Nat.mul_le_mul_left n jB
  cases o with
  | leaf =>
      show (a.M + 2) * 2 ^ W.depth + cLeaves L.offline.shape aT (wTC W).sh +
          (a.M + 1) * cLeaves L.link.shape aL (wLC W).sh +
          n * cLeaves L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ≤ allLeaves W a n
      rw [cLeaves_eq, cLeaves_eq, cLeaves_eq]
      exact le_rfl
  | rleaf =>
      show (a.M + 2) * 0 + joinsT L.offline.shape aT + (a.M + 1) * joinsT L.link.shape aL +
          n * joinsT L.onlineBatch.loc.shape L.onlineBatch.ann ≤ 1 + (a.M + 1) + n
      omega
  | rnode =>
      show (a.M + 2) * 0 + joinsT L.offline.shape aT * tl.T.dq +
          (a.M + 1) * (joinsT L.link.shape aL * tl.Lk.dq) +
          n * (joinsT L.onlineBatch.loc.shape L.onlineBatch.ann * tl.B.dq) ≤
        W.depthReqT + (a.M + 1) * W.depthReqL + n * W.depthReq
      rw [hT, hL, hB, Nat.mul_zero, Nat.zero_add]
      refine Nat.add_le_add (Nat.add_le_add ?_ (Nat.mul_le_mul_left _ ?_))
        (Nat.mul_le_mul_left _ ?_)
      · exact le_trans (Nat.mul_le_mul_right _ jT) (le_of_eq (Nat.one_mul _))
      · exact le_trans (Nat.mul_le_mul_right _ jL) (le_of_eq (Nat.one_mul _))
      · exact le_trans (Nat.mul_le_mul_right _ jB) (le_of_eq (Nat.one_mul _))
  | fb t =>
      cases t with
      | test =>
          show (a.M + 2) * 0 + L.offline.shape.length + (a.M + 1) * 0 + n * 0 ≤ L.offline.shape.length
          omega
      | link =>
          show (a.M + 2) * 0 + 0 + (a.M + 1) * L.link.shape.length + n * 0 ≤
            (a.M + 1) * L.link.shape.length
          omega
      | onl =>
          show (a.M + 2) * 0 + 0 + (a.M + 1) * 0 + n * L.onlineBatch.loc.shape.length ≤
            n * L.onlineBatch.loc.shape.length
          omega
  | fbw t k =>
      cases t with
      | test =>
          show (a.M + 2) * 0 + cTry k a.capT L.offline.shape aT (wTC W).sh 0 + (a.M + 1) * 0 + n * 0 ≤
            WholeKey.nLater L.offline.shape aT (wTC W).sh a.capT 0 k
          rw [cTry_eq]
          omega
      | link =>
          show (a.M + 2) * 0 + 0 + (a.M + 1) * cTry k a.capL L.link.shape aL (wLC W).sh 0 + n * 0 ≤
            (a.M + 1) * WholeKey.nLater L.link.shape aL (wLC W).sh a.capL 0 k
          rw [cTry_eq]
          omega
      | onl =>
          show (a.M + 2) * 0 + 0 + (a.M + 1) * 0 +
              n * cTry k a.capB L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh 0 ≤
            n * WholeKey.nLater L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh a.capB 0 k
          rw [cTry_eq]
          omega
  | g t =>
      cases t with
      | test =>
          show (a.M + 2) * 0 + joinsT L.offline.shape aT + (a.M + 1) * 0 + n * 0 ≤ 1
          omega
      | link =>
          show (a.M + 2) * 0 + 0 + (a.M + 1) * joinsT L.link.shape aL + n * 0 ≤ a.M + 1
          omega
      | onl =>
          show (a.M + 2) * 0 + 0 + (a.M + 1) * 0 + n * joinsT L.onlineBatch.loc.shape L.onlineBatch.ann ≤ n
          omega
  | node =>
      show (a.M + 2) * 0 + 0 + (a.M + 1) * 0 + n * 0 ≤ 0
      omega
  | ann =>
      show (a.M + 2) * 0 + 0 + (a.M + 1) * 0 + n * 0 ≤ 0
      omega
  | other =>
      show (a.M + 2) * 0 + 0 + (a.M + 1) * 0 + n * 0 ≤ 0
      omega

theorem e_le (n : ℕ) (o : OracleName) : eAllT W S a.side n o ≤ eW W S a n o := by
  cases o with
  | node =>
      show (a.M + 2) * 2 ^ W.depth + cLeaves L.offline.shape aT (wTC W).sh +
          (a.M + 1) * cLeaves L.link.shape aL (wLC W).sh +
          n * cLeaves L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ≤ allLeaves W a n
      rw [cLeaves_eq, cLeaves_eq, cLeaves_eq]
      exact le_rfl
  | fb t =>
      show (a.M + 2) * (if t = S.t then 2 else 0) + 0 + (a.M + 1) * 0 + n * 0 ≤
        if t = S.t then 2 * (a.M + 2) else 0
      split_ifs <;> omega
  | _ =>
      show (a.M + 2) * 0 + 0 + (a.M + 1) * 0 + n * 0 ≤ 0
      omega

theorem mW_zero (n : ℕ) (o : OracleName) (ho : o ∉ osW W a) : mW W a n o = 0 := by
  have hin : ∀ o' : OracleName, o' ∈ ({.leaf, .rleaf, .rnode, .g .test, .g .link, .g .onl, .fb .test,
              .fb .link, .fb .onl} : Finset OracleName) → o' ∈ osW W a := fun o' h' =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h'))
  cases o with
  | leaf => exact absurd (hin _ (by decide)) ho
  | rleaf => exact absurd (hin _ (by decide)) ho
  | rnode => exact absurd (hin _ (by decide)) ho
  | fb t => exact absurd (hin _ (by cases t <;> decide)) ho
  | g t => exact absurd (hin _ (by cases t <;> decide)) ho
  | node => rfl
  | ann => rfl
  | other => rfl
  | fbw t k =>
      cases t with
      | test =>
          have hk : WholeKey.maxCap L.offline.shape aT (wTC W).sh a.capT 0 ≤ k := by
            by_contra hlt
            exact ho (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_of_not_le hlt), rfl⟩))))
          exact nLater_zero _ k _ _ _ 0 hk
      | link =>
          have hk : WholeKey.maxCap L.link.shape aL (wLC W).sh a.capL 0 ≤ k := by
            by_contra hlt
            exact ho (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_of_not_le hlt), rfl⟩)))
          show (a.M + 1) * WholeKey.nLater L.link.shape aL (wLC W).sh a.capL 0 k = 0
          rw [nLater_zero _ k _ _ _ 0 hk, Nat.mul_zero]
      | onl =>
          have hk : WholeKey.maxCap L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh a.capB 0 ≤ k := by
            by_contra hlt
            exact ho (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_of_not_le hlt), rfl⟩))
          show n * WholeKey.nLater L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh a.capB 0 k = 0
          rw [nLater_zero _ k _ _ _ 0 hk, Nat.mul_zero]

theorem bits_eq (n : ℕ) (o : OracleName) (ho : mW W a n o ≠ 0) :
    bitsW (lam := lam) p c o = bitsOfT lam c.ℓ (min p.sFS lam) o := by
  cases o with
  | node => exact absurd rfl ho
  | ann => exact absurd rfl ho
  | other => exact absurd rfl ho
  | _ => rfl

/-- **A state within the token programs' counts is within the counts of the statement's error.** -/
theorem within_zeta (hT : tl.T.dq = W.depthReqT) (hL : tl.Lk.dq = W.depthReqL)
    (hB : tl.B.dq = W.depthReq) (n : ℕ) (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (h : d.Within (eAllT W S a.side n) (mAllT W a.side tl n) (bitsOfT lam c.ℓ (min p.sFS lam))
      (osAllT a.side)) :
    d.Within (eW W S a n) (mW W a n) (bitsW (lam := lam) p c) (osW W a) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun o => (h2 o).trans (e_le W S a n o),
    fun o => (h3 o).trans (m_le W a tl hT hL hB n o), fun v hv => ?_⟩
  have hpos : mW W a n v.o ≠ 0 := fun h0 => by
    have hlen := (h3 v.o).trans (m_le W a tl hT hL hB n v.o)
    rw [h0] at hlen
    have hm : v ∈ d.evs.filter fun v' => decide (v'.o = v.o) :=
      List.mem_filter.mpr ⟨hv, by simp⟩
    exact absurd (List.length_pos_of_mem hm) (Nat.not_lt.mpr hlen)
  refine ⟨by_contra fun hn => hpos (mW_zero W a n v.o hn), ?_⟩
  rw [bits_eq W p a c n v.o hpos]
  exact (h4 v hv).2

end Scheme

/-- **Every run against the challenger stays within the counts of the statement's error.** -/
def Spec.withinZeta : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (a : AtRecs lam L Bd aT aL)
      (c : CoinNums Bd) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) a.side.KT a.side.KL a.side.KB)
      (i : I) (m : Bool) (α : Type) (ok : ZKCP.Gen.Batch X Unit → Prop)
      (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
        (_root_.Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ),
    LensOK c.ℓ (min p.sFS lam) tl → tl.T.dq = W.depthReqT → tl.Lk.dq = W.depthReqL →
    tl.B.dq = W.depthReq → GAdm ok A false n →
    ∀ x ∈ (interact ((challT W S cA r₀ a.side tl i).world m) A (none, DSt.init _)).support,
      x.2.2.Within (eW W S a n) (mW W a n) (bitsW (lam := lam) p c) (osW W a)

theorem withinZeta_of (hW : Spec.withinTwin) : Spec.withinZeta := by
  intro I X lam L Bd aT aL W S cA r₀ p a c tl i m α ok A n hl hT hL hB hA x hx
  exact within_zeta W S p a c tl hT hL hB n x.2.2
    (hW I X lam L Bd aT aL W S cA r₀ a.side tl c.ℓ (min p.sFS lam) i m α ok A n hl hA x hx)

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.within_zeta
#print axioms OnBytes.TokenRules.withinZeta_of
