-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/Table.lean: THE MAKING OF ONE TABLE AS A TOKEN PROGRAM KEEPS THE RULES: the proof
of Spec.safeTab (Johnson/TokenRules/Spec.lean).

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

A table (tabT, Johnson/TokenSide/Whole.lean) is one tree whose leaves hold no further token
(safeTree, Johnson/TokenRel/Rules.lean, at an empty list), and then the seed's two queries. These
two are ordinary queries at a Fiat-Shamir oracle, at points of the set seedPts, which is what the
rules allow there. An ordinary query adds no marked evaluation, so what is known of the tree's
tokens stays.

  cnt1_le, cnt1_add_le   a count at one oracle, or at two different ones, is below a function if it
                         is so at these oracles.

-/
import Johnson.TokenRel.Rules

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRel
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

/-! ## Counts at one or two oracles -/

section Cnt
variable {S : OSpec} {a b : S.ι} {n m : ℕ} {f : S.ι → ℕ}

theorem cnt1_le (h : n ≤ f a) (o : S.ι) : cnt1 a n o ≤ f o := by
  unfold cnt1
  by_cases e : o = a
  · rw [if_pos e, e]
    exact h
  · rw [if_neg e]
    exact Nat.zero_le _

theorem cnt1_add_le (hab : a ≠ b) (ha : n ≤ f a) (hb : m ≤ f b) (o : S.ι) :
    cnt1 a n o + cnt1 b m o ≤ f o := by
  unfold cnt1
  by_cases e1 : o = a
  · rw [if_pos e1, if_neg (fun e2 => hab (e1.symm.trans e2)), e1]
    exact ha
  · rw [if_neg e1, Nat.zero_add]
    exact cnt1_le hb o

end Cnt

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The seed's two queries: ordinary queries that the rules allow. -/
theorem safe_seedsT (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    {bl bf : ℕ} (cm : Dig lam) {d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (hd : TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d) :
    SafeO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) (seedsT W S cm) d fun _ d' =>
      TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d' ∧
      RunO noTok noTok noTok (cnt1 (OracleName.fb S.t) 2) zr d d' := by
  unfold seedsT
  refine ⟨show seedPts W S S.t _ from Or.inl ⟨cm, rfl⟩, fun a0 T => ?_⟩
  refine ⟨show seedPts W S S.t _ from Or.inr ⟨_, rfl⟩, fun a1 T' => ?_⟩
  refine ⟨(hd.plain _ T).plain _ T', (run_ofPlain (M := zr) d _ T).trans
    (run_ofPlain (M := zr) _ _ T') (fun _ e => Or.inl e) (fun _ e => Or.inl e)
    (fun _ e => Or.inl e) ?_ (fun _ => le_rfl)⟩
  intro o
  simp only [cnt1]
  split <;> omega

/-- **One table.** -/
theorem safeTab : Spec.safeTab := by
  intro I X lam L Bd aT aL W S h tl bl bf b₀ i r d hbl hd
  unfold tabT
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safeTree _ _ lam W.K (typedOracleCarrier L Bd aT aL) bl bf
    (seedPts W S) tl.frE [] (fun _ => tl.preE) W.depth _ d hbl hd
    fun _ e => absurd e List.not_mem_nil))
  rintro T d₁ ⟨hd₁, hr₁, _, hT, hN⟩
  refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_seedsT W S T.root hd₁))
  rintro e d₂ ⟨hd₂, hr₂⟩
  refine ⟨hd₂, ?_, hT.keeps hr₂.charges fun _ _ e => e, hN⟩
  refine (hr₁.grows.mono (Ch := noTok) (R := noTok) (fun _ e => absurd e List.not_mem_nil)
    (fun _ e => Or.inl e) (fun _ => le_rfl) (fun _ => le_rfl)).trans hr₂.grows
    (fun _ e => Or.inl e) (fun _ e => Or.inl e) ?_ ?_
  · refine cnt1_add_le (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (a := OracleName.node) (b := OracleName.fb S.t)
      (f := eTab W.depth S.t) (show (OracleName.node : OracleName) ≠ OracleName.fb S.t from fun e => nomatch e) le_rfl ?_
    show 2 ≤ if S.t = S.t then 2 else 0
    rw [if_pos rfl]
  · exact fun o => (Nat.add_zero _).le.trans (cnt1_le
      (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (a := OracleName.leaf) (f := mTab W.depth) le_rfl o)

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.safeTab
