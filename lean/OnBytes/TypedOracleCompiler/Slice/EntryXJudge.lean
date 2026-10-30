-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryXJudge.lean: the analysis' conclusion on the entry's judge, for traces that
ask first: at the frame of OnBytes/TypedOracleCompiler/Slice/EntryX.lean; then at the seeds' protocol; then at the
record's own terms.

An instance is (both tables' answers; both tables' seeds): THE SEEDS LAST, as a pair. A first query
holds the answers and a fixed value twice (`earlyTwo`). The judge is `judgeEL`
(OnBytes/TypedOracleCompiler/Slice/JudgeE.lean) at two roots: the seeds' chain once under each root, two
comparisons, then the compiled verifier WITHOUT the test of the strict format (whole paths), under
both roots.

Main definitions.
 `earlyTwo d₁`          what a first query holds of an instance.
 `TSE`, `wTSE`, `seedOfE`   the seeds' protocol (OnBytes/TypedOracleCompiler/Slice/SeedsT.lean) at the description's
                        kit, its wiring at the description's wire, the value from its verifier's
                        messages.
 `lgEX`                 the entry's language of a typed world, `DecR.LgE`
                        (OnBytes/Slice/DecoderRecTyped.lean), at an instance.
Main theorems.
 `entry_judgeAtAsk`     from soundness instance by instance and the laws of the second lane to
                        `JudgeAtAsk`, at any second protocol T.
 `entry_judge_seeds`    at the seeds' protocol: the second lane's laws from two hypotheses: the
                        drawing round's verifier's messages are exactly uniform, and one probability
                        over them.
 `entry_judge_record`   THE ENTRY'S JUDGE AT THE RECORD'S OWN TERMS: these two hypotheses gone
                        (`hpr_record`, OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean; `chalP_unif_of`).
 `entry_pre_four`       what is asked first is at most 4 queries: the count is multiplied by 1 + 4.

Asked by `entry_judge_record`: a way to decide whether two seeds are equal; THE DEPTH OF THE
DESCRIPTION'S STORED TABLES IS THE CODE'S; the description's field is the second; 0 < s; the
description's number of blocks, WHICH IS NO LETTER BUT THE GREATEST NUMBER THAT A ROUND OF THE
DESCRIPTION'S OWN CHAIN DRAWS, is at least that of the seeds' sampler: evaluated at no description;
the six conditions of `collRaw_pr` (the radius within the Johnson bound among them); the bound of
`collRaw_pr` is at most εs; the wiring of `Link0` is lawful; every count of ε is at most εs; AND:
for each instance x the link `Link0 D (dec x)` is round-by-round sound for `lgEX` at x, with the one
list ε of counts.

THE PRICE. Where `JudgeAtAsk` is used the whole count, the judge's own count among it, is multiplied
BY 5 (1 + two roots times the seeds' protocol's two rounds: `entry_pre_four`), in both terms; for
the key it is 3.

Not claimed. NO SOUNDNESS IS PROVED: it is a hypothesis, and nobody has met it. At another depth of
the description's stored tables than the code's `DecR.badK` is false everywhere AND `lgEX` HOLDS OF
EVERYTHING (the first table does not decode): the hypothesis on soundness and the conclusion would
be true for free: so the depth is asked. That the two tables have one code: they have, in these
letters (one T, v, eM, lg, s), and one radius eM for both decoders; the link's two test radii are in
the hypothesis on soundness alone. No part is made: of the fields of `Part.OKAsk` this gives
`judge`; JudgeE.lean gives the three on `pre`. No page. That the judge ever says yes. No number is
evaluated. Nothing on proof of work. What the heads of EntryX.lean, JudgeE.lean, SeedsBridge.lean
and DecoderRecTyped.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryX
import OnBytes.TypedOracleCompiler.Slice.SeedsBridge

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE)
open _root_.Run.PQ (View SgX)
open _root_.Run (ckP chalP)
open OnBytes.Slice (replySt below_timesShared_one DecR decRec recZ seedBS seedOfDrawn roundDraws
  GE NZ chalP_unif_seeds)
open scoped ENNReal

/-! ## At any second protocol -/

section
variable {A S : Type} [DecidableEq S] (D : XD) (dec : A × (S × S) → View → Bool) {Bd : Type}
  (B : BodyD Bd) (E : OwnE Bd D) (d₁ : S) (T : InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX))
  (wT : ProtocolQueryLayout 256 (D.K + 1) (BatchInteractiveOracleProof.ofProto T))
  (eT : (p : OPos T.shape) → OSym T.shape p → Bd)
  (pT : (p : OPos T.shape) → Bd → Option (OSym T.shape p))

/-- What a first query holds of an instance: its first part, and the fixed value twice. -/
def earlyTwo (x : A × (S × S)) : A × (S × S) := (x.1, (d₁, d₁))

/-- From soundness instance by instance, and the laws of the second lane, to the analysis'
conclusion on the entry's judge, for traces that ask first. Asked: for each instance x the link
`Link0 D (dec x)` is round-by-round sound for Lg at x, with one list ε of counts, each at most εs;
the wiring of `Link0` is lawful; T has a round; the lane whose state is "bad₁ y (seedOf ρ)" obeys
the laws of a lane at one slot, with counts at most εs. -/
theorem entry_judgeAtAsk (saltT : Bits) (rtT : Dig 256) (rootsT : List (Dig 256))
    (plainsT : Plains T.shape) (seedOf : Rho T.shape → S)
    (R : Reading (LXE (Bd := Bd) D (earlyTwo d₁) T) B.embE)
    (Lg : A × (S × S) → (Fin (2 ^ D.a) → SgX) × (Fin (2 ^ D.a) → SgX) → Prop)
    (bad₁ : (Fin (2 ^ D.a) → SgX) → S → Bool) (ε : Err (Link0 D fun _ => true).shape)
    (εT : Err T.shape) (εs : ℝ≥0∞)
    (hS : ∀ x, (Link0 D (dec x)).Sound (fun _ => Lg x) ε) (hb : Err.Below ε εs)
    (hw : (wq0 D fun _ => true).OKG) (hneT : T.shape ≠ [])
    (oT : ((testXE D B E (earlyTwo d₁) T wT eT pT).laneBad R εT
      fun y ρ => bad₁ y (seedOf ρ)).OK 1) (bT : Err.Below εT εs) :
    JudgeAtAsk (WXE D B E (earlyTwo d₁) T wT eT pT)
      (judgeEL (ZXE D dec B E (earlyTwo d₁) T wT eT pT) (testXE D B E (earlyTwo d₁) T wT eT pT)
        saltT rtT rootsT plainsT seedOf (pack2 S) R Lg bad₁) εs
      (preE (testXE D B E (earlyTwo d₁) T wT eT pT) saltT rtT rootsT plainsT
        (ZXE D dec B E (earlyTwo d₁) T wT eT pT)) := by
  have h1 : Err.Below (Err.timesShared 1 (RoundSplits.allLocal (Link0 D fun _ => true).shape) ε)
      (((1 : ℕ) : ℝ≥0∞) * εs) := below_timesShared_one le_rfl _ ε εs hb
  rw [Nat.cast_one, one_mul] at h1
  exact judgeAtAsk_EL (ZXE D dec B E (earlyTwo d₁) T wT eT pT)
    (testXE D B E (earlyTwo d₁) T wT eT pT) saltT rtT rootsT plainsT seedOf (pack2 S) R Lg
    bad₁ id d₁ (Err.timesShared 1 (RoundSplits.allLocal (Link0 D fun _ => true).shape) ε)
    (replySt (LinkX D dec) ε id Lg) εT εs h1
    (jointE_reply (ZXE D dec B E (earlyTwo d₁) T wT eT pT) Lg ε)
    (stLawsE_reply (ZXE D dec B E (earlyTwo d₁) T wT eT pT) Lg ε
      ((linkX_sound_iff D dec Lg ε).2 hS))
    (ZXE_ok D dec B E (earlyTwo d₁) T wT eT pT hw) rfl rfl (le_refl 2) (fun _ => rfl) rfl
    (show Tag.test ≠ Tag.link by decide) hneT (fun _ => rfl) oT bT

end

/-! ## At the seeds' protocol -/

section
variable {A S : Type} [DecidableEq S] (D : XD) (dec : A × (S × S) → View → Bool) {Bd : Type}
  (B : BodyD Bd) (E : OwnE Bd D) (d₁ : S) (e : _root_.Fmt.Entry)

/-- The seeds' protocol at the description's kit, on one stored table's string. -/
abbrev TSE : InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX) := seedsT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX)

/-- Its wiring, at the description's wire "the first blocks of K". -/
abbrev wTSE : ProtocolQueryLayout 256 (D.K + 1) (BatchInteractiveOracleProof.ofProto (TSE D e)) :=
  wqT D.C D.K (chalP D.base.plan.field D.K) (dSeed e) (we1 D.a)

omit [DecidableEq S] in
/-- The value from the verifier's messages: `sOf` of what the drawing round draws. -/
def seedOfE (sOf : List _root_.Fmt.Drawn → S) (ρ : Rho (TSE D e).shape) : S :=
  sOf (drawnT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX) ρ)

/-- From soundness instance by instance, exactly uniform verifier's messages in the drawing round,
and one probability over them, to the analysis' conclusion on the entry's judge, for traces that ask
first. Asked: soundness and the wiring as `entry_judgeAtAsk` asks them; the description's wire
makes the drawing round's verifier's messages exactly uniform; for every string and every first
message "bad₁" holds of the value drawn with probability at most εs. -/
theorem entry_judge_seeds (sOf : List _root_.Fmt.Drawn → S)
    (R : Reading (LXE (Bd := Bd) D (earlyTwo d₁) (TSE D e)) B.embE)
    (Lg : A × (S × S) → (Fin (2 ^ D.a) → SgX) × (Fin (2 ^ D.a) → SgX) → Prop)
    (bad₁ : (Fin (2 ^ D.a) → SgX) → S → Bool) (ε : Err (Link0 D fun _ => true).shape)
    (εs : ℝ≥0∞) (hS : ∀ x, (Link0 D (dec x)).Sound (fun _ => Lg x) ε) (hb : Err.Below ε εs)
    (hw : (wq0 D fun _ => true).OKG)
    (hc : (unif (Fin D.K → Dig 256)).map
        (chalP D.base.plan.field D.K (dSeed e).entry (dSeed e).kind) =
      unif (D.C.Ch (dSeed e).entry (dSeed e).kind))
    (hpr : ∀ (y : Fin (2 ^ D.a) → SgX) c0,
      pr (unif (PQ.roundS D.C (dSeed e)).up.Chal)
        {c | bad₁ y (seedOfE D e sOf (c0, c, ())) = true} ≤ εs) :
    JudgeAtAsk
      (WXE D B E (earlyTwo d₁) (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _))
      (judgeEL
        (ZXE D dec B E (earlyTwo d₁) (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _))
        (testXE D B E (earlyTwo d₁) (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _))
        [] default [] (plainsT D.C (dSeed e) _) (seedOfE D e sOf) (pack2 S) R Lg bad₁) εs
      (preE
        (testXE D B E (earlyTwo d₁) (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _))
        [] default [] (plainsT D.C (dSeed e) _)
        (ZXE D dec B E (earlyTwo d₁) (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _))) := by
  obtain ⟨h1, h2⟩ := countOK_of_pr (PQ.s0 D.C).up (PQ.roundS D.C (dSeed e)).up
    (fun (y : Fin (2 ^ D.a) → SgX) ρ => bad₁ y (seedOfE D e sOf ρ)) εs hpr
  exact entry_judgeAtAsk D dec B E d₁ (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _) []
    default [] (plainsT D.C (dSeed e) _) (seedOfE D e sOf) R Lg bad₁ ε _ εs hS hb hw
    (seedsT_ne D.C (dSeed e) _)
    (lane_stBad_ok (TSE D e)
      (wqT_okg D.C D.K (chalP D.base.plan.field D.K) (dSeed e) (we1 D.a) hc (Nat.zero_le _)
        (we1_ok D.a)).sh h1) h2

end

/-- What is asked first is at most 4 queries: two roots times the seeds' protocol's two rounds:
`preE_queries` (OnBytes/TypedOracleCompiler/Slice/JudgeE.lean) at the entry's frame is at 4. So the count is
multiplied by 1 + 4 = 5. -/
theorem entry_pre_four {X : Type} (D : XD) (e : _root_.Fmt.Entry) (Bd : Type) (early : X → X) :
    (ext2R (LXE (Bd := Bd) D early (TSE D e))).k * (TSE D e).shape.length = 4 := rfl

/-! ## At the record's own terms -/

/-- The library's wire "the first blocks of K" makes the verifier's messages of the seeds' round
exactly uniform, in a field that is the second. -/
theorem chalP_unif_of (f : _root_.Fmt.Fld) (hf : f = .two) (lg s K : ℕ) (e : _root_.Fmt.Entry)
    (h : _root_.Fmt.dsOf e .seeds = roundDraws lg s) (hK : (seedBS lg s).b ≤ K) :
    (unif (Fin K → Dig 256)).map (chalP f K e .seeds) = unif ((ckP f).Ch e .seeds) := by
  subst hf
  exact chalP_unif_seeds lg s K e h hK

section
variable {An : Type} (T : _root_.Fmt.M1.Code) (v eM lg s : ℕ)
  [DecidableEq (Fin s → (Fin lg → GE) × NZ)] (D : XD)
  (dec : (An × An) × ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ)) → View → Bool)
  {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D) (d₁ : Fin s → (Fin lg → GE) × NZ)

/-- The entry's language of a typed world at an instance "both tables' answers; both tables' seeds":
`DecR.LgE` (OnBytes/Slice/DecoderRecTyped.lean) at the two records. -/
def lgEX (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
    (x : (An × An) × ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ)))
    (y : (Fin (2 ^ D.a) → SgX) × (Fin (2 ^ D.a) → SgX)) : Prop :=
  DecR.LgE (D := decRec T v eM lg s) (Equiv.refl _) an id (x.1.1, x.2.1) (x.1.2, x.2.2) y.1 y.2

/-- THE ENTRY'S JUDGE AT THE RECORD'S OWN TERMS: `entry_judge_seeds` at the entry `seedEntry lg
s`, the value `seedOfDrawn lg s`, the test `DecR.badK` and the language `lgEX`, with its two
hypotheses on the drawing round gone. Asked in their place: the description's field is the second; 0
< s; the description's number of blocks is at least that of the seeds' sampler; the six conditions
of `collRaw_pr`; the bound is at most εs. ASKED BESIDE, AND USED BY NO STEP OF THE PROOF: the depth
of the description's stored tables is the code's: elsewhere the language holds of everything
(`DecR.lgE_of_len`) and the statement is true for free. STILL ASKED: soundness record by record. -/
theorem entry_judge_record (hD : D.a = T.a) (hf : D.base.plan.field = .two) (hs0 : 0 < s)
    (hK : (seedBS lg s).b ≤ D.K)
    (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE) (ha : T.a ≤ 32)
    (hk : T.r + T.l ≤ 2 ^ T.a) (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg)
    (R : Reading (LXE (Bd := Bd) D (earlyTwo d₁) (TSE D (OnBytes.Slice.seedEntry lg s))) B.embE)
    (ε : Err (Link0 D fun _ => true).shape) (εs : ℝ≥0∞)
    (hS : ∀ x, (Link0 D (dec x)).Sound (fun _ => lgEX T v eM lg s D an x) ε)
    (hb : Err.Below ε εs) (hw : (wq0 D fun _ => true).OKG)
    (hε : kapSl 128 ^ (seedBS lg s).b *
      ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err : ℕ) :
        ℝ≥0∞) / Fintype.card (recZ T.l lg s).D) ≤ εs) :
    JudgeAtAsk
      (WXE D B E (earlyTwo d₁) (TSE D (OnBytes.Slice.seedEntry lg s))
        (wTSE D (OnBytes.Slice.seedEntry lg s)) (embST D.C (OnBytes.Slice.seedEntry lg s) _)
        (prjST D.C (OnBytes.Slice.seedEntry lg s) _))
      (judgeEL
        (ZXE D dec B E (earlyTwo d₁) (TSE D (OnBytes.Slice.seedEntry lg s))
          (wTSE D (OnBytes.Slice.seedEntry lg s)) (embST D.C (OnBytes.Slice.seedEntry lg s) _)
          (prjST D.C (OnBytes.Slice.seedEntry lg s) _))
        (testXE D B E (earlyTwo d₁) (TSE D (OnBytes.Slice.seedEntry lg s))
          (wTSE D (OnBytes.Slice.seedEntry lg s)) (embST D.C (OnBytes.Slice.seedEntry lg s) _)
          (prjST D.C (OnBytes.Slice.seedEntry lg s) _))
        [] default [] (plainsT D.C (dSeed (OnBytes.Slice.seedEntry lg s)) _)
        (seedOfE D (OnBytes.Slice.seedEntry lg s) (seedOfDrawn lg s)) (pack2 _) R
        (lgEX T v eM lg s D an) (DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id)) εs
      (preE
        (testXE D B E (earlyTwo d₁) (TSE D (OnBytes.Slice.seedEntry lg s))
          (wTSE D (OnBytes.Slice.seedEntry lg s)) (embST D.C (OnBytes.Slice.seedEntry lg s) _)
          (prjST D.C (OnBytes.Slice.seedEntry lg s) _))
        [] default [] (plainsT D.C (dSeed (OnBytes.Slice.seedEntry lg s)) _)
        (ZXE D dec B E (earlyTwo d₁) (TSE D (OnBytes.Slice.seedEntry lg s))
          (wTSE D (OnBytes.Slice.seedEntry lg s)) (embST D.C (OnBytes.Slice.seedEntry lg s) _)
          (prjST D.C (OnBytes.Slice.seedEntry lg s) _))) :=
  have _ := hD
  entry_judge_seeds D dec B E d₁ (OnBytes.Slice.seedEntry lg s) (seedOfDrawn lg s) R
    (lgEX T v eM lg s D an) (DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id) ε εs hS hb hw
    (chalP_unif_of D.base.plan.field hf lg s D.K (OnBytes.Slice.seedEntry lg s)
      (OnBytes.Slice.dsOf_seedEntry lg s hs0) hK)
    fun y c0 => (hpr_record T v eM lg s D.C (congrArg ckP hf) _ ha hk he hJ h3 hl
      (OnBytes.Slice.seedEntry lg s) (OnBytes.Slice.dsOf_seedEntry lg s hs0) y c0).trans hε

end

end TypedOracleCompiler.Slice
