-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesFrom.lean: (a) from what three files' parts deliver.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

`Three.Laws` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) has twenty-two clauses. This file shows fourteen of
them, once for all, of three parts that are made of three `FileSpec`s which meet `FileSpec.Delivers`
at one written reading: the three bounds, the three expressions for all tables, the stable root, one
raw string for all parts (twice), the three checkers' and their logs' deafness to the public
strings, the term for a clash, and that the key's part reads the reading in which "fine" is said.
The eight others are gathered in `Three.Beside`: the three languages, the keys and the ID's string,
the two readings. `Three.ofSpecs` makes the three parts of three specifications.

Main theorems.
 `PartO.pr_ownClash_map`, `measurable_ownClash_map`.
 `FileSpec.toO_raw`, `toO_ownLog_deaf`; `Delivers.toO_noCoin`, `toO_queries`, `stable`, `sameRaw`.
 `Three.laws_of_delivers`; `Three.soundB_of_delivers`: three times `Delivers`, and `Beside`, give
     `SoundB` with the bound bK t + bE t + bF t + 2 (tC + 1 + tP)^2 / 2^256 + (t + 2)^2 / 2^256 +
     ((t + rK)^2 + (t + rE)^2 + (t + rF)^2) / 2^256, t = tC + tP.

What is not claimed. AN IMPLICATION: no `FileSpec` is given, and `Delivers` is met by nothing. All
limits in the heads of Shapes.lean and ShapesTop.lean hold here too. The bound says nothing once it
reaches 1.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesTop
import OnBytes.TypedOracleCompiler.Slice.ShapesTyping

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob MeasureTheory
open scoped ENNReal

variable {lam : ℕ} {γ γ' Sg : Type}

/-- A clash in a part's checker's own log, for any maker and any function from its output to the
part's: probability at most (t + tR)^2 / 2^lam. -/
theorem PartO.pr_ownClash_map (s : PartO lam γ Sg) (hn : ∀ x, (s.chk x).NoCoin) (tR : ℕ)
    (hq : ∀ x, (s.chk x).QueryBound tR) (A : OComp (rom lam) γ') (f : γ' → γ) (t : ℕ)
    (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (fun g => {x | ¬ NoClash (s.ownLog g (f x.1))}) ≤
      (((t + tR) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam :=
  (s.comap f).pr_ownClash (fun x => hn (f x)) tR (fun x => hq (f x)) A t hA

/-- Its probability over the maker's coins is a measurable function of the oracle. -/
theorem PartO.measurable_ownClash_map (s : PartO lam γ Sg) (hn : ∀ x, (s.chk x).NoCoin)
    (A : OComp (rom lam) γ') (f : γ' → γ) :
    Measurable fun g => PrCoins g A.withTrace {x | ¬ NoClash (s.ownLog g (f x.1))} :=
  measurable_twoExp_det A (fun x => (s.chk (f x)).withTrace)
    (fun x => noCoin_withTrace _ (hn (f x))) {z | ¬ NoClash z.2.2}

namespace Shapes
open OnBytes.Tie (IdKey idCode firstId)

namespace FileSpec
variable (φ : FileSpec) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))

/-- The raw string that a part so made reads off a log is the part's own. -/
theorem toO_raw (T₀ T₁ : Tab) : (φ.toO S₀ S₁ T₀ T₁).raw = (φ.part T₀ T₁).raw := rfl

/-- Putting one table over an oracle twice is putting it over once. -/
theorem over_idem (P : Finset (List Bool)) (T : Tab) (g : Fam (rom 256)) :
    over P T (over P T g) = over P T g := by
  funext o s
  cases o
  by_cases hs : s ∈ P
  · rw [over_mem _ _ hs, over_mem _ _ hs]
  · rw [over_not_mem _ _ hs]

/-- The log of a part so made is deaf to the oracle at the public strings. -/
theorem toO_ownLog_deaf (T₀ T₁ : Tab) (g : Fam (rom 256)) (d : Files) :
    (φ.toO S₀ S₁ T₀ T₁).ownLog (over (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) g) d =
      (φ.toO S₀ S₁ T₀ T₁).ownLog g d := by
  show ((pinOn (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) ((φ.part T₀ T₁).chk d)).withTrace.det _).2 =
    ((pinOn (S₀ ∪ S₁ T₀) (mergeT S₀ T₀ T₁) ((φ.part T₀ T₁).chk d)).withTrace.det g).2
  rw [det_withTrace_pinOn, det_withTrace_pinOn, over_idem]

variable {φ S₀ S₁}
variable {rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX} {b : ℕ → ℝ≥0∞}

/-- The checker of a part so made tosses no coin. -/
theorem Delivers.toO_noCoin (h : φ.Delivers S₀ S₁ rd b) (T₀ T₁ : Tab) (x : Files) :
    ((φ.toO S₀ S₁ T₀ T₁).chk x).NoCoin :=
  noCoin_pinOn _ _ _ (h.noCoin T₀ T₁ x)

/-- It asks at most tR strings. -/
theorem Delivers.toO_queries (h : φ.Delivers S₀ S₁ rd b) (T₀ T₁ : Tab) (x : Files) :
    ((φ.toO S₀ S₁ T₀ T₁).chk x).QueryBound (φ.part T₀ T₁).tR :=
  queryBound_pinOn _ _ _ _ (h.queries T₀ T₁ x)

/-- What the join asks of the first part beside: what it reads under an announced root does not
change, except with probability at most 2 (tC + 1 + tP)^2 / 2^256. -/
theorem Delivers.stable (h : φ.Delivers S₀ S₁ rd b) (T₀ T₁ : Tab) :
    (φ.toO S₀ S₁ T₀ T₁).Stable fun tC tP => 2 * ((tC + 1 + tP : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  intro β δ C rt P tC tP hC hP
  refine le_trans (Rom.Pr_mono _ fun _ w hw => ?_)
    (TypedOracleCompiler.Slice.stableLeaf_maker (φ.part T₀ T₁).m (h.one T₀ T₁).leaf1 (h.one T₀ T₁).node1
      C rt P tC tP hC hP)
  obtain ⟨cm, hrt, hne⟩ := hw
  refine ⟨cm, hrt, (φ.part T₀ T₁).W.depth, ?_⟩
  by_contra hall
  push Not at hall
  exact hne (congrArg (rawOf (φ.part T₀ T₁).u) ((φ.part T₀ T₁).J.R.at_congr hall))

/-- Two parts that read the one written reading read one raw string. -/
theorem Delivers.sameRaw {φ' : FileSpec} {b' : ℕ → ℝ≥0∞} (h : φ.Delivers S₀ S₁ rd b)
    (h' : φ'.Delivers S₀ S₁ rd b') (T₀ T₁ : Tab) :
    SameRaw (φ.toO S₀ S₁ T₀ T₁) (φ'.toO S₀ S₁ T₀ T₁) := fun σ hσ cm =>
  (h.reads T₀ T₁ σ hσ cm).trans (h'.reads T₀ T₁ σ hσ cm).symm

end FileSpec

variable {D : DecR} {Xi : Type}

namespace Three
variable (Θ : Three D Xi)

/-- Three parts made of three files' specifications, over one pair of public sets. The readers
of records and instance take the values of the specifications' own parts. -/
noncomputable def ofSpecs (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (φK φE φF : FileSpec) (key keyC : Tab → Tab → Files → IdKey)
    (recK : ∀ T₀ T₁, (φK.part T₀ T₁).Out → D.Rec)
    (recE₀ recE₁ : ∀ T₀ T₁, (φE.part T₀ T₁).Out → D.Rec)
    (recF : ∀ T₀ T₁, (φF.part T₀ T₁).Out → D.Rec) (xOf : ∀ T₀ T₁, (φF.part T₀ T₁).Out → Xi)
    (xReq : Files → Xi) (A : D.Claims Xi) (recU : Fam (rom 256) → IdKey → Option D.Rec)
    (rawU : IdKey → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX) (okKey : IdKey → Prop) :
    Three D Xi where
  S₀ := S₀
  S₁ := S₁
  key := key
  keyC := keyC
  K := φK.toO S₀ S₁
  E := φE.toO S₀ S₁
  F := φF.toO S₀ S₁
  recK := recK
  recE₀ := recE₀
  recE₁ := recE₁
  recF := recF
  xOf := xOf
  xReq := xReq
  A := A
  recU := recU
  rawU := rawU
  okKey := okKey

/-- What (a) asks beside what three files' parts deliver: the three languages; the two keys and
the ID's string; the two readings in which "fine" is said. -/
structure Beside (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX) : Prop where
  /-- the key's language -/
  langK : ∀ T₀ T₁ oK Y, (Θ.K T₀ T₁).Lang oK [Y] →
    DecR.LangK Θ.A (DecR.wayColl D) (Θ.recK T₀ T₁ oK) Y
  /-- the entry's language -/
  langE : ∀ T₀ T₁ oE Y₀ Y₁, (Θ.E T₀ T₁).Lang oE [Y₀, Y₁] →
    DecR.LangE (DecR.wayColl D) (Θ.recE₀ T₀ T₁ oE) (Θ.recE₁ T₀ T₁ oE) Y₀ Y₁
  /-- the proof's language -/
  langF : ∀ T₀ T₁ oF Y, (Θ.F T₀ T₁).Lang oF [Y] →
    DecR.LangP Θ.A (DecR.wayColl D) (Θ.xOf T₀ T₁ oF) (Θ.recF T₀ T₁ oF) Y
  /-- no key's string is a public string -/
  apart : ∀ k s, idCode k = some s → s ∉ Θ.S₀ ∧ ∀ T₀, s ∉ Θ.S₁ T₀
  /-- the files' key has the right shape -/
  keyOK : ∀ T₀ T₁ d, Θ.okKey (Θ.key T₀ T₁ d)
  /-- the parts' one written reading is the reading in which "fine" is said, at the files' key -/
  rawRd : ∀ T₀ T₁ d σ cm, rd T₀ T₁ σ cm = Θ.rawU (Θ.key T₀ T₁ d) σ cm
  /-- the written reading does not see the entries at public strings -/
  rawOff : ∀ S k σ cm, (S = Θ.S₀ ∨ ∃ T₀, S = Θ.S₁ T₀) → Θ.rawU k (offSet S σ) cm = Θ.rawU k σ cm
  /-- every property of a key's record under the oracle is a measurable set of oracles -/
  measR : ∀ k (Q : D.Rec → Prop), MeasurableSet {g | ∃ rec, Θ.recU g k = some rec ∧ Q rec}

/-- The term for a clash in three checkers' logs, with at most rK, rE, rF strings. -/
noncomputable def bClash (rK rE rF t : ℕ) : ℝ≥0∞ :=
  (((t + rK) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((((t + rE) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
    (((t + rF) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- The term for a stable root. -/
noncomputable def bStable (tC tP : ℕ) : ℝ≥0∞ := 2 * ((tC + 1 + tP : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256

variable {Θ}

/-- `Laws` FROM WHAT THREE FILES' PARTS DELIVER, AND `Beside`. The three parts are made of three
`FileSpec`s over Θ's own public sets; one written reading for all; rK, rE, rF bound the checkers'
strings at all tables. -/
theorem laws_of_delivers {φK φE φF : FileSpec}
    (mK : ∀ T₀ T₁, Θ.K T₀ T₁ = φK.toO Θ.S₀ Θ.S₁ T₀ T₁)
    (mE : ∀ T₀ T₁, Θ.E T₀ T₁ = φE.toO Θ.S₀ Θ.S₁ T₀ T₁)
    (mF : ∀ T₀ T₁, Θ.F T₀ T₁ = φF.toO Θ.S₀ Θ.S₁ T₀ T₁)
    {rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX} {bK bE bF : ℕ → ℝ≥0∞}
    (hK : φK.Delivers Θ.S₀ Θ.S₁ rd bK) (hE : φE.Delivers Θ.S₀ Θ.S₁ rd bE)
    (hF : φF.Delivers Θ.S₀ Θ.S₁ rd bF) (rK rE rF : ℕ)
    (qK : ∀ T₀ T₁, (φK.part T₀ T₁).tR ≤ rK) (qE : ∀ T₀ T₁, (φE.part T₀ T₁).tR ≤ rE)
    (qF : ∀ T₀ T₁, (φF.part T₀ T₁).tR ≤ rF) (hB : Θ.Beside rd) :
    Θ.Laws bK bE bF (bClash rK rE rF) bStable where
  okK := fun T₀ T₁ => (mK T₀ T₁) ▸ hK.ok T₀ T₁
  okE := fun T₀ T₁ => (mE T₀ T₁) ▸ hE.ok T₀ T₁
  okF := fun T₀ T₁ => (mF T₀ T₁) ▸ hF.ok T₀ T₁
  flatK := fun T₀ T₁ t => (mK T₀ T₁) ▸ hK.flat T₀ T₁ t
  flatE := fun T₀ T₁ t => (mE T₀ T₁) ▸ hE.flat T₀ T₁ t
  flatF := fun T₀ T₁ t => (mF T₀ T₁) ▸ hF.flat T₀ T₁ t
  stable := fun T₀ T₁ => (mK T₀ T₁) ▸ hK.stable T₀ T₁
  sameKE := fun T₀ T₁ => by
    rw [mK, mE]
    exact hK.sameRaw hE T₀ T₁
  sameEF := fun T₀ T₁ => by
    rw [mE, mF]
    exact hE.sameRaw hF T₀ T₁
  langK := hB.langK
  langE := hB.langE
  langF := hB.langF
  deafK := fun T₀ T₁ g d => by
    rw [mK]
    exact φK.toO_deaf Θ.S₀ Θ.S₁ T₀ T₁ g d
  deafE := fun T₀ T₁ g d => by
    rw [mE]
    exact φE.toO_deaf Θ.S₀ Θ.S₁ T₀ T₁ g d
  deafF := fun T₀ T₁ g d => by
    rw [mF]
    exact φF.toO_deaf Θ.S₀ Θ.S₁ T₀ T₁ g d
  clash := fun T₀ T₁ γ' A f t hA => by
    unfold ClashB
    rw [mK, mE, mF]
    have nK := fun x => hK.toO_noCoin T₀ T₁ x
    have nE := fun x => hE.toO_noCoin T₀ T₁ x
    have nF := fun x => hF.toO_noCoin T₀ T₁ x
    refine le_trans (Pr_union_le A.withTrace
      (fun g => {x | ¬ NoClash ((φK.toO Θ.S₀ Θ.S₁ T₀ T₁).ownLog g (f x.1))})
      (fun g => {x | ¬ NoClash ((φE.toO Θ.S₀ Θ.S₁ T₀ T₁).ownLog g (f x.1)) ∨
        ¬ NoClash ((φF.toO Θ.S₀ Θ.S₁ T₀ T₁).ownLog g (f x.1))})
      ((φK.toO Θ.S₀ Θ.S₁ T₀ T₁).measurable_ownClash_map nK A f)) (add_le_add
      ((φK.toO Θ.S₀ Θ.S₁ T₀ T₁).pr_ownClash_map nK rK
        (fun x => (hK.toO_queries T₀ T₁ x).mono (qK T₀ T₁)) A f t hA) ?_)
    exact le_trans (Pr_union_le A.withTrace
      (fun g => {x | ¬ NoClash ((φE.toO Θ.S₀ Θ.S₁ T₀ T₁).ownLog g (f x.1))})
      (fun g => {x | ¬ NoClash ((φF.toO Θ.S₀ Θ.S₁ T₀ T₁).ownLog g (f x.1))})
      ((φE.toO Θ.S₀ Θ.S₁ T₀ T₁).measurable_ownClash_map nE A f)) (add_le_add
      ((φE.toO Θ.S₀ Θ.S₁ T₀ T₁).pr_ownClash_map nE rE
        (fun x => (hE.toO_queries T₀ T₁ x).mono (qE T₀ T₁)) A f t hA)
      ((φF.toO Θ.S₀ Θ.S₁ T₀ T₁).pr_ownClash_map nF rF
        (fun x => (hF.toO_queries T₀ T₁ x).mono (qF T₀ T₁)) A f t hA))
  deafC := fun T₀ T₁ g d h => by
    unfold ClashB at h ⊢
    rw [mK, mE, mF] at h ⊢
    rw [φK.toO_ownLog_deaf, φE.toO_ownLog_deaf, φF.toO_ownLog_deaf] at h
    exact h
  apart := hB.apart
  keyOK := hB.keyOK
  rawTie := fun T₀ T₁ d σ cm hσ => by
    rw [mK, ← hB.rawRd T₀ T₁ d σ cm]
    exact hK.reads T₀ T₁ σ hσ cm
  rawOff := hB.rawOff
  measR := hB.measR

/-- (a) FROM WHAT THREE FILES' PARTS DELIVER, AND `Beside`. -/
theorem soundB_of_delivers {φK φE φF : FileSpec}
    (mK : ∀ T₀ T₁, Θ.K T₀ T₁ = φK.toO Θ.S₀ Θ.S₁ T₀ T₁)
    (mE : ∀ T₀ T₁, Θ.E T₀ T₁ = φE.toO Θ.S₀ Θ.S₁ T₀ T₁)
    (mF : ∀ T₀ T₁, Θ.F T₀ T₁ = φF.toO Θ.S₀ Θ.S₁ T₀ T₁)
    {rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX} {bK bE bF : ℕ → ℝ≥0∞}
    (hK : φK.Delivers Θ.S₀ Θ.S₁ rd bK) (hE : φE.Delivers Θ.S₀ Θ.S₁ rd bE)
    (hF : φF.Delivers Θ.S₀ Θ.S₁ rd bF) (rK rE rF : ℕ)
    (qK : ∀ T₀ T₁, (φK.part T₀ T₁).tR ≤ rK) (qE : ∀ T₀ T₁, (φE.part T₀ T₁).tR ≤ rE)
    (qF : ∀ T₀ T₁, (φF.part T₀ T₁).tR ≤ rF) (hB : Θ.Beside rd) :
    Θ.SoundB (eps bK bE bF (bClash rK rE rF) bStable) :=
  soundB_of_laws (laws_of_delivers mK mE mF hK hE hF rK rE rF qK qE qF hB)

end Three

end Shapes

end OnBytes.Slice
