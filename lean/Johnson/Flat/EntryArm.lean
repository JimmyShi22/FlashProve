-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/EntryArm.lean: the entry's arm of the compiled verifier, with roots and answers alone
in the first query of Link, at the written link that stands as the entry file's protocol, at the two
sizes: sound against every maker over one hash function, under the theorem on codes.

`arm_pr_one` (Johnson/TypedOracleCompiler/RecCompile/LinkAnsOne.lean) and `arm_pr_hash` (LinkAnsMore.lean: the arm
itself asks the hash function) at: the object with records of the three files' protocols
(`threeProtocolsFromDryRunAtFullSize`, `threeProtocolsFromDryRunAtSmallSize`, OnBytes/Flat/FilesAt.lean; `Files.withProvers`, OnBytes/Flat/Object.lean), whose
link is the entry file's protocol, the written link `linkSibFull`, `linkSibSmall`
(OnBytes/Flat/LinkSibAt.lean); the marks `aLFull`, `aLSmall` of its rounds, all local
(`Run.Twin.allLo_eq`, Run/TwinKit.lean); they are the field `annL` of `threeProtocolsFromDryRunAtFullSize`, `threeProtocolsFromDryRunAtSmallSize`; the
written draw of a seed (`recSeedK`, OnBytes/Flat/RecordSeed.lean); the written code of the answers
(`codeA`, OnBytes/Flat/RecordCode.lean). Paid here: Link's soundness round by round (under
`BCHKS46At`), its locality, every round's error and the seed's law at 2^-128, the laws of the
answers' code, the annotation's coherence.

What stays a hypothesis, in each of the four theorems: `hA : BCHKS46At GF GE`, the theorem on codes;
`hW : OKLA W`, the laws of the wires that Link reads; `hV : IsArm W S cA V` (`isArm_armS`,
`isArm_armL` give it for the arm with the strict and with the lax Link); `h`, which stands in a
`variable` line: the number of digests of an answer covers the seed's draws. What stays a letter: X;
A (what a decoded table holds, with its own laws) and R; G (what the makers of the key file's and
the proof file's protocols take) and P (honest provers), of which nothing is asked; the type Bd of a
leaf's body; the annotation aT of the key's rounds; the wire W; the coding m; the arm V; of the
record's wire: the tag, the rest of a table's name and the plain parts of the seeds' queries,
`code`, `num`, the test of the equality of two seeds.

Limits: soundness alone.
  * The price: at most n 2^-128 + 2 (n + 1)² / 2^256 at n = 5 (tq + tVL W). One call of the maker
    counts five times, and so do the arm's own `tVL W` typed queries. `tVL W` is evaluated at a
    written wiring in Johnson/Flat/EntryCount.lean [not in this library].
  * The 128 bits of a round's error count proof of work. The rounds' data `dsFull`, `dsSmall` are
    the library's `frRds`, `srRds` carried over by `PQ.ofLib`, which keeps a round's work. At six
    rounds of the full-size files and at four of the small ones 32 of the bits are work (the heads
    of OnBytes/Slice/FullRecNum.lean, SmallRecNum.lean name the rounds). That work is worth its bits
    is not shown.
  * The link is a written term, made by no maker. Its decision is the verifier program's
    `linkVerify` at the keys written of the two records (`decFullX_recX`, `decSmallX_recX`). Its
    rounds' data are a written list: the list of the entry's description `entryXD recordGround c`
    (small: `smallRecordGround`) at every c (`letters_full`, `letters_small`). That an entry file of
    a program follows these rounds is not shown here.
  * No coding m is given here, and a coding must be onto all bit strings: one exists if X is
    countable (Johnson/Flat/EntryCoding.lean [not in this library; so here read: not proved in this
    library]), by choice; none is shown to be the programs'. W, S
    (`S.cfg` with it), cA, V and m are fixed before the function is drawn.
  * The maker puts out typed values, not bytes. Nothing here ties V to a program that ships, to
    bytes, or to any run; the keys written of two records are not shown to be a program's. No
    accepted transcript is shown.
  * Where the first table decodes to nothing, nothing is said of the further table. The words are
    those at the end of the whole log (earlier logs: Johnson/Flat/EntryMaker.lean [not in this library],
    EntryTwoStage.lean [not in this library], EntryKeyStage.lean [not in this library]).
  * That `OKLA W` can be met at this object is not shown in this file (Johnson/Flat/EntryWire.lean
    [not in this library; so here read: not proved in this library] shows it at a written wiring).
  * The limits in the heads of LinkAnsPr.lean, LinkAnsOne.lean and of the files named hold too.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsMore
import OnBytes.Flat.FilesAt
import OnBytes.Flat.RecordCode
import OnBytes.Flat.RecordSeed

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice OnBytes.Flat Cb Cb.Ood

section
variable {I X : Type} (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
  {K : ℕ} (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t))
  (seed : (Fin K → Dig 256) → L.OutOfDomainSeed) (code : L.Rec → List (Dig 256))
  (num : ℕ → Plains L.onlineBatch.loc.shape → Bool) (dS : DecidableEq L.OutOfDomainSeed)

/-- The record's wire, from its nine parts. -/
def sdE : OutOfDomainSampleQueryLayout 256 K L Bd aT aL where
  t := t
  cfg := cfg
  shape := shape
  pl0 := pl0
  pl1 := pl1
  seed := seed
  code := code
  num := num
  decS := dS

/-- The seed's law, read. -/
theorem sdE_law (κ : ℝ≥0∞) (h : ∀ y, pr (unif (Fin K → Dig 256)) {a | L.hasCollisionAt y (seed a)} ≤ κ) :
    (sdE L Bd aT aL t cfg shape pl0 pl1 seed code num dS).Law κ := h

end

/-- `arm_pr_one` where all rounds of Link are local (haL: the marks aL are `RoundSplits.allLocal`): the
errors of Link's rounds count as they are. -/
theorem arm_pr_one_local {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type}
    {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}
    {V : OutLA lam L aL →
      TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (haL : aL = RoundSplits.allLocal L.link.shape)
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below εL εs) (hV : IsArm W S cA V)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (A : OComp (rom lam) (OutLA lam L aL)) (t : ℕ)
    (hq : A.QueryBound t) :
    Rom.Pr A.withTrace
        (fun g => {o | (runA W V (readBlocks m g) o.1).1 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  subst haL
  exact arm_pr_one hsL hlL (_root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW hA hSd
    (by rw [timesShared_allLocal]; exact hbL) hV m A t hq

/-- `arm_pr_hash` where all rounds of Link are local (haL: the marks aL are `RoundSplits.allLocal`). -/
theorem arm_pr_hash_local {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type}
    {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}
    {V : OutLA lam L aL →
      TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (haL : aL = RoundSplits.allLocal L.link.shape)
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below εL εs) (hV : IsArm W S cA V)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (A : OComp (rom lam) (OutLA lam L aL)) (t : ℕ)
    (hq : A.QueryBound t) :
    Rom.Pr (A.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) x.1) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
            x.1.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  subst haL
  exact arm_pr_hash hsL hlL (_root_.Iop.BatchOne.BAnn.allLocal_coherent _) hW hA hSd
    (by rw [timesShared_allLocal]; exact hbL) hV m A t hq

/-- the marks of the written link's rounds at the full size: all local -/
abbrev aLFull : RoundSplits (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsFull)) :=
  _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsFull)

/-- the marks of the written link's rounds at the small size: all local -/
abbrev aLSmall : RoundSplits (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsSmall)) :=
  _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) dsSmall)

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (G : FilesParameters X RecFull) (P : (threeProtocolsFromDryRunAtFullSize A R G).Provers)
  (Bd : Type) (aT : RoundSplits ((threeProtocolsFromDryRunAtFullSize A R G).withProvers P).offline.shape)

/-- the object with records at the full files -/
abbrev obFull : HolographicProtocol (DecR.configurationOfStoredTable A R).I (DecR.configurationOfStoredTable A R).X := (threeProtocolsFromDryRunAtFullSize A R G).withProvers P

variable
  (W : QueryLayout 256 (typedOracleCarrier (obFull A R G P) Bd aT aLFull))
  (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (obFull A R G P) Bd aT aLFull) t)
    (annOf (typedOracleCarrier (obFull A R G P) Bd aT aLFull) t))
  (code : (obFull A R G P).Rec → List (Dig 256))
  (num : ℕ → Plains (obFull A R G P).onlineBatch.loc.shape → Bool) (h : (seedBS recLg recS).b ≤ W.K)
  (dS : DecidableEq (obFull A R G P).OutOfDomainSeed)

/-- The record's wire at the full entry: the seed is the written draw from the digests. -/
def sdFullE : OutOfDomainSampleQueryLayout 256 W.K (obFull A R G P) Bd aT aLFull :=
  sdE (obFull A R G P) Bd aT aLFull t cfg shape pl0 pl1 (recSeedK recT recLg recS W.K h)
      code
    num dS

/-- The code of a record's answers at the full entry: the array of the program's key, element by
element (`codeA_key`, OnBytes/Flat/RecordCode.lean; that any program hashes this list is not
claimed). -/
abbrev cAFull : (obFull A R G P).OutOfDomainAnswer → List (Dig 256) := codeA (v := frS.P.v) (s := 1)

/-- The written code of the answers is one to one, and all codes have one length. -/
theorem ansOK_full : AnsOK (cAFull A R G P) :=
  ⟨codeA_inj, fun a a' => (codeA_length a).trans (codeA_length a').symm⟩

set_option maxRecDepth 20000 in
/-- The entry's arm at the full entry is sound against every maker over one hash function, under the
theorem on codes, `OKLA W`, `IsArm` and h (an answer's digests cover the seed's draws): at most
n 2^-128 + 2 (n + 1)² / 2^256, n = 5 (tq + tVL W), where tq bounds the maker's calls (hq). -/
theorem entryFull_arm_one (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (obFull A R G P) aLFull →
      TypedOracleComputation 256 W.K (typedOracleCarrier (obFull A R G P) Bd aT aLFull) Bool}
    (hV : IsArm W (sdFullE A R G P Bd aT W t cfg shape pl0 pl1 code num h dS)
      (cAFull A R G P) V)
    (m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier (obFull A R G P) Bd aT aLFull)) 256)
    (Mk : OComp (rom 256) (OutLA 256 (obFull A R G P) aLFull)) (tq : ℕ)
    (hq : Mk.QueryBound tq) :
    Rom.Pr Mk.withTrace
        (fun g => {o | (runA W V (readBlocks m g) o.1).1 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hb, hs⟩ := threeProtocolsFromDryRunAtFullSize_entrySound A R G hA
  exact arm_pr_one_local (L := obFull A R G P) (εL := ε) (_root_.Run.Twin.allLo_eq _) hs
    (threeProtocolsFromDryRunAtFullSize_local A R G).2.1 hW (ansOK_full A R G P)
    (sdE_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => entryFull_seedLawK A R W.K h y) hb hV m Mk tq hq

set_option maxRecDepth 20000 in
/-- The entry's arm at the full entry is sound against every maker over one hash function, the arm
itself asking that function, under the theorem on codes, `OKLA W`, `IsArm` and h (an answer's
digests cover the seed's draws): at most n 2^-128 + 2 (n + 1)² / 2^256, n = 5 (tq + tVL W), where tq
bounds the maker's calls (hq). -/
theorem entryFull_arm_hash (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (obFull A R G P) aLFull →
      TypedOracleComputation 256 W.K (typedOracleCarrier (obFull A R G P) Bd aT aLFull) Bool}
    (hV : IsArm W (sdFullE A R G P Bd aT W t cfg shape pl0 pl1 code num h dS)
      (cAFull A R G P) V)
    (m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier (obFull A R G P) Bd aT aLFull)) 256)
    (Mk : OComp (rom 256) (OutLA 256 (obFull A R G P) aLFull)) (tq : ℕ)
    (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) x.1) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
            x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hb, hs⟩ := threeProtocolsFromDryRunAtFullSize_entrySound A R G hA
  exact arm_pr_hash_local (L := obFull A R G P) (εL := ε) (_root_.Run.Twin.allLo_eq _) hs
    (threeProtocolsFromDryRunAtFullSize_local A R G).2.1 hW (ansOK_full A R G P)
    (sdE_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => entryFull_seedLawK A R W.K h y) hb hV m Mk tq hq

end

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (G : FilesParameters X RecSmall) (P : (threeProtocolsFromDryRunAtSmallSize A R G).Provers)
  (Bd : Type) (aT : RoundSplits ((threeProtocolsFromDryRunAtSmallSize A R G).withProvers P).offline.shape)

/-- the object with records at the small files -/
abbrev obSmall : HolographicProtocol (DecR.configurationOfStoredTable A R).I (DecR.configurationOfStoredTable A R).X := (threeProtocolsFromDryRunAtSmallSize A R G).withProvers P

variable
  (W : QueryLayout 256 (typedOracleCarrier (obSmall A R G P) Bd aT aLSmall))
  (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (obSmall A R G P) Bd aT aLSmall) t)
    (annOf (typedOracleCarrier (obSmall A R G P) Bd aT aLSmall) t))
  (code : (obSmall A R G P).Rec → List (Dig 256))
  (num : ℕ → Plains (obSmall A R G P).onlineBatch.loc.shape → Bool) (h : (seedBS 19 1).b ≤ W.K)
  (dS : DecidableEq (obSmall A R G P).OutOfDomainSeed)

/-- The record's wire at the small entry: the seed is the written draw from the digests. -/
def sdSmallE : OutOfDomainSampleQueryLayout 256 W.K (obSmall A R G P) Bd aT aLSmall :=
  sdE (obSmall A R G P) Bd aT aLSmall t cfg shape pl0 pl1 (recSeedK srT 19 1 W.K h) code
    num dS

/-- The code of a record's answers at the small entry: the array of the program's key, element by
element (`codeA_key`, OnBytes/Flat/RecordCode.lean; that any program hashes this list is not
claimed). -/
abbrev cASmall : (obSmall A R G P).OutOfDomainAnswer → List (Dig 256) := codeA (v := srS.P.v) (s := 1)

/-- The written code of the answers is one to one, and all codes have one length. -/
theorem ansOK_small : AnsOK (cASmall A R G P) :=
  ⟨codeA_inj, fun a a' => (codeA_length a).trans (codeA_length a').symm⟩

set_option maxRecDepth 20000 in
/-- The entry's arm at the small entry is sound against every maker over one hash function, under
the theorem on codes, `OKLA W`, `IsArm` and h (an answer's digests cover the seed's draws): at most
n 2^-128 + 2 (n + 1)² / 2^256, n = 5 (tq + tVL W), where tq bounds the maker's calls (hq). -/
theorem entrySmall_arm_one (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (obSmall A R G P) aLSmall →
      TypedOracleComputation 256 W.K (typedOracleCarrier (obSmall A R G P) Bd aT aLSmall) Bool}
    (hV : IsArm W (sdSmallE A R G P Bd aT W t cfg shape pl0 pl1 code num h dS)
      (cASmall A R G P) V)
    (m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier (obSmall A R G P) Bd aT aLSmall)) 256)
    (Mk : OComp (rom 256) (OutLA 256 (obSmall A R G P) aLSmall)) (tq : ℕ)
    (hq : Mk.QueryBound tq) :
    Rom.Pr Mk.withTrace
        (fun g => {o | (runA W V (readBlocks m g) o.1).1 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) o) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hb, hs⟩ := threeProtocolsFromDryRunAtSmallSize_entrySound A R G hA
  exact arm_pr_one_local (L := obSmall A R G P) (εL := ε) (_root_.Run.Twin.allLo_eq _) hs
    (threeProtocolsFromDryRunAtSmallSize_local A R G).2.1 hW (ansOK_small A R G P)
    (sdE_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => entrySmall_seedLawK A R W.K h y) hb hV m Mk tq hq

set_option maxRecDepth 20000 in
/-- The entry's arm at the small entry is sound against every maker over one hash function, the arm
itself asking that function, under the theorem on codes, `OKLA W`, `IsArm` and h (an answer's
digests cover the seed's draws): at most n 2^-128 + 2 (n + 1)² / 2^256, n = 5 (tq + tVL W), where tq
bounds the maker's calls (hq). -/
theorem entrySmall_arm_hash (hA : BCHKS46At GF GE) (hW : OKLA W)
    {V : OutLA 256 (obSmall A R G P) aLSmall →
      TypedOracleComputation 256 W.K (typedOracleCarrier (obSmall A R G P) Bd aT aLSmall) Bool}
    (hV : IsArm W (sdSmallE A R G P Bd aT W t cfg shape pl0 pl1 code num h dS)
      (cASmall A R G P) V)
    (m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier (obSmall A R G P) Bd aT aLSmall)) 256)
    (Mk : OComp (rom 256) (OutLA 256 (obSmall A R G P) aLSmall)) (tq : ℕ)
    (hq : Mk.QueryBound tq) :
    Rom.Pr (Mk.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds W (logOne W V m (readBlocks m g) x.1) x.1.1.1 x.1.1.2.1 x.1.1.2.2.1
            x.1.1.2.2.2.1}) ≤
      (((tq + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ 128 +
        2 * (((tq + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  obtain ⟨ε, hb, hs⟩ := threeProtocolsFromDryRunAtSmallSize_entrySound A R G hA
  exact arm_pr_hash_local (L := obSmall A R G P) (εL := ε) (_root_.Run.Twin.allLo_eq _) hs
    (threeProtocolsFromDryRunAtSmallSize_local A R G).2.1 hW (ansOK_small A R G P)
    (sdE_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => entrySmall_seedLawK A R W.K h y) hb hV m Mk tq hq

end

end TypedOracleCompiler.Compile.Batch.Cms
