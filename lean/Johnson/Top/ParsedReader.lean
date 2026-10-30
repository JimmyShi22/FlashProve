-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/ParsedReader.lean: from the struct of record (`Parsed`, OnBytes/Maker/Parsed.lean) to
`innerCompiledVerifier`'s proof type (Johnson/Top/InnerCompiledVerifier.lean) as ONE algorithm over the hash function: ask
the configuration's digest; make `Lay` of it; `typeW` (Johnson/Top/ParsedTyping.lean). And:
soundness of `innerCompiledVerifier r` is soundness of the verifier that runs on the struct, at fifteen queries
more.

AT LETTERS: the input r, the user's public files and the function `layOf` from the digest to `Lay`
are letters. Nothing here can be run before they are written.

States.
  `hAsk`: the format's hash with every call asked of the one oracle.
  `readTree files layOf F`: the reading as a tree of queries; it returns nothing where `layOf`
    returns nothing at the digest (the planner refuses the public files) or the typing does.
    `readTree_asks`: at most fifteen queries (one for the digest; a call 169 and a call 172 for each
    of seven chains). `readTree_noCoin`: no coin.
  `reader`: the reading as an algorithm of the type that `soundForWith_behind`
    (Johnson/Top/SoundBehind.lean) asks: total: a fixed proof where the reading returns nothing.
    `reader_asks`: fifteen.
  `verifyParsed r files layOf`: the verifier that runs: the reading; no where it returns nothing;
    else `innerCompiledVerifier r`. `verifyParsed_yes`: at every hash function its yes is `innerCompiledVerifier r`'s yes on
    what the reader returns.
  `soundForWith_parsed`, `sound_parsed`: from `SoundForWith (innerSystem r) extractor claim ε` (from
    `Sound`): the same for the system whose proofs are structs and whose verifier is `verifyParsed`,
    at ε (t + 15); the same extractor and claim.

Limits. The two theorems hold WHATEVER `layOf` AND `files` ARE: so no test that stands in the typing
is a test of `innerCompiledVerifier`, and nothing that the typing computes is trusted: it counts as the
prover's. Nothing is said on acceptance: at a `layOf` that returns nothing the verifier refuses
everything. That `files` are the public files from which r is made is said nowhere here: r is fixed
before the hash function is drawn, the digest is asked after. The soundness of `innerCompiledVerifier r` is a
hypothesis. `verifyParsed` asks the reading's queries once; `reader` stands in the proof alone. For
proofs and for whoever writes r, `files` and `layOf`; no program imports this file.



Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ParsedTyping
import Johnson.Top.SoundBehind
import Johnson.Top.InnerCompiledVerifier
import Run.OCompM
import VerifiableInference.Deterministic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace OnBytes.Maker.ParsedRead

open OnBytes.Maker.Parsed
open VerifiableInference VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open ZKCP.OComp (asks_bind' asks_pure' asks_map' NoCoin.bind' noCoin_pure' det_map')

/-- The deterministic algorithm of a tree, evaluated at a hash function, is the tree run at it. (For
trees in the generic language the like stands in Johnson/Top/FrontGeneral.lean:
`OnBytes.K.evaluate_ofRom`.) -/
theorem evaluate_deterministicOf_det {α : Type} (hash : Hash) :
    ∀ c : ZKCP.OComp 256 α, (deterministicOf c).evaluate hash = c.det hash
  | .pure _ => rfl
  | .query q k => evaluate_deterministicOf_det hash (k (hash q))
  | .sample _ k => evaluate_deterministicOf_det hash (k 0)

/-- The format's hash with every call asked of the one oracle: one query a call (two at the call
162, which the reading below does not make). -/
abbrev hAsk : Nat → Nat → Nat → ByteArray → ByteArray → ZKCP.OComp 256 ByteArray :=
  _root_.Fmt.HM _root_.Run.askB

theorem hAsk_asks {n : Nat} (hn : n ≠ 162) (t i : Nat) (s b : ByteArray) :
    (hAsk n t i s b).QueryBound 1 := by
  unfold hAsk _root_.Fmt.HM
  rw [if_neg hn]
  exact _root_.Run.asks_askB _

theorem hAsk_noCoin {n : Nat} (hn : n ≠ 162) (t i : Nat) (s b : ByteArray) :
    (hAsk n t i s b).NoCoin := by
  unfold hAsk _root_.Fmt.HM
  rw [if_neg hn]
  exact fun _ => trivial

/-- A chain's run value costs two queries. -/
theorem runW_asks (lab : Nat) (params rnd : ByteArray) :
    (runW hAsk lab params rnd).QueryBound 2 := by
  unfold runW
  split
  · exact asks_bind' (s := 1) (t := 1) (hAsk_asks (by decide) _ _ _ _) fun _ =>
      asks_bind' (s := 1) (t := 0) (hAsk_asks (by decide) _ _ _ _) fun _ => asks_pure' _ _
  · exact asks_pure' _ _

theorem runW_noCoin (lab : Nat) (params rnd : ByteArray) : (runW hAsk lab params rnd).NoCoin := by
  unfold runW
  split
  · exact NoCoin.bind' (hAsk_noCoin (by decide) _ _ _ _) fun _ =>
      NoCoin.bind' (hAsk_noCoin (by decide) _ _ _ _) fun _ => noCoin_pure' _
  · exact noCoin_pure' _

/-- Three chains' run values cost six. -/
theorem runsW_asks (l₁ l₂ l₃ : Nat) (q₁ q₂ q₃ : ByteArray) (c : Chains) :
    (c.runsW hAsk l₁ l₂ l₃ q₁ q₂ q₃).QueryBound 6 :=
  asks_bind' (s := 2) (t := 4) (runW_asks _ _ _) fun _ =>
    asks_bind' (s := 2) (t := 2) (runW_asks _ _ _) fun _ =>
      asks_bind' (s := 2) (t := 0) (runW_asks _ _ _) fun _ => asks_pure' _ _

theorem runsW_noCoin (l₁ l₂ l₃ : Nat) (q₁ q₂ q₃ : ByteArray) (c : Chains) :
    (c.runsW hAsk l₁ l₂ l₃ q₁ q₂ q₃).NoCoin :=
  NoCoin.bind' (runW_noCoin _ _ _) fun _ => NoCoin.bind' (runW_noCoin _ _ _) fun _ =>
    NoCoin.bind' (runW_noCoin _ _ _) fun _ => noCoin_pure' _

section
variable {I X : Type} {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- The typing asks at most fourteen queries. -/
theorem typeW_asks (A : Lay L aT aL) (F : Parsed) : (typeW hAsk A F).QueryBound 14 :=
  asks_bind' (s := 6) (t := 8) (runsW_asks _ _ _ _ _ _ _) fun _ =>
    asks_bind' (s := 2) (t := 6) (runW_asks _ _ _) fun _ =>
      asks_bind' (s := 6) (t := 0) (runsW_asks _ _ _ _ _ _ _) fun _ => asks_pure' _ _

theorem typeW_noCoin (A : Lay L aT aL) (F : Parsed) : (typeW hAsk A F).NoCoin :=
  NoCoin.bind' (runsW_noCoin _ _ _ _ _ _ _) fun _ => NoCoin.bind' (runW_noCoin _ _ _) fun _ =>
    NoCoin.bind' (runsW_noCoin _ _ _ _ _ _ _) fun _ => noCoin_pure' _

variable (files : List ByteArray) (layOf : ByteArray → Option (Lay L aT aL))

/-- **The reading, as a tree of queries.** files: the user's public files. layOf: from the
configuration's digest all that the typing takes beside the struct; nothing where the planner
refuses the files: then the reading returns nothing. -/
def readTree (F : Parsed) : ZKCP.OComp 256 (Option (InnerCompiledVerifierProof L aT aL)) := do
  let c ← _root_.Fmt.configDigestW hAsk files
  match layOf c with
  | none => pure none
  | some A => typeW hAsk A F

/-- **The reading asks at most fifteen queries.** -/
theorem readTree_asks (F : Parsed) : (readTree files layOf F).QueryBound 15 :=
  asks_bind' (s := 1) (t := 14) (hAsk_asks (by decide) _ _ _ _) fun c => by
    cases layOf c with
    | none => exact asks_pure' _ _
    | some A => exact typeW_asks A F

/-- The reading draws no coin. -/
theorem readTree_noCoin (F : Parsed) : (readTree files layOf F).NoCoin :=
  NoCoin.bind' (hAsk_noCoin (by decide) _ _ _ _) fun c => by
    cases layOf c with
    | none => exact noCoin_pure' _
    | some A => exact typeW_noCoin A F

/-- **The reader**, of the type that `soundForWith_behind` asks: total: the fixed proof π₀ where the
typing returns nothing. It reads neither prompt nor output. -/
def reader (π₀ : InnerCompiledVerifierProof L aT aL) (_ _ : List Token) (F : Parsed) :
    DeterministicAlgorithm (InnerCompiledVerifierProof L aT aL) :=
  deterministicOf ((fun o => o.getD π₀) <$> readTree files layOf F)

theorem reader_asks (π₀ : InnerCompiledVerifierProof L aT aL) (prompt output : List Token) (F : Parsed) :
    (reader files layOf π₀ prompt output F).toRandomized.QueryBound 15 :=
  queryBound_deterministicOf _ 15 (asks_map' _ (readTree_asks files layOf F))

end

/-- `innerCompiledVerifier`'s proofs are of the type `InnerCompiledVerifierProof`. -/
example (r : InnerCompilerInput) : (innerSystem r).Proof = InnerCompiledVerifierProof r.protocol r.offlineRoundSplits r.linkRoundSplits := rfl

variable (r : InnerCompilerInput) (files : List ByteArray) (layOf : ByteArray → Option (Lay r.protocol r.offlineRoundSplits r.linkRoundSplits))

/-- **The verifier that runs**: the reading; no where it returns nothing; else `innerCompiledVerifier`. -/
def verifyParsed (commitment : Commitment) (prompt output : List Token) (F : Parsed) :
    DeterministicAlgorithm Bool :=
  (deterministicOf (readTree files layOf F)).followedBy fun
    | none => .done false
    | some π => innerCompiledVerifier r commitment prompt output π

/-- Its yes is `innerCompiledVerifier`'s yes on what the reader returns, at every hash function. -/
theorem verifyParsed_yes (π₀ : InnerCompiledVerifierProof r.protocol r.offlineRoundSplits r.linkRoundSplits) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (F : Parsed)
    (h : (verifyParsed r files layOf commitment prompt output F).evaluate hash = true) :
    (innerSystem r).accepts hash commitment prompt output
      ((reader files layOf π₀ prompt output F).evaluate hash) = true := by
  unfold verifyParsed at h
  rw [DeterministicAlgorithm.evaluate_followedBy, evaluate_deterministicOf_det] at h
  have e : (reader files layOf π₀ prompt output F).evaluate hash =
      ((readTree files layOf F).det hash).getD π₀ :=
    (evaluate_deterministicOf_det hash _).trans (det_map' hash _ _)
  cases hq : (readTree files layOf F).det hash with
  | none =>
    rw [hq] at h
    exact absurd h Bool.false_ne_true
  | some π =>
    rw [hq] at h e
    exact (congrArg (fun x => (innerSystem r).accepts hash commitment prompt output x) e).trans h

/-- **Soundness of `innerCompiledVerifier r` is soundness of the verifier that runs on the struct of record**,
at fifteen queries more: the same extractor, the same claim; whatever `files` and `layOf` are. -/
theorem soundForWith_parsed
    (prove' : (innerSystem r).Weights → (innerSystem r).CommitmentRandomness → List Token →
      List Token → RandomizedAlgorithm Parsed)
    {extractor : Commitment → QueryLog → Option (innerSystem r).Weights}
    {claim : (innerSystem r).Weights → List Token → List Token → Prop} {ε : ℕ → ℝ≥0∞}
    (hs : SoundForWith (innerSystem r) extractor claim ε) :
    SoundForWith ((innerSystem r).withVerifier Parsed prove' (verifyParsed r files layOf)) extractor
      claim fun t => ε (t + 15) :=
  soundForWith_behind (innerSystem r) prove' (verifyParsed r files layOf)
    (reader files layOf ([], r.fallbackProof)) 15 (verifyParsed_yes r files layOf ([], r.fallbackProof))
    (reader_asks files layOf ([], r.fallbackProof)) hs

/-- **The same for `Sound`.** -/
theorem sound_parsed
    (prove' : (innerSystem r).Weights → (innerSystem r).CommitmentRandomness → List Token →
      List Token → RandomizedAlgorithm Parsed)
    {ε : ℕ → ℝ≥0∞} (hs : Sound (innerSystem r) ε) :
    Sound ((innerSystem r).withVerifier Parsed prove' (verifyParsed r files layOf))
      fun t => ε (t + 15) :=
  sound_behind (innerSystem r) prove' (verifyParsed r files layOf)
    (reader files layOf ([], r.fallbackProof)) 15 (verifyParsed_yes r files layOf ([], r.fallbackProof))
    (reader_asks files layOf ([], r.fallbackProof)) hs

end OnBytes.Maker.ParsedRead

#print axioms OnBytes.Maker.ParsedRead.readTree_asks
#print axioms OnBytes.Maker.ParsedRead.readTree_noCoin
#print axioms OnBytes.Maker.ParsedRead.reader_asks
#print axioms OnBytes.Maker.ParsedRead.verifyParsed_yes
#print axioms OnBytes.Maker.ParsedRead.soundForWith_parsed
#print axioms OnBytes.Maker.ParsedRead.sound_parsed
