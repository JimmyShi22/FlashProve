-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Premises.lean: THE PREMISES of the statement of index privacy for the scheme with
the whole key published (Johnson/WholeKey/Statement.lean), each a small named property, TYPED ON THE
INTERACTIVE PROTOCOLS' HONEST SIDES THAT THE SCHEME's COMMITTER AND PROVER PLAY.

General definitions. This file states no goal of the release, and it proves nothing. Whether any
object, wire or honest side meets these properties is not said here.

ONE VALUE OF THE PROVERS. AtRecs holds the three protocols' honest sides (ThreeProvers,
Johnson/Prover/All/OfHonest.lean) with the decisions of their abort sets, and the other letters of
the scheme's honest side; AtRecs.side is the scheme's honest side made of them (HonestSide,
Johnson/WholeKey/Defs.lean). A statement on completeness, one on index binding and one on index
privacy that all speak of argW … a.side speak of the same provers, because a.Hs occurs once. That
matters: silent honest sides, which send fixed messages and never stop, meet every premise on
provers with error 0, and a statement of index privacy says something of a protocol only beside
completeness of the same honest sides.

The properties.
  ExtEnc Hs     the external strings of each honest side are the encoded index(es) of its private
               input.
  RunVals a ok   at the indices of the range ok: the strings of which the public starts of a
               compiled run's leaf salts are made stand in the plain parts of the honest run, at all
               verifier messages OUTSIDE THE HONEST SIDE's ABORT SET (where its messages are
               withheld nothing is asked).
  Hiop.Seeded.ReadsG L Gs b qT qpar qch qon (Hiop/Seeded/Game.lean; not defined here)   how many
               positions of a table the three verifiers read; and, at every seed of the PUBLIC set
               Gs, the law of (honest out-of-domain answers, the encoded index at any b positions)
               does not hang on the index.
  Sims.Good    each of the three simulators of the interactive protocols (the session's: one for
               each number of a copy) has exactly the honest output's law, at every private input
               whose INDEX IS IN THE RANGE ok (a letter: a property of indices) and whose seeds lie
               in Gs, for EVERY value of the encoding's randomness, but for a set of
               verifier messages of bounded measure. TWO THINGS ON ITS FORM.
               (1) THE STOPS ARE A TERM OF THEIR OWN. The honest output is "none" on the honest
               side's abort set. One part of that set is public (Honest.Bad) and a simulator can
               know it. The other part may hang on the private input (Honest.Hid), so on the index:
               a simulator cannot know it. Good is asked OUTSIDE that part, and StopsSmall bounds
               its measure by numbers hT, hL, hO of their own. There is no premise "the honest side
               does not stop".
               (2) It is asked AT VERIFIER MESSAGES WHOSE TEST BITS ARE 0: the measure is that of
               the uniform ρ for which the two laws differ at (ρ with its test bits set to 0). That
               is the law of the verifier messages of a compiled run that has passed its searches
               for nonces. So nothing is asked on how the honest side behaves at other test bits.
  StopsSmall   see (1).
  ReadsFree    the positions that a verifier reads do not hang on the nonces in the plain parts.
  SeedPlain    the plain parts of a seed's two queries stand for the number 0 where the wire reads a
               nonce off a plain part: a seed's query is nobody's second or later try.
  WithinWin    a window of rounds, trees and leaves holds all trees of a wire.
  CoinsFit     the laws on all coins (Johnson/WholeKey/CoinLaws.lean), with the lengths that the
               verifier's strict format asks.
  NoncesBack   in every round with a test, each number that the search may try, up to the cap, is
               read back from the plain part into which it was written. (So two tries are two
               queries. The wire's own law says it up to the wire's own number of tries alone; the
               cap is a letter of its own.)
  PremW        ALL PREMISES TOGETHER, with the budget of reads FOR EACH TABLE: the first table bears
               its test and M + 1 links; a copy bears its link and s1 sessions.

Limits. Definitions alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.OfRecs
import Johnson.WholeKey.CoinLaws
import Johnson.WholeKey.Sim
import Hiop.Seeded.Game

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ}

/-! ## The scheme's honest side, made of the protocols' honest sides -/

/-- **The scheme's honest side's letters, with the strategies given by the three protocols' honest
sides.** -/
structure AtRecs (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) where
  /-- the three protocols' honest sides -/
  Hs : ThreeProvers L
  /-- the decisions of their abort sets, as data -/
  dc : Decs Hs
  b₀ : Bd
  capT : ℕ → ℕ
  capL : ℕ → ℕ
  capB : ℕ → ℕ
  /-- the number of copies is M + 1 -/
  M : ℕ
  nm : ℕ → ℕ
  RV : Type
  /-- which run values are of the right form (their strings have the right lengths) -/
  okV : RV → Prop
  rvT : Hs.T.Coin → RV
  rvL : Hs.Lk.Coin → RV
  rvB : Hs.B.Coin → RV
  startT : RV → ℕ → Bool → Bits → Bits
  startL : RV → ℕ → Bool → Bits → Bits
  startB : RV → ℕ → Bool → Bits → Bits
  pvT : Plains L.offline.shape → RV
  pvL : Plains L.link.shape → RV
  pvB : Plains L.onlineBatch.loc.shape → RV
  rtail : ℕ → Bits
  nR : ℕ
  nK : ℕ
  nJ : ℕ
  fill : Bits
  ri : Enum L.EncodingRandomness
  sl : Enum (ℕ → Bits)
  kT : Enum Hs.T.Coin
  kL : Enum Hs.Lk.Coin
  kB : Enum Hs.B.Coin
  coT : Enum (Coins lam (typedOracleCarrier L Bd aT aL))
  coL : Enum (Coins lam (typedOracleCarrier L Bd aT aL))
  coB : Enum (Coins lam (typedOracleCarrier L Bd aT aL))

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- The scheme's honest side made of them: the strategies are theirs, and a run's messages are
withheld exactly on their abort sets (Plays.ofRecs, Johnson/WholeKey/OfRecs.lean). -/
def AtRecs.side (a : AtRecs lam L Bd aT aL) : HonestSide lam L Bd aT aL where
  KT := a.Hs.T.Coin
  KL := a.Hs.Lk.Coin
  KB := a.Hs.B.Coin
  st := Plays.ofRecs a.Hs a.dc
  b₀ := a.b₀
  capT := a.capT
  capL := a.capL
  capB := a.capB
  M := a.M
  nm := a.nm
  RV := a.RV
  rvT := a.rvT
  rvL := a.rvL
  rvB := a.rvB
  startT := a.startT
  startL := a.startL
  startB := a.startB
  pvT := a.pvT
  pvL := a.pvL
  pvB := a.pvB
  rtail := a.rtail
  nR := a.nR
  nK := a.nK
  nJ := a.nJ
  fill := a.fill
  ri := a.ri
  sl := a.sl
  kT := a.kT
  kL := a.kL
  kB := a.kB
  coT := a.coT
  coL := a.coL
  coB := a.coB

/-! ## On the protocols' honest sides -/

/-- The external strings of each honest side are the encoded index(es) of its private input. -/
structure ExtEnc (Hs : ThreeProvers L) : Prop where
  T : ∀ i r e, Hs.T.ext (i, r, e) = L.encodeIndex i r
  Lk : ∀ i r e r' e', Hs.Lk.ext (i, (r, e), (r', e')) = (L.encodeIndex i r, L.encodeIndex i r')
  B : ∀ i r e n, Hs.B.ext (i, r, e, n) = L.encodeIndex i r

/-- The run values, of which the starts of a compiled run's leaf salts are made, stand in the plain
parts of the honest run, at all verifier messages at which the honest side does not withhold its
messages: read off these plain parts they are what is read off the strategy's coins. -/
structure RunVals (a : AtRecs lam L Bd aT aL) (ok : I → Prop) : Prop where
  T : ∀ i r e κ ρ, ok i → ρ ∉ a.Hs.T.withheld (i, r, e) (L.recOf i r e) →
    a.pvT ((a.Hs.T.strat (i, r, e) (L.recOf i r e) κ).run ρ).1.plains = a.rvT κ
  Lk : ∀ i u u' κ ρ, ok i →
    ρ ∉ a.Hs.Lk.withheld (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) →
    a.pvL ((a.Hs.Lk.strat (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) κ).run ρ).1.plains =
      a.rvL κ
  B : ∀ i r e n x κ ρ, ok i → ρ ∉ a.Hs.B.withheld (i, r, e, n) (x, L.recOf i r e) →
    a.pvB ((a.Hs.B.strat (i, r, e, n) (x, L.recOf i r e) κ).run ρ).1.plains = a.rvB κ

/-- **The simulators of the interactive protocols are good for the honest sides**, at seeds of Gs,
at verifier messages with the test bits 0. The head says how it is to be read. -/
structure Sims.Good (Sm : Sims L) (Hs : ThreeProvers L) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (zT zL zO : ℝ≥0∞) : Prop where
  T : ∀ i r e, ok i → Gs e →
    pr (unif (Rho L.offline.shape))
      {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∉ Hs.T.Hid (i, r, e) (L.recOf i r e) ∧
        Hs.T.output (i, r, e) (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ) ≠
        Sm.T (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ)
          (L.offline.extAns (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ)
            (L.encodeIndex i r))} ≤ zT
  Lk : ∀ i r e r' e', ok i → Gs e → Gs e' →
    pr (unif (Rho L.link.shape))
      {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∉
          Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ∧
        Hs.Lk.output (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')
          (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) ≠
        Sm.Lk (L.recOf i r e, L.recOf i r' e') (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ)
          (L.link.extAns (L.recOf i r e, L.recOf i r' e')
            (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) (L.encodeIndex i r, L.encodeIndex i r'))} ≤ zL
  B : ∀ n i r e x, ok i → Gs e → Ryes i x →
    pr (unif (Rho L.onlineBatch.loc.shape))
      {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∉
          (sessionAt Hs n).Hid (i, r, e) (x, L.recOf i r e) ∧
        (sessionAt Hs n).output (i, r, e) (x, L.recOf i r e)
          (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) ≠
        Sm.B n (x, L.recOf i r e) (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ)
          (L.onlineBatch.loc.extAns (x, L.recOf i r e)
            (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) (L.encodeIndex i r))} ≤ zO

/-- **The stops that hang on the private input are rare**: the measure, in the same sense, of that
part of each honest side's abort set which may hang on the private input (Honest.Hid,
Iop/InteractiveOracleProof.lean). -/
structure StopsSmall (Hs : ThreeProvers L) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (ok : I → Prop)
    (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (hT hL hO : ℝ≥0∞) : Prop where
  T : ∀ i r e, ok i → Gs e →
    pr (unif (Rho L.offline.shape))
      {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ Hs.T.Hid (i, r, e) (L.recOf i r e)} ≤ hT
  Lk : ∀ i r e r' e', ok i → Gs e → Gs e' →
    pr (unif (Rho L.link.shape))
      {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈
        Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')} ≤ hL
  B : ∀ n i r e x, ok i → Gs e → Ryes i x →
    pr (unif (Rho L.onlineBatch.loc.shape))
      {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈
        (sessionAt Hs n).Hid (i, r, e) (x, L.recOf i r e)} ≤ hO

/-! ## On the protocols and the wires -/

/-- The positions that the verifier reads do not hang on the nonces: at two transcripts that are
alike but for nonces (Puts, OnBytes/Prover/Inv.lean) it reads the same positions. -/
def ReadsFree {K : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) : Prop :=
  ∀ (x : Y) (τ τ' : Tr Q.loc.shape), Puts Q.loc.shape Q.ann sh τ τ' →
    Q.loc.reads x τ.rho τ'.plains = Q.loc.reads x τ.rho τ.plains

/-- The number for which the nonce in a plain part stands; 0 if its component has no test. -/
def nonceOf {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PlainPart s A → ℕ
  | [], _, _, z => nomatch z
  | _ :: _, (_, _), (w, _), .inl (.inl α) =>
      match w.gr0 with
      | none => 0
      | some g => g.get α
  | _ :: _, (_, _), (w, _), .inl (.inr α) =>
      match w.grJ with
      | none => 0
      | some g => g.get α
  | _ :: s, (_, A), (_, W), .inr z => nonceOf s A W z

/-- The wires of the rounds of a protocol, by its tag. -/
def wiresOf {I' X' : Type} {L' : BatchProtocolWithLeafBody I' X'} (W : QueryLayout lam L') :
    (t : Tag) → RoundsQueryLayout lam W.K (shapeOf L' t) (annOf L' t)
  | .test => W.T.sh
  | .link => W.Lk.sh
  | .onl => W.B.sh

/-- The plain parts of a seed's two queries stand for the number 0. -/
def SeedPlain (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) : Prop :=
  nonceOf _ _ (wiresOf W S.t) S.pl0 = 0 ∧ nonceOf _ _ (wiresOf W S.t) S.pl1 = 0

/-- In every round with a test, each number up to the cap is read back from the plain part into
which it was written. i: the number of the first of the rounds s. -/
def NoncesBack {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → Prop
  | [], _, _, _, _ => True
  | _ :: s, (a, A), (w, W), cap, i =>
      (match a.kind with
        | .lo => ∀ g, w.grJ = some g → ∀ k α, k ≤ cap i → g.get (g.put k α) = k
        | .sh => ∀ g, w.gr0 = some g → ∀ k α, k ≤ cap i → g.get (g.put k α) = k) ∧
        NoncesBack s A W cap (i + 1)

/-- All trees of the rounds' wires lie within a window: at most nK trees a component, at most nJ
leaves a tree. -/
def WithinWin {K : ℕ} (nK nJ : ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, W) =>
      (w.depth0.length ≤ nK ∧ w.depthJ.length ≤ nK ∧ (∀ d ∈ w.depth0, 2 ^ d ≤ nJ) ∧
        ∀ d ∈ w.depthJ, 2 ^ d ≤ nJ) ∧ WithinWin nK nJ s A W

/-! ## On the coins -/

/-- The letters of the laws on coins. -/
structure CoinNums (Bd : Type) where
  /-- the public start of a table's leaf salt -/
  pre₀ : Bits
  /-- THE FREE BITS of a leaf's salt -/
  ℓ : ℕ
  /-- the bits of the string behind a slot's value -/
  ℓr : ℕ
  /-- the fixed padding and slot of each of the three kinds of run: public -/
  padT : Bd
  padL : Bd
  padB : Bd
  slotT : ℕ
  slotL : ℕ
  slotB : ℕ

/-- **The laws on all coins.** Each enumeration of a finite type lists each member once. The tables'
salts, and the coins of the three kinds of compiled run, have a public start and free bits that are
uniform and independent; with their public starts the salts have the length that the verifier's
strict format asks; the windows hold all that the wires have. -/
structure CoinsFit (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params) (a : AtRecs lam L Bd aT aL)
    (c : CoinNums Bd) : Prop where
  ri : a.ri.OK
  kT : a.kT.OK
  kL : a.kL.OK
  kB : a.kB.OK
  sl : SaltsLaw a.sl (2 ^ W.depth) c.pre₀ c.ℓ
  len₀ : c.pre₀.length + c.ℓ = p.sMT
  /-- the run values that the strategies' coins give are of the right form -/
  okT : ∀ κ, a.okV (a.rvT κ)
  okL : ∀ κ, a.okV (a.rvL κ)
  okB : ∀ κ, a.okV (a.rvB κ)
  /-- at run values of the right form, a round within the window and a first salt of the right
  length, a leaf's salt has the length that the strict format asks -/
  lenT : ∀ v i b s, a.okV v → i < a.nR → s.length = p.sFS →
    (a.startT v i b s).length + c.ℓ = p.sMT
  lenL : ∀ v i b s, a.okV v → i < a.nR → s.length = p.sFS →
    (a.startL v i b s).length + c.ℓ = p.sMT
  lenB : ∀ v i b s, a.okV v → i < a.nR → s.length = p.sFS →
    (a.startB v i b s).length + c.ℓ = p.sMT
  coT : RunLaw a.coT a.nR a.nK a.nJ p.sFS c.ℓ c.ℓr W.depthReqT c.padT c.slotT
  coL : RunLaw a.coL a.nR a.nK a.nJ p.sFS c.ℓ c.ℓr W.depthReqL c.padL c.slotL
  coB : RunLaw a.coB a.nR a.nK a.nJ p.sFS c.ℓ c.ℓr W.depthReq c.padB c.slotB
  rounds : L.offline.shape.length ≤ a.nR ∧ L.link.shape.length ≤ a.nR ∧
    L.onlineBatch.loc.shape.length ≤ a.nR
  winT : WithinWin a.nK a.nJ L.offline.shape aT (wTC W).sh
  winL : WithinWin a.nK a.nJ L.link.shape aL (wLC W).sh
  winB : WithinWin a.nK a.nJ L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh

/-! ## All together -/

/-- The numbers of the statement. -/
structure NumsW where
  /-- positions of one table that may be read -/
  b : ℕ
  /-- read by the key's test; by a link on the first table; by a link on its copy; by a session -/
  qT : ℕ
  qpar : ℕ
  qch : ℕ
  qon : ℕ
  /-- sessions that a copy bears -/
  s1 : ℕ
  /-- the errors of the three simulators of the interactive protocols -/
  zT : ℝ≥0∞
  zL : ℝ≥0∞
  zO : ℝ≥0∞
  /-- the measures of the stops that hang on the private input, for the three kinds of run -/
  hT : ℝ≥0∞
  hL : ℝ≥0∞
  hO : ℝ≥0∞
  /-- the chance that a seed lies outside Gs -/
  δ : ℝ≥0∞

/-- **ALL PREMISES of the statement of index privacy.** -/
structure PremW (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : Params) (a : AtRecs lam L Bd aT aL) (Sm : Sims L)
    (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (c : CoinNums Bd) (N : NumsW) :
    Prop where
  /-- the honest sides speak of the encodings -/
  ext : ExtEnc a.Hs
  /-- the run values stand in the plain parts -/
  runVals : RunVals a ok
  /-- the encoding hides, at the seeds of Gs; the verifiers' reads are counted -/
  reads : Hiop.Seeded.ReadsG L Gs N.b N.qT N.qpar N.qch N.qon
  /-- the first table's budget: its test and M + 1 links -/
  budget₀ : N.qT + (a.M + 1) * N.qpar ≤ N.b
  /-- a copy's budget: its link and s1 sessions -/
  budget₁ : N.qch + N.s1 * N.qon ≤ N.b
  /-- the simulators of the interactive protocols are good for the honest sides -/
  good : Sm.Good a.Hs W ok Gs Ryes N.zT N.zL N.zO
  /-- the stops that hang on the private input are rare -/
  stops : StopsSmall a.Hs W ok Gs Ryes N.hT N.hL N.hO
  /-- a seed made from uniform digests lies outside Gs with probability at most δ -/
  seeds : pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ N.δ
  /-- the positions read do not hang on nonces -/
  freeT : ReadsFree (batTC L aT) (wTC W).sh
  freeL : ReadsFree (batLC L aL) (wLC W).sh
  freeB : ReadsFree L.onlineBatch (wBC W).sh
  /-- the wires' laws and the code of the answers -/
  wires : OKA W cA
  /-- every round has a format -/
  fmt : aT.Fmt ∧ aL.Fmt ∧ L.onlineBatch.ann.Fmt
  /-- the numbers that a search may try are read back -/
  backT : NoncesBack L.offline.shape aT (wTC W).sh a.capT 0
  backL : NoncesBack L.link.shape aL (wLC W).sh a.capL 0
  backB : NoncesBack L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh a.capB 0
  /-- a seed's query is nobody's later try -/
  plain : SeedPlain W S
  /-- the marks fit together; the verifiers read at the declared positions alone -/
  coherent : aT.Coherent ∧ aL.Coherent ∧ L.onlineBatch.ann.Coherent
  isLocal : L.offline.IsLocal ∧ L.link.IsLocal ∧ L.onlineBatch.loc.IsLocal
  /-- the coins -/
  coins : CoinsFit W p a c

end OnBytes.WholeKey
