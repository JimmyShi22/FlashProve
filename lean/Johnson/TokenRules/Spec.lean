-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/Spec.lean: THE TOKEN PROGRAMS OF THE SCHEME WITH THE WHOLE KEY PUBLISHED KEEP THE
RULES OF DEFERRED PROGRAMMING, AND HOW MANY EVALUATIONS THEY MAKE. DEFINITIONS AND STATEMENTS; a few
small members at the end. The proofs are in the other files of this folder, over the lemmas of
Johnson/TokenRel/; Closed.lean has the proofs of Spec.safeTwin and Spec.countTwin.

General statements. This file states no goal of the release.

The programs are those of Johnson/TokenSide/ (a compiled run: hashT, then endC, together proveC,
Johnson/TokenRules/Chunks.lean; a table: tabT; the committer commitT; the prover proveWT; the
challenger challT). The programs are a device of one step of
a proof of index privacy and stand in no statement on the scheme: deferred programming
(Rom.Spec.defer, Rom/Defer.lean) asks of every run in mode I that no rule is broken and that the
numbers of ordinary and marked evaluations stay within written counts (DSt.Within). The form of the
statements is the library's own (Compile/Batch/SpecDiscipline.lean, whose pattern this file
follows): SafeO Rl c d Q says that from the state d the program c keeps the rules Rl and ends in Q,
whatever the coins, the answers and the tables are; TidyO says that a state is well formed; GrowsO
Ch R e M d d' says what a run has added: which old tokens its evaluations hold (Ch), which old
tokens it shows (R), and at most e o ordinary and M o marked evaluations at the oracle o. So the
counts are part of the same statements.

What is known of a tree's tokens (TreeOKT d us T). For each leaf the tree keeps two tokens: the free
bits of the salt, and the empty tail of the leaf's answer. Both exist; every evaluation that is
charged to the first has the second as its tail and holds no further token outside us; no evaluation
is charged to the second. us is empty for a table, and is the run's first salt for a tree of a
compiled run. This is what makes the two tokens fit to be shown together (with us).

The statements.
  Spec.safeProveC  A compiled run (all hashing, the test for a stop, the reveals) keeps the rules,
                   holds no old token, shows of the old tokens only such of the external strings'
                   trees, and stays within (eRun, mRun).
  Spec.safeTab     One table: within (eTab, mTab); its tree's tokens are new and have TreeOKT.
  Spec.safeCommit, Spec.safeProveW   The committer; the prover on a batch.
  Spec.safeStep    EACH STEP OF THE CHALLENGER keeps the rules and the invariant InvT, within the
                   counts of a setup or of a session.
  Spec.marksHash, Spec.marksTab   The hashing of a run, and the making of a table, reveal nothing
                   and fit a test on the oracle's name (Marks, Compile/DeferRun/Spec.lean): mkHash,
                   mkTable. The two queries of a table's seed are ordinary queries at a Fiat-Shamir
                   oracle, at which a run's queries are marked: so the two tests differ there.
  Spec.safeTwin    All of these together.
  Spec.stepCount   The step of the induction over an adversary (within_interactB,
                   Compile/Batch/DisciplineWorld.lean), in both modes.
  Spec.zeroOutside The counts allow no marked evaluation outside the oracles osAllT.
  Spec.withinTwin  Every run of an admissible adversary with n batches against the challenger, in
                   both modes, ends within (eAllT n, mAllT n, the rules' bits, osAllT).
  Spec.countTwin   These three together.

The letters bl and bf of the rules (the least number of bits of a token that is charged at a leaf,
at a Fiat-Shamir oracle) must not pass the lengths of the programs' tokens: LensOK. blOf and bfOf
are the largest letters that meet it.

Limits. Statements on token programs: by themselves they say nothing on the scheme. One request a
proof, one run of the committer, as in the programs.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Counts
import Compile.Batch.DisciplineRun
import Compile.Batch.DisciplineWorld
import Compile.DeferRun.Spec

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc (SafeO TidyO GrowsO ClosedO Deps callCostB)
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

/-! ## What is known of a tree's tokens -/

section Generic
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- no token -/
abbrev noTok : Tok → Prop := fun _ => False

/-- u is one of the tokens that the tree keeps -/
def TreeTokT (T : TreeT lam L) (u : Tok) : Prop := ∃ a ∈ T.tok, u = a.1 ∨ u = a.2

/-- **The tokens of a tree can be shown**, leaf by leaf, together with us: see the head. -/
def TreeOKT (d : DSt (typedOracleFamily lam K L)) (us : List Tok) (T : TreeT lam L) : Prop :=
  ∀ a ∈ T.tok, a.1 < d.vals.length ∧ a.2 < d.vals.length ∧ Deps d a.1 (a.2 :: us) ∧ Deps d a.2 []

/-- all tokens of the tree are numbers from n on -/
def TreeNewT (n : ℕ) (T : TreeT lam L) : Prop := ∀ u, TreeTokT T u → n ≤ u

/-! ## The tests on an oracle's name -/

/-- The test that the hashing of a compiled run fits: marked are leaves, Fiat-Shamir queries under
both kinds of names, g, and the request tree's oracles. -/
def mkHash : Mark (typedOracleFamily lam K L) := fun o _ => match o with
  | .leaf => true
  | .rleaf => true
  | .rnode => true
  | .fb _ => true
  | .fbw _ _ => true
  | .g _ => true
  | _ => false

/-- The test that the making of a table fits: marked are the leaves alone. -/
def mkTable : Mark (typedOracleFamily lam K L) := fun o _ => match o with
  | .leaf => true
  | _ => false

end Generic

/-! ## A compiled run -/

namespace Spec

/-- **A compiled run**, which shows its tokens in several reveals: it holds no old token, and shows
of the old tokens only such of the external strings' trees. -/
def safeProveC : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (bl bf : ℕ) (sd : (t : Tag) → FbIn lam L t → Prop)
      (t : Tag) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
      (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeT lam L) (preX : Bits)
      (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits)
      (cap : ℕ → ℕ) (stop : Rho Q.loc.shape → Bool) (d : DSt (typedOracleFamily lam K L)),
    bl ≤ ln.fr → bf ≤ ln.sFS → bf ≤ lam →
    TidyO (rulesT K L lam bl bf sd) d → (∀ k, TreeOKT d [] (xt k)) →
    SafeO (rulesT K L lam bl bf sd)
      (proveC t Q wq embS embP xin cms x y xt preX σ ln pre cap stop) d fun _ d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      GrowsO noTok (fun u => ∃ k, TreeTokT (xt k) u) (eRun Q.loc.shape Q.ann wq.sh)
        (mRun t Q.loc.shape Q.ann wq.sh cap ln.dq) d d'

/-- The hashing of a compiled run reveals nothing and fits the test mkHash, from every store. -/
def marksHash : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X)
      (t : Tag) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
      (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (cms : List (Dig lam)) (x : Y) (σ : Strat Q.loc.shape Unit)
      (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ) (vs : List Bits),
    Marks mkHash (hashT t Q wq embS embP xin cms x σ ln pre cap) vs

end Spec

/-! ## The scheme -/

section Scheme
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The tokens of the prover's key can be shown, leaf by leaf. -/
def IskOKT {K : ℕ} (d : DSt (typedOracleFamily lam K (typedOracleCarrier L Bd aT aL))) (k : IskT lam L Bd aT aL) : Prop :=
  ∀ t ∈ k.copies, TreeOKT d [] t.tree

/-- u is one of the tokens of the prover's key -/
def IskTokT (k : IskT lam L Bd aT aL) (u : Tok) : Prop := ∃ t ∈ k.copies, TreeTokT t.tree u

/-- **The invariant of the challenger**: the state of the experiment is well formed, and the tokens
of the prover's key, once there is one, can be shown. -/
def InvT {K : ℕ} (Rl : Rules (typedOracleFamily lam K (typedOracleCarrier L Bd aT aL)))
    (s : Option (IskT lam L Bd aT aL)) (d : DSt (typedOracleFamily lam K (typedOracleCarrier L Bd aT aL))) : Prop :=
  TidyO Rl d ∧ ∀ k, s = some k → IskOKT d k

/-- The rules' letters do not pass the lengths of the programs' tokens. -/
structure LensOK {KT KL KB : Type} (bl bf : ℕ)
    (tl : TokLen lam (typedOracleCarrier L Bd aT aL) KT KL KB) : Prop where
  frE : bl ≤ tl.frE
  frT : bl ≤ tl.T.fr
  frL : bl ≤ tl.Lk.fr
  frB : bl ≤ tl.B.fr
  sT : bf ≤ tl.T.sFS
  sL : bf ≤ tl.Lk.sFS
  sB : bf ≤ tl.B.sFS
  dig : bf ≤ lam

/-- the largest letter bl: the fewest free bits of a leaf's salt -/
def blOf {KT KL KB : Type} (tl : TokLen lam (typedOracleCarrier L Bd aT aL) KT KL KB) : ℕ :=
  min (min tl.frE tl.T.fr) (min tl.Lk.fr tl.B.fr)

/-- the largest letter bf: the shortest first salt, or the digests' length -/
def bfOf {KT KL KB : Type} (tl : TokLen lam (typedOracleCarrier L Bd aT aL) KT KL KB) : ℕ :=
  min (min tl.T.sFS tl.Lk.sFS) (min tl.B.sFS lam)

end Scheme

namespace Spec

/-- **One table.** -/
def safeTab : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (bl bf : ℕ) (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))),
    bl ≤ tl.frE →
    TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d →
    SafeO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) (tabT W S h tl b₀ i r) d
      fun t d' =>
      TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d' ∧
      GrowsO noTok noTok (eTab W.depth S.t) (mTab W.depth) d d' ∧
      TreeOKT d' [] t.tree ∧ TreeNewT d.vals.length t.tree

/-- The making of a table reveals nothing and fits the test mkTable, from every store. -/
def marksTab : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (vs : List Bits),
    Marks mkTable (tabT W S h tl b₀ i r) vs

/-- **The committer**: it holds and shows no old token; the tokens of the key that it keeps can be
shown. -/
def safeCommit : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam))
      (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (bl bf : ℕ) (i : I) (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))),
    LensOK bl bf tl →
    TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d →
    SafeO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) (commitT W S cA h tl i) d
      fun o d' =>
      TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d' ∧
      IskOKT d' o.2 ∧ GrowsO noTok noTok (eSetup W S h) (mSetup W h tl) d d'

/-- **The prover on a batch**: it holds no old token, and shows of the old tokens only such of its
key; these can still be shown afterwards. -/
def safeProveW : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
      (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (bl bf : ℕ) (k : IskT lam L Bd aT aL) (b : ZKCP.Gen.Batch X Unit)
      (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))),
    LensOK bl bf tl →
    TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d → IskOKT d k →
    SafeO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) (proveWT W cA r₀ h tl k b) d
      fun _ d' =>
      TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d' ∧
      IskOKT d' k ∧ GrowsO noTok (IskTokT k) (eSess W) (mSess W h tl) d d'

/-- **Each step of the challenger** keeps the rules and the invariant, within the counts of a setup
or of a session. -/
def safeStep : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
      (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (bl bf : ℕ) (i : I) (s : Option (IskT lam L Bd aT aL)) (c : GCall X Unit)
      (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))),
    LensOK bl bf tl →
    InvT (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) s d →
    SafeO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S))
      ((challT W S cA r₀ h tl i).step s c) d fun y d' =>
      InvT (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) y.2 d' ∧
      GrowsO noTok (fun u => ∃ k, s = some k ∧ IskTokT k u)
        (callCostB (eSetup W S h) (eSess W) c) (callCostB (mSetup W h tl) (mSess W h tl) c) d d'

/-- **The token programs keep the rules.** -/
def safeTwin : Prop :=
  safeProveC ∧ safeTab ∧ safeCommit ∧ safeProveW ∧ safeStep ∧ marksHash ∧ marksTab

/-- The step of the induction over an adversary, in both modes: the invariant is kept, and a call
adds at most the counts of a setup or of a session. -/
def stepCount : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
      (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (bl bf : ℕ) (i : I) (m : Bool) (s : Option (IskT lam L Bd aT aL))
      (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (c : GCall X Unit),
    LensOK bl bf tl →
    InvT (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) s d →
    ∀ y ∈ (((challT W S cA r₀ h tl i).step s c).run m d).support,
      InvT (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) y.1.2 y.2 ∧
      ∀ o,
        y.2.nPlain o ≤ d.nPlain o + callCostB (eSetup W S h) (eSess W) c o ∧
        nEv y.2 o ≤ nEv d o + callCostB (mSetup W h tl) (mSess W h tl) c o

/-- Outside the oracles osAllT the counts allow no marked evaluation. -/
def zeroOutside : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
      (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (n : ℕ) (o : OracleName), o ∉ osAllT h → mAllT W h tl n o = 0

/-- **Every run against the challenger stays within the counts**: what deferred programming asks
(Rom.Spec.defer), for an adversary that asks for one setup and then for at most n batches. -/
def withinTwin : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
      (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (bl bf : ℕ) (i : I) (m : Bool) (α : Type) (ok : ZKCP.Gen.Batch X Unit → Prop)
      (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
        (_root_.Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ),
    LensOK bl bf tl → GAdm ok A false n →
    ∀ x ∈ (interact ((challT W S cA r₀ h tl i).world m) A (none, DSt.init _)).support,
      x.2.2.Within (eAllT W S h n) (mAllT W h tl n) (bitsOfT lam bl bf) (osAllT h)

/-- **The counts of the token programs.** -/
def countTwin : Prop := stepCount ∧ zeroOutside ∧ withinTwin

end Spec

/-! ## Members: the premises can be met, and the idle steps meet the statement -/

section Members
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The largest letters meet LensOK, at all lengths. -/
theorem lensOK_of {KT KL KB : Type} (tl : TokLen lam (typedOracleCarrier L Bd aT aL) KT KL KB) :
    LensOK (blOf tl) (bfOf tl) tl where
  frE := le_trans (min_le_left _ _) (min_le_left _ _)
  frT := le_trans (min_le_left _ _) (min_le_right _ _)
  frL := le_trans (min_le_right _ _) (min_le_left _ _)
  frB := le_trans (min_le_right _ _) (min_le_right _ _)
  sT := le_trans (min_le_left _ _) (min_le_left _ _)
  sL := le_trans (min_le_left _ _) (min_le_right _ _)
  sB := le_trans (min_le_right _ _) (min_le_left _ _)
  dig := le_trans (min_le_right _ _) (min_le_right _ _)

/-- LensOK can fail: a letter above a length. -/
theorem not_lensOK {KT KL KB : Type} (tl : TokLen lam (typedOracleCarrier L Bd aT aL) KT KL KB) (bl : ℕ) :
    ¬ LensOK bl (lam + 1) tl := fun h => absurd h.dig (Nat.not_succ_le_self lam)

/-- The invariant holds at the start of the experiment. -/
theorem invT_init {K : ℕ} (Rl : Rules (typedOracleFamily lam K (typedOracleCarrier L Bd aT aL))) :
    InvT Rl (none : Option (IskT lam L Bd aT aL)) (DSt.init _) :=
  ⟨_root_.Compile.Batch.Disc.TidyO.init, fun _ h => nomatch h⟩

/-- A tree without leaves has TreeOKT in every state. -/
theorem treeOKT_nil {K : ℕ} {L' : BatchProtocolWithLeafBody I X} (d : DSt (typedOracleFamily lam K L')) (us : List Tok)
    (body : ℕ → Body L') (lv : List (List (Dig lam))) : TreeOKT d us ⟨body, [], lv⟩ :=
  fun _ h => absurd h List.not_mem_nil

/-- TreeOKT can fail: a token that does not exist. -/
theorem not_treeOKT_init {K : ℕ} {L' : BatchProtocolWithLeafBody I X} (us : List Tok) (body : ℕ → Body L')
    (lv : List (List (Dig lam))) (a : Tok × Tok) :
    ¬ TreeOKT (DSt.init (typedOracleFamily lam K L')) us ⟨body, [a], lv⟩ :=
  fun h => absurd (h a (List.mem_singleton.mpr rfl)).1 (Nat.not_lt_zero _)

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
  (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)

/-- The statement on a step, at the two idle steps: a batch before the setup, a second setup. -/
theorem safeStep_idle (bl bf : ℕ) (i : I) (d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (s : Option (IskT lam L Bd aT aL)) (c : GCall X Unit)
    (hc : (∃ b, c = .batch b ∧ s = none) ∨ (c = .setup ∧ ∃ k, s = some k))
    (hd : InvT (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) s d) :
    SafeO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S))
      ((challT W S cA r₀ h tl i).step s c) d fun y d' =>
      InvT (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) y.2 d' ∧
      GrowsO noTok (fun u => ∃ k, s = some k ∧ IskTokT k u)
        (callCostB (eSetup W S h) (eSess W) c) (callCostB (mSetup W h tl) (mSess W h tl) c) d
        d' := by
  rcases hc with ⟨b, rfl, rfl⟩ | ⟨rfl, k, rfl⟩
  · exact ⟨hd, _root_.Compile.Batch.Disc.GrowsO.refl d⟩
  · exact ⟨hd, _root_.Compile.Batch.Disc.GrowsO.refl d⟩

end Members

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.safeStep_idle
#print axioms OnBytes.TokenRules.lensOK_of
#print axioms OnBytes.TokenRules.invT_init
