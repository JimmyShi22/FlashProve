-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/BatchClauseOff.lean: the named set of bad traces and its four laws for a written
batch protocol whose instances have a part that stands in no query and is read off the trace.

OnBytes/TypedOracleCompiler/Slice/BatchClause.lean asks of the state function laws at `L.early x`, what the first
query holds of an instance x. Where `early` forgets a part of x that the decision reads, these laws
ask more than soundness instance by instance, and can be false. Here instances are pairs (a, s); the
first query holds (a, d) for a fixed d, and no later query holds the instance. The lane's state
takes its s from a reading off the trace, `extS`, a free parameter. THE LAWS OF THE STATE FUNCTION
ARE ASKED AT THE WHOLE INSTANCE (`StLawsOwn`): they follow from round-by-round soundness instance by
instance (`stLawsOwn_reply`).

In a lane the one thing that sees the trace is the reading of the external strings, so the value
rides beside the string, in a protocol over `ExtSpec.withS`. That stays inside the proofs: the
sibling's `plusQ` (OnBytes/TypedOracleCompiler/Compile/Batch/Plus.lean) has the given protocol's shape, annotation
and reads, and its compiled verifier is the given protocol's.
 - `accepted_off_at`: `accepted_off` (OnBytes/TypedOracleCompiler/Slice/AcceptedOff.lean) for a protocol over any
   kind of external strings: the run is the compiled verifier's at the protocol itself;
 - `StLawsOwn`, `stLawsOwn_reply`, `joint_reply_id`: the three laws at the whole instance; they and
   the law on verifier's messages hold of the state function `replySt` at the identity, if the
   protocol is sound for the language;
 - `WrittenB.laneOff`, `laneOff_ok`: the lane, and that it obeys the laws of a lane, whatever `extS`
   is, IF the wiring is lawful and the state function obeys the law on verifier's messages;
 - `SeedFirst`: at every challenge query whose chain begins with the root and with what the first
   query holds of the instance, what `extS` reads off the trace before it is what it reads off the
   whole trace;
 - `batBadOff`: the two clashes, a lucky step of that lane, a lucky step of a SECOND GIVEN LANE
   under another tag, one query with two answers; `batBadOff_rare`, `batBadOff_mono`,
   `batBadOff_lang`, `batBadOff_second`, `batBadOff_stable`.

`batBadOff_lang`: outside the set, for a string whose external openings the reading keeps, whose run
is in the trace, UNDER `SeedFirst`: the value that `extS` reads off the trace is not the instance's,
or the language holds.

Main definitions: `StLawsOwn`, `WrittenB.laneOff`, `SeedFirst`, `batBadOff`.
Main theorems: `accepted_off_at`, `stLawsOwn_reply`, `joint_reply_id`, `laneOff_ok`,
`batBadOff_rare`, `batBadOff_mono`, `batBadOff_lang`, `batBadOff_second`, `batBadOff_stable`.

Not claimed. `SeedFirst` IS A HYPOTHESIS ON THE TRACE. A maker can break it at no cost (it asks for
the value late: after a first query that holds the root), so it is in no set of small probability:
`batBadOff_lang` by itself speaks of makers that ask first alone. No `extS` is given, and nothing
shuts out its first way out, "the value read off the trace is not the instance's". The second lane
is a parameter of which only its laws, its tag and its counts are asked: no theorem here draws
anything from its step event but that outside the set there is none (`batBadOff_second`). No form
with "there is" is stated, and no judge. The verifier is the one without the test of the strict
format. One external string and one root. What the heads of BatchClause.lean and AcceptedOff.lean do
not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it
builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ReplyClause
import OnBytes.TypedOracleCompiler.Slice.AcceptedOff
import OnBytes.TypedOracleCompiler.Compile.Batch.Plus
import OnBytes.TypedOracleCompiler.Compile.Batch.TwoLanes

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (ReplyLost replySt replySt_start replySt_prover replySt_full replyLost_id_iff
  replySt_joint_times)
open scoped ENNReal

/-! ## The lemma at the protocol itself -/

section
variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- `accepted_off` for a protocol over any kind of external strings: the run is the compiled
verifier's at Q itself; the lane is made at `plusQ Q Sd`, which has Q's shape and annotation. -/
theorem accepted_off_at (t : Tag) {Y0 Sd : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof (Y0 × Sd) E)
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y0 × Sd → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    {Lg : Y0 × Sd → E.Str → Prop} (State : E.Str → Y0 × Sd → PTr Q.loc.shape → Bool)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y0) (d : Sd)
    (extY : Tc W → List (Dig lam) → E.Str) (extS : Tc W → List (Dig lam) → Sd)
    (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr) (hF : ¬ EF tr)
    (hS : ¬ StepEvent (laneOf W t (plusQ Q Sd) wq.sh prjS prjP ε
      (fun (y : E.Str × Sd) x τ => State y.1 (x.1, y.2) τ) (fun o => (xout o).map fun a => (a, d))
      (fun tr cms => (extY tr cms, extS tr cms))).step tr)
    (cms : List (Dig lam)) (x : Y0 × Sd) (π : OneProtocolProof lam Q) (inst : ℕ → Y0)
    (hx : ∀ i, xout (instX L (xin x) i) = some (inst i))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hst1 : ∀ y, ¬ Lg x y → State y (inst 0, x.2) (PTr.empty Q.loc.shape) = false)
    (hst2 : ∀ y (τ : AtP Q.loc.shape) (m : τ.round.Msg), ¬ Lg x y →
      State y (inst (τ.idx - 1), x.2) (.atP τ) = false →
      State y (inst τ.idx, x.2) (.atV (τ.snoc m)) = false)
    (hst3 : ∀ y τ, ¬ Lg x y →
      State y (inst (Q.loc.shape.length - 1), x.2) (.full τ) = false →
      Q.loc.accept x y τ = false)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE (W.dReq t) cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post l cur,
      tr = pre ++ fbE t q a :: post →
      Ours (⟨tr, t, cms, xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) pre q l cur →
      extY pre cms = extY tr cms ∧ extS pre cms = extS tr cms)
    (hagree : ∀ p op, π.ext p = some op →
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE op.sym, op.salt⟩ →
      E.rd (extY tr cms) p = op.sym) : extS tr cms ≠ x.2 ∨ Lg x (extY tr cms) :=
  accepted_off t (plusQ Q Sd) (plusW wq d) embS embP xin embE (plus_okg d hOK)
    (plus_isLocal Sd hloc) (plus_coherent Sd hco) State prjS hprjS prjP hprjP xout d extY extS ε
    hM hF hS cms x (plusPi π Sd) inst hx hlate hst1 hst2 (fun y _ τ => hst3 y τ)
    ((verifyB_plus t Q wq d embS embP xin embE (W.dReq t) cms x π).symm ▸ hrun) hstab hagree

end

/-! ## A written batch protocol whose instances are pairs -/

variable {I A Sd : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)}

/-- The laws of a state function for the language Lg AT THE WHOLE INSTANCE: a false statement starts
in state 0; a prover's message never changes 0 to 1; at the end state 0 means that a false instance
is rejected. -/
structure StLawsOwn {W : QueryLayout lam L} (Z : WrittenB W)
    (State : (Fin L.wordLength → L.Symbol) → A × Sd → PTr Z.Q.loc.shape → Bool)
    (Lg : A × Sd → (oneExternalString L.wordLength L.Symbol).Str → Prop) : Prop where
  start : ∀ y x, ¬ Lg x y → State y x (PTr.empty Z.Q.loc.shape) = false
  prover : ∀ y x (τ : AtP Z.Q.loc.shape) (m : τ.round.Msg),
    State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false
  full : ∀ y x (τ : Tr Z.Q.loc.shape), ¬ Lg x y → State y x (.full τ) = false →
    Z.Q.loc.accept x y τ = false

/-- Round-by-round soundness, instance by instance, gives these laws, of the state function
`replySt` at the identity. -/
theorem stLawsOwn_reply {W : QueryLayout lam L} (Z : WrittenB W)
    (Lg : A × Sd → (oneExternalString L.wordLength L.Symbol).Str → Prop) (ε : Err Z.Q.loc.shape)
    (h : Z.Q.loc.Sound Lg ε) : StLawsOwn Z (replySt Z.Q.loc ε id Lg) Lg where
  start := fun y x _ => replySt_start (replyLost_id_iff.2 h) y x
  prover := fun y x τ m h0 => replySt_prover y x τ m h0
  full := fun y x τ hL h0 => replySt_full y x τ hL h0

/-- The law on verifier's messages holds of that state function, at the errors ε with those of the
shared rounds multiplied by the number of slots. -/
theorem joint_reply_id {W : QueryLayout lam L} (Z : WrittenB W)
    (Lg : A × Sd → (oneExternalString L.wordLength L.Symbol).Str → Prop) (ε : Err Z.Q.loc.shape) :
    Joint Z (Err.timesShared L.maxBatchSize Z.Q.ann ε) (replySt Z.Q.loc ε id Lg) :=
  fun y x => replySt_joint_times L.maxBatchSize Z.Q.ann y x

section
variable {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
  (extS : Tc W → List (Dig lam) → Sd) (d : Sd) (ε : Err Z.Q.loc.shape)
  (State : (Fin L.wordLength → L.Symbol) → A × Sd → PTr Z.Q.loc.shape → Bool)

/-- The written batch protocol as a lane whose state takes the first part of the instance from the
query and THE SECOND PART FROM THE TRACE, by `extS`; judged at the string as R reads it. (d only
fills the second place of a pair whose second place the state does not read.) -/
def WrittenB.laneOff : Lane W :=
  laneOf W Z.t (plusQ Z.Q Sd) Z.wq.sh Z.prjS Z.prjP ε
    (fun (y : (Fin L.wordLength → L.Symbol) × Sd) x τ => State y.1 (x.1, y.2) τ)
    (fun o => (o.map Prod.fst).map fun a => (a, d))
    (fun tr cms => (R.at W tr (cms.getD 0 default), extS tr cms))

/-- That lane obeys the laws of a lane, whatever `extS` is, if the wiring is lawful and the
state function obeys the law on verifier's messages. -/
theorem laneOff_ok (hZ : Z.OK) (hJ : Joint Z ε State) : (Z.laneOff R extS d ε State).OK L.maxBatchSize :=
  lane_off_ok (Q := plusQ Z.Q Sd) (xout := fun o => o.map Prod.fst) hZ.wire.sh hJ

/-- At every challenge query under the protocol's tag whose chain begins with the root cm and with
what the first query holds of x (`Ours`: whatever the salt, the rounds' roots and the plain parts:
the accepted string's own chain is one of these), what `extS` reads off the trace before the query
is what it reads off the whole trace. -/
def SeedFirst (tr : Tc W) (cm : Dig lam) (x : A × Sd) (π : OneProtocolProof lam Z.Q) : Prop :=
  ∀ pre (q : FbIn lam L Z.t) (a : FsAns lam W.K) post l cur, tr = pre ++ fbE Z.t q a :: post →
    Ours (⟨tr, Z.t, [cm], some x, π.salt, π.rtreq, π.slot⟩ : Ctx W) pre q l cur →
    extS pre [cm] = extS tr [cm]

variable (ℓ : Lane W)

/-- The named set of bad traces: the two clashes, a lucky step of the written protocol's lane, a
lucky step of a second given lane ℓ, and one query with two answers (a list of entries can hold
that; a log of a run under oracle functions cannot). -/
def batBadOff : Tc W → Prop := Bad3 (Z.laneOff R extS d ε State) ℓ

/-- Under the typed random oracles the named set is reached with small probability: by an
algorithm of at most t queries with probability at most t εs + 2 (t + 1)² / 2 ^ lam. Asked: every
count of ε and of the second lane is at most εs; the state function obeys the law on verifier's
messages; `Z.OK`; there are as many slots as the request tree at Z's tag has leaves; the second
lane stands under another tag and obeys the laws of a lane, at as many slots as the request tree at
ITS tag has leaves. The two numbers need not be equal. -/
theorem batBadOff_rare (εs : ℝ≥0∞) (hb : Err.Below ε εs) (hJ : Joint Z ε State) (hZ : Z.OK)
    (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) {Nℓ : ℕ} (hNℓ : Nℓ = 2 ^ (W.dReq ℓ.t)) (hne : Z.t ≠ ℓ.t)
    (oℓ : ℓ.OK Nℓ) (bℓ : Err.Below ℓ.ε εs)
    (β : Type) (Alg : TypedOracleComputation lam W.K L β) (t : ℕ) (hA : Alg.QueryBound t) :
    pr Alg.withTrace.law {o | batBadOff Z R extS d ε State ℓ o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  bad3_rare (ℓ₁ := Z.laneOff R extS d ε State) hne hN hNℓ (laneOff_ok Z R extS d ε State hZ hJ) oℓ
    hb bℓ β Alg t hA

/-- The named set is closed under appending. -/
theorem batBadOff_mono (tr tr' : Tc W) (h : batBadOff Z R extS d ε State ℓ tr) :
    batBadOff Z R extS d ε State ℓ (tr ++ tr') := bad3_mono tr tr' h

/-- Outside the named set, under `SeedFirst`, an accepted string whose external openings R keeps
means: the value that `extS` reads off the trace is not the instance's, or the language holds of
the instance and the string that R reads off the trace under the root. Asked: the first query holds
(x.1, d) of an instance x and no later query holds the instance; the state function has the laws
`StLawsOwn` for the language; `Z.OK`. -/
theorem batBadOff_lang (Lg : A × Sd → (oneExternalString L.wordLength L.Symbol).Str → Prop) (hS : StLawsOwn Z State Lg)
    (hZ : Z.OK) (hE : ∀ x, L.early x = (x.1, d)) (hl : L.late = none) (tr : Tc W) (cm : Dig lam)
    (x : A × Sd) (π : OneProtocolProof lam Z.Q) (hB : ¬ batBadOff Z R extS d ε State ℓ tr)
    (hk : ∀ p op, π.ext p = some op → R.keeps p op.sym op.salt)
    (hrun : RunsIn tr (Z.verifier cm x π) true) (hsf : SeedFirst Z extS tr cm x π) :
    extS tr [cm] ≠ x.2 ∨ Lg x (R.at W tr cm) := by
  obtain ⟨hM, hF, hS1, -, -⟩ := not_bad3 hB
  exact accepted_off_at Z.t Z.Q Z.wq Z.embS Z.embP some W.embE hZ.wire hZ.loc hZ.coh
    (Lg := Lg) State Z.prjS hZ.backS Z.prjP hZ.backP (fun o => o.map Prod.fst) d
    (fun tr cms => R.at W tr (cms.getD 0 default)) extS ε hM hF hS1 [cm] x π (fun _ => x.1)
    (fun i => by
      show (instX L (some x) i).map Prod.fst = some x.1
      unfold instX
      rw [hl]
      show ((some x).map L.early).map Prod.fst = some x.1
      rw [Option.map_some, hE]
      rfl)
    (fun n hn _ => hZ.late n hn)
    (fun y hL => hS.start y x hL)
    (fun y τ m _ h => hS.prover y x τ m h)
    (fun y τ hL h => hS.full y x τ hL h) hrun
    (fun pre q a post l cur htr ho =>
      ⟨R.at_before htr hM (ours_cms _ a ho _ (by simp)), hsf pre q a post l cur htr ho⟩)
    (fun p op hop h => by
      rw [hZ.extDepth, (hZ.ext p).1, (hZ.ext p).2] at h
      exact R.law _ p op.sym op.salt h (hk p op hop))

/-- Outside the named set the second lane has had no lucky step, and each query has one answer. -/
theorem batBadOff_second (tr : Tc W) (hB : ¬ batBadOff Z R extS d ε State ℓ tr) :
    ¬ StepEvent ℓ.step tr ∧ OneAns tr :=
  ⟨(not_bad3 hB).2.2.2.1, (not_bad3 hB).2.2.2.2⟩

/-- If the longer trace is outside the named set, what is read off under a root that was announced
in the shorter one does not change. -/
theorem batBadOff_stable (tr tr' : Tc W) (cm : Dig lam)
    (hB : ¬ batBadOff Z R extS d ε State ℓ (tr ++ tr')) (hann : Announced W tr cm) :
    R.at W tr cm = R.at W (tr ++ tr') cm :=
  R.at_stable (not_bad3 hB).1 (List.prefix_append _ _) (occursIn_of_announced hann)

end

end TypedOracleCompiler.Slice
