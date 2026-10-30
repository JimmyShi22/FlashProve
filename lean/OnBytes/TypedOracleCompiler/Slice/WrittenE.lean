-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/WrittenE.lean: a written batch protocol on external strings that are made of one
or two strings of the interface's kind, each under an outer root of its own; and the clause of
OnBytes/TypedOracleCompiler/Slice/BatchClauseOff.lean, said once for both.

WHY. `WrittenB` (OnBytes/TypedOracleCompiler/Slice/BatchClause.lean) has a protocol over ONE external string, and
its verifier stands under ONE outer root. The key's part and the proof's part have one stored table;
the entry's has two. The lemma beneath (`accepted_off_at`) is general in the kind of external
strings and in the list of outer roots. What `WrittenB` and its clause fix is: the type of the
strings; the list of one root; how the string is read off a trace under that root; and one step of
proof, that an opening which the reading keeps agrees with the string read. Here these four are
letters.

Main definitions.
 `ExtRd L`              a kind of external strings made of k strings of L's kind: `asm` makes the
                        external string of the strings under the roots; `side`, `place` say under
                        which root and where a position lies; two laws. `ExtRd.spec`: it as the
                        library's `ExtSpec`, with L's symbols.
 `ext1R L`, `ext2R L`   one string, two strings: their `spec` is the library's `oneExternalString`, `twoExternalStrings`, by
                        unfolding (`ext1R_spec`, `ext2R_spec`).
 `WrittenE W Ex`, `WrittenE.OK`   `WrittenB` and `WrittenB.OK` with Ex in the place of one string.
 `ExtRd.read`           the external string that a reading reads off a trace under a list of outer
                        roots.
 `WrittenE.verifier`, `WrittenE.verifierS`   the sibling's compiled verifiers under a list of outer
                        roots.
 `JointE`, `KeepsE`, `StLawsE`, `WrittenE.laneOff`, `SeedFirstE`, `badE`   as `Joint`, the condition
                        on openings, `StLawsOwn`, `WrittenB.laneOff`, `SeedFirst`, `batBadOff`.
                        `StLawsE` has one letter more, e: what the first query holds of an
                        instance's first part; the state is judged at (e x.1, x.2), the decision at
                        x itself.
Main theorems.
 `stLawsE_reply`, `jointE_reply`   round-by-round soundness, instance by instance, gives `StLawsE`
                        at e the identity, and `JointE`.
 `stLawsE_reply_e`, `jointE_reply_e`   for any e: from `ReplyLost` (OnBytes/Slice/ReplyState.lean)
                        at the early part (e x.1, x.2).
 `laneOffE_ok`, `badE_rare`, `badE_mono`, `badE_second`, `badE_stable`   as their models.
 `badE_lang`            OUTSIDE THE NAMED SET, UNDER `SeedFirstE`, AN ACCEPTED STRING WHOSE EXTERNAL
                        OPENINGS R KEEPS MEANS: the value read off the trace is not the instance's,
                        or the language holds of the instance and the external string read under the
                        outer roots. With `getD_mem_take`.

The proofs are the models' texts; two places are turned in `badE_lang`: what is read before a query
is what is read at the end, at EACH root below k (the sibling's `ours_cms` has it for the first two
outer roots: so k ≤ 2 is asked); and the step on openings goes by `rd_asm`.

Not claimed. NO PROTOCOL, NO INTERFACE, NO WIRING, NO STATE FUNCTION IS GIVEN: nothing speaks of a
file or of the program. That `WrittenB` is `WrittenE` at `ext1R`: by reading; no lemma says so, and
OnBytes/TypedOracleCompiler/Slice/BatchClause.lean and what stands over it are left as they lie. That `ReplyLost`
holds of any protocol at any early part. NO SOUNDNESS IS PROVED. What the heads of BatchClause.lean
and BatchClauseOff.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.BatchClauseOff

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (ReplyLost replySt replySt_start replySt_prover replySt_full replyLost_id_iff
  replySt_joint_times)
open scoped ENNReal

/-- A member of a list before the place k is a member of its first k members. -/
theorem getD_mem_take {α : Type} (d : α) : ∀ (l : List α) (i k : ℕ), i < l.length → i < k →
    l.getD i d ∈ l.take k
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ + 1, _, _ => List.mem_cons_self
  | _ :: l, i + 1, k + 1, h, h' =>
    List.mem_cons_of_mem _ (getD_mem_take d l i k (Nat.lt_of_succ_lt_succ h)
      (Nat.lt_of_succ_lt_succ h'))

/-! ## External strings that are made of strings of the interface's kind -/

section
variable {I X : Type}

/-- A kind of external strings that is made of k strings of L's kind, one under each of k outer
roots. `asm`: the external string, from the strings under the roots number 0, 1, ..; `side`,
`place`: under which root, and at which place there, a position lies. That `side p` is below k is
not asked: it follows from the two laws where L has two symbols. -/
structure ExtRd (L : BatchProtocolWithLeafBody I X) where
  /-- the external strings -/
  Str : Type
  /-- their positions -/
  Pos : Type
  /-- the symbol at a position -/
  rd : Str → Pos → L.Symbol
  /-- the number of outer roots -/
  k : ℕ
  /-- the external string, from the strings under the roots -/
  asm : (ℕ → Fin L.wordLength → L.Symbol) → Str
  /-- the number of the root under which a position lies -/
  side : Pos → ℕ
  /-- its place there -/
  place : Pos → Fin L.wordLength
  /-- what is read at a position is the symbol at its place in the string under its root -/
  rd_asm : ∀ f p, rd (asm f) p = f (side p) (place p)
  /-- the external string hangs on the first k strings alone -/
  asm_congr : ∀ f g, (∀ i, i < k → f i = g i) → asm f = asm g

/-- It as the library's kind of external strings. -/
@[reducible] def ExtRd.spec {L : BatchProtocolWithLeafBody I X} (Ex : ExtRd L) : ExtSpec := ⟨Ex.Str, Ex.Pos, L.Symbol, Ex.rd⟩

/-- One string under one root: its `spec` is the library's `oneExternalString`. -/
def ext1R (L : BatchProtocolWithLeafBody I X) : ExtRd L where
  Str := Fin L.wordLength → L.Symbol
  Pos := Fin L.wordLength
  rd := fun y p => y p
  k := 1
  asm := fun f => f 0
  side := fun _ => 0
  place := fun p => p
  rd_asm := fun _ _ => rfl
  asm_congr := fun _ _ h => h 0 Nat.one_pos

/-- Two strings under two roots: its `spec` is the library's `twoExternalStrings`. -/
def ext2R (L : BatchProtocolWithLeafBody I X) : ExtRd L where
  Str := (Fin L.wordLength → L.Symbol) × (Fin L.wordLength → L.Symbol)
  Pos := Fin L.wordLength ⊕ Fin L.wordLength
  rd := fun y p => Sum.elim y.1 y.2 p
  k := 2
  asm := fun f => (f 0, f 1)
  side := fun p => Sum.elim (fun _ => 0) (fun _ => 1) p
  place := fun p => Sum.elim id id p
  rd_asm := fun _ p => by cases p <;> rfl
  asm_congr := fun _ _ h => Prod.ext (h 0 (by decide)) (h 1 (by decide))

/-- The first is `oneExternalString`. -/
theorem ext1R_spec (L : BatchProtocolWithLeafBody I X) : (ext1R L).spec = oneExternalString L.wordLength L.Symbol := rfl

/-- The second is `twoExternalStrings`. -/
theorem ext2R_spec (L : BatchProtocolWithLeafBody I X) : (ext2R L).spec = twoExternalStrings L.wordLength L.Symbol := rfl

end

/-! ## A written batch protocol on such strings -/

section
variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A batch protocol on external strings of the kind Ex, with instances of L's type, as it is
written into the oracles of the interface L under the wiring W: `WrittenB`
(OnBytes/TypedOracleCompiler/Slice/BatchClause.lean) with Ex in the place of one string. -/
structure WrittenE (W : QueryLayout lam L) (Ex : ExtRd L) where
  /-- the tag under which its challenge queries are asked -/
  t : Tag
  /-- the protocol; it need not be one of L's -/
  Q : BatchInteractiveOracleProof X Ex.spec
  /-- its wiring -/
  wq : ProtocolQueryLayout lam W.K Q
  /-- how a symbol of its oracles is written into a leaf's body -/
  embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L
  /-- how such a body is read back at a position -/
  prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p)
  /-- how a plain part is written into a query -/
  embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)
  /-- how it is read back -/
  prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)

variable {W : QueryLayout lam L} {Ex : ExtRd L}

/-- What is asked of it: the clauses of `WrittenB.OK`; the last says that the wiring opens a
position under the root, and at the leaf, that Ex names. -/
structure WrittenE.OK (Z : WrittenE W Ex) : Prop where
  /-- a symbol that is written into a body is read back -/
  backS : ∀ p a, Z.prjS p (Z.embS p a) = some a
  /-- a plain part that is written into a query is read back -/
  backP : ∀ z, Z.prjP (Z.embP z) = some z
  /-- the wiring is lawful -/
  wire : Z.wq.OKG
  /-- the verifier is local -/
  loc : Z.Q.loc.IsLocal
  /-- the marks of shared and local rounds are coherent -/
  coh : Z.Q.ann.Coherent
  /-- where a later query holds the instance, the rounds before it are local -/
  late : ∀ n, L.late = some n → 0 < n ∧ RoundSplits.LocalTo n Z.Q.loc.shape Z.Q.ann
  /-- the external trees have the wiring's depth -/
  extDepth : Z.wq.ext.depth = W.depth
  /-- a position is opened under the root, and at the leaf, that Ex names -/
  ext : ∀ p, Z.wq.ext.which p = Ex.side p ∧ Z.wq.ext.leaf p = (Ex.place p).val

/-- The external string that a reading R reads off a trace under a list of outer roots. -/
def ExtRd.read (Ex : ExtRd L) (R : Reading L W.embE) (tr : Tc W) (cms : List (Dig lam)) : Ex.Str :=
  Ex.asm fun i => R.at W tr (cms.getD i default)

/-- The compiled verifier of one slot, with the outer roots cms and the instance x: the sibling's
`verifyB`, without the test of the strict format. -/
def WrittenE.verifier (Z : WrittenE W Ex) (cms : List (Dig lam)) (x : X) (π : OneProtocolProof lam Z.Q) :
    TypedOracleComputation lam W.K L Bool :=
  verifyB Z.t Z.Q Z.wq Z.embS Z.embP some W.embE (W.dReq Z.t) cms x π

/-- The same with the strict format: the sibling's `verifyOneProtocol`. -/
def WrittenE.verifierS (Z : WrittenE W Ex) (sMT sFS : ℕ) (cms : List (Dig lam)) (x : X)
    (π : OneProtocolProof lam Z.Q) : TypedOracleComputation lam W.K L Bool :=
  verifyOneProtocol sMT sFS Z.t Z.Q Z.wq Z.embS Z.embP some W.embE (W.dReq Z.t) cms x π

/-- The law on verifier's messages, for every external string and every vector of instances, at the
error counts ε: the library's `JointLaw`. -/
def JointE (Z : WrittenE W Ex) (ε : Err Z.Q.loc.shape)
    (State : Ex.Str → X → PTr Z.Q.loc.shape → Bool) : Prop :=
  ∀ y (x : Fin L.maxBatchSize → Option X),
    JointLaw L.maxBatchSize Z.Q.loc.shape Z.Q.ann ε fun j => (x j).map (State y)

/-- All external openings of a string are kept by R, each at its place. -/
def KeepsE (Z : WrittenE W Ex) (R : Reading L W.embE) (π : OneProtocolProof lam Z.Q) : Prop :=
  ∀ p op, π.ext p = some op → R.keeps (Ex.place p) op.sym op.salt

end

/-! ## Instances that are pairs: the second part is read off the trace -/

variable {I A Sd : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L} {Ex : ExtRd L}

/-- The laws of a state function for the language Lg: `StLawsOwn`
(OnBytes/TypedOracleCompiler/Slice/BatchClauseOff.lean) on strings of the kind Ex, with one letter more. e: what the
first query holds of an instance's first part. The state is judged at (e x.1, x.2): a false
statement starts there in state 0; a prover's message never changes 0 to 1; at the end state 0 there
means that the false instance x ITSELF is rejected. At e the identity: at the whole instance. -/
structure StLawsE (Z : WrittenE W Ex) (e : A → A)
    (State : Ex.Str → A × Sd → PTr Z.Q.loc.shape → Bool) (Lg : A × Sd → Ex.Str → Prop) : Prop where
  /-- a false statement starts in state 0 -/
  start : ∀ y x, ¬ Lg x y → State y (e x.1, x.2) (PTr.empty Z.Q.loc.shape) = false
  /-- a prover's message never changes 0 to 1 -/
  prover : ∀ y x (τ : AtP Z.Q.loc.shape) (m : τ.round.Msg),
    State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false
  /-- at the end state 0 means that the false instance itself is rejected -/
  full : ∀ y x (τ : Tr Z.Q.loc.shape), ¬ Lg x y → State y (e x.1, x.2) (.full τ) = false →
    Z.Q.loc.accept x y τ = false

/-- Round-by-round soundness, instance by instance, gives these laws, of the state function
`replySt` at the identity, with e the identity. -/
theorem stLawsE_reply (Z : WrittenE W Ex) (Lg : A × Sd → Ex.Str → Prop) (ε : Err Z.Q.loc.shape)
    (h : Z.Q.loc.Sound Lg ε) : StLawsE Z id (replySt Z.Q.loc ε id Lg) Lg where
  start := fun y x _ => replySt_start (replyLost_id_iff.2 h) y x
  prover := fun y x τ m h0 => replySt_prover y x τ m h0
  full := fun y x τ hL h0 => replySt_full y x τ hL h0

/-- The law on verifier's messages holds of that state function, at the errors ε with those of the
shared rounds multiplied by the number of slots. -/
theorem jointE_reply (Z : WrittenE W Ex) (Lg : A × Sd → Ex.Str → Prop) (ε : Err Z.Q.loc.shape) :
    JointE Z (Err.timesShared L.maxBatchSize Z.Q.ann ε) (replySt Z.Q.loc ε id Lg) :=
  fun y x => replySt_joint_times L.maxBatchSize Z.Q.ann y x

/-- The same for any e, for a caller whose first query erases: if for every early part (e x.1,
x.2) and every external string the prover has lost at the start towards "every instance with this
early part that the verifier accepts is in the language" (`ReplyLost`,
OnBytes/Slice/ReplyState.lean), the state function `replySt` at that early part has the laws at e.
The early part erases in the first part of an instance and keeps the second, which the lane reads
off the trace. -/
theorem stLawsE_reply_e (Z : WrittenE W Ex) (e : A → A) (Lg : A × Sd → Ex.Str → Prop)
    (ε : Err Z.Q.loc.shape) (h : ReplyLost Z.Q.loc ε (fun x => (e x.1, x.2)) Lg) :
    StLawsE Z e (replySt Z.Q.loc ε (fun x => (e x.1, x.2)) Lg) Lg where
  start := fun y _ _ => replySt_start h y _
  prover := fun y x τ m h0 => replySt_prover y x τ m h0
  full := fun y x τ hL h0 => replySt_full y x τ hL h0

/-- The law on verifier's messages holds of that state function too. -/
theorem jointE_reply_e (Z : WrittenE W Ex) (e : A → A) (Lg : A × Sd → Ex.Str → Prop)
    (ε : Err Z.Q.loc.shape) :
    JointE Z (Err.timesShared L.maxBatchSize Z.Q.ann ε) (replySt Z.Q.loc ε (fun x => (e x.1, x.2)) Lg) :=
  fun y x => replySt_joint_times L.maxBatchSize Z.Q.ann y x

section
variable (Z : WrittenE W Ex) (R : Reading L W.embE) (extS : Tc W → List (Dig lam) → Sd) (d : Sd)
  (ε : Err Z.Q.loc.shape) (State : Ex.Str → A × Sd → PTr Z.Q.loc.shape → Bool)

/-- The written batch protocol as a lane whose state takes the first part of the instance from the
query and the second part from the trace, by `extS`; judged at the external string as R reads it
under the outer roots. -/
def WrittenE.laneOff : Lane W :=
  laneOf W Z.t (plusQ Z.Q Sd) Z.wq.sh Z.prjS Z.prjP ε
    (fun (y : Ex.Str × Sd) x τ => State y.1 (x.1, y.2) τ)
    (fun o => (o.map Prod.fst).map fun a => (a, d))
    (fun tr cms => (Ex.read R tr cms, extS tr cms))

/-- That lane obeys the laws of a lane, whatever `extS` is. -/
theorem laneOffE_ok (hZ : Z.OK) (hJ : JointE Z ε State) : (Z.laneOff R extS d ε State).OK L.maxBatchSize :=
  lane_off_ok (Q := plusQ Z.Q Sd) (xout := fun o => o.map Prod.fst) hZ.wire.sh hJ

/-- At every challenge query under the protocol's tag whose chain begins with the outer roots cms
and with what the first query holds of x, what `extS` reads off the trace before the query is what
it reads off the whole trace. -/
def SeedFirstE (tr : Tc W) (cms : List (Dig lam)) (x : A × Sd) (π : OneProtocolProof lam Z.Q) : Prop :=
  ∀ pre (q : FbIn lam L Z.t) (a : FsAns lam W.K) post l cur, tr = pre ++ fbE Z.t q a :: post →
    Ours (⟨tr, Z.t, cms, some x, π.salt, π.rtreq, π.slot⟩ : Ctx W) pre q l cur →
    extS pre cms = extS tr cms

variable (ℓ : Lane W)

/-- The named set of bad traces: the two clashes, a lucky step of the written protocol's lane, a
lucky step of a second given lane ℓ, and one query with two answers. -/
def badE : Tc W → Prop := Bad3 (Z.laneOff R extS d ε State) ℓ

/-- Under the typed random oracles the named set is reached by an algorithm of at most t queries
with probability at most t εs + 2 (t + 1)² / 2 ^ lam. Asked: as `batBadOff_rare` asks. -/
theorem badE_rare (εs : ℝ≥0∞) (hb : Err.Below ε εs) (hJ : JointE Z ε State) (hZ : Z.OK)
    (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) {Nℓ : ℕ} (hNℓ : Nℓ = 2 ^ (W.dReq ℓ.t)) (hne : Z.t ≠ ℓ.t)
    (oℓ : ℓ.OK Nℓ) (bℓ : Err.Below ℓ.ε εs)
    (β : Type) (Alg : TypedOracleComputation lam W.K L β) (t : ℕ) (hA : Alg.QueryBound t) :
    pr Alg.withTrace.law {o | badE Z R extS d ε State ℓ o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  bad3_rare (ℓ₁ := Z.laneOff R extS d ε State) hne hN hNℓ (laneOffE_ok Z R extS d ε State hZ hJ) oℓ
    hb bℓ β Alg t hA

/-- The named set is closed under appending. -/
theorem badE_mono (tr tr' : Tc W) (h : badE Z R extS d ε State ℓ tr) :
    badE Z R extS d ε State ℓ (tr ++ tr') := bad3_mono tr tr' h

/-- Outside the named set, under `SeedFirstE`, an accepted string whose external openings R keeps
means: the value that `extS` reads off the trace is not the instance's, or the language holds of
the instance and the external string that R reads off the trace under the outer roots. Asked: there
are as many outer roots as Ex has, at most two; the first query holds (e x.1, d) of an instance x
and no later query holds the instance; the state function has the laws `StLawsE` at e; `Z.OK`. -/
theorem badE_lang (e : A → A) (Lg : A × Sd → Ex.Str → Prop) (hS : StLawsE Z e State Lg) (hZ : Z.OK)
    (hE : ∀ x, L.early x = (e x.1, d)) (hl : L.late = none) (tr : Tc W) (cms : List (Dig lam))
    (hlen : cms.length = Ex.k) (hk2 : Ex.k ≤ 2) (x : A × Sd) (π : OneProtocolProof lam Z.Q)
    (hB : ¬ badE Z R extS d ε State ℓ tr) (hk : KeepsE Z R π)
    (hrun : RunsIn tr (Z.verifier cms x π) true) (hsf : SeedFirstE Z extS tr cms x π) :
    extS tr cms ≠ x.2 ∨ Lg x (Ex.read R tr cms) := by
  obtain ⟨hM, hF, hS1, -, -⟩ := not_bad3 hB
  exact accepted_off_at Z.t Z.Q Z.wq Z.embS Z.embP some W.embE hZ.wire hZ.loc hZ.coh
    (Lg := Lg) State Z.prjS hZ.backS Z.prjP hZ.backP (fun o => o.map Prod.fst) d
    (fun tr cms => Ex.read R tr cms) extS ε hM hF hS1 cms x π (fun _ => e x.1)
    (fun i => by
      show (instX L (some x) i).map Prod.fst = some (e x.1)
      unfold instX
      rw [hl]
      show ((some x).map L.early).map Prod.fst = some (e x.1)
      rw [Option.map_some, hE]
      rfl)
    (fun n hn _ => hZ.late n hn)
    (fun y hL => hS.start y x hL)
    (fun y τ m _ h => hS.prover y _ τ m h)
    (fun y τ hL h => hS.full y x τ hL h) hrun
    (fun pre q a post l cur htr ho =>
      ⟨Ex.asm_congr _ _ fun i hi => R.at_before htr hM (ours_cms _ a ho _
          (getD_mem_take default cms i 2 (hlen ▸ hi) (lt_of_lt_of_le hi hk2))),
        hsf pre q a post l cur htr ho⟩)
    (fun p op hop h => by
      rw [hZ.extDepth, (hZ.ext p).1, (hZ.ext p).2] at h
      exact (Ex.rd_asm _ p).trans (R.law _ (Ex.place p) op.sym op.salt h (hk p op hop)))

/-- Outside the named set the second lane has had no lucky step, and each query has one answer. -/
theorem badE_second (tr : Tc W) (hB : ¬ badE Z R extS d ε State ℓ tr) :
    ¬ StepEvent ℓ.step tr ∧ OneAns tr :=
  ⟨(not_bad3 hB).2.2.2.1, (not_bad3 hB).2.2.2.2⟩

/-- If the longer trace is outside the named set, what is read off under a root that was announced
in the shorter one does not change. -/
theorem badE_stable (tr tr' : Tc W) (cm : Dig lam)
    (hB : ¬ badE Z R extS d ε State ℓ (tr ++ tr')) (hann : Announced W tr cm) :
    R.at W tr cm = R.at W (tr ++ tr') cm :=
  R.at_stable (not_bad3 hB).1 (List.prefix_append _ _) (occursIn_of_announced hann)

end

end TypedOracleCompiler.Slice
