-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Inv.lean: WHAT HOLDS ALONG THE CHAIN OF A COMPILED RUN AS A TOKEN PROGRAM: the
invariants and the counts from a round on. DEFINITIONS, with small members.

General definitions. This file states no goal of the release. The token programs are a device of one
step of a proof of index privacy and stand in no statement on the scheme.

The chain (chainT, Johnson/TokenSide/Chain.lean) reveals nothing. At its end lists of tokens are to
be revealed: the first salt with all tokens that the chain has made; the tokens of the opened
leaves. The rules ask that the tail and the further tokens of each evaluation that is charged to a
token of such a list are in the list or shown. So the proof carries a list V, "the chain's tokens so
far" (the first salt, then what was made), which is closed in that sense:

  CI d t salt sFS V ph   The invariant before a round, in the phase ph. The first salt and the
       phase's tokens are in V; each token of V exists, and the tail and the further tokens of each
       evaluation that is charged to it are in V (Deps); and the phase's tokens can be charged where
       the coming rounds charge them (PhOK).
  PhOK   first: the first salt can be charged under every Fiat-Shamir name of the tag (Live): so far
       it stands in points of leaves alone. loc, aft: nothing holds the chaining value. shr: nothing
       holds the shared chaining value, and the slot value, which the request tree's leaf holds, can
       still be charged under every Fiat-Shamir name.
  oName t n   The name under which try number n is written: fb t, then fbw t 0, fbw t 1, ..
  ChainEnd n d' salt V z   What holds at the end, if the chain has the value z: V with z's tokens is
       closed in the same sense; z's tokens are numbers from n on; each kept tree's tokens can be
       shown together with the first salt and are numbers from n on (KeptOK).
  Cls n Vs e   Of an evaluation that the chain has added: either it is a leaf, charged to a token
       from n on that is not in Vs; or it is no leaf, and is charged to a token of Vs. With Vs the
       chain's tokens: THE EVALUATIONS THAT ARE CHARGED TO THE CHAIN's TOKENS ARE THOSE THAT ARE NO
       LEAVES.
  KeptAt d st s i kept   Each kept tree has LeafAt (Johnson/TokenRules/ReleaseSpec.lean) at the
       start of its round and component: for each leaf just one evaluation, at the leaf's input,
       with the leaf's digest.

The counts from round number i on, in the phase ph (mChain): those of a whole run (mRun,
Johnson/TokenSide/Counts.lean), but that the joining round's evaluations are counted only as long as
the chains have not joined (jOf).

-/
import Johnson.TokenRel.Kit
import Johnson.TokenSide.Counts

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRel
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRules
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1 val_of_prefix val_afterFresh)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Names, phases -/

/-- the name under which try number n of a Fiat-Shamir query is written -/
def oName (t : Tag) : ℕ → OracleName
  | 0 => .fb t
  | n + 1 => .fbw t n

/-- The token u has n bits and can be charged under every Fiat-Shamir name of the tag t. -/
structure Live (d : DSt (typedOracleFamily lam K L)) (t : Tag) (u : Tok) (n : ℕ) : Prop where
  free : ∀ m, FreeAt d (oName t m) u
  len : Len d u n

/-- the tokens of a phase that a coming round may put into a point -/
def phToks : PhT → List Tok
  | .first => []
  | .loc tk => [tk]
  | .shr tk0 c => [tk0, c]
  | .aft tk _ => [tk]

/-- the first salt, or a token of the phase -/
def PhTok (salt : Tok) (ph : PhT) (u : Tok) : Prop := u = salt ∨ u ∈ phToks ph

/-- The phase's tokens can be charged where the coming rounds charge them. -/
def PhOK (d : DSt (typedOracleFamily lam K L)) (t : Tag) (salt : Tok) (sFS : ℕ) : PhT → Prop
  | .first => Live d t salt sFS
  | .loc tk => tk ≠ salt ∧ Untouched d tk ∧ Len d tk lam
  | .shr tk0 c => tk0 ≠ salt ∧ c ≠ salt ∧ c ≠ tk0 ∧ Untouched d tk0 ∧ Len d tk0 lam ∧ Live d t c lam
  | .aft tk _ => tk ≠ salt ∧ Untouched d tk ∧ Len d tk lam

/-- **The invariant before a round.** -/
structure CI (d : DSt (typedOracleFamily lam K L)) (t : Tag) (salt : Tok) (sFS : ℕ) (V : List Tok) (ph : PhT) :
    Prop where
  salt_mem : salt ∈ V
  ph_mem : ∀ u ∈ phToks ph, u ∈ V
  deps : ∀ u ∈ V, u < d.vals.length ∧ Deps d u V
  ph_ok : PhOK d t salt sFS ph

/-! ## The end of the chain -/

/-- Each kept tree's tokens can be shown together with the first salt, and are numbers from n on. -/
def KeptOK (n : ℕ) (d : DSt (typedOracleFamily lam K L)) (salt : Tok) : (s : Shape) → KeptT lam L s → Prop
  | [], _ => True
  | _ :: s, (kp, ks) =>
      (∀ T ∈ kp.2.1 ++ kp.2.2, TreeOKT d [salt] T ∧ TreeNewT n T) ∧ KeptOK n d salt s ks

/-- **What holds at the end of the chain.** -/
structure ChainEnd (n : ℕ) (d : DSt (typedOracleFamily lam K L)) (salt : Tok) (V : List Tok) {s : Shape}
    (z : OutT lam L s) : Prop where
  deps : ∀ u ∈ V ++ z.toks, u < d.vals.length ∧ Deps d u (V ++ z.toks)
  new : ∀ u ∈ z.toks, n ≤ u
  kept : KeptOK n d salt s z.kept

/-! ## The counts from a round on -/

/-- 1 if the chains can still join in the rounds s, else 0 -/
def jOf : PhT → (s : Shape) → RoundSplits s → ℕ
  | .first, s, A => joinsT s A
  | .loc _, s, A => joinsT s A
  | _, _, _ => 0

/-- marked evaluations of the rounds s, the first of which has the number i, from the phase ph -/
def mChain (t : Tag) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (cap : ℕ → ℕ) (dq i : ℕ)
    (ph : PhT) : OracleName → ℕ
  | .leaf => cLeaves s A W
  | .rleaf => jOf ph s A
  | .rnode => jOf ph s A * dq
  | .fb t' => if t' = t then s.length else 0
  | .fbw t' k => if t' = t then cTry k cap s A W i else 0
  | .g t' => if t' = t then jOf ph s A else 0
  | _ => 0

/-- From the first round and the first phase these are the counts of a run. -/
theorem mChain_first (t : Tag) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (cap : ℕ → ℕ)
    (dq : ℕ) : mChain t s A W cap dq 0 .first = mRun t s A W cap dq := by
  funext o
  cases o <;> rfl

/-- the leaves of trees of the given depths -/
def nLv (ds : List ℕ) : ℕ := (ds.map fun d => 2 ^ d).sum

/-! ## For the rule of release -/

/-- See the head. -/
def Cls (n : ℕ) (Vs : List Tok) (e : Ev (typedOracleFamily lam K L)) : Prop :=
  (e.o = OracleName.leaf ∧ n ≤ e.charged ∧ e.charged ∉ Vs) ∨ (e.o ≠ OracleName.leaf ∧ e.charged ∈ Vs)

/-- See the head. st i b: the start of a leaf's salt in round number i, in a tree over the slot's
component (b = true) or over the shared one. i: the number of the first of the rounds s. -/
def KeptAt (d : DSt (typedOracleFamily lam K L)) (st : ℕ → Bool → Bits) :
    (s : Shape) → ℕ → KeptT lam L s → Prop
  | [], _, _ => True
  | _ :: s, i, (kp, ks) =>
      (∀ T ∈ kp.2.1, LeafAt d T (st i false)) ∧ (∀ T ∈ kp.2.2, LeafAt d T (st i true)) ∧
        KeptAt d st s (i + 1) ks

/-! ## Members -/

/-- The invariant can be met: just after the first salt has been drawn, with V the salt alone. -/
theorem ci_start {Rl : Rules (typedOracleFamily lam K L)} {d : DSt (typedOracleFamily lam K L)} (hd : TidyO Rl d) (t : Tag)
    {sFS : ℕ} (u : Fin sFS → Bool) :
    CI (afterFresh d (List.ofFn u)) t d.vals.length sFS [d.vals.length] .first where
  salt_mem := List.mem_singleton.mpr rfl
  ph_mem := fun _ h => absurd h List.not_mem_nil
  deps := fun v hv => by
    rw [List.mem_singleton.mp hv]
    exact ⟨(Untouched.of_fresh hd _).lt, (Untouched.of_fresh hd _).deps _⟩
  ph_ok := ⟨fun _ => (Untouched.of_fresh hd _).freeAt _, Len.of_fresh d u⟩

/-- The invariant can fail: a first salt that does not exist. -/
theorem not_ci_init (t : Tag) (salt sFS : ℕ) (V : List Tok) (ph : PhT) :
    ¬ CI (DSt.init (typedOracleFamily lam K L)) t salt sFS V ph :=
  fun h => absurd (h.deps salt h.salt_mem).1 (Nat.not_lt_zero _)


end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.ci_start
