-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBase.lean: the base case, that is the last step, of a proximity test for a linear code, at
radii beyond unique decoding, with a linear constraint on the encoded message: an interactive oracle
reduction of two rounds to the trivial statement.

Definitions and statements; the proofs are in Cb/Ld/LdBaseProofs.lean. The mathematics on plain
words is in Cb/Ld/LdBaseWords.lean.
`LdCode E P` (Cb/Ld/LdRel.lean) has an encoder from (message, randomness) to native words, and a
transformation T from native words to long words, at the long positions P. `C.Laws` says that both
are linear, that the encoder is injective, and that T reads, for a long position x, the native
positions in `C.src x` only. Three conditions on C are defined there too. `C.MCAat e bad`: mutual
correlated agreement on lines under the transformation, as a count of exceptional θ: for any two
native words f₀, f₁ there are at most bad values θ for which, on some set that misses at most e long
positions, the line T f₀ + θ T f₁ is on the code while T f₀ and T f₁ are not both. `C.ListAt e L`:
every native word has at most L codewords within e long positions, counted as pairs (message,
randomness). `C.Transparent`: some bk computes, from a long position and the long symbol of a
codeword there, the native symbols that were read for it (`C.TranspBy bk`).

The block starts from the main relation of Cb/Ld/LdRel.lean, for any code C read under a
transformation (`Cb.LdCode`) and any linear form with a state sl: the explicit part is (target,
state); the implicit part is a native word f, which is read as the long word T f; a witness is
(message, randomness). In the relaxation at the radius e (`ConL`, Cb/Ld/LdRel.lean) T f differs from
the transform of the witness's encoding at no more than e long positions, and the form at the
message is the target.
This block is not succinct: the prover's last message is as long as message and randomness.
Rounds (what the prover sends; what the verifier sends):
  1: an oracle g (a native word of C, blinded) and a scalar u; μ in E.
  2: an answer ms = (message, randomness), in full, no oracle; Q, a list of t long positions. ρ =
    (μ, Q) stands for the verifier's two messages.
The verifier reads T f at the positions of Q (t queries), reads g at the native positions that T
needs for the positions of Q, and accepts if the form at the message of ms is u + μ·target and T
(encoding of ms) = T g + μ T f at every position of Q (`LdwAccept`).
The honest prover draws h = (message, randomness) uniform (its only coins), sends g = the encoding
of h, u = the form at h, and ms = h + μ w, w its witness. Nothing is withheld.
The extractor (`ldBaseExt d`) reads T f, T g, μ and ms; not the explicit part, not u, not Q. At
radii not below half the distance it cannot be a function of f and g alone (the head of
Ior/KnowCollGood.lean; under which hypotheses: see "Limits:"), so the record of the block is
`IOR.GoodT`. `IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one
reduction, with its honest side, between two joints, at given numbers; among its clauses:
completeness between the honest relations, outside sets of verifier randomness whose probabilities
further clauses bound by the numbers; round-by-round knowledge soundness (`Know`) between the
relaxed relations, on the input joint's set of statements, with a given extractor, at the numbers'
list of errors; and one on honest-verifier zero knowledge.
`tie`: a native position p of g gives away one long position of the input (data: see `given`,
Ior/Honest.lean): a position of Q for which p is read, if there is one, else cov p (cov is a
parameter: where to look up a native position that the verifier does not read; it matters for
further reads only).

Main names (each statement also takes, as an instance argument, that there is a long position):
  `Spec.ldBase_within`: if `C.MCAat e bad` and `(C.il Bool).ListAt e L2`, the named bad sets
    (`ldBaseBad`), round by round, are within the errors ( bad + L2 , (N - e - 1)^t ), counts of
    values of μ and of Q; bad bounds the count of mutual correlated agreement of C at the radius e,
    L2 bounds the list size at e of C with two interleaved rows, N = the number of long positions.
    The bad values of μ do not read ms.
  `Spec.ldBase_clean`: the backward step (see its doc comment).
  `Spec.ldBase_exact`: under `C.Laws`, if T is transparent on the code, the named simulator
    (`ldBaseSim`) is exact at every ρ, for every set of further native positions of g that are read
    for their looked-up long position.
  `Spec.ldBase_reads`: at most t long positions of the input; at most b t native positions of g if T
    reads at most b for one; the simulator is given at most t + |further positions| long symbols of
    the input.
  `Spec.ldBase_good`: under `C.Laws`, `C.Transparent`, e < d, `C.MCAat e bad` and
    `(C.il Bool).ListAt e L2`, `IOR.GoodT`: strings (`GoodT.point`: `Shape.IsPoint`,
    Iop/Shape.lean), local (`GoodT.isLocal`: `IOR.IsLocal`, Ior/Ior.lean), perfectly complete,
    knowledge sound round by round with the named extractor and these errors, exactly
    honest-verifier zero knowledge (`GoodT.exact`: `Honest.Exact`, Ior/Honest.lean); both
    probabilities of withheld sets are 0.
  `Spec.ldBase_literal`: under the hypotheses of `Spec.ldBase_good` but for `C.Transparent`, the
    same knowledge soundness in the field's form (`HasRbrKnowledge`, Ior/Know.lean).

Why the range of the radius: The paper that this protocol builds on (lean/CREDITS.md) states the
block for every distance below the minimum distance of the transformed code. Here d is only the
threshold of the corrector, and what is asked is e < d: with d the distance of C (`C.Dist d`) that
is the text's range, and then the extracted witness is the only one that agrees on the extractor's
agreement set (`Spec.lde_unique`, Cb/Gen/CodeEraseLd.lean); for a larger d the statement still holds
(the corrector then picks one of those that agree). So Lean's range is wider, not other.

Limits: this file says nothing on how large bad and L2 are, nor that the errors are below the
numbers of values (|E|, N^t). Without a further read's looked-up symbol of the input, one more
symbol of g is not simulated. It says nothing on running times.
That no extractor which sees only the implicit part and the oracles reaches these errors, where they
say something, at radii not below half the distance is, under its hypotheses, a theorem of
Cb/Ld/LdBaseTest.lean (`blind_fails`), with an instance there at 2 e = d (`instance2_blind`);
instances below a third of the distance, under the hypotheses of `Spec.ldBase_good_third`, are in
Cb/Ld/LdBaseCode.lean.
The condition on the data, as an instance argument: there is at least one long position. t = 0 is
allowed (the text asks t ≥ 1): then there is one list Q, and the second error, 1, says nothing.
Declared differences to that text, beside those of Cb/Ld/LdRel.lean (a field for ring, module and
challenge set, so that the chance that two different polynomials of degree at most one agree is one
value of μ). (1) Errors are counts; (N - e - 1)^t of N^t lists is at most (1 - δ)^t for e = ⌊δ N⌋.
(2) Zero knowledge is in the exact form of Ior/Honest.lean: the simulator is given ρ and the
input's symbols at the t positions of Q (with further reads: at most t + |further positions| long
symbols of the input: `Spec.ldBase_reads`), and is exact at every ρ; the text's simulator draws ρ
itself, uniformly, and asks the same t positions. Further reads are more than the text asks. (3) The
witness of the relaxation does not hold the corrected word (`Spec.ld_conLit_iff`).
The block follows a construction of the paper that this protocol builds on (lean/CREDITS.md).

Terms: lean/GLOSSARY.md: long position, native position, radius, agreement, list, not below half the
distance, further reads, withheld, blinded, block, explicit part, implicit part, trivial statement,
literal form (here: the field's form), joint, reduction, honest side, round-by-round knowledge
soundness.
-/
import Cb.Ld.LdRelKit
import Cb.Gen.CodeEraseLd
import Cb.Ld.LdBaseWords
import Ior.KnowCollGood
import Blocks.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop

section
variable {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) {St : Type}
  (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P)

omit [Fintype E] [Fintype P] [Nonempty P] in
/-- encode, then transform -/
def ldCw : C.MR → P → C.Aa → E := fun w => C.T (C.enc w.1 w.2)

variable {C} in
omit [Fintype E] [Fintype P] [Nonempty P] in
/-- the form of the statement x, on (message, randomness): it reads the message -/
def ldForm (x : E × St) : C.MR → E := fun w => ∑ j, sl x.2 j * w.1 j

/-- the two rounds -/
abbrev ldBaseShape : Shape := [C.sendRound E E 0, plainRound C.MR (Fin t → P) 0]

def ldBasePoint : (ldBaseShape C t).IsPoint := (C.sendPoint E E 0, plainPoint _ _ _, ())

omit [Field E] [Fintype E] [Fintype P] [Nonempty P] in
open Classical in
/-- Where a native position is looked up: at a position of Q for which it is read, if there is one;
else at cov p. -/
def ldPick {t : ℕ} (Q : Fin t → P) (p : C.NP) : P :=
  if h : ∃ i, p ∈ C.src (Q i) then Q h.choose else cov p

open Classical in
/-- The base case. -/
def ldBaseIOR : IOR (E × St) C.ext Unit extNone where
  shape := ldBaseShape C t
  blinded _ := true
  extReads ρ := Finset.univ.image ρ.2.1
  reads ρ := ((Finset.univ.image ρ.2.1).biUnion C.src).image Sum.inl
  out x y τ := if LdwAccept (ldCw C) (ldForm sl x) x.1 (C.T y) (C.T τ.1.1)
        τ.1.2 τ.2.1 τ.2.2.1.2 τ.2.2.2.1 then some ()
    else none
  imp _ _ := ()
  srcE _ _ := ∅
  srcO _ _ := ∅
  tie ρ p := Sum.elim (fun p => {ldPick C cov ρ.2.1 p}) (fun _ => ∅) p

/-- The honest side. Coins: h, uniform. Nothing is withheld. -/
def ldBaseHon : (ldBaseIOR C sl t cov).Honest C.N.Wit Unit where
  Coin := C.MR
  strat w x h :=
    ((C.enc h.1 h.2, ldForm sl x h), fun μ => (((), h + μ • (w : C.MR)), fun _ => ((), ())))
  Bad := ∅
  Hid _ _ := ∅

variable {C t} in
/-- the transcript with the verifier's messages ρ, the scalar u, the answer ms and the native word g
-/
def ldBaseTr (ρ : Rho (ldBaseShape C t)) (u : E) (ms : C.MR) (g : C.Word) : Tr (ldBaseShape C t) :=
  ((g, u), ρ.1, ((), ms), ρ.2.1, ())

/-- The simulator, for a way bk to compute native symbols of codewords from long ones: ms uniform; u
:= the form at ms - μ·target; the native symbol of g at p := that of the encoding of ms - μ·(that of
the input, computed from the long symbol given at the looked-up position). It outputs what this
transcript shows. -/
def ldBaseSim (bk : P → (C.Aa → E) → C.Word) :
    IOR.Honest.Sim (ldBaseIOR C sl t cov) := fun x ρ T a =>
  (unif C.MR).map fun ms =>
    some ((ldBaseIOR C sl t cov).view T
        (ldBaseTr ρ (ldForm sl x ms - ρ.1 * x.1) ms fun p =>
          C.enc ms.1 ms.2 p -
            ρ.1 • bk (ldPick C cov ρ.2.1 p) ((a (ldPick C cov ρ.2.1 p)).getD 0) p))

/-- The extractor: the corrector of erasures with the threshold d, on the input word T f and the
largest agreement set of the line T g + μ T f with the answer ms. -/
def ldBaseExt (d : ℕ) :
    (E × St) × C.ext.Str → Tr (ldBaseShape C t) → Unit → C.N.Wit :=
  fun a τ _ => C.eraseD d (C.agr (C.T τ.1.1 + τ.2.1 • C.T a.2) τ.2.2.1.2) (C.T a.2)

/-- The bad values of μ and of Q, for the statement a, at the radius e. -/
def ldBaseBad (e : ℕ) (a : (E × St) × C.ext.Str) : BadFam (ldBaseShape C t) :=
  (fun m => {μ | LdwBad1 (ldCw C) e (ldForm sl a.1) a.1.1 (C.T a.2) (C.T m.1) m.2 μ},
   fun m μ => (fun m' => {Q | LdwBad2 (ldCw C) e (C.T a.2) (C.T m.1) μ m'.2 Q}, fun _ _ => ()))

/-- the errors, as counts -/
def ldBaseErr (e bad L2 : ℕ) : Err (ldBaseShape C t) :=
  (bad + L2, ((Fintype.card P - e - 1) ^ t, ()))

/-- the budget of further reads: native positions of g that are read for the long position at which
they are looked up -/
def ldBaseBud : Rho (ldBaseShape C t) → Finset (OPos (ldBaseShape C t)) → Prop := fun ρ T =>
  ∀ p : C.NP, Sum.inl p ∈ T → p ∈ C.src (ldPick C cov ρ.2.1 p)

def ldBaseNums (e bad L2 : ℕ) : IOR.Nums Unit (ldBaseIOR C sl t cov) :=
  ⟨ldBaseErr C t e bad L2, 0, 0, ldBaseBud C t cov, fun _ => ∅⟩

end

namespace Spec
open IOR

/-- If `C.MCAat e bad`, `(C.il Bool).ListAt e L2` and there is a long position, the bad sets are
within the errors, round by round. -/
def ldBase_within : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (St : Type)
      (sl : Slf E St C.J) (t e bad L2 : ℕ),
    C.MCAat e bad → (C.il Bool).ListAt e L2 →
    ∀ a, (ldBaseBad C sl t e a).Within (ldBaseErr C t e bad L2)

/-- The backward step. Under `C.Laws` and e < d, and if there is a long position: no bad value, and
the verifier accepts: then the extractor's result is a witness in the relaxation at the radius e. -/
def ldBase_clean : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (St : Type)
      (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (d e : ℕ),
    C.Laws → e < d →
    ∀ a (τ : Tr (ldBaseShape C t)), (ldBaseBad C sl t e a).Clean τ →
      (ldBaseIOR C sl t cov).out a.1 a.2 τ = some () →
      (C.rels sl e fun _ => ()).relR a (ldBaseExt C t d a τ ())

/-- Honest-verifier zero knowledge, with the simulator named. -/
def ldBase_exact : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (St : Type)
      (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (e : ℕ) (bk : P → (C.Aa → E) → C.Word),
    C.Laws → C.TranspBy bk →
    (ldBaseHon C sl t cov).ExactWith
      (C.rels sl e fun _ => ()).rel (ldBaseBud C t cov) (ldBaseSim C sl t cov bk)

/-- How much is read. -/
def ldBase_reads : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P)
      (St : Type) (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (b : ℕ)
      (ρ : Rho (ldBaseShape C t)) (T : Finset (OPos (ldBaseShape C t))),
    ((ldBaseIOR C sl t cov).extReads ρ).card ≤ t ∧
    (C.LocalLE b → ((ldBaseIOR C sl t cov).reads ρ).card ≤ t * b) ∧
    ((ldBaseIOR C sl t cov).given ρ T).card ≤ t + T.card

/-- Under the hypotheses below, the base case leads from the main relation to the trivial statement
(`GoodT`). -/
def ldBase_good : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (St : Type)
      (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (d e bad L2 : ℕ),
    C.Laws → C.Transparent → e < d → C.MCAat e bad → (C.il Bool).ListAt e L2 →
    GoodT (ldBaseIOR C sl t cov) (ldBaseHon C sl t cov) (C.rels sl e fun _ => ()) trivRels
      (ldBaseExt C t d) (ldBaseNums C sl t cov e bad L2)

/-- Knowledge soundness in the field's form (a knowledge state function, an extractor for each
round, a bound for each round). -/
def ldBase_literal : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (St : Type)
      (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (d e bad L2 : ℕ),
    C.Laws → e < d → C.MCAat e bad → (C.il Bool).ListAt e L2 →
    (ldBaseIOR C sl t cov).red.HasRbrKnowledge (fun _ => True)
      (onLeft (WB := Unit) (C.rels sl e fun _ => ()).relR) (onRight (WA := C.N.Wit) trivRels.relR)
      (fun a => RExt.ofFull (ldBaseShape C t) (ldBaseExt C t d a)) (ldBaseErr C t e bad L2)

end Spec
end Cb
