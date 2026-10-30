-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Joined/Silent.lean: a round that the verifier does not look at costs no error.

A second form of the compiler's verifier side, beside the library's own. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Of a file with three joined hash chains `Chains.Seams` (Compile/Joined/Types.lean) says that the
front, the joining round and the seam send a plain part alone. A description of such a file may lay
them as rounds that none of its steps reads. To lay such a round between two reductions one needs a
reduction of which it is the only round, and that reduction's clause of knowledge soundness
(`Reduction.Know`, Ior/Know.lean).

Main names:
  `silentAt A r`: the reduction whose one round is r. It hands its statement on and never rejects.
  `silentAt_know`: it has `Know` at any one relation on both sides, with the identity as the
    extractor and the error 0. Nothing is asked of r: not that it has one verifier message alone.
  `know_seq_silent`, `know_silent_seq`: a reduction with its clause, and such a round behind it or
    before it: the same relations, the same errors, and a 0 at the round.
  `extSeq_silent_seq`, `extSeq_seq_silent`: the extractors of these two, worked out.
  `silent X E T t`: the same as an interactive oracle reduction (`IOR`, Ior/Ior.lean), at the round
    `plainRound T t`, which has no position; `silent_isLocal`, `silent_red_out`, `silent_know`.
Other files of the library use `silentAt` and `silentAt_know` alone
(OnBytes/TypedOracleCompiler/Joined/MidLinks.lean).

Limits: the clause for batches (`IOR.KnowB`, Ior/BatchSeq.lean) is not stated here; from `Know` to
its like for reductions: CompileK/Joined/ExtractKnow.lean. What the plain part of such a round holds
is tied to nothing: the reduction does not read it. A description that lays the front and the
joining round as silent rounds never reads their plain parts: its verifier's yes does not depend on
what stands there, so `Compile.Joined.Desc.Answers` need not hold of it; the record's answers can
reach it through the instance alone. Nothing on an honest prover.

Terms: lean/GLOSSARY.md.

-/
import Ior.Know
import Ior.Ior
import Compile.Joined.Types

set_option autoImplicit false

namespace CompileK.Joined
open Iop Compile.Joined

variable {A B WA WB : Type}

/-! ## As a reduction, at any round -/

/-- The reduction whose one round is r: it hands its statement on and never rejects. -/
@[reducible] def silentAt (A : Type) (r : Round) : Reduction A A where
  shape := [r]
  out a _ := some a

/-- **A round that is not looked at costs no error.** -/
theorem silentAt_know (r : Round) (on : A → Prop) (R : A → WA → Prop) :
    (silentAt A r).Know on R R (fun _ _ w => w) (0, ()) :=
  fun _ _ => Doomed.of_forall _ _ fun _ _ _ hb hw => Option.some.inj hb ▸ hw

/-- such a round behind a reduction -/
theorem know_seq_silent {K : Reduction A B} {on : A → Prop} {RA : A → WA → Prop}
    {RB : B → WB → Prop} {e : A → Tr K.shape → WB → WA} {ε : Err K.shape}
    (h : K.Know on RA RB e ε) (r : Round) (d : WA) :
    (K.seq (silentAt B r)).Know on RA RB
      (Reduction.extSeq K (silentAt B r) e (fun _ _ w => w) d) (Err.app ε (0, ())) :=
  Reduction.Know.seq h (silentAt_know r (fun _ => True) RB) (fun _ _ _ _ _ => trivial) d

/-- such a round before a reduction -/
theorem know_silent_seq {K : Reduction A B} {on : A → Prop} {RA : A → WA → Prop}
    {RB : B → WB → Prop} {e : A → Tr K.shape → WB → WA} {ε : Err K.shape}
    (h : K.Know on RA RB e ε) (r : Round) (d : WA) :
    ((silentAt A r).seq K).Know on RA RB
      (Reduction.extSeq (silentAt A r) K (fun _ _ w => w) e d) ((0, ε) : Err (r :: K.shape)) :=
  Reduction.Know.seq (silentAt_know r on RA) h (fun _ _ _ ha hb => Option.some.inj hb ▸ ha) d

/-- the extractor with the round in front: that of K, on the rounds behind the first -/
theorem extSeq_silent_seq (K : Reduction A B) (e : A → Tr K.shape → WB → WA) (r : Round) (d : WA)
    (a : A) (τ : Tr (r :: K.shape)) (w : WB) :
    Reduction.extSeq (silentAt A r) K (fun _ _ w => w) e d a τ w = e a τ.2.2 w := rfl

/-- the extractor with the round behind: that of K, on K's rounds, where K's verifier does not
reject -/
theorem extSeq_seq_silent (K : Reduction A B) (e : A → Tr K.shape → WB → WA) (r : Round) (d : WA)
    (a : A) (τ : Tr (K.shape ++ [r])) (w : WB) {b : B} (hb : K.out a (Tr.fst τ) = some b) :
    Reduction.extSeq K (silentAt B r) e (fun _ _ w => w) d a τ w = e a (Tr.fst τ) w := by
  unfold Reduction.extSeq
  rw [hb]

/-! ## As an interactive oracle reduction, at a round that sends a plain part alone -/

/-- The interactive oracle reduction whose one round sends a plain part in T: both parts of the
statement are handed on, nothing is read, and it never rejects. -/
def silent (X : Type) (E : ExtSpec) (T : Type) (t : T) : IOR X E X E where
  shape := [plainRound T t]
  blinded := fun _ => false
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun x _ _ => some x
  imp := fun y _ => y
  srcE := fun _ q => {q}
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

theorem silent_isLocal (X : Type) (E : ExtSpec) (T : Type) (t : T) : (silent X E T t).IsLocal where
  out := fun _ _ _ _ _ _ _ _ _ => rfl
  imp := fun _ _ _ _ q _ _ h _ => h q (Finset.mem_singleton_self q)

/-- as a reduction between statements it is `silentAt` -/
theorem silent_red_out (X : Type) (E : ExtSpec) (T : Type) (t : T) (a : X × E.Str)
    (τ : Tr [plainRound T t]) : (silent X E T t).red.out a τ = some a := rfl

theorem silent_know (X : Type) (E : ExtSpec) (T : Type) (t : T) (on : X × E.Str → Prop)
    (R : X × E.Str → WA → Prop) :
    (silent X E T t).red.Know on R R (fun _ _ w => w) (0, ()) :=
  fun a _ => Doomed.of_forall _ _ fun τ b w hb hw => by
    have e : a = b := Option.some.inj ((silent_red_out X E T t a τ).symm.trans hb)
    subst e
    exact hw

end CompileK.Joined
