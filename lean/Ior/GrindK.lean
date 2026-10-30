-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/GrindK.lean: rounds with a test (proof of work, "grinding") keep round-by-round knowledge
soundness of a batch IOP, with the same witness map on the same symbols.

Statements and proofs.
A batch IOP (`BatchInteractiveOracleProof`, Iop/Batch.lean) is one IOP, for the local transcript of a slot, with an
annotation of its shape (`RoundSplits`): which verifier messages the slots share, and how each prover
message splits into a shared part and a slot's part. A slot is one of the N places of a batch, each
with one instance or empty, with its own local transcript. `SndBK` (Ior/Batch.lean) is (Snd-B) with
a witness: round-by-round knowledge soundness for the instances of a batch, with a witness map that
reads a witness off the instance and the prover's oracles.
The step on batch IOPs is that of Iop/BatchGrind.lean (`Q.grind W g`; W is the type of nonces, with
one fixed element (`[Inhabited W]`), g a number of test bits for each round): in a round with b test
bits the prover's message ends in a nonce, the verifier's message holds b further uniform bits, and
the verifier accepts only if all test bits of all rounds are 0. Iop/BatchGrindProofs.lean shows that
(Snd-B), in its late form (`BatchInteractiveOracleProof.SndBL`, Iop/Batch.lean), is kept with the same counts: e of
|C| values become e of |C| 2^b values.

Main names:
  `Orcs.strip g o`: the oracles of the old shape.
  `Spec.sndBK_grind`: (Snd-B) with a witness is kept: same relation, witness map wit ∘ Orcs.strip,
    the same counts on the new shape (`Err.grind g ε`). No hypothesis on g, N, ε.

Why `Spec.guard_grind`: `SndBK` is the late form of (Snd-B) of the guarded protocol for the empty
language; `Iop.BatchGrind.sndBL_grind` applies to the guarded protocol; `guard_grind` says what the
guarded protocol with tests is.

Limits: the witness map after the step sees, by its type, the instance and the prover's oracles: no
nonce (a nonce is a plain part), no test bit, no verifier message.
What the errors mean: as a probability the error of round i is e_i / (|C_i| 2^b_i). It is small
because a prover of the interactive protocol, honest or not, passes a test with chance 2^-b only;
what that is worth is a matter of the compiler's theorem, in which every try is a query (the heads
of Iop/Grind.lean and Compile/Batch/SpecGrind.lean).
This file says nothing on the honest side. The new interactive protocol is not complete, under the
conditions told in the heads of Iop/BatchGrind.lean and Iop/Grind.lean [no theorem here]. This file
says nothing on whether any batch IOP has `SndBK`. It says nothing on a converse. It says nothing on
the size of an error beyond "What the errors mean" above and `Err.grind g ε`: ε is a variable.
The construction is the field's (Iop/Grind.lean names its source). That work should count round by
round, in the knowledge form, was asked for (lean/CREDITS.md).
Terms: lean/GLOSSARY.md: batch IOP, error, guard, honest side, plain part, proof of work, shape,
(Snd-B), witness map.
-/
import Ior.Batch
import Iop.BatchGrindProofs

set_option autoImplicit false

namespace Iop
open Prob

/-- The oracles of the old shape: the step changes neither positions nor alphabets. -/
def Orcs.strip {W : Type} [Inhabited W] : {s : Shape} → (g : GBits s) → Orcs (s.grind W g) → Orcs s
  | [], _, _ => fun p => nomatch p
  | _ :: _, (_, g), o => fun p => match p with
    | .inl p => o (.inl p)
    | .inr p => Orcs.strip g (fun q => o (.inr q)) p

namespace Spec

/-- States: `Orcs.strip` holds, at the position that belongs to p, the symbol at p. -/
def strip_at : Prop :=
  ∀ (W : Type) [Inhabited W] (s : Shape) (g : GBits s)
      (o : Orcs (s.grind W g)) (p : OPos (s.grind W g)),
    Orcs.strip g o (OPos.stripE g p) = OSym.strip g p (o p)

/-- States: the oracles of a stripped transcript are the stripped oracles of the transcript. -/
def read_stripO : Prop :=
  ∀ (W : Type) [Inhabited W] (s : Shape) (g : GBits s) (τ : Tr (s.grind W g)),
    (Tr.strip g τ).read = Orcs.strip g τ.read

/-- States: guard and tests commute, with the witness map wit ∘ Orcs.strip on the side with
tests. -/
def guard_grind : Prop :=
  ∀ (W : Type) [Inhabited W] (X Wn : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E)
      (R : X → E.Str → Wn → Prop) (wit : X → Orcs Q.loc.shape → Wn) (g : GBits Q.loc.shape),
    (Q.guard R wit).grind W g = (Q.grind W g).guard R (fun x o => wit x (Orcs.strip g o))

/-- States: (Snd-B) with a witness is kept by the step that adds tests: the same counts, now out of
|C| 2^b values. -/
def sndBK_grind : Prop :=
  ∀ (W : Type) [Inhabited W] (X Wn : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E)
      (g : GBits Q.loc.shape) (N : ℕ) (early : X → X) (late : Option ℕ) (R : X → E.Str → Wn → Prop)
      (wit : X → Orcs Q.loc.shape → Wn) (ε : Err Q.loc.shape),
    Q.SndBK N early late R wit ε →
    (Q.grind W g).SndBK N early late R (fun x o => wit x (Orcs.strip g o)) (Err.grind g ε)

end Spec

theorem strip_at : Spec.strip_at
  | _, _, _ :: _, (_, _), _, .inl _ => rfl
  | W, _, _ :: s, (_, g), o, .inr p => strip_at W s g (fun q => o (.inr q)) p

theorem read_stripO : Spec.read_stripO
  | _, _, [], _, _ => funext fun p => nomatch p
  | W, _, _ :: s, (_, g), (_, _, τ) => funext fun p => match p with
    | .inl _ => rfl
    | .inr p => congrFun (read_stripO W s g τ) p

open Classical in
/-- the two verifiers decide alike -/
theorem GrindK.accept_eq {W : Type} [Inhabited W] {X Wn : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof X E)
    (R : X → E.Str → Wn → Prop) (wit : X → Orcs Q.loc.shape → Wn) (g : GBits Q.loc.shape) :
    (fun (x : X) (y : E.Str) (τ : Tr (Q.loc.shape.grind W g)) =>
        Rho.pass g τ.rho &&
          (Q.loc.accept x y (Tr.strip g τ) && !decide (R x y (wit x (Tr.strip g τ).read)))) =
      fun x y τ =>
        (Rho.pass g τ.rho && Q.loc.accept x y (Tr.strip g τ)) &&
            !decide (R x y (wit x (Orcs.strip g τ.read))) := by
  funext x y τ
  rw [read_stripO, Bool.and_assoc]

theorem guard_grind : Spec.guard_grind := fun W _ X _ E Q R wit g =>
  congrArg (fun acc : X → E.Str → Tr (Q.loc.shape.grind W g) → Bool =>
      (⟨{ Q.loc.grind W g with accept := acc }, Q.ann.grind W g⟩ : BatchInteractiveOracleProof X E))
    (GrindK.accept_eq Q R wit g)

theorem sndBK_grind : Spec.sndBK_grind := by
  intro W _ X Wn E Q g N early late R wit ε h
  have h' : ((Q.guard R wit).grind W g).SndBL N early late (fun _ _ => False) (Err.grind g ε) :=
    BatchGrind.sndBL_grind (Q := Q.guard R wit) g h
  exact cast
    (congrArg (fun acc : X → E.Str → Tr (Q.loc.shape.grind W g) → Bool =>
        (⟨{ Q.loc.grind W g with accept := acc }, Q.ann.grind W g⟩ : BatchInteractiveOracleProof X E).SndBL
          N early late (fun _ _ => False) (Err.grind g ε))
      (GrindK.accept_eq Q R wit g)) h'

end Iop
