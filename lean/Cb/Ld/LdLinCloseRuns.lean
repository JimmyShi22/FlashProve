-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseRuns.lean: several proximity tests on groups of oracles (whole tests), one after the
other, as one interactive oracle reduction, until no oracle and no claim is left (the trivial
statement).

Group, zero-evader, "relaxed by decoding with a sample", a joint's condition and "collision-free"
are told in the head of Cb/Ld/LdLinCloseRun.lean.

Definitions and statements; the proofs are in Cb/Ld/LdLinCloseRunsProofs.lean.

Why: at the end of a protocol a statement carries oracle messages with their samples (a signature S,
Cb/Ld/LdSig.lean) and claims rows on several groups of them; an oracle message may lie in several
groups. Each test drops the members of its group that no later test reads.

Main names:
  `LdRunD S`, the data of one test: the group G, with a common long position (neP); who is kept (kp,
    decidable: decKp; every oracle message is a member or kept: hc); the rows of the claim (names B,
    a finite type: finB; states Sb, forms sl on the message of the group's complex); the zero-evader
    Z of the bridge; the whole test T on the complex (an end block of Cb/Ld/LdTower.lean); two
    numbers: L (a bound for the list of the complex at the joint radius), t (the long positions of
    the complex that T needs).
  `D.OK`: four of the premises of `Spec.ldClose_run`: Z evades; the complex has lists of at most L
    members at the joint radius; the joint radius implies each member's own; T is a tail that needs
    at most t long positions.
  `LdTl S E₀ Wp`, the data of a closing of a statement over S: St (the explicit part beside the
    samples), "base" (what is claimed of the messages: a base joint), a reduction to the trivial
    statement with honest side, extractor, numbers, and q (what is needed of the oracles). E₀:
    further oracles, never sampled; Wp: a further witness.
  `Q.OK`: it is a tail (Cb/Ld/LdTowerKit.lean) from `S.over Q.base`, relaxed by decoding with a
    sample, on collision-free statements with the base joint's own condition, to the trivial
    statement.
  `LdTl.cons D Q`: explicit part: (targets and states of D's rows, Q's). Claim: D's rows hold of the
    group's message, and Q's claim of the kept messages. Needed of the oracles: one position of each
    member for each of at most t common long positions, and what Q needs of what is kept.
  `LdTl.nil`: for a signature without oracle messages: nothing is claimed: a step without rounds.
  `Spec.ldRuns_cons`: `D.OK` → `Q.OK` → `(LdTl.cons D Q ..).OK`. `Spec.ldRuns_nil`: if S has no
    oracle message, `LdTl.nil` is OK. `Spec.ldRuns_cf`: a closing that is OK is also a tail from the
    joint with the condition moved into the relaxed relation (the form that comes after a sending).
  `Spec.ldRuns_data` states that the rounds are (T's + 1) + Q's, and the errors in a row L · (the
    evader's number), T's, Q's (this statement has the errors of `ldRunEN` at that number, then Q's;
    that the first are that number, then T's: `Spec.ldClose_run_data`, Cb/Ld/LdLinCloseRun.lean).
An oracle message in several groups is a member of D's group and kept; it is tested again in Q. What
it has to bear is the sum of what the tests read of it: that is what q adds up.

Limits: this file does not say which groups a protocol forms, nor that any bound on a list holds (L
is a hypothesis; such a bound, under hypotheses of its own: `ldGroupJohn_list`,
Cb/Ld/LdGroupJohn.lean). It says nothing on splittings of rows that lie on two groups (another
file's).
Declared differences to a write-up of ours (lean/CREDITS.md; by a reading): those of
Cb/Ld/LdLinCloseRun.lean. Tests that run side by side in the same rounds are not here: one after the
other.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinCloseRun
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

/-- One whole test on a group: the data. -/
structure LdRunD {E : Type} [Field E] [Fintype E] (S : Sig E) where
  G  : Grp S
  [neP : Nonempty G.P]
  /-- the oracle messages that something after the test still reads -/
  kp : S.O → Prop
  [decKp : DecidablePred kp]
  hc : ∀ o, G.mem o ∨ kp o
  /-- the rows of the claim -/
  B  : Type
  [finB : Fintype B]
  Sb : B → Type
  sl : ∀ b, Slf E (Sb b) G.C.J
  /-- the zero-evader of the bridge -/
  Z  : Evader E (G.Row B)
  /-- the whole test on the complex -/
  T  : LdEnd (G.joint Sb sl Z)
  /-- a bound for the list of the complex at the joint radius; the long positions of the complex
  that T needs -/
  L  : ℕ
  t  : ℕ

attribute [instance] LdRunD.neP LdRunD.decKp LdRunD.finB

/-- What is asked of one test. -/
structure LdRunD.OK {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) : Prop where
  ev   : D.Z.OK
  list : D.G.C.ListAt D.G.e D.L
  fits : D.G.Fits
  tail : D.T.OK D.t

/-- A closing of a statement over S: the data. -/
structure LdTl {E : Type} [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) where
  St   : Type
  base : IOR.Rels Unit St E₀ (S.Msg × Wp)
  R    : IOR (St × S.Smp) (E₀.prod S.ext) Unit extNone
  H    : R.Honest (S.Wit × Wp) Unit
  ext  : (St × S.Smp) × (E₀.prod S.ext).Str → Tr R.shape → Unit → S.Wit × Wp
  N    : IOR.Nums Unit R
  q    : Finset (E₀.prod S.ext).Pos → Prop

namespace LdTl
variable {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

/-- The closing is a tail of a chain. -/
def OK (Q : LdTl S E₀ Wp) : Prop := TailTr Q.R Q.H (S.over Q.base) trivRels Q.ext Q.N Q.q

/-- For a signature without oracle messages (`[IsEmpty S.O]`: `Spec.ldRuns_nil`): no oracle message
is left, nothing is claimed. -/
def nil (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp) : LdTl S E₀ Wp where
  St := Unit
  base := ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩
  R := ldDone _ _
  H := ldDoneH _ _ _
  ext := fun _ _ _ => w₀
  N := IOR.Nums.pure Unit _ _
  q := fun U => U = ∅

variable [Fintype E]

open Classical in
/-- The test D, then the closing Q of what is kept. d, d': values of the extractor where nothing was
output. -/
def cons (D : LdRunD S) (Q : LdTl (S.sub D.kp) E₀ Wp)
    (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) : LdTl S E₀ Wp where
  St := ((D.B → E) × (∀ b, D.Sb b)) × Q.St
  base := claimRels (fun x m => Slf.All D.sl x (D.G.msg m))
    (onMsgRels (S.res (T := OMsg.Msg) D.kp) Q.base)
  R := (ldRunE D.G D.kp D.Sb D.sl D.Z Q.St E₀ D.T).seq Q.R
  H := (ldRunEH D.G D.kp D.Sb D.sl D.Z Q.St Wp E₀ D.T).seq Q.H
  ext := IOR.extSeq _ _ (ldRunEX D.G D.kp D.Sb D.sl D.Z Q.St Wp E₀ D.T D.hc d d') Q.ext d
  N := (ldRunEN D.G D.kp D.Sb D.sl D.Z Q.St E₀ D.T Unit (D.L * D.Z.err)).seq Q.N
  q := fun V =>
    ∃ U,
      besideQ ((D.G.joint D.Sb D.sl D.Z).atMost D.t) Q.q U ∧ V = U.biUnion (ldBrG D.G D.kp E₀).src

end LdTl

namespace Spec

/-- States: if `D.OK` and `Q.OK`, a test, then a closing of what is kept, is a closing that is OK.
-/
def ldRuns_cons : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (D : LdRunD S)
      (Q : LdTl (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp),
    D.OK → Q.OK → (LdTl.cons D Q d d').OK

/-- Nothing is left. States: if S has no oracle message, `LdTl.nil` is OK. -/
def ldRuns_nil : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) [IsEmpty S.O] (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp),
    (LdTl.nil S E₀ Wp w₀).OK

/-- After a sending: a closing that is OK is a tail from the joint whose condition may fail. -/
def ldRuns_cf : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (Q : LdTl S E₀ Wp),
    Q.OK → TailTr Q.R Q.H (S.over Q.base).cf trivRels Q.ext Q.N Q.q

/-- Rounds and errors. -/
def ldRuns_data : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (D : LdRunD S)
      (Q : LdTl (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp),
    (LdTl.cons D Q d d').R.shape.length = (D.T.R.shape.length + 1) + Q.R.shape.length ∧
    (LdTl.cons D Q d d').N.err =
      Err.app (s := (ldRunE D.G D.kp D.Sb D.sl D.Z Q.St E₀ D.T).shape)
        (ldRunEN D.G D.kp D.Sb D.sl D.Z Q.St E₀ D.T Unit (D.L * D.Z.err)).err Q.N.err

end Spec
end Cb
