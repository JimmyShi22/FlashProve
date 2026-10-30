-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SpecEraseDead.lean: a token whose string is never used may have any string. Definitions and
statements; nothing is proved here (the proofs: Compile/EraseDead.lean; words of this library:
lean/GLOSSARY.md).

Committer and prover are written as token programs (`Step`, Rom/Defer.lean): a secret string is
named by a token. The scheme consists of the oracle algorithms that `erase` (Compile/Star.lean)
makes of these programs: a token is then an index into a list of strings, the store. `fresh` and
`marked` append a new string to the store; `marked` and `reveal` read the store at the tokens that
they name.

Purpose. A prover that searches for a nonce (proof of work) queries the Fiat-Shamir oracle once for
each attempt. Each query puts the secret tail of its answer into the store. The tail of a failed
attempt that is not the last is never used again. So the step to one hash function
(Rom/SpecOverOneA.lean, Rom/TestFirst.lean) need not ask for it. But the conditions under which
such a step is exact (what is proved of that: the end of this paragraph) compare programs, and the
erased programs after two answers with different tails hold different stores. Compile/NeedRel.lean
(`SFacR.marked`) therefore asks that related answers have equal tails. Here is what is needed to
drop that. (Exactness under such a condition: `runEager_stateFirstA`, Rom/StateFirstLazy.lean:
`OComp.stateFirstA` against `OComp.stateFirst`, the expansion from a state; for `OComp.overOneN` and
`OComp.overOneA` see the heads of Rom/OverOneN.lean and Rom/SpecOverOneA.lean.)

  `NoUse D Q c n`      The program c, started on a store of length n, never uses the string of a
                       token in D (the dead tokens): no marked query is charged to such a token or
                       has it among its further tokens; and what follows a reveal does not depend on
                       the strings of such tokens. A reveal may name a dead token: the prover's last
                       step also reveals the tails of its failed attempts that are not the last, so
                       as to release their queries (`finishSlot`, Compile/Batch/Prover.lean), and
                       then uses none of these strings. Q is a condition on what c returns (say:
                       "the value holds no dead token where a later piece would use it"), so that
                       `NoUse` can be established part by part (`Spec.noUseBind`; `Spec.noUseMono`:
                       for fewer dead tokens and a weaker Q).
  `Spec.eraseDead`     On two stores that agree outside D (`StoreRel D`), a program with `NoUse` has
                       erasures that are the same tree, with the same values at the ends, and stores
                       in `StoreRel D`. By `Spec.alikeBind`, a scheme that in the end forgets the
                       store does not depend on the dead tokens.
  `FacDead ag Q R c n`
                       The condition for a whole program: at every marked query, after two answers
                       related by ag the program goes on in the same way and never uses the string
                       of the new token d; at its ends Q d holds. At a plain query: the same
                       continuation. R: what holds at the ends in any case.
  `Spec.facDeadErase`  The link to the step to one hash function: the erasure of such a program,
                       followed by a g that does not depend on the string of a dead token (given Q)
                       and itself depends on its answers only up to ag, depends on its answers only
                       up to ag (`OComp.FactorsBy`, Rom/OverOneN.lean). Here ag-related answers may
                       have different tails.
  `Spec.deadTail`      The use. At a marked query on a store vs: if after the answers r and r' the
                       program goes on in the same way, and that continuation never uses the string
                       of the new token, then the two erased continuations are the same tree, with
                       the same values at the ends and stores that agree except at the new token.

Notation: the step to one hash function: "The step implements a family of typed oracles by one hash
function f (Rom/Family.lean)." (the head of Rom/SpecOverOneA.lean); exact: as in "That the two have
the same output distribution if the program reads no unmarked hash block is not proved in this
library." (of `overOneN` and `overOne`: the head of Rom/OverOneN.lean, "What is proved and what is
not"); a marked query: `Step.marked o t us pt inj k` (Rom/Defer.lean, where it is called a marked
evaluation): "every marked evaluation is charged to one token t, in which its point is injective; it
may hold further tokens us" (the head there); `ag`: for each oracle o and query q a relation on
`S.Rng o`; "a relation ag on answers" (`OComp.FactorsBy`, Rom/OverOneN.lean); `(sp.split o r).1`,
`.2`: the two parts of the answer r; `sp`: a `Split S` (Rom/Defer.lean).

Limits: it does not say that any program of the scheme never uses the tails of its failed attempts
that are not the last: that takes an induction through Cp and Pp (Compile/Batch/Star.lean). And
these statements can serve only a scheme that forgets the store: the committer of the base scheme
returns its whole store in isk (`C`, which is `realQ` of `Ctok`, Compile/Batch/Star.lean), the tails
of failed attempts too, so its output depends on them. From the scheme with a seed upward (isk =
(i, seed): `argP`, Compile/Batch/StarS.lean) no store is returned.
-/
import Compile.Star
import Rom.OverOneN

set_option autoImplicit false

namespace Compile
open Rom

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- Two stores of the same length that agree outside the dead tokens. -/
def StoreRel (D : Tok → Prop) (vs vs' : List Bits) : Prop :=
  vs.length = vs'.length ∧ ∀ i, ¬ D i → vs.getD i [] = vs'.getD i []

/-- The program, started on a store of length n, never uses the string of a token in D. (At a
reveal: what follows is the same program for any two assignments of strings to tokens that agree
outside D.) Q: what holds of the value that it returns and of the length of the store then. -/
def NoUse (D : Tok → Prop) (Q : α → ℕ → Prop) : Step S sp α → ℕ → Prop
  | .pure a, n => Q a n
  | .sample _ k, n => ∀ r, NoUse D Q (k r) n
  | .plain _ _ k, n => ∀ r, NoUse D Q (k r) n
  | .fresh _ k, n => NoUse D Q (k n) (n + 1)
  | .marked _ t us _ _ k, n => ¬ D t ∧ (∀ u ∈ us, ¬ D u) ∧ ∀ v, NoUse D Q (k v n) (n + 1)
  | .reveal ts k, n =>
    (∀ f f' : Tok → Bits, (∀ u, ¬ D u → f u = f' u) → k (ts.map f) = k (ts.map f')) ∧
    ∀ w, NoUse D Q (k w) n

/-- The same oracle algorithm but for the values at its ends, which are related by R. (For token
programs: `Alike`, Compile/NeedRel.lean.) -/
inductive OAlike (R : α → α → Prop) : OComp S α → OComp S α → Prop
  | pure {a a' : α} (h : R a a') : OAlike R (.pure a) (.pure a')
  | sample (n : ℕ) {k k' : Fin (n + 1) → OComp S α} (h : ∀ r, OAlike R (k r) (k' r)) :
      OAlike R (.sample n k) (.sample n k')
  | query (o : S.ι) (q : S.Dom o) {k k' : S.Rng o → OComp S α} (h : ∀ r, OAlike R (k r) (k' r)) :
      OAlike R (.query o q k) (.query o q k')

/-- at the ends of two erased programs: the same value, of which Q holds, and stores that agree
outside the dead tokens -/
def EndRel (D : Tok → Prop) (Q : α → ℕ → Prop) (x y : α × List Bits) : Prop :=
  x.1 = y.1 ∧ StoreRel D x.2 y.2 ∧ Q x.1 x.2.length

/-- After two answers related by ag the program goes on in the same way and never uses the string of
the new token. n: the length of the store. Q d: what holds at the ends, for a token d that has
become dead in this way. R: what holds at the ends in any case. -/
def FacDead (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop)
    (Q : Tok → α → ℕ → Prop) (R : α → ℕ → Prop) : Step S sp α → ℕ → Prop
  | .pure a, n => R a n
  | .sample _ k, n => ∀ r, FacDead ag Q R (k r) n
  | .plain o q k, n => (∀ r r', ag o q r r' → k r = k r') ∧ ∀ r, FacDead ag Q R (k r) n
  | .fresh _ k, n => FacDead ag Q R (k n) (n + 1)
  | .marked o _ _ pt _ k, n =>
      (∀ v ws r r', ag o (pt v ws) r r' →
        k (sp.split o r).1 n = k (sp.split o r').1 n ∧
        NoUse (fun t => t = n) (Q n) (k (sp.split o r).1 n) (n + 1)) ∧
      ∀ v, FacDead ag Q R (k v n) (n + 1)
  | .reveal _ k, n => ∀ w, FacDead ag Q R (k w) n

namespace Spec

/-- A token whose string is never used (`NoUse`) may have any string. -/
def eraseDead : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (D : Tok → Prop) (Q : α → ℕ → Prop)
      (c : Step S sp α) (vs vs' : List Bits),
    StoreRel D vs vs' → NoUse D Q c vs.length → OAlike (EndRel D Q) (erase c vs) (erase c vs')

/-- Followed by programs that are equal at related values, two algorithms that are alike are
equal. -/
def alikeBind : Prop :=
  ∀ (S : OSpec) (α β : Type) (R : α → α → Prop) (c c' : OComp S α) (g g' : α → OComp S β),
    OAlike R c c' → (∀ a a', R a a' → g a = g' a') → c.bind g = c'.bind g'

/-- `NoUse` for one program after another: what follows is started at a value and a length of the
store of which the first program's Q holds. -/
def noUseBind : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α β : Type) (D : Tok → Prop) (Q : α → ℕ → Prop) (Q' : β → ℕ → Prop)
      (c : Step S sp α) (g : α → Step S sp β) (n : ℕ),
    NoUse D Q c n → (∀ a n', Q a n' → NoUse D Q' (g a) n') → NoUse D Q' (c.bind g) n

def noUseMono : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (D D' : Tok → Prop) (Q Q' : α → ℕ → Prop)
      (c : Step S sp α) (n : ℕ),
    (∀ t, D' t → D t) → (∀ a m, Q a m → Q' a m) → NoUse D Q c n → NoUse D' Q' c n

/-- A marked query after which the new token's string is never used: the answers r, r' may have
different tails (hypotheses below). -/
def deadTail : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (Q : α → ℕ → Prop) (o : S.ι)
      (k : sp.Vis o → Tok → Step S sp α) (vs : List Bits) (r r' : S.Rng o),
    k (sp.split o r).1 vs.length = k (sp.split o r').1 vs.length →
    NoUse (fun t => t = vs.length) Q (k (sp.split o r).1 vs.length) (vs.length + 1) →
    OAlike (EndRel (fun t => t = vs.length) Q)
      (erase (k (sp.split o r).1 vs.length) (vs ++ [List.ofFn (sp.split o r).2]))
      (erase (k (sp.split o r').1 vs.length) (vs ++ [List.ofFn (sp.split o r').2]))

/-- `FacDead` for one program after another. -/
def facDeadBind : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α β : Type) (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop)
      (Q : Tok → α → ℕ → Prop) (Q' : Tok → β → ℕ → Prop) (R : α → ℕ → Prop) (R' : β → ℕ → Prop)
      (c : Step S sp α) (g : α → Step S sp β) (n : ℕ),
    FacDead ag Q R c n → (∀ d a m, Q d a m → NoUse (fun t => t = d) (Q' d) (g a) m) →
    (∀ a m, R a m → FacDead ag Q' R' (g a) m) → FacDead ag Q' R' (c.bind g) n

/-- `FacDead` for weaker conditions at the ends -/
def facDeadMono : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop)
      (Q Q' : Tok → α → ℕ → Prop) (R R' : α → ℕ → Prop) (c : Step S sp α) (n : ℕ),
    (∀ d a m, Q d a m → Q' d a m) → (∀ a m, R a m → R' a m) →
    FacDead ag Q R c n → FacDead ag Q' R' c n

/-- The link to the step to one hash function: see the header. -/
def facDeadErase : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α β : Type) (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop)
      (Q : Tok → α → ℕ → Prop) (R : α → ℕ → Prop) (c : Step S sp α) (vs : List Bits)
      (g : α × List Bits → OComp S β),
    FacDead ag Q R c vs.length →
    (∀ d a st st', StoreRel (fun t => t = d) st st' → Q d a st.length → g (a, st) = g (a, st')) →
    (∀ a st, R a st.length → (g (a, st)).FactorsBy ag) → ((erase c vs).bind g).FactorsBy ag



end Spec

end Compile
