-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkSound.lean: the written link, and one hypothesis on the rounds after the fifth.

The language (`Sz.Lang`, OnBytes/Slice/LinkAt.lean): the first stored table does not decode, or the
copy decodes to the same rows' messages. "Decodes": the table is within eM columns of a table of
code words (below half the code's distance there is at most one). No theorem of this library is
stated for `Sz.Lang`.

The written protocol: Run/PlanQX.lean's `skeletonOverBothExternalStrings` at hash blocks as verifier messages, for any list of
rounds that begins with the link's five rounds, any openings of the stored tables and any decision.

What the written link's soundness asks, beside its hypotheses on the tables' code (`link_sound_at`,
`link_sound_rec`, OnBytes/Slice/LinkSoundRec.lean; there (c) is asked in the form `ClosesR`):
 (a) the compared entries have different vertices; the lists of the two folded rows' oracle messages
     have at most L members, and two different members of a list have the same answers at no more
     than a counted number of seeds;
 (b) each of the five rounds draws nothing beyond what the link draws in it, and positions of at
     most 64 bits (`DrawsOK`: the map from the round's typed values to the link's verifier message
     is injective). That a round draws all of it shows only in the size of its error count;
 (c) **the hypothesis on what follows** (`Closes`): after every transcript of the five rounds, if
     the statement that the library's verifier holds then (`st4`) has no witness in the relaxed
     relation of the link's last joint (enlarged by the statements outside its condition), the
     prover has lost in the rounds that follow.

(a) and (b) are hypotheses on the codes and sizes, which do not depend on the decision. (c) speaks
of the batching and the proximity test, and it is the only place where the decision is looked at. It
is a hypothesis in this file.

Main definitions: `on0`, `on1`, `written`, `Closes`. Main theorem: `doomed_cons_all`.
Not claimed here. That the written link is sound. That (c) holds. Nothing on the sizes of the error
counts: with large counts `Closes` holds for free, wherever a round follows the fifth. Nothing on
files, on a hash function or on a program: `Closes` speaks of an interactive protocol. Nothing on an
honest prover: the written verifier refuses unless all test bits of work are 0, so it refuses an
honest prover too, but for a small share of its messages (the test bits: OnBytes/Slice/README.md,
"The vocabulary", the written link). The language's first clause is a way out (there, "The way out
and the key"). No theorem of this library takes `Closes` as a hypothesis; the link's soundness
theorems ask `ClosesR` (OnBytes/Slice/LinkSoundRec.lean).

-/
import OnBytes.Slice.CorePeel
import Cb.Ld.LdFoldEqProofs

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run Blocks

namespace Sz
variable (S : Sz)

/-- the condition on the first table: it decodes -/
def on0 : (S.lk.D.X.Row → S.Pos → GE) → S.lk.D.X.Rec → Prop := fun f r => S.lk.D.X.dec f r ≠ none
/-- the condition on the copy: no two tables of code words near it differ in their messages -/
def on1 : (S.lk.D.X.Row → S.Pos → GE) → S.lk.D.X.Rec → Prop := fun f r => ¬ S.lk.D.X.Coll f r.1

end Sz

section
variable (S : Sz) (d1 d2 d3 d4 d5 : PQ.RD) (tl : List PQ.RD) (xs : List PQ.XO)
  (dec : PQ.View → Bool)

/-- The written protocol. -/
abbrev written : InteractiveOracleProof Unit (twoExternalStrings (2 ^ S.P.T.a) PQ.SgX) :=
  (PQ.skeletonOverBothExternalStrings (ckP .two) (d1 :: d2 :: d3 :: d4 :: d5 :: tl) S.P.T.a xs dec).up.loc

/-- **The hypothesis on the rounds after the fifth.** After every transcript of the five rounds, if
the statement that the library's verifier holds then (`st4`) has no witness in the last joint's
relaxed relation (enlarged by the statements outside its condition), the prover has lost in the
rounds that follow. -/
def Closes (εt : Err (PQ.uL (ckP .two) tl)) : Prop :=
  ∀ (y : S.lk.E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5,
    (∀ w, ¬ S.lk.j4.cf.relR (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5) w) →
    Doomed (PQ.uL (ckP .two) tl) εt fun b =>
      (written S d1 d2 d3 d4 d5 tl xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, b) = false

/-- A prover that has lost after every first round has lost at the start. -/
theorem doomed_cons_all {r : Round} {s : Shape} (ε : Err s) (bad : Tr (r :: s) → Prop)
    (h : ∀ m c, Doomed s ε fun τ => bad (m, c, τ)) : Doomed (r :: s) (0, ε) bad := fun m =>
  le_of_eq (cnt_false fun c hc => hc (h m c))

end

end OnBytes.Slice

