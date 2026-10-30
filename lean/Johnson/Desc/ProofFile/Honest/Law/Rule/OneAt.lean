-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OneAt.lean: the join (`one_exact_at`): one slot of `honestBatchProverOfFile`
(Honest/StratC.lean), written over an index committer's share (Honest/Committer.lean), compared with
`simOne` (Honest/Law/Rule/OneSim.lean). It follows from the six equations `TiedAt`
(Honest/Law/Rule/Tied.lean) and the two clauses of a valid pair of an object with OOD samples, with
`Owed`, `G.owns` and `DataFits F D`: not from `Tied` as a hypothesis. A conditional lemma at
`honestBatchProverOfFile`, general in the description, at no description of the protocol.

  1  `one_exact_paid`   the skeleton `one_exact` with its two hypotheses proved (`backAt_of`:
     Honest/Law/BackAt.lean; `asksIn_of`: Honest/Law/BackFile.lean; `stOffAt_of`:
     Honest/Law/Rule/StOff.lean). `Tied` is still among its hypotheses: not to be quoted by itself:
     an honest side whose front round says the index passes it
  2  `one_exact_at`   the join: one application of `tied` and one of `one_exact_paid`. `n`: the
     copy's number, fixed before the index. At every (index, the stored tables' pads and encoding
     randomness, OOD seed) and every instance of the object that is valid for them, at every
     verifier's message whose list of challenges is such as the rounds can draw and that is outside
     the second set of stops (`Hid`): the library's output of one slot, at what is written for
     that instance, is `simOne` of what is written, the message and the external answers
  3  `three_same`   one written input, the same three values of the rounds without a challenge
  4  `one_same`   no simulator in its conclusion: under the join's hypotheses, two valid pairs, one
     written input, the same external answers, at a verifier's message whose list of challenges is
     such as the rounds can draw, outside both second sets of stops: one distribution

What meets it. Two toy examples meet all its hypotheses together (`member_U`, `member_E`): they have
no fall and no first stop. At both, at every typed message, whether the prover answers tells apart
some two indices with one written input and one external string (`tells_at_each_U`,
`tells_at_each_E`). So the equation does not hold at every message, for `simOne` or for any function
of what is public (`not_at_every_U`, `not_at_every_E`, `no_fn_at_every_U`, `no_fn_at_every_E`). How
often: counted by nobody. That a given position is drawn: not proved. The examples are no part of
the protocol (`member_U`: Honest/Law/Rule/ToyOut.lean; `member_E`: Honest/Law/Rule/ToyEightAt.lean;
the six others: Honest/Law/Rule/ToyTellsAny.lean; none of these is in the sealed library, and its
build does not check them).
A third toy example meets the join's hypotheses on the lists of parts, with a fall declared and a
first stop beside the second (Honest/Law/Rule/ToyFullAt.lean: `one_at_G`; `member_G` and
`first_stop_G` are in the same file; not in the sealed library, and its build does not check it). It
has a point outside both stops at every typed message whose challenge at "check" is not 13
(`member_G`); at 13 every input is stopped alike (`first_stop_G`). That either is drawn: not proved.
That a run falls: checked by evaluation, not proved. Which of the two sets of `honestBatchProverOfFile` holds the
first stop: not written in Lean. Read once, its `Owed` in part.

An honest side whose front round says the index, beside a joining round and a seam that read
no private input, fails `TiedAt.silent3`, whatever pubJ is put beside it, if and only if two private
inputs with different indices have one written input (one direction, at any three rounds:
`three_same`; both: Honest/Law/Rule/ThreePub.lean: `silent3_iff`, and in that form `front_iff`; at
toy examples: Honest/Law/Rule/ToyTied.lean, Honest/Law/Rule/ToyOne.lean; none of these files is in
the sealed library, and its build does not check them). ans is a parameter: where the sample says
the index such an honest side still passes, and what is written says it too. pubJ is still a
parameter: fixed by `silent3`, not gone.

Limits.
  * `Owed` is a hypothesis, at the relation `relAt`, so at all OOD seeds.
    What this level adds to the rule (data, a second stop, a stored column out of the
    external answers, an instance that holds a sample) three toy examples have: one thin, in which
    no coin is spent or carried; one with a block that is spent and carried, a condition at an entry
    that asks something, and parts and coins in the shared chain: in these two nobody rejects and
    the first set of stops is empty (Honest/Law/Rule/ToyNoBad.lean; not in the sealed library, and
    its build does not check it), so "outside both sets" is "outside the second" there; and one
    with, beside all that, a sub-protocol that can reject and a first stop.
  * Beside its parameters (the simulators, `key`, `pubJ`, the public stops) `simOne` is given, by
    type, what is written, the message and the external answers. By value what is written holds the
    OOD answers and the external answers hold the encoded index at the positions read: both are
    computed from the index and the stored tables' pads and encoding randomness, which are fixed: no
    distribution over them occurs here.
  * The second set of stops. The second stops read the index, the stored tables' pads and encoding
    randomness and the trace, and nobody counts them. Inside them the verifier sees whether the
    prover answers: a stop on a bit of the index meets the join whole and tells the bit.
  * At a relation proper that fixes the index a part that says it passes (limit (4) of
    Honest/Law/Rule/Row.lean).
  * One slot: the library's level with OOD samples asks its field on a batch of maxBatchSize slots
    (Hiop/RecInterface.lean:220): from one slot no lemma of the library's leads there, at maxBatchSize = 1
    either: here the shared chain's coins are drawn afresh with the slot.
  * One n; who picks n is not said.
  * Where the first set of stops holds every verifier's message both sides are `none` and the
    equation says nothing.
  * That the second set reads no test bit of the message is not said.
  * A run that the verifier rejects is shown, as substitutes: the share of rejections is stated
    nowhere.
  * How many positions the protocol reads of the external string is not counted: where it reads all,
    the answers are the whole string.
  * What the three rounds without a challenge send at an instance that is not valid is not said.
  * `TiedAt` does not say that the committer's columns are an encoder's (the head of
    Honest/Law/Rule/Tied.lean).
  * All limits of the heads of Honest/Law/Rule/Row.lean and Honest/Law/Rule/Tied.lean.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.BackAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK SgX)

section Frame
variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}
variable {C : CK} {D : WholeD} {tF : TF} {tJ : TJ} {t3 : T3} {F : FileDescription Xi}
  {silent : Xi → TF → TJ → T3 → Bool} {Bk : ProverCoinCounts} [Fintype R2] [Nonempty R2] [Fintype R3]
  [Inhabited R3] {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
  {J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3} {sh : Ky → F.S₂}
  {ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str} {pubJ : R2 → R3 → Xi → TF × TJ × T3}
  {Rel : W₀ → Rc → Xi → Prop}

/-- The skeleton `one_exact`, with its two hypotheses proved. `Tied` is still a hypothesis: not to
be quoted by itself. -/
theorem one_exact_paid (hO : Owed F Bk H G Rel) (hE : G.owns = true) (hD : DataFits F D)
    (w : W₀ × Rc × Sd) (x : Xi) (hv : Tied D F H J ext pubJ sh Rel w x)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hρ : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.Hid w x) :
    (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.output w x ρ =
      simOne C D tF tJ t3 F silent Bk G.sims H.key pubJ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover
                         H) J sh ext).one.Bad x ρ
        ((batchOf C D tF tJ t3 F silent).loc.extAns x ρ (ext w)) :=
  one_exact hO hE (backAt_of hO.plan hD)
    (stOffAt_of (asksIn_of C D tF tJ t3 F silent hO.plan hD)) w x hv ρ hdue hρ

end Frame

section Join
variable {I X RI Seed Ans Xi Ky Tr X₀ Xh TF TJ T3 R2 R3 : Type} {ans : I → RI → Seed → Ans}
  {Ryes : I → X → Prop} {wr : X × (Seed × Ans) → Xi} {Cm : Committer I RI Seed X Xi Ky}
  {kp : Seed × Ans → Ky} {n : ℕ} {C : CK} {D : WholeD} {tF : TF} {tJ : TJ} {t3 : T3}
  {F : FileDescription Xi} {silent : Xi → TF → TJ → T3 → Bool} {Bk : ProverCoinCounts} {sh : Ky → F.S₂}
  {front : ℕ → R2 → R3 → I → RI → Seed → Xi → TF} {join : R2 → I → RI → Seed → TJ}
  {seam : R2 → R3 → I → RI → Seed → Xi → T3} {pubJ : ℕ → R2 → R3 → Xi → TF × TJ × T3}
  [Fintype R2] [Nonempty R2] [Fintype R3] [Inhabited R3] {H : Prover I RI Xi Ky Tr X₀ Xh}
  {G : Sides F Bk I RI Ky Tr X₀ Xh}

/-- **The join.** A conditional lemma on one slot of `honestBatchProverOfFile` over a committer's share. None of
the library's goals. -/
theorem one_exact_at (h : TiedAt ans wr Cm kp n D F sh front join seam pubJ)
    (hO : Owed F Bk (Cm.prover H) G (relAt ans Ryes wr)) (hE : G.owns = true) (hD : DataFits F D)
    (w : I × RI × Seed)
    (a : X × (Seed × Ans)) (ha : a.2 = (w.2.2, ans w.1 w.2.1 w.2.2) ∧ Ryes w.1 a.1)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hρ : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Hid w (wr
          a)) :
    (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.output w
          (wr a) ρ =
      simOne C D tF tJ t3 F silent Bk G.sims (Cm.prover H).key (pubJ n)
        (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Bad (wr a)
          ρ
        ((batchOf C D tF tJ t3 F silent).loc.extAns (wr a) ρ (Cm.ext D.a w)) :=
  one_exact_paid hO hE hD w (wr a) (tied h H w a ha) ρ hdue hρ

omit [Fintype R2] [Nonempty R2] [Fintype R3] [Inhabited R3] in
/-- **One written input, the same three values**: what the three rounds without a challenge send at
two private inputs and two requests for which one explicit input is written. -/
theorem three_same (h : TiedAt ans wr Cm kp n D F sh front join seam pubJ) (r2 : R2) (r3 : R3)
    (k k' : Isk I RI Seed) (x' x'' : X) (e : Cm.xi k x' = Cm.xi k' x'') :
    (front n r2 r3 k.index k.coins k.seed (Cm.xi k x'), join r2 k.index k.coins k.seed,
      seam r2 r3 k.index k.coins k.seed (Cm.xi k x')) =
    (front n r2 r3 k'.index k'.coins k'.seed (Cm.xi k' x''), join r2 k'.index k'.coins k'.seed,
      seam r2 r3 k'.index k'.coins k'.seed (Cm.xi k' x'')) := by
  rw [h.silent3 r2 r3 k x', h.silent3 r2 r3 k' x'', e]

/-- **No simulator occurs in its conclusion.** Under the hypotheses of the join (`TiedAt`, `Owed`,
`G.owns`, `DataFits F D`): two valid pairs for which one explicit input is written, with the same
external answers, at a verifier's message whose list of challenges is such as the rounds can draw
and that is outside the second set of stops of both: one slot's output has one distribution. That
two private inputs with different indices share what is written and the answers is not said. -/
theorem one_same (h : TiedAt ans wr Cm kp n D F sh front join seam pubJ)
    (hO : Owed F Bk (Cm.prover H) G (relAt ans Ryes wr)) (hE : G.owns = true) (hD : DataFits F D)
    (w w' : I × RI × Seed)
    (a a' : X × (Seed × Ans)) (ha : a.2 = (w.2.2, ans w.1 w.2.1 w.2.2) ∧ Ryes w.1 a.1)
    (ha' : a'.2 = (w'.2.2, ans w'.1 w'.2.1 w'.2.2) ∧ Ryes w'.1 a'.1) (e : wr a = wr a')
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hx : (batchOf C D tF tJ t3 F silent).loc.extAns (wr a) ρ (Cm.ext D.a w) =
      (batchOf C D tF tJ t3 F silent).loc.extAns (wr a') ρ (Cm.ext D.a w'))
    (hρ : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Hid w (wr
          a))
    (hρ' : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Hid w' (wr
          a')) :
    (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.output w
          (wr a) ρ =
      (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.output w'
          (wr a') ρ := by
  rw [one_exact_at h hO hE hD w a ha ρ hdue hρ,
    one_exact_at h hO hE hD w' a' ha' ρ hdue hρ', hx, e]

end Join

end ProofFile.Honest

#print axioms ProofFile.Honest.one_exact_paid
#print axioms ProofFile.Honest.one_exact_at
#print axioms ProofFile.Honest.three_same
#print axioms ProofFile.Honest.one_same
