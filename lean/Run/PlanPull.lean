-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPull.lean: challenges as hash blocks: a choice of challenge types for the generic
construction at which a round's verifier message is its blocks, the wiring hands blocks on, and the
view applies the sampler. There, under the hypothesis of `Spec.planPull_unif`, the condition that
challenges be uniform holds at every round, also where field elements are drawn.

Definitions, statements (`Spec.planPull_cut` to `Spec.planPull_okg`) and proofs. The matter is how
the verifier messages of a public-coin protocol (`InteractiveOracleProof`, Iop/InteractiveOracleProof.lean) are made from the output
of a hash function. Many statements of this library are written twice: a definition in the namespace
`Spec` states a proposition, and a theorem of the same name outside that namespace proves it
(lean/GLOSSARY.md).

A wiring is the data that say how deep the trees are, where a position stands among a tree's leaves,
and how blocks of a hash answer give a verifier message (`ProtocolQueryLayout`, Iop/BatchWire.lean); the
conditions on a wiring are `ProtocolQueryLayout.OKG`. The generic construction (Run/PlanQTypes.lean,
Run/PlanQWire.lean, Run/PlanQS.lean) makes, from a description (`Fmt.Spec`, Fmt/Rules8.lean), the
typed protocol, its wiring and the functions that run a file. It is generic in a choice of challenge
types (`PQ.CK`): for each round, by its entry e and kind k, the type of the verifier's message, and
its view, the map from such a message to the format's record of what was drawn. Challenges as
sampled values (`ck`, Run/PlanDrawsQ.lean): the message is the values that the format draws, field
elements and positions among them. Challenges as hash blocks (`ckP`): it is the round's 256-bit
blocks, and reads and decision apply the sampling rule; the library calls the step from sampled
values to hash blocks "pull".

Why: one of the conditions on a wiring (`chal_unif`, Iop/BatchWire.lean) asks that uniform blocks
give an exactly uniform verifier message. With challenges as sampled values, `ck f` (the wiring
applies the sampler), that is false for every round that draws a field element. The library's way
with a biased sampler is not another condition. It changes the protocol (Iop/Pull.lean,
Iop/BatchWireDraw.lean). The message becomes the sampler's source, the string of its blocks. Reads
and decision apply the sampler. The wiring hands the first b of its K blocks on. The bias goes into
the numbers (`Shape.Draws.Good`, Iop/Draw.lean; `planQ_good`, Run/PlanDrawsQ.lean). The generic
construction is generic in the choice of challenge types, so the pulled form needs no new
construction.

Main names:
  `ckP f`, `chalP f K`: b is the number of blocks of the round's sampler (`bsRound`,
    Run/PlanDraws.lean).
  `Spec.planPull_cut`: the wiring's function with challenges as sampled values (`PQ.cutK`) is the
    sampler applied to the value of `chalP`.
  `Spec.planPull_view`: the views of the two choices agree along the sampler; and the view of blocks
    is `Fmt.drawRound` on the words read off their bytes.
  `Spec.planPull_round`: a round at `ckP f` is the library's pull of the round at `ck f` along the
    sampler. `Spec.planPull_shape`: so is the shape `PQ.shapeL`, along the samplers of
    Run/PlanDrawsQ.lean's `planL`.
  `Spec.planPull_unif`: if every round's b ≤ K, then `PQ.ChalUnif (ckP f) K (chalP f K) ds`: exact,
    at every round.
  `Spec.planPull_fits`: at both choices what was drawn has exactly the entry's number of positions.
    (`PQ.DrawnFits`, Run/PlanQWireLaws.lean, asks at most that number.)
  `Spec.planPull_okg`: if every round's b ≤ K and every round's work (`entry.work`: its bits of
    proof of work) ≤ 64, then `(PQ.wqS (ckP f) K (chalP f K) ds dec).OKG`: the conditions on a
    wiring, for every plan (`ds`: any list of rounds' data), nothing else assumed.

Notation:
  `f`: the field, one of the format's two (`Fmt.Fld`, Fmt/Rules1.lean);
  `K`: the number of blocks from which a verifier message is made;
  `(bsRound f e k).φ`: the block sampler's map from `b` blocks to a verifier message (`BS`,
    Iop/Draw.lean);
  `(bsRound ..).sampler`: the block sampler as a sampler of a round (`BS.sampler`, Iop/Draw.lean);
  `dec`: a decision: a function `PQ.View → Bool`.

Limits: this file does not say that the protocol at `ckP f` is the library's pull of the protocol at
`ck f`. The shape `PQ.shapeL` at `ckP f` is the pull of that at `ck f` (`planPull_shape`); reads and
decision: not shown here; the whole equation stands in Run/PlanPullProto.lean.
This file does not say that its wiring is a part of the compiler's generic wiring (`DataK.W`,
CompileK/Main.lean). That wiring has whole paths (no pruned openings), depths by a logarithm of a
number of positions, and places by a numbering. This file's `PQ.wqS` has pruned openings. What this
file does not say of its wiring is shown for the wiring with whole paths alone (`PQ.wqSF`,
Run/PlanQSF.lean). For that wiring, Run/PlanPullWire.lean and Run/PlanPullWireT.lean show it round
by round; Run/PlanPullWq.lean states one of two equations that would say it whole
(`Spec.planPull_wq`; proved: `planPull_wq`, Run/PlanPullWqProofs.lean:216); `data_T` is declared in
no file of this library. The part meant is the record field `T` of `DataK.WWk`
(CompileK/GrindMain.lean), that is of `DataK.W` after the library's step for the tests.
That these terms are that field, at a `DataK` and a `Work` written down, is not stated
in this file.
This file says nothing on soundness, and nothing on a run.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSLaws
import Iop.WireOK

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

/-- the round in front (entry `PQ.e0`, kind `.nothing`: it draws nothing) has no block: a theorem,
not a definition -/
theorem b_front (f : _root_.Fmt.Fld) : (bsRound f PQ.e0 .nothing).b = 0 :=
  (planDraws_law f PQ.e0 .nothing (by decide)).2

theorem noFront (f : _root_.Fmt.Fld) (i : Fin (bsRound f PQ.e0 .nothing).b) : False :=
  Nat.not_lt_zero i.val (lt_of_lt_of_eq i.isLt (b_front f))

/-- With no block there is exactly one string of blocks. -/
@[reducible] def frontCkP (f : _root_.Fmt.Fld) :
    Unique (Fin (bsRound f PQ.e0 .nothing).b → Dig 256) :=
  ⟨⟨fun i => (noFront f i).elim⟩, fun _ => funext fun i => (noFront f i).elim⟩

/-- Challenges as hash blocks: the choice of challenge types (`PQ.CK`) of the pulled form. -/
def ckP (f : _root_.Fmt.Fld) : PQ.CK :=
  ⟨fun e k => Fin (bsRound f e k).b → Dig 256,
    fun _ _ => inferInstance,
    fun _ _ => inferInstance,
    fun e k u => drawnOf f e k ((bsRound f e k).φ u),
    frontCkP f⟩

/-- The wiring's function from hash blocks to a challenge: the first b of K blocks. -/
def chalP (f : _root_.Fmt.Fld) (K : ℕ) : ∀ e k, (Fin K → Dig 256) → (ckP f).Ch e k := fun e k =>
  firstBlocks 256 K (bsRound f e k).b

namespace Spec

def planPull_cut : Prop :=
  ∀ (f : _root_.Fmt.Fld) (K : ℕ) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) (u : Fin K → Dig 256),
    PQ.cutK (bsRound f e k) K u = (bsRound f e k).φ (chalP f K e k u)

def planPull_view : Prop :=
  ∀ (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry)
      (k : _root_.Fmt.Kind) (u : Fin (bsRound f e k).b → Dig 256),
    (ckP f).dr e k u = (ck f).dr e k ((bsRound f e k).φ u) ∧
    (ckP f).dr e k u = _root_.Fmt.drawRound f e k (rowOfDigs u)

def planPull_round : Prop :=
  ∀ (f : _root_.Fmt.Fld) (d : PQ.RD),
    PQ.roundOf (ckP f) d = (PQ.roundOf (ck f) d).pull (bsRound f d.entry d.kind).sampler

def planPull_shape : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List PQ.RD), PQ.shapeL (ckP f) ds =
    (PQ.shapeL (ck f) ds).pull (Samplers.ofDraws _ (drawsOf f _ (planL f ds)))

def planPull_unif : Prop :=
  ∀ (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD),
    (∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ K) → PQ.ChalUnif (ckP f) K (chalP f K) ds

def planPull_fits : Prop :=
  ∀ (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind),
    (∀ c, ((ck f).dr e k c).poss.length = e.poss) ∧ (∀ c, ((ckP f).dr e k c).poss.length = e.poss)

def planPull_okg : Prop :=
  ∀ (f : _root_.Fmt.Fld) (K : ℕ) (ds : List PQ.RD) (dec : PQ.View → Bool),
    (∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ K) → (∀ d ∈ ds, d.entry.work ≤ 64) →
    (PQ.wqS (ckP f) K (chalP f K) ds dec).OKG

end Spec

theorem planPull_cut : Spec.planPull_cut := fun _ _ _ _ _ => rfl

theorem planPull_view : Spec.planPull_view := fun f e k u => ⟨rfl, planDraws_tie f e k u⟩

theorem planPull_round : Spec.planPull_round := fun _ _ => rfl

theorem planPull_shape : Spec.planPull_shape := by
  intro f ds
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    show PQ.roundOf (ckP f) d :: PQ.shapeL (ckP f) ds =
      (PQ.roundOf (ck f) d).pull (bsRound f d.entry d.kind).sampler ::
        (PQ.shapeL (ck f) ds).pull (Samplers.ofDraws _ (drawsOf f _ (planL f ds)))
    rw [ih]
    rfl

theorem planPull_unif : Spec.planPull_unif := fun f K _ h d hd =>
  map_firstBlocks_unif (Dig 256) (fun _ => false) (bsRound f d.entry d.kind).b K (h d hd)

/-! ### What was drawn holds the entry's number of positions -/

def isPos : _root_.Fmt.Draw → Bool
  | .pos _ => true
  | _ => false

theorem poss_len (f : _root_.Fmt.Fld) :
    ∀ (ds : List _root_.Fmt.Draw) (v : Vals f ds),
      (_root_.Fmt.collect (outAll f ds v)).poss.length = ds.countP isPos
  | [], _ => rfl
  | d :: ds, v => by
    have ih := poss_len f ds v.2
    cases d with
    | elem => rw [List.countP_cons_of_neg (by decide)]; exact ih
    | elemNZ => rw [List.countP_cons_of_neg (by decide)]; exact ih
    | pos k =>
      rw [List.countP_cons_of_pos (by rfl)]
      show ((_root_.Fmt.collect (outAll f ds v.2)).poss.length + 1) = _
      rw [ih]
    | trits n => rw [List.countP_cons_of_neg (by show ¬ (false = true); decide)]; exact ih
    | sealed => rw [List.countP_cons_of_neg (by decide)]; exact ih

theorem count_dsOf (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) :
    (_root_.Fmt.dsOf e k).countP isPos = e.poss := by
  have h1 : (_root_.Fmt.dsElems e k).countP isPos = 0 := List.countP_eq_zero.2 fun d hd => by
    cases d with
    | pos k' => exact absurd hd (pos_not_elems e k k')
    | elem => decide
    | elemNZ => decide
    | trits n => show ¬ (false = true); decide
    | sealed => decide
  have h2 : (_root_.Fmt.Draw.trits e.trits ::
        (if k = .sealed then [_root_.Fmt.Draw.sealed] else [])).countP isPos = 0 := by
    split <;> rfl
  unfold _root_.Fmt.dsOf
  rw [List.countP_append, List.countP_append, h1, h2, List.countP_replicate]
  rfl

theorem planPull_fits : Spec.planPull_fits := fun f e k =>
  ⟨fun c => (poss_len f _ c).trans (count_dsOf e k),
    fun _ => (poss_len f _ _).trans (count_dsOf e k)⟩

theorem planPull_okg : Spec.planPull_okg := fun f K ds dec hK hw =>
  PQ.wqS_okg (ckP f) K (chalP f K) ds dec (planPull_unif f K ds hK)
    (fun d _ c => le_of_eq ((planPull_fits f d.entry d.kind).2 c)) hw

end Run
