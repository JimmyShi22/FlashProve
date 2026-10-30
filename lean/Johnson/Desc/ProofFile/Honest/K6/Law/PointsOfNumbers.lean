-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/PointsOfNumbers.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
THE PREMISE points OF `K6HeadDebts` (Honest/K6/Law/ScriptAtHead.lean) AND OF `K6HeadBelow`
(Honest/K6/Law/ScriptBelowFree.lean), A SENTENCE ON EVERY STATE AT WHICH THE THREAD STANDS, BROUGHT
DOWN TO TWO EQUATIONS ON PUBLIC VALUES, AND WITH IT THE FIELD keyTie OF `K6Script`: UNDER h, WHERE
THE THREAD STANDS, AND UNDER THE TWO EQUATIONS hs AND hb, WHICH STAY PREMISES. Two definitions
(premises' forms); three theorems.

What is here. points says: what the verifier's text reads at the state in front of the member as the
lookup's point and each call's key point is what the small input makes of the challenges heard. The
authors of the kind "lookup" have a text for what the lookup on the head's calls returns, made of
the public shape and the challenges alone (`headLookOfK3`,
Honest/K3/Law/Thread/HeadCallsTie.lean), and, under h, the law that the state which the first 341
members make of any rounds agrees with that text in eleven fields (`head_calls_tie`, there), and
that this state holds such a structure at all (`calls_heard_link`,
Honest/K3/Law/Thread/CallsHeardLink.lean). The thread's clause `Made`
(Honest/Thread/Thr.lean) says that the state in front of our member is that fold over the rounds
seen, and that these rounds' challenges are the challenges heard. So points holds wherever the
thread stands, if the small input's maker reads the challenges at the authors' shape and from the
authors' number on. The road is the one that the authors of the feed-forward layers' own rounds
(K4) took for their like (Honest/K4/Law/LookPtsHead.lean).

  `HeadLookShapeIs`       (shape): the shape that `headLookNumbers` (Honest/K6/Wit.lean) yields is
                          `headCallsShape`. A definition: a premise's form
  `HeadLookBaseIs`        (number): the number of rounds in front that it yields, off the plan's
                          table of steps, is the number of rounds that the first 340 members of the
                          description's flat list declare. A definition: a premise's form
  `headLook_of_two`       the two give `headLookNumbers`' value
  `k6_points_of_numbers`  **THE PREMISE points**
  `k6_keyTie_of_numbers`  **THE FIELD keyTie**, by `k6_keyTie_of_points`
                          (Honest/K6/Law/ScriptFields.lean)

Limits.
  * hs AND hb ARE PREMISES: NEITHER IS PROVED HERE, OR ANYWHERE THAT WE KNOW. Both are equations of
    values that code makes of the public files; at the three files of `VerifierAndGoals.storedPublicFiles` Lean's
    evaluator has printed both sides of each alike: a print, no theorem; off a loose sheet in which
    `headCallsShape` is spelt again, not called.
  * THAT THE THREAD STANDS AT ANY RUN: by nothing that we hold.
  * h: the full size and the format's second hash function alone.
  * Two of the eleven fields are read: zx and zk.
  * IT IMPORTS TWO FILES OF THE AUTHORS OF THE KIND "lookup". A law, no part: modules under
    lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.ScriptFields
import Johnson.Desc.ProofFile.Honest.K6.Wit
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadCallsTie
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CallsHeardLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Strs Place foldBlocks)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds (Head.Law.readsOf)
open VerifiableInference.Desc.Kinds.Head (seatAt parOf given)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K3.Law.AtThr (headCallsShape headLookOfK3 head_calls_tie calls_heard_link
  fold_rest)

/-- **(shape)**: the shape that the small input's maker takes for the lookup on the head's calls is
the lookup's authors' own. A definition: a premise's form. Nothing is claimed of it. -/
def HeadLookShapeIs (Zp : ProofFile.Pub) (G : Ground) : Prop :=
  (headLookNumbers Zp G).map (·.1) = some (headCallsShape Zp)

/-- **(number)**: the number of the first chain's rounds that the maker takes to stand in front of
that lookup is the number that the first 340 members of the flat list declare. A definition: a
premise's form. Nothing is claimed of it. -/
def HeadLookBaseIs (Zp : ProofFile.Pub) (G : Ground) (cF : Chain TS ProofFile.Cl) : Prop :=
  headBaseOf Zp G = some ((cF.blocksInOrder.take 340).flatMap (·.rounds)).length

/-- The two give the pair. -/
theorem headLook_of_two {Zp : ProofFile.Pub} {G : Ground} {cF : Chain TS ProofFile.Cl}
    (hs : HeadLookShapeIs Zp G) (hb : HeadLookBaseIs Zp G cF) :
    headLookNumbers Zp G =
      some (headCallsShape Zp, ((cF.blocksInOrder.take 340).flatMap (·.rounds)).length) := by
  unfold HeadLookShapeIs at hs
  unfold HeadLookBaseIs headBaseOf at hb
  cases e : headLookNumbers Zp G with
  | none =>
    rw [e] at hs
    simp at hs
  | some y =>
    rw [e] at hs hb
    exact congrArg some (Prod.ext (Option.some.inj hs) (Option.some.inj hb))

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- CONDITIONAL: the hypothesis h; the thread; hs; hb. **THE PREMISE points OF `K6HeadDebts`.** -/
theorem k6_points_of_numbers (cells : Tr → Cells) (weights : W₀ → Weights) (G : Ground)
    (hs : HeadLookShapeIs Zp G) (hb : HeadLookBaseIs Zp G cF) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))).lookup s =
      some ((headWit' cells weights Zp G m.st.input).lookup m.st.heard) := by
  intro k s m E hT
  obtain ⟨_, _, _, _, hM, _, _⟩ := hT.1
  obtain ⟨e1, _, _, _, s₀, cols, _, _, hf⟩ := hM
  have hf' : foldBlocks 0 (cF.blocksInOrder.take 341) s₀ m.seen cols = .ok (s, [], []) := hf
  obtain ⟨_, _, _, _, blk, hblk0, _, hstep⟩ := calls_heard_link h 24 (by omega)
  have hblk : cF.blocksInOrder[340]? = some blk := hblk0
  obtain ⟨t, rs', cols', n, _, hy⟩ := IM.fold_last hblk hf'
  obtain ⟨_, g, _, _, _, hg, _⟩ := hstep 0 t s n _ cols' hy
  have W := head_calls_tie h s₀ m.seen cols s [] [] g [] hf' hg
  obtain ⟨er, _⟩ := fold_rest 0 _ _ _ _ _ _ _ hf'
  have et : m.seen.take ((cF.blocksInOrder.take 341).flatMap (·.rounds)).length = m.seen :=
    List.take_of_length_le (List.drop_eq_nil_iff.1 er.symm)
  rw [et, List.append_nil, e1] at W
  have hR : (headWit' cells weights Zp G m.st.input).lookup m.st.heard =
      headLookupAt (headCallsShape Zp) ((cF.blocksInOrder.take 340).flatMap (·.rounds)).length
        m.st.heard := by
    show headLookupOf (headWhereOf Zp G) m.st.heard = _
    unfold headLookupOf
    show (match headLookNumbers Zp G with
      | some y => headLookupAt y.1 y.2 m.st.heard
      | none => (#[], fun _ => #[])) = _
    rw [headLook_of_two hs hb]
  rw [hR]
  show (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = _
  rw [hg]
  show some (g.zx, fun c => g.zk.getD c #[]) = _
  rw [W.zx, W.zk]
  rfl

/-- CONDITIONAL: the hypothesis h; the thread; hb₀; hs; hb. **THE FIELD keyTie OF `K6Script`**: the
verifier's letters at the state are the prover's. -/
theorem k6_keyTie_of_numbers (hb₀ : b₀ ≤ 341) (cells : Tr → Cells) (weights : W₀ → Weights)
    (G : Ground) (hs : HeadLookShapeIs Zp G) (hb : HeadLookBaseIs Zp G cF) : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    given (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))
        (seatAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))) s =
      .ok ((headWit' cells weights Zp G m.st.input).given
        (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) m.st.heard) :=
  k6_keyTie_of_points h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb₀
    (headWit' cells weights Zp G) (fun _ => rfl) (fun _ => rfl)
    (k6_points_of_numbers h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G hs hb)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headLook_of_two
#print axioms ProofFile.Honest.K6.k6_points_of_numbers
#print axioms ProofFile.Honest.K6.k6_keyTie_of_numbers
