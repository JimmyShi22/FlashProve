--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/BehindStepped.lean: THE DEBT `BehindS` AT THE OUTPUT HEAD'S OWN
ROUNDS (K6, border 341), WITH THE PREMISE ON THE LETTER FOR `keeps` ASKED ONLY WHERE THE FORM BEHIND
THE STEP HOLDS. CONDITIONAL: h · hf · hb₀ · hst · hl. Two theorems.

Why. `k6_behindS` (Honest/K6/Law/Behind.lean) takes "wherever `K6Keeps` holds, the kind's clause
holds": a sentence on ALL pairs of states. A letter that lays a further clause on the hind state
beside `K6Keeps`, one that is had from the thread's `Form` behind a step, does not meet it:
`K6Keeps` relates states that stand on no thread. That premise is spent once, at the two states of a
step at a stand of the thread, where the `Form` behind the step is had without it.

  `k6_form_keeps_stepped`  with the thread's clause of `keeps`. CONDITIONAL: h · hKp: where
                           `K6Keeps s s'` holds AND the `Form` at 342 holds of s', the letter holds
  `k6_behindS_stepped`     THE DEBT. CONDITIONAL: h · hf (hKp's form at the kind's clause) · hb₀ ·
                           hst · hl, the last three as in `k6_behindS`

How. The first: `k6_form_behind` (Honest/K6/Law/FormBehind.lean) has the `Form` behind the step at
every letter Kp; `K6Keeps` of the two states is `k6_keeps_of_member_step`; then `head_keeps`. The
second by the lines of `k6_behindS`, their authors' own, one premise weaker. `k6_behindS`'s
premise gives this one at once: what `k6_behindS` reaches, this one does.

Limits. THAT THE THREAD HOLDS AT ANY STAND IS HAD BY NOBODY HERE: where it holds nowhere the two
say nothing. `BehindS` is a definition of the honest side's frame, a premise's form of its rules:
none of the library's goals. That hf is met at any letter is not had here. THE FULL SIZE ALONE, and
the format's second hash function alone, as h. Honest/K6/Law/Behind.lean does not turn. Modules under
lean/Johnson/Goal/ are among what it imports: it imports none by name and calls nothing that is
declared there. No new mathematics. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.Behind
import Johnson.Desc.ProofFile.Honest.K6.Law.FormBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Strs Wit Place Block noDigest viewWordsBelowPrime)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps plK6 k6_at341 k6_keeps_of_member_step
  k6_promise_behind)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS mgAtAll)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_reach foldFacts_raw head_keeps noStrs
  head_rides_and head_reply_next)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.Small (formP_iff honestLike_honest)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)


/-- **WITH THE THREAD's CLAUSE OF `keeps`.** CONDITIONAL: the hypothesis h; hKp: the letter Kp at
the sub-protocol's place holds wherever `K6Keeps` does and the `Form` behind the member holds of the
hind state. -/
theorem k6_form_keeps_stepped
    (hKp : ∀ (k : Coins Bk) (s s' : TS) (m' : Mid (Local W₀ Rc ProofFile.Inst Tr) X), K6Keeps s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (341 + 1) k s' m' →
      Kp plK6 s s') :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (341 + 1) k s' y.2 ∧
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 341 s s' := by
  intro blk hblk k s m E ds y cols s' hT hd hS
  have hF := k6_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hblk k s m E ds y cols s'
    hT hd hS
  obtain ⟨b, hfl, M⟩ := P4.k6_member_at_mg h.toAtMg
  obtain rfl : blk = b := Option.some.inj (hblk.symm.trans hfl)
  have K : K6Keeps s s' := k6_keeps_of_member_step M hS.2
  exact ⟨hF, (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k6_at341 s s').2
    (hKp k s s' y.2 K hF)⟩

/-- **THE DEBT `BehindS` AT THE MEMBER, THE PREMISE ON `keeps` ASKED BEHIND A STEP.** CONDITIONAL:
the hypothesis h; hf: the kind's clause holds wherever `K6Keeps` does and the `Form` behind the
member holds of the hind state; hb₀; hst; hl: as in `k6_behindS`. -/
theorem k6_behindS_stepped (f : VerifiableInference.Desc.KindName → Place → TS → TS → Prop)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
    (hf : ∀ (k : Coins Bk) (s s' : TS) (m' : Mid (Local W₀ Rc ProofFile.Inst Tr) X), K6Keeps s s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w).thread.Form
        (341 + 1) k s' m' → f .K6 plK6 s s')
    (hb₀ : b₀ ≠ 341 + 1)
    (hst : ∀ c ∈ cs, c.lo ≤ 341 → 341 + 1 ≤ c.hi → StaysBy
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w).thread 341 c)
    (hl : ∀ c ∈ cs, c.lo = 341 + 1 →
      (∃ hi, c = riderHead (341 + 1) hi fun o => o.x.isSome = true) ∨ LaysAtS
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w).thread Said 341
        c) :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w).thread Said
      341 := by
  have hM : ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w).thread.bs[341]? =
        some blk →
      VerifiableInference.Desc.Kinds.Head.Law.K6MemberIs (P5J.At.X Zp) 24 ProofFile.sameReply IM.k6Place
        blk := by
    intro blk hblk
    obtain ⟨b, hfl, M⟩ := P4.k6_member_at_mg h.toAtMg
    obtain rfl : blk = b := Option.some.inj (hblk.symm.trans hfl)
    exact M
  refine behindS_of_keeps_and _ Said
    (R₀ := fun c (v : Local W₀ Rc ProofFile.Inst Tr) (s : TS) => b₀ ≤ c → s.out.reply = some v.x.asked)
    (head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs (kpBy f) w)
    (fun blk hblk k s m E ds y cols s' hA hd hS =>
      k6_form_keeps_stepped h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w hf blk hblk
        k s m E ds y cols s' hA.1 hd hS)
    (fun blk hblk k s m E ds y cols s' hA _ hS => ?_) hst (fun c hc e => ?_)
  · have K : K6Keeps s s' := k6_keeps_of_member_step (hM blk hblk) hS.2
    have hA' := hA.1
    unfold Thr at hA'
    obtain ⟨-, -, -, -, -, hR0, -⟩ := hA'
    show b₀ ≤ 341 + 1 → s'.out.reply = some m.st.input.x.asked
    exact head_reply_next (asked := fun v : Local W₀ Rc ProofFile.Inst Tr => v.x.asked)
      ((head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs (kpBy f) w 341 _ s).1 hR0).1
      (fun e => absurd e hb₀) (fun _ => by rw [K.here])
  · rcases hl c hc e with ⟨hi, rfl⟩ | h'
    · exact laysAtS_of _ Said (k6_lays _ hM)
    · exact h'

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_form_keeps_stepped
#print axioms ProofFile.Honest.K6.k6_behindS_stepped
