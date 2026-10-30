-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/FormBehind.lean: BEHIND THE ACCEPTED STEP OF THE MEMBER "the
output head's own rounds" (K6, number 341): THE THREAD's FORM AT THE NEXT BORDER, AND THE TABLE's
TEST ON THE FORMS AT THE HEAD's FOUR RUNS, AT EVERY LETTER Kp: three theorems of
Honest/K6/Law/Behind.lean and FormsBehind.lean once more, WITHOUT THEIR PREMISE hKp.

WHAT IT IS NOT. NOTHING NEW IS PROVED: `k6_form_keeps` (Behind.lean) concludes the form and the
thread's clause of `keeps`, and spends hKp (the letter Kp at the sub-protocol's place holds wherever
`K6Keeps` does) on the second alone; `k6_forms_behind` and `k6_forms_behindS` (FormsBehind.lean)
take the first half of it and throw the second away: so they ask hKp for nothing. Here the first
half stands alone. Nothing is said of `keeps`. It is shown of no run that the thread holds at any
stand, and no state is shown at which the member accepts. THE FULL SIZE ALONE, and at that family of
threads alone. Nothing on any property.

WHERE THE LINES COME FROM. The proof of `k6_form_behind` is `k6_form_keeps`' own, line for line, up
to its last `refine`, which here has the first half alone, and the two bullets behind it. The proofs
of `k6_forms_behind'` and `k6_forms_behindS'` are those of `k6_forms_behind` and `k6_forms_behindS`,
with `k6_form_behind` called in the place of `k6_form_keeps`.

WHAT STAYS A PREMISE: the hypothesis h; that the member stands at 341 in the thread's list; the
thread in front; the challenges fit; the step. Said is a letter: nothing of it is spent.

  `k6_form_behind`      the form at border 342
  `k6_forms_behind'`    the table's test on the forms accepts at each of the four runs
  `k6_forms_behindS'`   the same from the thread with a sentence Said beside it

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.FormsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Strs Place noDigest viewWordsBelowPrime)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head (Law.K6Name)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps k6_keeps_of_member_step k6_promise_behind)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS mgAtAll)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_reach foldFacts_raw noStrs)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.Small (formP_iff honestLike_honest partsAt_of_formP)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **BEHIND THE MEMBER's ACCEPTED STEP: THE FORM**, at the first chain's thread as it is laid at
the library's hypothesis, AT EVERY LETTER Kp. `k6_form_keeps`' first half, without hKp. CONDITIONAL:
the hypothesis h; the thread in front; the challenges fit; the step. -/
theorem k6_form_behind :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (341 + 1) k s' y.2 := by
  intro blk hblk k s m E ds y cols s' hT hd hS
  obtain ⟨b, hfl, M⟩ := P4.k6_member_at_mg h.toAtMg
  obtain rfl : blk = b := Option.some.inj (hblk.symm.trans hfl)
  have hstep : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have K : K6Keeps s s' := k6_keeps_of_member_step M hstep
  have hb : 341 ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hfl).1
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  -- every word of the played rounds is below the prime
  have hdl : l.map (·.decl) = blk.rounds := by
    rw [steps_decl hl, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hcan : viewWordsBelowPrime ⟨(roundsOf y.1).map noDigest, []⟩ = true :=
    okRounds_noDigest (okViewW_of_yields _ _ _ _ (play_yields _ _ _ _ _ hy)
      (by rw [hdl]; exact drawsFit_bare _ _ hd) okViewW_nil)
  -- the promise in front
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, ⟨hf, hP⟩, -, -, -, -⟩ := hT'
  have hu : s.failed = none := Option.isNone_iff_eq_none.1 hf
  -- five facts on every reached state
  obtain ⟨Lp, hLp⟩ := P5J.At.laid_some Zp h.opts.laid
  have FF := foldFacts_raw h.toAtMg
    (fun k (a : ProofFile.InstPub × TS) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
    (fun _ _ hr => hr) hLp (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  have Fo : VerifiableInference.Desc.Kinds.Head.Law.AtFold.FoldAt Lp
      (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1) h.𝔇.cs h.𝔇.shape
      (P5J.At.layout Zp) s :=
    ⟨FF.seatsCarried 341 (m.st.input.x.pub, s) hr hu, FF.msgShapes 341 _ hr hu,
      FF.codes 341 _ hr hu, FF.liveShape 341 _ hr hu, FF.liveLayout 341 _ hr hu⟩
  have hon' := k6_promise_behind h _ (honestLike_honest (mgAtAll h) _ test) M (by decide)
    (fun s t e => by
      show (s.out.reply == t.out.reply) = true
      rw [e]
      exact beq_self_eq_true _) hfl hstep hcan hr hLp Fo
    ((formP_iff (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 341
      (m.st.input.x.pub, s) noStrs).1 hP) (y' := noStrs)
  refine ⟨?_, ?_⟩
  · show s'.failed.isNone = true
    rw [K.1]
    rfl
  · show (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.formP (341 + 1)
      (y.2.st.input.x.pub, s')
    rw [ei]
    exact (formP_iff (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (341 + 1)
      (m.st.input.x.pub, s') noStrs).2 hon'

/-- **THE TABLE's TEST ON THE FORMS, BEHIND THE MEMBER's ACCEPTED STEP, AT THE THREAD**, AT EVERY
LETTER Kp. `k6_forms_behind` without hKp. CONDITIONAL: as the last. -/
theorem k6_forms_behind' :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      ∀ n, Law.K6Name n →
        VerifiableInference.Desc.K9.formsInT (h.𝔇.Rd 24) (h.𝔇.N.sent 24 0) 3 n s' = true := by
  intro blk hblk k s m E ds y cols s' hT hd hS
  obtain ⟨hf, hP⟩ := k6_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hblk k s
    m E ds y cols s' hT hd hS
  have hf' : s'.failed.isNone = true := hf
  exact forms_of_parts h (a := (y.2.st.input.x.pub, s'))
    (partsAt_of_formP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (341 + 1)
      (y.2.st.input.x.pub, s') hP (Option.isNone_iff_eq_none.1 hf'))

/-- **The same from the thread with a sentence Said beside it**: the binders of the debt on the
three items' share, in their order. `k6_forms_behindS` without hKp. CONDITIONAL: as the last; Said
is a letter, and nothing of it is spent. -/
theorem k6_forms_behindS'
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ blk k s m E ds y cols s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      ∀ n, Law.K6Name n →
        VerifiableInference.Desc.K9.formsInT (h.𝔇.Rd 24) (h.𝔇.N.sent 24 0) 3 n s' = true :=
  fun blk k s m E ds y cols s' hblk hT hd hS =>
    k6_forms_behind' h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hblk k s m E ds y cols s'
      hT.1 hd hS

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_form_behind
#print axioms ProofFile.Honest.K6.k6_forms_behind'
#print axioms ProofFile.Honest.K6.k6_forms_behindS'
