-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Behind.lean: BEHIND THE ACCEPTED STEP OF THE MEMBER "the output
head's own rounds" (K6; number 341 of the first chain's flat list): THE THREAD's FORM AND ITS CLAUSE
OF `keeps`, at the first chain's thread as it is laid at the library's hypothesis (`lettersHead`,
Honest/Thread/FirstHead.lean), at all its letters. Two theorems (`k6_form_keeps`,
`k6_form_keeps_by`) in the shape of the premise hFK of `behind_of_keeps` (Honest/Thread/Riders.lean)
and, through the first half of the pair, of `behindS_of_keepsS` (Honest/Thread/SharesS.lean). And
the debt itself: `k6_behindS`, `k6_behindS_sorts`, by `behindS_of_keeps_and`
(Honest/Thread/RidersAnd.lean): at that family the rider is the reply's clause beside the letter Rd,
so it is no list of clauses; at Rd := a list of clauses it has the form that this lemma takes, by
unfolding (`head_rides_and`). EVERY THEOREM IS CONDITIONAL.

HOW. A JOIN: calls alone. The promise behind: `k6_promise_behind`
(Johnson/Desc/K6/Honest/Law/BehindAtHead.lean). Its premises: the member's form at 341:
`P4.k6_member_at_mg` (Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean); the filling is like the closed
one: `honestLike_honest`, and the thread's clause on the promise is the library's promise:
`formP_iff` (Honest/Small/FormParts.lean); the state is reached: `thr_reach`, and five facts along
the fold: `foldFacts_raw` (Honest/Thread/ReachFacts.lean), whose two tests on public data are paid
at the hypothesis (`P5J.startB_at_head`, Johnson/P5J/StartAtHead.lean; `P5J.sendsB_of_madeRow`,
Johnson/P5J/FoldJ3.lean, with `P5J.madeRow_at_head`, Johnson/P5J/AtMgRAtHead.lean); every word of
the played rounds is below the prime: `okViewW_of_yields` (Honest/Law/Play.lean) with
`okRounds_noDigest` (Honest/Thread/SaidOk.lean); the list of seats is laid: `P5J.At.laid_some`. No
mark behind, and `keeps`: `K6Keeps` (Johnson/Desc/K6/Honest/Law/Keeps.lean) by
`k6_keeps_of_member_step`, through hKp and `head_keeps`.

WHAT IS LEFT AS PREMISES: the hypothesis h; hKp: the letter Kp at the sub-protocol's place holds
wherever `K6Keeps` does. Of the debt's own premises all three are spent: the thread in front, "the
challenges fit", the step. Of `k6_behindS` besides: hb₀: the border from which on the state holds
the reply that the instance asks about (b₀ is a letter of that family; by its makers' word it is
meant to be the border behind the one place that hears the reply, which stands in front of this one)
is not 342 (this member hears no reply; past it the reply is as it was, by `K6Keeps`:
`head_reply_next`); hst: each clause that speaks on both sides of the member stays past it (whoever
lays the thread pays it, out of the clause of `keeps`; for three sorts of clause
Honest/K6/Law/Stays.lean has it); hl: a clause that begins right behind the member is the one that
`k6_lays` (Honest/K6/Law/Lays.lean) pays, or comes with its own payer. At the empty list of clauses
hst and hl hold idly: so on the rider's side the premises can be met together, and there the
statement says least. `k6_behindS_sorts` pays hst where each such clause is of one of four sorts
(`K6Stays`), with hf both ways.

ON THE PREMISE hKp. It runs from `K6Keeps` to the letter: a yes must GIVE the thread's clause. What
Honest/K6/Law/Stays.lean shows on what stays past this member takes the other direction. Together
they say that at this place the letter IS `K6Keeps`, up to "if and only if": a weaker letter meets
this law and starves those; a stronger one the reverse. Where the letter is laid by the place's kind
(`kpBy`), the thread's clause at this member is the kind's own, both ways (`head_keeps_kind`,
Honest/Thread/KeepsBy.lean): `k6_form_keeps_by`; at f .K6 := fun _ => K6Keeps both directions hold
by definition.

Limits. THE FULL SIZE ALONE, and at that family of threads alone: the thread is no variable here.
The hypothesis h is met under the four premises of the library's `P5J.head_exists_at_name`
(Johnson/P5J/HeadExistsAtName.lean: in scope; the files are read; the verifier's own three values
are laid; one condition more); by that file's own limits the first three are evaluated
true at the release's full-size files (runs, no theorem), and of the fourth nothing is said.
 What is there stands at two named values of the letters D and r; here both are letters. That
the thread holds at any stand is shown by nobody here. Among what this file imports are modules
under lean/Johnson/Goal/: it imports no module of that folder by name and calls nothing that is
declared there: they lie beneath the library's files that it calls. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd
import Johnson.Desc.ProofFile.Honest.Small.FormParts
import Johnson.Desc.K6.Honest.Law.BehindAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.Lays
import Johnson.Desc.ProofFile.Honest.K6.Law.Stays
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.P5J.StartAtHead
import Johnson.P5J.AtMgRAtHead

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

/-- **BEHIND THE MEMBER's ACCEPTED STEP: THE FORM, AND THE THREAD's CLAUSE OF `keeps`**, at the
first chain's thread as it is laid at the library's hypothesis. CONDITIONAL: the hypothesis h; hKp:
the letter Kp at the sub-protocol's place holds wherever `K6Keeps` does. -/
theorem k6_form_keeps (hKp : ∀ s s', K6Keeps s s' → Kp plK6 s s') :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (341 + 1) k s' y.2 ∧
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 341 s s' := by
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
  refine ⟨⟨?_, ?_⟩, (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w k6_at341 s s').2
    (hKp s s' K)⟩
  · show s'.failed.isNone = true
    rw [K.1]
    rfl
  · show (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.formP (341 + 1)
      (y.2.st.input.x.pub, s')
    rw [ei]
    exact (formP_iff (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (341 + 1)
      (m.st.input.x.pub, s') noStrs).2 hon'

/-- **The same where the letter is laid by the place's kind** (`kpBy`, Honest/Thread/KeepsBy.lean).
CONDITIONAL: the hypothesis h; hf: the kind's clause holds wherever `K6Keeps` does. -/
theorem k6_form_keeps_by (f : VerifiableInference.Desc.KindName → Place → TS → TS → Prop)
    (hf : ∀ s s', K6Keeps s s' → f .K6 plK6 s s') :
    ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.bs[341]? = some blk →
      ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.Stepped blk k s m E ds y
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.Form (341 + 1) k s'
          y.2 ∧
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps 341 s s' :=
  k6_form_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hf

/-- **THE DEBT `BehindS` AT THE MEMBER**, at the first chain's thread as it is laid at the library's
hypothesis, with the rider's letter a list of clauses and the letter for `keeps` laid by the place's
kind; Said is a variable. CONDITIONAL: the hypothesis h; hf; hb₀: the border from which the state
holds the reply that the instance asks about is not the one right behind this member, which hears no
reply; hst: each clause that speaks on both sides of the member stays past it; hl: a clause that
begins right behind the member is "what the head's rounds have heard is laid", or is laid by the
member. -/
theorem k6_behindS (f : VerifiableInference.Desc.KindName → Place → TS → TS → Prop)
    (hf : ∀ s s', K6Keeps s s' → f .K6 plK6 s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS)) (hb₀ : b₀ ≠ 341 + 1)
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
      k6_form_keeps_by h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) w f hf blk hblk k s m E ds
        y cols s' hA.1 hd hS)
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

/-- A clause of one of the four sorts that Honest/K6/Law/Stays.lean carries past this member. It is
a definition: a premise's form. -/
def K6Stays {W : Type} (c : RiderCl W TS) : Prop :=
  (∃ lo hi, ∃ P : VerifiableInference.Desc.First.HeadOwn → Prop, c = riderHead lo hi P ∧
    ∀ (o : VerifiableInference.Desc.First.HeadOwn) (F : OnBytes.Model.Fork) x q,
      P o → P { o with F := F, x := x, squaresP := q }) ∨
  (∃ lo hi, c = riderHead lo hi fun a => OnBytes.PscRun.Sized a.F) ∨
  (∃ lo hi, ∃ n : Nat → Nat, c = riderPile lo hi n ∧ n (341 + 1) = n 341) ∨
  ∃ lo hi fvs kCol, c = riderRoom lo hi fvs kCol

/-- **THE DEBT, WITH "IT STAYS" PAID AT FOUR SORTS OF CLAUSE.** CONDITIONAL: as `k6_behindS`, with
hf both ways (at this place the kind's clause IS `K6Keeps`), and, for hst: hcs: each clause that
speaks on both sides of the member is of one of the four sorts. -/
theorem k6_behindS_sorts (f : VerifiableInference.Desc.KindName → Place → TS → TS → Prop)
    (hf : ∀ s s', f .K6 plK6 s s' ↔ K6Keeps s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS)) (hb₀ : b₀ ≠ 341 + 1)
    (hcs : ∀ c ∈ cs, c.lo ≤ 341 → 341 + 1 ≤ c.hi → K6Stays c)
    (hl : ∀ c ∈ cs, c.lo = 341 + 1 →
      (∃ hi, c = riderHead (341 + 1) hi fun o => o.x.isSome = true) ∨ LaysAtS
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w).thread Said 341
        c) :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w).thread Said
      341 := by
  have hk : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w).thread.keeps 341 s
        s' → K6Keeps s s' := fun s s' hK =>
    (hf s s').1
      ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w k6_at341 s s').1 hK)
  refine k6_behindS h H Q test carryX item n₁ n₂ b₀ Vd w f (fun s s' K => (hf s s').2 K) Said cs
    hb₀ (fun c hc h1 h2 => ?_) hl
  rcases hcs c hc h1 h2 with ⟨lo, hi, P, rfl, hP⟩ | ⟨lo, hi, rfl⟩ | ⟨lo, hi, n, rfl, hn⟩ |
    ⟨lo, hi, fvs, kCol, rfl⟩
  · exact k6_staysBy_head _ hk hP
  · exact k6_staysBy_sized _ hk
  · exact k6_staysBy_pile _ hk hn
  · exact k6_staysBy_room _ hk

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_form_keeps
#print axioms ProofFile.Honest.K6.k6_form_keeps_by
#print axioms ProofFile.Honest.K6.k6_behindS
#print axioms ProofFile.Honest.K6.k6_behindS_sorts
