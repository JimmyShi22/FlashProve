-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/FormsBehind.lean: BEHIND THE ACCEPTED STEP OF THE OUTPUT HEAD's
OWN SUB-PROTOCOL THE TABLE's TEST ON THE FORMS ACCEPTS AT EACH OF THE HEAD's FOUR RUNS: read off the
promise behind.

What the file holds. `forms_of_parts`: where the promise's clauses hold at border 342, at the
library's closed meaning: the test `K9.formsInT` accepts at "norm", "policy", "logits" and "join".
It is the converse of the library's `made_own` and `made_join`
(Johnson/Desc/Kinds/Law/K6FormsMade.lean): the two public tests formsInT 24 4 "own" and "join",
which are open at 342 (`open342`, Kinds/Law/K6PubKept.lean), ARE these four answers, by
`pubAll_formsInT` (Johnson/Desc/First/PubAllAt.lean) and the two lists of runs (`runs_at_head`,
Kinds/Law/K6PubMore.lean). The library makes the same move at another sub-protocol's run "objects"
(`hIn_plus`, Johnson/Desc/First/Att/Door/Law/K5LeftSmall.lean). `k6_forms_behind`,
`k6_forms_behind_by`, `k6_forms_behindS`, `k6_forms_behindS_by`: at the first chain's thread as it
is laid at the library's hypothesis, behind the member's step: by `k6_form_keeps`
(Honest/K6/Law/Behind.lean) and `partsAt_of_formP` (Honest/Small/FormParts.lean).

Limits. THE FULL SIZE ALONE, and at that family of threads alone. The hypothesis h and the premise
on the letter for `keeps` are those of Honest/K6/Law/Behind.lean. It is shown of no step that the
member accepts it, nor that the thread holds at any stand. Modules under lean/Johnson/Goal/ are
among what this file imports: it imports no module of that folder by name; by a reader's program on
names its text names nothing that is declared there: a comparison of text, which proves no absence.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.Behind
import Johnson.Desc.Kinds.Law.K6FormsMade
import Johnson.Desc.Kinds.Law.K6PubKept
import Johnson.Desc.Kinds.Law.K6PubMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (Pub pubOfItems)
open VerifiableInference.Desc.Sound (MsgT mgBase mgMore openQ pubQ)
open VerifiableInference.Desc.Kinds.Head (Law.K6Name)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps plK6)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS mgAtAll)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.Small (PartsAt partsAt_of_formP)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE FOUR ANSWERS, OFF THE PROMISE's CLAUSES AT BORDER 342.** CONDITIONAL: the hypothesis h;
the clauses hold of the pair. -/
theorem forms_of_parts {a : ProofFile.InstPub × TS}
    (Pa : PartsAt (P5J.At.N Zp cF) (mgAtAll h) P5J.At.links P5J.At.ps (341 + 1) a) :
    ∀ n, Law.K6Name n →
      VerifiableInference.Desc.K9.formsInT (h.𝔇.Rd 24) (h.𝔇.N.sent 24 0) 3 n a.2 = true := by
  obtain ⟨Lk, hl, -⟩ := P4.six_at_head h
  have Pd := VerifiableInference.Desc.Kinds.Head.Law.AtTable.paid_at_const h Lk hl
  obtain ⟨-, -, rj, ro, -⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.AtTable.runs_at_head h.𝔇 Pd.sorts
  have hm : (mgAtAll h).more = mgMore := VerifiableInference.Desc.Sound.mgAll_more_base h.𝔇
  have h342 : pubQ mgMore P5J.At.links P5J.At.ps (341 + 1) ++
      pubOfItems (openQ P5J.At.links P5J.At.ps (341 + 1)) = _ :=
    VerifiableInference.Desc.Kinds.Head.Law.AtTable.open342
  have hown := Pa.pub (.formsInT 24 4 "own") (by rw [hm, h342]; simp)
  have hjoin := Pa.pub (.formsInT 24 4 "join") (by rw [hm, h342]; simp)
  have hp : (mgAtAll h).pub = _ := VerifiableInference.Desc.Sound.mgAll_pub h.𝔇 mgBase
  rw [hp, VerifiableInference.Desc.First.pubAll_formsInT] at hown hjoin
  have eo : h.𝔇.pubD.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")] := ro
  have ej : h.𝔇.pubD.runs 24 4 "join" = [(3, "join")] := rj
  rw [eo] at hown
  rw [ej] at hjoin
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hown hjoin
  intro n hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact hown.1
  · exact hown.2.1
  · exact hown.2.2
  · exact hjoin

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **BEHIND THE MEMBER's ACCEPTED STEP, AT THE THREAD.** CONDITIONAL: the hypothesis h; hKp: the
letter Kp at the sub-protocol's place holds wherever `K6Keeps` does; the thread in front; the
challenges fit; the step. -/
theorem k6_forms_behind (hKp : ∀ s s', K6Keeps s s' → Kp plK6 s s') :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[341]? = some blk →
      ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' →
      ∀ n, Law.K6Name n →
        VerifiableInference.Desc.K9.formsInT (h.𝔇.Rd 24) (h.𝔇.N.sent 24 0) 3 n s' = true := by
  intro blk hblk k s m E ds y cols s' hT hd hS
  obtain ⟨⟨hf, hP⟩, -⟩ := k6_form_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hKp blk hblk k s
    m E ds y cols s' hT hd hS
  have hf' : s'.failed.isNone = true := hf
  exact forms_of_parts h (a := (y.2.st.input.x.pub, s'))
    (partsAt_of_formP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (341 + 1)
      (y.2.st.input.x.pub, s') hP (Option.isNone_iff_eq_none.1 hf'))

/-- **The same where the letter is laid by the place's kind** (`kpBy`, Honest/Thread/KeepsBy.lean).
CONDITIONAL: as the last, with hf: the kind's clause holds wherever `K6Keeps` does. -/
theorem k6_forms_behind_by (f : VerifiableInference.Desc.KindName → Place → TS → TS → Prop)
    (hf : ∀ s s', K6Keeps s s' → f .K6 plK6 s s') :
    ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.bs[341]? = some blk →
      ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.Stepped blk k s m E ds y
        cols s' →
      ∀ n, Law.K6Name n →
        VerifiableInference.Desc.K9.formsInT (h.𝔇.Rd 24) (h.𝔇.N.sent 24 0) 3 n s' = true :=
  k6_forms_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hf

/-- **The same from the thread with a sentence Said beside it**: the binders of the debt on the
three items' share, in their order. CONDITIONAL: as `k6_forms_behind`; Said is a letter, and nothing
of it is spent. -/
theorem k6_forms_behindS (hKp : ∀ s s', K6Keeps s s' → Kp plK6 s s')
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
    k6_forms_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hKp blk hblk k s m E ds y cols s'
      hT.1 hd hS

/-- **And there, where the letter is laid by the place's kind.** CONDITIONAL: as the last, with hf.
-/
theorem k6_forms_behindS_by (f : VerifiableInference.Desc.KindName → Place → TS → TS → Prop)
    (hf : ∀ s s', K6Keeps s s' → f .K6 plK6 s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ blk k s m E ds y cols s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.bs[341]? = some blk →
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said 341 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.Stepped blk k s m E ds y
        cols s' →
      ∀ n, Law.K6Name n →
        VerifiableInference.Desc.K9.formsInT (h.𝔇.Rd 24) (h.𝔇.N.sent 24 0) 3 n s' = true :=
  k6_forms_behindS h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hf Said

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.forms_of_parts
#print axioms ProofFile.Honest.K6.k6_forms_behind
#print axioms ProofFile.Honest.K6.k6_forms_behind_by
#print axioms ProofFile.Honest.K6.k6_forms_behindS
#print axioms ProofFile.Honest.K6.k6_forms_behindS_by
