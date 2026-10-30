-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean: the first chain's parameters under the
library's hypothesis `AtMgA`, with what has a definition supplied, as a family in the run's input.
`lettersAt` (Honest/Thread/FirstAt.lean) leaves twelve arguments besides the hypothesis. Here six of
them get their definition or their form. The prover's sides are a prover's own. The stored table's
columns are that prover's. A pin says `ansJT` at the hypothesis's own parameters
(Honest/Thread/Ans.lean). `valid` is "the input is this run's" and a parameter. `rides` is the
reply's clause and a parameter. `keeps` goes by the sub-protocol's place, a parameter by place: each
kind's clause at its own sub-protocol. The `Script` stays a parameter: what a kind's author uses of
it is a hypothesis of that author's. One definition; and equations by unfolding, in the forms in
which the kinds' structures of hypotheses ask for them.

  `lettersHead`   the term
  `head_valid`, `head_reply`, `head_rest`, `head_keeps`, `head_pin`, `head_stored`,
                  `head_form`   what each parameter is there: by unfolding
  `sits_head`     the five equations of `Sits.one`

The parameters that are left. `Q`: the `Script`. `test`: for each segment the fall that is placed
after its batching. `carryX`: the exact carry. `item`, `n₁`, `n₂`: three numbers of the plan. `b₀`:
the border after the sub-protocol that hears the reply. `Vd`: what else an input must satisfy for
something to be stated of it. `Rd`: the riders besides the reply's. `Kp`: the clauses of `keeps`, by
place.

Limits.
  * The full size alone, and the hash function `secondHashFunction` alone (Honest/Thread/FirstAt.lean says which
    that is).
  * A term of the library's hypothesis `AtMgA` exists at the name under four hypotheses on the
    public files (the library's `head_exists_at_name`); this file does not call it, and it proves of
    no such term that the invariant holds at a run.
  * It is not proved that the invariant holds at any run.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstSits
import Johnson.Desc.ProofFile.Honest.Thread.Ans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The first chain's parameters under the hypothesis `AtMgA`, at a run's input `w`.** -/
noncomputable def lettersHead (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) :
    Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT :=
  lettersAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
    (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)) test carryX item
    n₁ n₂ (fun v => v = w ∧ Vd v)
    (fun b v s => (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ Rd b v s)
    (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → Kp p s s')

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

theorem head_valid (v : Local W₀ Rc ProofFile.Inst Tr) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).valid v ↔ v = w ∧ Vd v := Iff.rfl

/-- From the border `b₀` on, the reply that the state holds is the one that the instance asks about.
-/
theorem head_reply {b : Nat} {v : Local W₀ Rc ProofFile.Inst Tr} {s : TS} (hb : b₀ ≤ b)
    (hr : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).rides b v s) :
    s.out.reply = some v.x.asked := hr.1 hb

theorem head_rest {b : Nat} {v : Local W₀ Rc ProofFile.Inst Tr} {s : TS} :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).rides b v s ↔
      (b₀ ≤ b → s.out.reply = some v.x.asked) ∧ Rd b v s := Iff.rfl

/-- At a border whose place is written, `keeps` is that place's clause. -/
theorem head_keeps {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) (s s' : TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).keeps b s s' ↔ Kp p s s' :=
  ⟨fun k => k p hp, fun k q hq => by
    have e : q = p := Option.some.inj (hq.symm.trans hp)
    rw [e]
    exact k⟩

theorem head_pin (v : Local W₀ Rc ProofFile.Inst Tr) :
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v).pin =
      ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) := rfl

theorem head_stored (v : Local W₀ Rc ProofFile.Inst Tr) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.stored v =
      H.storedWords v.w₀ v.rc := rfl

/-- The `form` of the `Thread` is "no mark" (`failed.isNone`). -/
theorem head_form (b : Nat) (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.form b a =
      a.2.failed.isNone := rfl

/-- **The first clause of `Sits`.** -/
theorem sits_head :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.φ = .own ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain = 0 ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ft = 0 ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs =
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ∧
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs = H.first :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_valid
#print axioms ProofFile.Honest.FirstThread.head_reply
#print axioms ProofFile.Honest.FirstThread.head_rest
#print axioms ProofFile.Honest.FirstThread.head_keeps
#print axioms ProofFile.Honest.FirstThread.head_pin
#print axioms ProofFile.Honest.FirstThread.head_stored
#print axioms ProofFile.Honest.FirstThread.head_form
#print axioms ProofFile.Honest.FirstThread.sits_head
