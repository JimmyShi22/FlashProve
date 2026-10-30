-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/KeepsBy.lean: the parameter `Kp` of the first chain's `Thread`,
defined by the place's kind. `lettersHead` (Honest/Thread/FirstHead.lean) defines `keeps` by the
sub-protocol's place, through a parameter Kp : Place → S → S → Prop. Each kind's author supplies its
kind's clause in one form: a function of the place (its public parameters are computed from the
place) and of the two states. Here is the one term that joins them: at a place of kind κ the clause
is that kind's own, and no other kind's clause is beside it: so at a sub-protocol of kind κ "keeps"
is that kind's clause at the sub-protocol's place, in both directions: `Behind` for a kind uses the
one direction and `RidesPast` the other. One definition, a term; two equivalences.

  `kpBy`   the term
  `kpBy_at`   at a place of kind κ it is κ's clause
  `head_keeps_kind`   the same at a sub-protocol of the `Thread` of `lettersHead`

Why by the kind and not as a conjunction of all kinds' clauses (`k3KeepsAt`, of the authors of K3's
lemmas, not in the sealed library, fits either): under a conjunction a kind's `Behind` would owe
every other kind's clause at its own place, each by a lemma "it says nothing there".

Limits.
  * The family f stays a parameter: no kind's clause is named here.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName)

/-- **`keeps` by the place's kind.** `f κ`: the clause of the kind κ, a function of the place. -/
def kpBy {S : Type} (f : KindName → Place → S → S → Prop) : Place → S → S → Prop :=
  fun p => f p.kind p

theorem kpBy_at {S : Type} (f : KindName → Place → S → S → Prop) {p : Place} {κ : KindName}
    (h : p.kind = κ) (s s' : S) : kpBy f p s s' ↔ f κ p s s' := by
  subst h
  exact Iff.rfl

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit Block)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **At a sub-protocol of kind κ `keeps` is κ's clause at the sub-protocol's place.** -/
theorem head_keeps_kind {b : Nat} {blk : Block TS ProofFile.Cl} {κ : KindName}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.bs[b]? = some blk)
    (hκ : blk.place.kind = κ) (s s' : TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).keeps b s s' ↔
      f κ blk.place s s' :=
  (head_keepsAt h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hb s s').trans
    (kpBy_at f hκ s s')

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.kpBy_at
#print axioms ProofFile.Honest.FirstThread.head_keeps_kind
