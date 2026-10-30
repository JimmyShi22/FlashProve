-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadStaysAll.lean: lemmas that gather the `StaysBy` lemmas of
HeadStays.lean, HeadStaysK3.lean and HeadStaysK11.lean. For four clauses of the list `csHead`
(CsHead.lean) about the output head's own part of the verifier's state, they say that the clause
survives every sub-protocol that lies inside its span, or every one up to number 346. A last lemma
gives, at the first chain's invariant at the full size (`lettersHead`, FirstHead.lean), the
hypothesis that all these lemmas share. No definition.

The five sub-protocols are, by their numbers in the first chain's list: 342, the sending of the
reads (kind K1); 343, the draw of the smallness test (K8); 344, a later commitment (K1); 345, the
lookup argument on the digits (K3); 346, the merge (K11). For each, a hypothesis says that the
`Thread`'s `keeps` at that number gives the kind's own clause.

  1  `staysBy_x_all`   "the field `x` is set", from border 342 to border 347: all five
  2  `staysBy_t_upto`   "the field `t` is set", from border 343 to border 348: the four up to 346
  3  `staysBy_fold0_all`, `staysBy_fold1_all`   "`tl.foldDrawn` is 0" (344 to 345) and "is 1" (346
     to 347): the one sub-protocol inside each span
  4  `head_hk`   at `lettersHead` with `keeps` given kind by kind (`kpBy f`, KeepsBy.lean): `keeps`
     at number `b` gives whatever the kind's clause `f κ p` gives at the place `p` of that number

Limits.
  * The hypotheses `h342` to `h346` are proved here at no `Thread`. `head_hk` reduces each to three
    facts: the place at that number, the place's kind, and what `f` gives there. No `f` is defined.
  * At 345 the clause that the kind's authors supply goes by the place and gives `K3KeepsHead` only
    under public facts on that place (HeadStaysK3.lean says which).
  * "The field `t` is set" also has to survive number 347, the batching. That is not covered.
  * The clauses on `wo`, on `F.next` and `st 24` are not covered.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadStays
import Johnson.Desc.ProofFile.Honest.Thread.HeadStaysK3
import Johnson.Desc.ProofFile.Honest.Thread.HeadStaysK11
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S HeadOwn)

section
variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- The clause "the field `x` is set", which holds from border 342 to border 347, survives each of
the five sub-protocols inside its span. -/
theorem staysBy_x_all {sh : OnBytes.Model.Forest.Shape}
    {P : Johnson.Desc.First.ForkMerge.HeadMergeP}
    (h342 : ∀ s s', T.keeps 342 s s' → ProofFile.Honest.K1.K1ReadsKeeps s s')
    (h343 : ∀ s s', T.keeps 343 s s' → VerifiableInference.Desc.First.K8.Honest.K8Keeps s s')
    (h344 : ∀ s s', T.keeps 344 s s' → ProofFile.Honest.K1.K1CommitKeeps s s')
    (h345 : ∀ s s', T.keeps 345 s s' → ProofFile.Honest.K3.Law.AtThr.K3KeepsHead sh s s')
    (h346 : ∀ s s', T.keeps 346 s s' → Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s') :
    ∀ b, 342 ≤ b → b + 1 ≤ 347 →
      StaysBy T b (riderHead 342 347 fun a => a.x.isSome = true) := by
  intro b h₁ h₂
  have hb : b = 342 ∨ b = 343 ∨ b = 344 ∨ b = 345 ∨ b = 346 := by omega
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact staysBy_x_reads T h342
  · exact staysBy_x_k8 T h343
  · exact staysBy_x_commit T h344
  · exact staysBy_x_k3 T h345
  · exact staysBy_x_k11 T h346

/-- The clause "the field `t` is set", which holds from border 343 to border 348, survives each of
the four sub-protocols from 343 to 346. -/
theorem staysBy_t_upto {sh : OnBytes.Model.Forest.Shape}
    {P : Johnson.Desc.First.ForkMerge.HeadMergeP}
    (h343 : ∀ s s', T.keeps 343 s s' → VerifiableInference.Desc.First.K8.Honest.K8Keeps s s')
    (h344 : ∀ s s', T.keeps 344 s s' → ProofFile.Honest.K1.K1CommitKeeps s s')
    (h345 : ∀ s s', T.keeps 345 s s' → ProofFile.Honest.K3.Law.AtThr.K3KeepsHead sh s s')
    (h346 : ∀ s s', T.keeps 346 s s' → Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s') :
    ∀ b, 343 ≤ b → b + 1 ≤ 347 →
      StaysBy T b (riderHead 343 348 fun a => a.t.isSome = true) := by
  intro b h₁ h₂
  have hb : b = 343 ∨ b = 344 ∨ b = 345 ∨ b = 346 := by omega
  rcases hb with rfl | rfl | rfl | rfl
  · exact staysBy_t_k8 T h343
  · exact staysBy_t_commit T h344
  · exact staysBy_t_k3 T h345
  · exact staysBy_t_k11 T h346

/-- The clause "`tl.foldDrawn` is 0", which holds at the borders 344 and 345, survives the one
sub-protocol inside its span. -/
theorem staysBy_fold0_all
    (h344 : ∀ s s', T.keeps 344 s s' → ProofFile.Honest.K1.K1CommitKeeps s s') :
    ∀ b, 344 ≤ b → b + 1 ≤ 345 →
      StaysBy T b (riderHead 344 345 fun a => a.tl.foldDrawn = 0) := by
  intro b h₁ h₂
  obtain rfl : b = 344 := by omega
  exact staysBy_fold_commit T h344

/-- The clause "`tl.foldDrawn` is 1", which holds at the borders 346 and 347, survives the one
sub-protocol inside its span. -/
theorem staysBy_fold1_all {P : Johnson.Desc.First.ForkMerge.HeadMergeP}
    (h346 : ∀ s s', T.keeps 346 s s' → Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s') :
    ∀ b, 346 ≤ b → b + 1 ≤ 347 →
      StaysBy T b (riderHead 346 347 fun a => a.tl.foldDrawn = 1) := by
  intro b h₁ h₂
  obtain rfl : b = 346 := by omega
  exact staysBy_fold_k11 T h346

end

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
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

/-- At `lettersHead` with `keeps` given kind by kind: if `p` is the place at number `b`, `κ` is its
kind, and the kind's clause `f κ p` gives `K`, then the `Thread`'s `keeps` at `b` gives `K`. -/
theorem head_hk {b : Nat} {p : Place} {κ : KindName} {K : TS → TS → Prop}
    (hp : P5J.At.ps[b]? = some p) (hκ : p.kind = κ) (hf : ∀ s s', f κ p s s' → K s s') :
    ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      K s s' :=
  fun s s' hk => hf s s' ((kpBy_at f hκ s s').1 (hk p hp))

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.staysBy_x_all
#print axioms ProofFile.Honest.staysBy_t_upto
#print axioms ProofFile.Honest.staysBy_fold0_all
#print axioms ProofFile.Honest.staysBy_fold1_all
#print axioms ProofFile.Honest.FirstThread.head_hk
