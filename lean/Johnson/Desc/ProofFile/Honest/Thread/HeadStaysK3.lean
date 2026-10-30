-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadStaysK3.lean: lemmas of the form `StaysBy` (Riders.lean)
for rider clauses about the output head's own part of the verifier's state, at the lookup argument
on the digits in the head's segment (kind K3). They continue HeadStays.lean, which covers the three
sub-protocols before it. No definition.

The clause of `keeps` for this sub-protocol is `K3KeepsHead` (Honest/K3/Law/Thread/K3Keeps.lean).
It writes the state after the step out: of
the head's own part only the fields `tl`, `F` and `claim` change. The file stands apart from
HeadStays.lean because `K3KeepsHead`'s file depends on many other files.

  1  `head_k3`   what `K3KeepsHead` says of the head's own part
  2  `staysBy_head_k3`   for any fact `P` that reads none of the three fields
  3  `staysBy_x_k3`, `staysBy_t_k3`   the clauses of `csHead` (CsHead.lean) on the fields `x` and
     `t`

Limits.
  * Each `StaysBy` lemma has the hypothesis `hk`: the thread's `keeps` at `b` gives `K3KeepsHead`.
    It is not proved here at any thread.
  * `K3KeepsHead` is not the clause that its authors supply for `keeps`. That one goes by the place:
    `k3KeepsAt Z p` (Honest/K3/Law/Thread/K3KeepsAt.lean). It gives `K3KeepsHead` only if a site of
    `lookSites Z` is at `p`, is on the digits, and the step without a round after it has the form
    `quietHead` (`k3KeepsAt_head`). These three public facts are not proved here. If no site is at
    `p`, `k3KeepsAt Z p` holds of every pair of states, and `hk` cannot be proved.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersStayH
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S HeadOwn)

/-- After the lookup argument on the digits in the head's segment, the head's own part is the one
before it with the fields `tl`, `F` and `claim` changed. -/
theorem head_k3 {h : OnBytes.Model.Forest.Shape} {s s' : S}
    (hK : ProofFile.Honest.K3.Law.AtThr.K3KeepsHead h s s') :
    ∀ a, s.here = .head a →
      ∃ tl' G c, s'.here = .head { a with tl := tl', F := G, claim := some c } := by
  obtain ⟨-, tl, F, H, G, a₀, c, -, -, h0, -, rfl, -⟩ := hK
  intro a ha
  obtain rfl : a₀ = a := VerifiableInference.Desc.First.Here.head.inj (h0.symm.trans ha)
  exact ⟨_, G, c, rfl⟩

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- A fact `P` on the head's own part survives that sub-protocol, if `P` reads none of the fields
`tl`, `F` and `claim`. -/
theorem staysBy_head_k3 {h : OnBytes.Model.Forest.Shape} {b lo hi : Nat} {P : HeadOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → ProofFile.Honest.K3.Law.AtThr.K3KeepsHead h s s')
    (hP : ∀ a tl' G c, P a → P { a with tl := tl', F := G, claim := some c }) :
    StaysBy T b (riderHead lo hi P) :=
  staysBy_head_of T fun s s' hK a ha =>
    let ⟨tl', G, c, e⟩ := head_k3 (hk s s' hK) a ha
    ⟨_, e, hP a tl' G c⟩

/-- The clause "the field `x` is set" survives that sub-protocol. -/
theorem staysBy_x_k3 {h : OnBytes.Model.Forest.Shape} {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → ProofFile.Honest.K3.Law.AtThr.K3KeepsHead h s s') :
    StaysBy T b (riderHead lo hi fun a => a.x.isSome = true) :=
  staysBy_head_k3 T hk fun _ _ _ _ h => h

/-- The clause "the field `t` is set" survives that sub-protocol. -/
theorem staysBy_t_k3 {h : OnBytes.Model.Forest.Shape} {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → ProofFile.Honest.K3.Law.AtThr.K3KeepsHead h s s') :
    StaysBy T b (riderHead lo hi fun a => a.t.isSome = true) :=
  staysBy_head_k3 T hk fun _ _ _ _ h => h

end ProofFile.Honest

#print axioms ProofFile.Honest.head_k3
#print axioms ProofFile.Honest.staysBy_head_k3
#print axioms ProofFile.Honest.staysBy_x_k3
#print axioms ProofFile.Honest.staysBy_t_k3
