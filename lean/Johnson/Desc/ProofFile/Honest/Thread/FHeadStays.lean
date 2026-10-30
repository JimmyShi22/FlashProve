-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadStays.lean: two hypotheses of `csHead_stays`
(GatherStays.lean), `hatt` and `hlay`, at the first chain's invariant at the full size with `keeps`
given by `fHead` (FHead.lean). `head_hatt` and `head_hlay` (HeadKeepsAt.lean) bring them down to
facts on the clause of each kind at its place. Here these facts come from the clauses themselves:
`attG_k5`, `attG_reads`, `attG_k8`, `attG_commit` (AttGStays.lean), `layOwn_reads`, `layOwn_k8`,
`layOwn_commit` (LayOwnStays.lean), `attG_k3`, `layOwn_k3` (K3Stays.lean). No definition.

  1  `fHead_hatt`   the field `g` of an attention segment's part of the state stays over the five
     sub-protocols from K5 to the lookup on the digits
  2  `fHead_hlay`   the field `own` of a feed-forward segment's part stays over the five from K1's
     sending of the reads to the batching

What they leave as hypotheses.
  * `hA`: the public input has an attention plan for each of the 12 groups.
  * `h3`, `h3'`: at the place of the lookup on the digits, the clause by the place gives the clause
    `K3KeepsDigits`. The authors of K3's lemmas prove this from two public conditions
    (`k3KeepsAt_digits`, `site_there_head`). It is not joined here.
  * `hB`: `own` stays over the batching. No lemma proves this yet.

Limits.
  * Conditional lemmas on this folder's own definitions.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadKeepsAt
import Johnson.Desc.ProofFile.Honest.Thread.AttGStays
import Johnson.Desc.ProofFile.Honest.Thread.LayOwnStays
import Johnson.Desc.ProofFile.Honest.Thread.K3Stays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K1 (K1ReadsKeepsM K1CommitKeepsM)
open ProofFile.Honest.K3.Law.AtThr (k3KeepsAt K3KeepsDigits)
open VerifiableInference.Desc.First.K8.Honest (K8KeepsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The hypothesis `hatt` of `csHead_stays`, at `fHead`. -/
theorem fHead_hatt (hA : ∀ g, g < 12 → ∃ a, (P5J.At.X Zp).A[g]? = some a)
    (h3 : ∀ g, g < 12 → ∃ sh claims, ∀ s s',
      k3KeepsAt Zp { chain := 1, link := some (2 * g + 1), piece := 7, kind := .K3 } s s' →
      K3KeepsDigits sh claims s s') :
    ∀ g, g < 12 → ∀ b, 14 * (2 * g + 1) + 4 ≤ b → b + 1 ≤ 14 * (2 * g + 1) + 9 →
      ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps b s s' →
      ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g := by
  refine head_hatt h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (fHead Zp cF G take P11 p12 P13) w ?_
  intro g hg i k hi2 hi6 hk s s' hf
  have hi : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · obtain rfl : KindName.K5 = k := Option.some.inj hk
    obtain ⟨a, ha⟩ := hA g hg
    exact attG_k5 ((H2K5.Honest.k5KeepsAt_iff ha s s').1 hf)
  · obtain rfl : KindName.K1 = k := Option.some.inj hk
    have hf' : K1ReadsKeepsM s s' :=
      (fHead_K1_later Zp cF G take P11 p12 P13
        (p := { chain := 1, link := some (2 * g + 1), piece := 3 + 1, kind := .K1 })
        (l := 2 * g + 1) rfl
        (show (3 + 1 : Nat) ≠ 1 by decide) s s').1 hf |>.1
    exact attG_reads hf'.1
  · obtain rfl : KindName.K8 = k := Option.some.inj hk
    have hf' : K8KeepsM s s' := hf
    exact attG_k8 hf'.1
  · obtain rfl : KindName.K1 = k := Option.some.inj hk
    have hf' : K1CommitKeepsM s s' :=
      (fHead_K1_later Zp cF G take P11 p12 P13
        (p := { chain := 1, link := some (2 * g + 1), piece := 5 + 1, kind := .K1 })
        (l := 2 * g + 1) rfl
        (show (5 + 1 : Nat) ≠ 1 by decide) s s').1 hf |>.1
    exact attG_commit hf'.1
  · obtain rfl : KindName.K3 = k := Option.some.inj hk
    obtain ⟨sh, claims, h3'⟩ := h3 g hg
    exact attG_k3 (h3' s s' hf)

/-- The hypothesis `hlay` of `csHead_stays`, at `fHead`. -/
theorem fHead_hlay
    (h3 : ∀ g, g < 12 → ∃ sh claims, ∀ s s',
      k3KeepsAt Zp { chain := 1, link := some (2 * g), piece := 7, kind := .K3 } s s' →
      K3KeepsDigits sh claims s s')
    (hB : ∀ g, g < 12 → ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps (28 * g + 9) s s' →
      ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own) :
    ∀ g, g < 12 → ∀ b, 28 * g + 5 ≤ b → b + 1 ≤ 28 * g + 10 →
      ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps b s s' →
      ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  refine head_hlay h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (fHead Zp cF G take P11 p12 P13) w ?_ hB
  intro g hg i k hi3 hi6 hk s s' hf
  have hi : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · obtain rfl : KindName.K1 = k := Option.some.inj hk
    have hf' : K1ReadsKeepsM s s' :=
      (fHead_K1_later Zp cF G take P11 p12 P13
        (p := { chain := 1, link := some (2 * g), piece := 3 + 1, kind := .K1 }) (l := 2 * g) rfl
        (show (3 + 1 : Nat) ≠ 1 by decide) s s').1 hf |>.1
    exact layOwn_reads hf'.1
  · obtain rfl : KindName.K8 = k := Option.some.inj hk
    have hf' : K8KeepsM s s' := hf
    exact layOwn_k8 hf'.1
  · obtain rfl : KindName.K1 = k := Option.some.inj hk
    have hf' : K1CommitKeepsM s s' :=
      (fHead_K1_later Zp cF G take P11 p12 P13
        (p := { chain := 1, link := some (2 * g), piece := 5 + 1, kind := .K1 }) (l := 2 * g) rfl
        (show (5 + 1 : Nat) ≠ 1 by decide) s s').1 hf |>.1
    exact layOwn_commit hf'.1
  · obtain rfl : KindName.K3 = k := Option.some.inj hk
    obtain ⟨sh, claims, h3'⟩ := h3 g hg
    exact layOwn_k3 (h3' s s' hf)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_hatt
#print axioms ProofFile.Honest.FirstThread.fHead_hlay
