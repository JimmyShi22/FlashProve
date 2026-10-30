-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadStaysAll.lean: the column `hst` of the gathering
(`owesS_head_form`, GatherHeadForm.lean) at the rider clauses `csHead` (CsHead.lean) and at `f :=
fHead` (FHead.lean): every clause survives every sub-protocol inside its span. `csHead_stays`
(GatherStays.lean) asks eight families of hypotheses. Here each is proved from the clause of `fHead`
at the sub-protocol's place. The pieces are FHeadStays.lean, HeadStaysAll.lean,
Law/NoHouse/BackStays.lean, and three files of the authors of K3's lemmas
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RngHead.lean, QuietAtLink.lean, QuietAtHeadLink.lean).
No definition.

  1  `fHead_h3`, `fHead_h3H`   at the place of a lookup on the digits, K3's clause by place gives
     the clause of that sort of lookup
  2  `fHead_hA`   the public part has the twelve attention plans
  3  `fHead_hst`   the column `hst`

What `fHead_hst` leaves as hypotheses.
  * `hW`: `rngWrittenB = true`, a test without a free variable on the written table of stretches.
    RngHead.lean evaluates it in a `#guard` line. Its authors say that the kernel does not get
    through its evaluation, so it is not proved.
  * `hσ`: the argument `st` of `csHead` at segment 24 survives whatever `K11Keeps` allows.

Limits.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadStays
import Johnson.Desc.ProofFile.Honest.Thread.GatherStays
import Johnson.Desc.ProofFile.Honest.Thread.HeadStaysAll
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BackStays
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietAtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietAtHeadLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (kindsBeforeBatching)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K3.Law.AtThr (k3KeepsAt K3KeepsDigits K3KeepsHead rngWrittenB site_digits_of
  quiet_digits_head quiet_attention_head quiet_head_head)
open ProofFile.Honest.K1 (K1ReadsKeepsM K1CommitKeepsM)
open VerifiableInference.Desc.First.K8.Honest (K8KeepsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h

/-- At the lookup on the digits of a segment other than the output head's. -/
theorem fHead_h3 (hW : rngWrittenB = true) {l : Nat} (hl : l < 24) :
    ∃ sh claims, ∀ s s',
      k3KeepsAt Zp { chain := 1, link := some l, piece := 7, kind := .K3 } s s' →
      K3KeepsDigits sh claims s s' := by
  obtain ⟨t, ht, e1, e2, e3, -⟩ := site_digits_of h hW l (by omega) true
  obtain ⟨used, claims, hq⟩ := quiet_digits_head h l hl
  refine ⟨t.shape, claims, fun s s' hk => ?_⟩
  have hp : t.at_.place = { chain := 1, link := some l, piece := 7, kind := .K3 } := by
    rw [e3]
    show ({ chain := 1, link := some l, piece := (6 + if l = 24 then 1 else 0) + 1, kind := .K3 } :
      Place) = _
    rw [if_neg (show ¬ l = 24 by omega)]
  exact (hk t ht hp).2.2.1 e2 used claims (by rw [e1]; exact hq)

/-- At the lookup on the digits of the output head's segment. -/
theorem fHead_h3H (hW : rngWrittenB = true) :
    ∃ sh, ∀ s s', k3KeepsAt Zp { chain := 1, link := some 24, piece := 7 + 1, kind := .K3 } s s' →
      K3KeepsHead sh s s' := by
  obtain ⟨t, ht, e1, e2, e3, -⟩ := site_digits_of h hW 24 (by decide) true
  refine ⟨t.shape, fun s s' hk => ?_⟩
  have hp : t.at_.place = { chain := 1, link := some 24, piece := 7 + 1, kind := .K3 } := e3
  exact (hk t ht hp).2.2.2 e2 (by rw [e1]; exact quiet_head_head h)

/-- The public part has the twelve attention plans. -/
theorem fHead_hA : ∀ g, g < 12 → ∃ a, (P5J.At.X Zp).A[g]? = some a := fun g hg => by
  obtain ⟨a, ha, -⟩ := quiet_attention_head h g hg
  exact ⟨a, ha⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The column `hst` at `csHead` and `fHead`.** -/
theorem fHead_hst (hW : rngWrittenB = true) {ν : Nat} {st : Nat → TS → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps P11 s s' → st 24 s → st 24 s') :
    ∀ b, ∀ c ∈ csHead ν st R, c.lo ≤ b → b + 1 ≤ c.hi →
      StaysBy (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread b c := by
  obtain ⟨sh, k345⟩ := fHead_h3H h hW
  have hh : ∀ {i : Nat} {κ : KindName},
      (kindsBeforeBatching (IM.subAt 24) (24 == 0))[i]? = some κ → ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps (14 * 24 + i + 2) s s' →
      fHead Zp cF G take P11 p12 P13 κ { chain := 1, link := some 24, piece := i + 1, kind := κ } s
        s' :=
    fun hk s s' hK => (head_keeps_hear h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (fHead Zp cF G take P11 p12 P13) w (by decide) hk s s').1 hK
  have h342 : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps 342 s s' →
      ProofFile.Honest.K1.K1ReadsKeeps s s' := fun s s' hK => by
    have a := hh (i := 4) (κ := .K1) rfl s s' hK
    have c : K1ReadsKeepsM s s' := ((fHead_K1_later Zp cF G take P11 p12 P13
      (p := { chain := 1, link := some 24, piece := 4 + 1, kind := .K1 }) (l := 24) rfl
      (show (4 + 1 : Nat) ≠ 1 by decide) s s').1 a).1
    exact c.1
  have h343 : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps 343 s s' →
      VerifiableInference.Desc.First.K8.Honest.K8Keeps s s' := fun s s' hK => by
    have a : K8KeepsM s s' := hh (i := 5) (κ := .K8) rfl s s' hK
    exact a.1
  have h344 : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps 344 s s' →
      ProofFile.Honest.K1.K1CommitKeeps s s' := fun s s' hK => by
    have a := hh (i := 6) (κ := .K1) rfl s s' hK
    have c : K1CommitKeepsM s s' := ((fHead_K1_later Zp cF G take P11 p12 P13
      (p := { chain := 1, link := some 24, piece := 6 + 1, kind := .K1 }) (l := 24) rfl
      (show (6 + 1 : Nat) ≠ 1 by decide) s s').1 a).1
    exact c.1
  have h345 : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps 345 s s' →
      K3KeepsHead sh s s' := fun s s' hK =>
    k345 s s' (hh (i := 7) (κ := .K3) rfl s s' hK)
  have h346 : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps 346 s s' →
      Johnson.Desc.First.ForkMerge.Returns.K11Keeps P11 s s' := fun s s' hK => by
    have a : Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAt P11 _ s s' :=
      hh (i := 8) (κ := .K11) rfl s s' hK
    exact a.2.1
  have h347 := head_keeps_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (fHead Zp cF G take P11 p12 P13) w rfl (l := 24) (by decide)
  exact csHead_stays _ (staysBy_x_all _ h342 h343 h344 h345 h346)
    (staysBy_t_all _ h343 h344 h345 h346 h347)
    (head_hwo h H Q test carryX item n₁ n₂ b₀ Vd Rd (fHead Zp cF G take P11 p12 P13) w take rfl rfl
      fun _ => rfl)
    (staysBy_fold0_all _ h344) (staysBy_fold1_all _ h346)
    (fun b h1 h2 => by
      obtain rfl : b = 346 := by omega
      exact staysBy_sentence _ h346 hσ)
    (fHead_hatt h H Q test carryX item n₁ n₂ b₀ Vd Rd G take P11 p12 P13 w (fHead_hA h)
      fun g hg => fHead_h3 h hW (by omega))
    (fHead_hlay h H Q test carryX item n₁ n₂ b₀ Vd Rd G take P11 p12 P13 w
      (fun g hg => fHead_h3 h hW (by omega))
      (head_hB h H Q test carryX item n₁ n₂ b₀ Vd Rd (fHead Zp cF G take P11 p12 P13) w rfl))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_h3
#print axioms ProofFile.Honest.FirstThread.fHead_h3H
#print axioms ProofFile.Honest.FirstThread.fHead_hA
#print axioms ProofFile.Honest.FirstThread.fHead_hst
