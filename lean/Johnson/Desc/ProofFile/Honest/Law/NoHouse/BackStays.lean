-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BackStays.lean: hypotheses of `csHead_stays`
(Thread/GatherStays.lean), the lemma that asks `StaysBy` (Thread/Riders.lean) for every rider clause
of the list `csHead` at every sub-protocol inside the clause's span. Here: the clause "the field
`wo` is set" over the five sub-protocols 347 to 351; the clause "the field `t` is set" over 347; and
"the field `own` is the same" over the batching of each of the 12 feed-forward segments. The facts
on the clauses of `keeps` come from BackLeaves.lean. No definition.

  1  `staysBy_head3_wo`, `staysBy_head3_t`, `staysBy_sentence`   at any `Thread`: a rider clause
     survives a sub-protocol whose clause of `keeps` leaves what it reads
  2  `staysBy_wo_all`, `staysBy_t_all`   at any `Thread`: the hypotheses `hwo` and `ht` of
     `csHead_stays`, from "`keeps` at that number gives the kind's clause"
  3  `head_keeps_bat`, `head_keeps_behind`, `head_keeps_eq`, `head_keeps_k10`, `head_keeps_shut`
     at the first chain's invariant at the full size (`lettersHead`, Thread/FirstHead.lean) with
     `keeps` given kind by kind (`kpBy f`, Thread/KeepsBy.lean), in each of the 25 segments: what
     `keeps` gives at the numbers `14 * l + IM.nAt l + 2` to `14 * l + IM.nAt l + 6`
  4  `head_hwo`, `head_ht_bat`, `head_hB`   there: the hypothesis `hwo`; the sub-protocol 347 of
     `ht`; the hypothesis `hB` of `head_hlay` (Thread/HeadKeepsAt.lean)

The family `f` is an argument. Items 3 and 4 take equations on it as hypotheses: `hf9` (the clause
of K9 is `k9KeepsAt cF Zp`), `hfF` (the clause of the kind `frame` is `keepsFrame P5J.At.links
take`), `hf10` (the clause of K10 is `K10Keeps` at every place). They hold by unfolding at the
family `fHead` (Thread/FHead.lean), which this file does not import.

`staysBy_sentence` is for the clause `st 24` of `csHead`, whose text is an argument of the list. It
survives number 346, the merge, if the merge's clause of `keeps` carries it from the state before
to the state after. That condition stays a hypothesis.

Limits.
  * Nothing shows that `keeps` holds at any step.
  * Items 3 and 4: full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BackLeaves
import Johnson.Desc.ProofFile.Honest.K9.CloseLeaves
import Johnson.Desc.ProofFile.Honest.Thread.HeadStaysAll
import Johnson.Desc.ProofFile.Honest.Thread.Numbers358
import Johnson.LPFK10R.CloseShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.LinkJoin (rest9)
open ProofFile.Honest.K9 (EqKeeps ShutKeeps)
open ProofFile.Honest.K10.YesFree (K10Keeps)
open ProofFile.Honest.FirstThread (keepsBehind keepsBehind_wo rest9_head3 k10_head3)

section
variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-! ## 1 A rider clause and what a sub-protocol leaves -/

/-- "The field `wo` is set" survives a sub-protocol that leaves the field. -/
theorem staysBy_head3_wo {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .head a →
      ∃ a', s'.here = .head a' ∧ a'.wo = a.wo) :
    StaysBy T b (riderHead lo hi fun a => a.wo.isSome = true) :=
  staysBy_head_of T fun s s' hK a ha =>
    let ⟨a', ha', e⟩ := hk s s' hK a ha
    ⟨a', ha', fun hP => by
      show a'.wo.isSome = true
      rw [e]
      exact hP⟩

/-- "The field `t` is set" survives a sub-protocol that leaves the field. -/
theorem staysBy_head3_t {b lo hi : Nat}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .head a →
      ∃ a', s'.here = .head a' ∧ a'.t = a.t) :
    StaysBy T b (riderHead lo hi fun a => a.t.isSome = true) :=
  staysBy_head_of T fun s s' hK a ha =>
    let ⟨a', ha', e⟩ := hk s s' hK a ha
    ⟨a', ha', fun hP => by
      show a'.t.isSome = true
      rw [e]
      exact hP⟩

/-- A condition `σ` on the state survives a sub-protocol whose clause `K` carries it over. -/
theorem staysBy_sentence {b lo hi : Nat} {K : S → S → Prop} {σ : S → Prop}
    (hk : ∀ s s', T.keeps b s s' → K s s') (hσ : ∀ s s', K s s' → σ s → σ s') :
    StaysBy T b ⟨lo, hi, fun _ _ s => σ s⟩ :=
  fun _ s s' hK hP => hσ s s' (hk s s' hK) hP

/-! ## 2 The hypotheses `hwo` and `ht` -/

/-- The hypothesis `hwo` of `csHead_stays`. -/
theorem staysBy_wo_all
    (h347 : ∀ s s', T.keeps 347 s s' → ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s)
    (h348 : ∀ s s', T.keeps 348 s s' → keepsBehind s s')
    (h349 : ∀ s s', T.keeps 349 s s' → EqKeeps s s')
    (h350 : ∀ s s', T.keeps 350 s s' → K10Keeps s s')
    (h351 : ∀ s s', T.keeps 351 s s' → ShutKeeps s s') :
    ∀ b, 347 ≤ b → b + 1 ≤ 352 →
      StaysBy T b (riderHead 347 352 fun a => a.wo.isSome = true) := by
  intro b h₁ h₂
  have hb : b = 347 ∨ b = 348 ∨ b = 349 ∨ b = 350 ∨ b = 351 := by omega
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact staysBy_head3_wo T fun s s' hK a ha =>
      let ⟨a', ha', _, _, e⟩ := rest9_head3 (h347 s s' hK) a ha
      ⟨a', ha', e⟩
  · exact staysBy_head3_wo T fun s s' hK a ha => keepsBehind_wo (h348 s s' hK) a ha
  · exact staysBy_head3_wo T fun s s' hK a ha =>
      let ⟨a', ha', _, _, e⟩ := (h349 s s' hK).head a ha
      ⟨a', ha', e⟩
  · exact staysBy_head3_wo T fun s s' hK a ha =>
      let ⟨a', ha', _, _, e⟩ := k10_head3 (h350 s s' hK) a ha
      ⟨a', ha', e⟩
  · exact staysBy_head3_wo T fun s s' hK a ha =>
      let ⟨a', ha', _, _, e⟩ := (h351 s s' hK).head a ha
      ⟨a', ha', e⟩

/-- "The field `t` is set" survives the batching of the output head's segment. -/
theorem staysBy_t_bat {lo hi : Nat}
    (h347 : ∀ s s', T.keeps 347 s s' → ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    StaysBy T 347 (riderHead lo hi fun a => a.t.isSome = true) :=
  staysBy_head3_t T fun s s' hK a ha =>
    let ⟨a', ha', _, e, _⟩ := rest9_head3 (h347 s s' hK) a ha
    ⟨a', ha', e⟩

/-- The hypothesis `ht` of `csHead_stays`: `staysBy_t_upto` (Thread/HeadStaysAll.lean) and number
347. -/
theorem staysBy_t_all {sh : OnBytes.Model.Forest.Shape}
    {P : Johnson.Desc.First.ForkMerge.HeadMergeP}
    (h343 : ∀ s s', T.keeps 343 s s' → VerifiableInference.Desc.First.K8.Honest.K8Keeps s s')
    (h344 : ∀ s s', T.keeps 344 s s' → ProofFile.Honest.K1.K1CommitKeeps s s')
    (h345 : ∀ s s', T.keeps 345 s s' → ProofFile.Honest.K3.Law.AtThr.K3KeepsHead sh s s')
    (h346 : ∀ s s', T.keeps 346 s s' → Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s')
    (h347 : ∀ s s', T.keeps 347 s s' → ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    ∀ b, 343 ≤ b → b + 1 ≤ 348 →
      StaysBy T b (riderHead 343 348 fun a => a.t.isSome = true) := by
  intro b h₁ h₂
  by_cases h7 : b = 347
  · subst h7
    exact staysBy_t_bat T h347
  · exact staysBy_t_upto T h343 h344 h345 h346 b h₁ (by omega)

end

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K9 (k9KeepsAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-! ## 3 What `keeps` gives from a segment's batching to its shutting -/

/-- At the batching of segment `l`. -/
theorem head_keeps_bat (hf9 : f KindName.K9 = k9KeepsAt cF Zp) {l : Nat} (hl : l < 25) :
    ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps
        (14 * l + IM.nAt l + 2) s s' →
      ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s := by
  intro s s' hK
  obtain ⟨Lk, p, w', Q', bE, bS, Sd, -⟩ := ProofFile.Honest.K9.seats_at_head h hl
  have hc := (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w Sd.batching
    (ProofFile.Honest.K9.kind_bat_at h hl Sd.batching) s s').1 hK
  rw [hf9] at hc
  exact bat_rest9_at h hl _ Sd.batching s s' hc

/-- At the frame's step after the batching of segment `l`. -/
theorem head_keeps_behind (take : Nat → Bool)
    (hfF : f KindName.frame = keepsFrame P5J.At.links take) {l : Nat} (hl : l < 25) :
    ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps
        (14 * l + IM.nAt l + 3) s s' → keepsBehind s s' := by
  intro s s' hK
  obtain ⟨Lk, p9, Q9, b₃, b₅, St⟩ := P5J.sits_at h l hl
  have hs := behind_seat h St
  rw [LPFK9.batch_nAt l hl] at hs
  have hs' : cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some Lk.behindB := hs
  have hc := (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hs'
    (κ := KindName.frame) rfl s s').1 hK
  rw [hfF] at hc
  exact (behind_arm h take hl _ hs' s s').1 hc

/-- At the one equation of segment `l`. -/
theorem head_keeps_eq (hf9 : f KindName.K9 = k9KeepsAt cF Zp) {l : Nat} (hl : l < 25) :
    ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps
        (14 * l + IM.nAt l + 4) s s' → EqKeeps s s' := by
  intro s s' hK
  obtain ⟨Lk, p, w', Q', bE, bS, Sd, C⟩ := ProofFile.Honest.K9.seats_at_head h hl
  have e := C.atE
  rw [Sd.hears] at e
  have e0 : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some bE := e
  have hc := (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w e
    (ProofFile.Honest.K9.kind_eq_at h hl e0) s s').1 hK
  rw [hf9] at hc
  exact eq_at h hl _ e s s' hc

/-- At the closing of segment `l`. -/
theorem head_keeps_k10 (hf10 : ∀ p, f KindName.K10 p = K10Keeps) {l : Nat} (hl : l < 25) :
    ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps
        (14 * l + IM.nAt l + 5) s s' → K10Keeps s s' := by
  have eL : LPFK10.LW = linksFull := by decide
  have eP : LPFK10.PW = P5J.At.ps := by
    show flatPlacesOf LPFK10.LW true = flatPlacesOf linksFull true
    rw [eL]
  obtain ⟨p, hp, hk⟩ := LPFK10.k10_place_w hl
  rw [eP] at hp
  have hp' : P5J.At.ps[14 * l + IM.nAt l + 5]? = some p := hp
  exact head_hk h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hp' hk fun s s' hc => by
    rw [hf10] at hc
    exact hc

/-- At the shutting of segment `l`. -/
theorem head_keeps_shut (hf9 : f KindName.K9 = k9KeepsAt cF Zp) {l : Nat} (hl : l < 25) :
    ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps
        (14 * l + IM.nAt l + 6) s s' → ShutKeeps s s' := by
  intro s s' hK
  obtain ⟨Lk, p, w', Q', bE, bS, Sd, C⟩ := ProofFile.Honest.K9.seats_at_head h hl
  have e := C.atS
  rw [Sd.hears] at e
  have e2 : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some bS := e
  have hc := (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w e
    (ProofFile.Honest.K9.kind_shut_at h hl e2) s s').1 hK
  rw [hf9] at hc
  exact shut_at h hl _ e s s' hc

/-! ## 4 The hypotheses of `csHead_stays` -/

/-- The hypothesis `hwo` of `csHead_stays`. -/
theorem head_hwo (take : Nat → Bool) (hf9 : f KindName.K9 = k9KeepsAt cF Zp)
    (hfF : f KindName.frame = keepsFrame P5J.At.links take)
    (hf10 : ∀ p, f KindName.K10 p = K10Keeps) :
    ∀ b, 347 ≤ b → b + 1 ≤ 352 →
      StaysBy (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
        (riderHead 347 352 fun a => a.wo.isSome = true) := by
  have n9 := nAt_head
  have e2 : 347 = 14 * 24 + IM.nAt 24 + 2 := by omega
  have e3 : 348 = 14 * 24 + IM.nAt 24 + 3 := by omega
  have e4 : 349 = 14 * 24 + IM.nAt 24 + 4 := by omega
  have e5 : 350 = 14 * 24 + IM.nAt 24 + 5 := by omega
  have e6 : 351 = 14 * 24 + IM.nAt 24 + 6 := by omega
  refine staysBy_wo_all _ (fun s s' hK => ?_) (fun s s' hK => ?_) (fun s s' hK => ?_)
    (fun s s' hK => ?_) fun s s' hK => ?_
  · rw [e2] at hK
    exact head_keeps_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 (by omega) s s' hK
  · rw [e3] at hK
    exact head_keeps_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w take hfF (by omega) s s' hK
  · rw [e4] at hK
    exact head_keeps_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 (by omega) s s' hK
  · rw [e5] at hK
    exact head_keeps_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf10 (by omega) s s' hK
  · rw [e6] at hK
    exact head_keeps_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 (by omega) s s' hK

/-- The sub-protocol 347 of the hypothesis `ht` of `csHead_stays`. -/
theorem head_ht_bat (hf9 : f KindName.K9 = k9KeepsAt cF Zp) :
    StaysBy (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread 347
      (riderHead 343 348 fun a => a.t.isSome = true) := by
  have n9 := nAt_head
  have e2 : 347 = 14 * 24 + IM.nAt 24 + 2 := by omega
  refine staysBy_t_bat _ fun s s' hK => ?_
  rw [e2] at hK
  exact head_keeps_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 (by omega) s s' hK

/-- The hypothesis `hB` of `head_hlay` (Thread/HeadKeepsAt.lean). -/
theorem head_hB (hf9 : f KindName.K9 = k9KeepsAt cF Zp) :
    ∀ g, g < 12 → ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps (28 * g + 9) s
        s' →
      ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  intro g hg s s' hK
  have n7 := nAt_lt (l := 2 * g) (by omega)
  have e : 28 * g + 9 = 14 * (2 * g) + IM.nAt (2 * g) + 2 := by omega
  rw [e] at hK
  exact rest9_lay_own
    (head_keeps_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 (by omega) s s' hK)

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.staysBy_head3_wo
#print axioms ProofFile.Honest.staysBy_head3_t
#print axioms ProofFile.Honest.staysBy_sentence
#print axioms ProofFile.Honest.staysBy_wo_all
#print axioms ProofFile.Honest.staysBy_t_bat
#print axioms ProofFile.Honest.staysBy_t_all
#print axioms ProofFile.Honest.FirstThread.head_keeps_bat
#print axioms ProofFile.Honest.FirstThread.head_keeps_behind
#print axioms ProofFile.Honest.FirstThread.head_keeps_eq
#print axioms ProofFile.Honest.FirstThread.head_keeps_k10
#print axioms ProofFile.Honest.FirstThread.head_keeps_shut
#print axioms ProofFile.Honest.FirstThread.head_hwo
#print axioms ProofFile.Honest.FirstThread.head_ht_bat
#print axioms ProofFile.Honest.FirstThread.head_hB
