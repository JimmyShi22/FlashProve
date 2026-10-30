-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/KeepsBehind.lean: THE STATEMENT "BEHIND" (`BehindS`, Honest/Thread/PaysS.lean) AT THE THREE SUB-PROTOCOLS OF THE
KIND K9 IN EACH OF THE 25 SEGMENTS, at the first chain's letters (`lettersHead`, Honest/Thread/FirstHead.lean) with the list of
riders `csHead` (Honest/Thread/CsHead.lean) and a family f of the kinds' clauses of "keeps": where the sub-protocol's step
accepts, the form and the riders hold at the next border, and the step kept what f names at this kind.

  `K9Left s s'`        what all three steps leave: no mark of failure behind; the reply; what a feed-forward segment's own rounds
                      returned; in the output head's segment its three records
  `left_bat`, `left_eq`, `left_shut`   a yes of the block at the member's number gives it, with this kind's clause at the place
  `k9_cases`           the three numbers of a segment, written out in two cases
  `k9_riders_behind`   the clauses of `csHead` that speak at the border behind one of these members spoke in front of it, and
                      `K9Left` carries them
  **`k9_behindS`**      `BehindS` at 14 l + `IM.nAt l` + 2, + 4, + 6, at every Said; f is a variable, with one premise hf: this
                      kind's clause and the forms' clause give f at this kind
  **`k9_behindS_I`**    that at f := `fHeadI` (Honest/Thread/FHeadI.lean)

Limits. The library's hypothesis `AtMgA` is a premise. The step's yes is a premise of `BehindS` itself: nothing here says that a
member accepts. That the thread's invariant holds at any run is not proved here. This file proves no property of a prover or
a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.KeepsReadings
import Johnson.Desc.ProofFile.Honest.K9.CloseLeaves
import Johnson.Desc.ProofFile.Honest.Thread.K9FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.FHeadI
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- What each of this kind's three steps leaves. -/
structure K9Left (s s' : S) : Prop where
  mark : s'.failed = none
  reply : s'.out.reply = s.out.reply
  own : s'.own? = s.own?
  head : ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl} (ft : ℕ) {s s' : S}
include h hl

theorem left_bat (hb : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk) (hy : IM.Yes ft blk s s') : K9Left s s' := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, -⟩ := seats_at_head h hl
  obtain rfl := Option.some.inj (hb.symm.trans Sd.batching)
  obtain ⟨rs, cols, n, hstep⟩ := hy
  have K := k9Keeps_of_step Sd ft s s' rs cols n hstep
  exact ⟨K.mark, K.reply, bat_keeps_reading h hl Sd S.own? rests_own set_own K,
    head_form (bat_keeps_reading h hl Sd headOf rests_headOf set_headOf K)⟩

theorem left_eq (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk) (hy : IM.Yes ft blk s s') : K9Left s s' := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atE
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  obtain ⟨rs, cols, n, hstep⟩ := hy
  have K := H.eqKeeps ft s s' rs cols n hstep
  exact ⟨K.mark, K.reply, K.own, K.head⟩

theorem left_shut (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some blk) (hy : IM.Yes ft blk s s') : K9Left s s' := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atS
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  obtain ⟨rs, cols, n, hstep⟩ := hy
  have K := H.shutKeeps ft s s' rs cols n hstep
  exact ⟨K.mark, K.reply, K.own, K.head⟩

end

/-- A number of this kind: in a segment in front of the last 14 l + 9, + 11 or + 13; in the last 347, 349 or 351. -/
def K9No (b : ℕ) : Prop :=
  (∃ l, l < 24 ∧ (b = 14 * l + 9 ∨ b = 14 * l + 11 ∨ b = 14 * l + 13)) ∨ b = 347 ∨ b = 349 ∨ b = 351

/-- The same with the segment's number named. -/
theorem K9No.named {b : ℕ} (hb : K9No b) : ∃ l, (l < 24 ∧ (b = 14 * l + 9 ∨ b = 14 * l + 11 ∨ b = 14 * l + 13)) ∨
    (b = 347 ∨ b = 349 ∨ b = 351) := by
  rcases hb with ⟨l, hl, e⟩ | e
  · exact ⟨l, Or.inl ⟨hl, e⟩⟩
  · exact ⟨0, Or.inr e⟩

theorem k9_cases {l : ℕ} (hl : l < 25) (i : ℕ) (hi : i = 2 ∨ i = 4 ∨ i = 6) : K9No (14 * l + IM.nAt l + i) := by
  unfold K9No
  by_cases e : l = 24
  · subst e
    have : IM.nAt 24 = 9 := rfl
    rw [this]
    omega
  · have : IM.nAt l = 7 := if_neg e
    rw [this]
    exact Or.inl ⟨l, by omega, by omega⟩

/-- **The clauses of `csHead` behind a member of this kind.** -/
theorem k9_riders_behind {W : Type} (ν : ℕ) (st : ℕ → S → Prop)
    (R : ℕ → Option OnBytes.Model.Forest.Heard → Prop) {b : ℕ} (hb : K9No b) (v : W) {s s' : S}
    (K : K9Left s s') (hR : ridersOf (csHead ν st R) b v s) : ridersOf (csHead ν st R) (b + 1) v s' := by
  intro c hc hlo hhi
  have hfront := hR c hc
  obtain ⟨l, hb⟩ := hb.named
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  · have a1 : 342 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 347 := hhi
    exfalso
    omega
  · have a1 : 343 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 348 := hhi
    obtain ⟨a, ha, hp⟩ := hfront (show 343 ≤ b by omega) (show b ≤ 348 by omega)
    obtain ⟨a', ha', -, e2, -⟩ := K.head a ha
    exact ⟨a', ha', by show a'.t.isSome = true; rw [e2]; exact hp⟩
  · have a1 : 347 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 352 := hhi
    obtain ⟨a, ha, hp⟩ := hfront (show 347 ≤ b by omega) (show b ≤ 352 by omega)
    obtain ⟨a', ha', -, -, e3⟩ := K.head a ha
    exact ⟨a', ha', by show a'.wo.isSome = true; rw [e3]; exact hp⟩
  · have a1 : 346 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 346 := hhi
    exfalso
    omega
  · have a1 : 344 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 345 := hhi
    exfalso
    omega
  · have a1 : 346 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 347 := hhi
    exfalso
    omega
  · have a1 : 346 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 347 := hhi
    exfalso
    omega
  · have a1 : 14 * l' + 9 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 14 * l' + 9 := hhi
    exfalso
    omega
  · have a1 : 14 * (2 * g + 1) + 4 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 14 * (2 * g + 1) + 9 := hhi
    exfalso
    omega
  · have a1 : 28 * g + 5 ≤ b + 1 := hlo
    have a2 : b + 1 ≤ 28 * g + 10 := hhi
    obtain ⟨o, ho⟩ := hfront (show 28 * g + 5 ≤ b by omega) (show b ≤ 28 * g + 10 by omega)
    exact ⟨o, K.own.trans ho⟩

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
  (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (f : KindName → Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- The common part: from the form behind, what the step leaves, and this kind's clause at the place. -/
theorem behind_of_left
    (hf : ∀ pl s s', k9KeepsAt cF Zp pl s s' → formsBehind h.𝔇.pubD pl s' → f KindName.K9 pl s s')
    {b : ℕ} (hb : K9No b) {blk : Block TS ProofFile.Cl}
    (hblk : (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread.bs[b]? =
      some blk) (hkind : blk.place.kind = KindName.K9)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread b k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread.Stepped blk k s
      m E ds y cols s')
    (hForm : (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread.Form (b + 1)
      k s' y.2)
    (K : K9Left s s') (hK : k9KeepsAt cF Zp blk.place s s') :
    (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread.Form (b + 1) k s' y.2 ∧
      (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread.rides (b + 1)
        y.2.st.input s' ∧
      (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread.keeps b s s' := by
  have hThr := hT
  unfold Thr at hThr
  obtain ⟨-, -, -, -, -, hR, -⟩ := hThr
  have hp := head_place h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w hblk
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l', -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨hForm, ⟨fun hb9 => ?_, ?_⟩, ?_⟩
  · have hb' : 339 ≤ b := by
      obtain ⟨l, hb⟩ := hb.named
      omega
    have hR₁ := head_reply h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w hb' hR
    rw [ei, K.reply]
    exact hR₁
  · rw [ei]
    exact k9_riders_behind ν st R hb _ K hR.2
  · exact (head_keeps_kind h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) f w hblk hkind s s').2
      (hf _ _ _ hK (formsBehind_of_form h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w hp
        hForm))

/-- **`BehindS` at this kind's three members of each segment**, at every Said. -/
theorem k9_behindS
    (hf : ∀ pl s s', k9KeepsAt cF Zp pl s s' → formsBehind h.𝔇.pubD pl s' → f KindName.K9 pl s s')
    (l : ℕ) (hl : l < 25) :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread Said
        (14 * l + IM.nAt l + 2) ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread Said
        (14 * l + IM.nAt l + 4) ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread Said
        (14 * l + IM.nAt l + 6) := by
  refine ⟨?_, ?_, ?_⟩
  · intro blk hblk k s m E ds y cols s' hT _ hS
    have hb : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk := hblk
    have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
    have hF := hT.1
    unfold Thr at hF
    exact behind_of_left h H Q test carryX item n₁ n₂ Vd ν st R f w hf (k9_cases hl 2 (Or.inl rfl)) hblk
      (kind_bat_at h hl hb) hT.1 hS
      (k9_form_behind_bat h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w hl hb hF.2.2.1 hS)
      (left_bat h hl 0 hb hyes) (k9KeepsAt_step_bat h hl 0 hb hyes)
  · intro blk hblk k s m E ds y cols s' hT _ hS
    have hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk := hblk
    have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
    exact behind_of_left h H Q test carryX item n₁ n₂ Vd ν st R f w hf (k9_cases hl 4 (Or.inr (Or.inl rfl))) hblk
      (kind_eq_at h hl hb) hT.1 hS
      (k9_form_behind_eq h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w hl hb hT.1 hS)
      (left_eq h hl 0 hb hyes) (k9KeepsAt_step_eq h hl 0 hb hyes)
  · intro blk hblk k s m E ds y cols s' hT _ hS
    have hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some blk := hblk
    have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
    have hF := hT.1
    unfold Thr at hF
    exact behind_of_left h H Q test carryX item n₁ n₂ Vd ν st R f w hf (k9_cases hl 6 (Or.inr (Or.inr rfl))) hblk
      (kind_shut_at h hl hb) hT.1 hS
      (k9_form_behind_shut h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w hl hb hF.2.2.1 hS)
      (left_shut h hl 0 hb hyes) (k9KeepsAt_step_shut h hl 0 hb hyes)

end

/-- **That at the family `fHeadI`.** -/
theorem k9_behindS_I (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : ℕ) (hl : l < 25) :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said (14 * l + IM.nAt l + 2) ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said (14 * l + IM.nAt l + 4) ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy (fHeadI Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said (14 * l + IM.nAt l + 6) :=
  k9_behindS h H Q test carryX item n₁ n₂ Vd ν st R _ w Said
    (fun _ _ _ hK hFo => ⟨⟨⟨⟨hK, hFo⟩, trivial⟩, trivial⟩, trivial⟩) l hl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.left_bat
#print axioms ProofFile.Honest.K9.left_eq
#print axioms ProofFile.Honest.K9.left_shut
#print axioms ProofFile.Honest.K9.K9No.named
#print axioms ProofFile.Honest.K9.k9_cases
#print axioms ProofFile.Honest.K9.k9_riders_behind
#print axioms ProofFile.Honest.K9.behind_of_left
#print axioms ProofFile.Honest.K9.k9_behindS
#print axioms ProofFile.Honest.K9.k9_behindS_I
