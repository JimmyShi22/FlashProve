-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/FrameOwes.lean: three of the four conditions that the
first chain's invariant has to meet at a sub-protocol (`PlaysS`, `BehindS`, `ExchangeS`,
Thread/PaysS.lean), at the 77 sub-protocols of the kind `frame` at the full size, with `keeps` given
kind by kind (`kpBy f`, Thread/KeepsBy.lean). Each lemma calls the structure `NoHouse` at that
sub-protocol (FirstStill.lean, BehindKp.lean, Cleared.lean, Seal.lean) and `noHouse_owes`
(Bare.lean). No definition.

  1  `saidOk_past`    the condition `SaidOk` (Thread/SaidOk.lean) survives rounds in which the
     prover sends nothing
  2  `items_again`    at any `Thread`: items that are open before a sub-protocol, and that it has to
     show again, hold after it if each of them survives it (`RidesPastAtS`, Thread/SharesS.lean)
  3  `frame_owes_front`, `frame_owes_laid`, `frame_owes_behind`, `frame_owes_cleared`,
     `frame_owes_seal`   the three conditions at the numbers 0, `14 * l + 1`,
     `14 * l + IM.nAt l + 3`, `14 * l + IM.nAt l + 7`, 357

How the acceptance is left out. `NoHouse` also has a field that says that the sub-protocol accepts
where an abort test `fall` does not fire, and some of these structures take a hypothesis for it. The
three conditions do not mention `fall`. So the structures are taken at a `fall` that always fires,
where that hypothesis holds vacuously. After a batching `fall` is the invariant's own argument
`test`, because the structure there ties the two.

What stays a hypothesis of every lemma.
  * `hfF`: the clause of the kind `frame` is `keepsFrame`. It holds by unfolding at `fHead`
    (Thread/FHead.lean), which this file does not import.
  * `noHalf`: the prover has no side at a place of the kind `frame`.
  * `hb₀`: the border after the sub-protocol that hears the reply is not the border after this one.
  * `hRd`: the argument `Rd` of the invariant passes over the sub-protocol.
  * `said`: so does the argument `Said`.
  * `rides`: the fourth condition, `RidesPastS`, which the structure only passes on.
And of single lemmas: after a batching `htst` (where the step accepts, `test` does not fire); at
"cleared" `owes` (the items that the table's row asks for hold after the step; `items_again` gives
it).

Limits.
  * Nothing shows that the invariant holds at any state.
  * That any of these sub-protocols accepts is not shown here.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrameAt
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Cleared
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Seal
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindKp
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Guards
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.LPFK9R.HtinAtConstant
import Johnson.P5J.K09List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (viewWordsBelowPrime)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- `SaidOk` survives rounds in which nothing is sent, at challenges that the rounds can draw. -/
theorem saidOk_past {b b' : Nat} {k : Coins Bk} : ∀ (l : List Fmt.DeclaredRound) (ds : List Fmt.Drawn)
    (m : Mid W X), drawsFit l ds = true → SaidOk b k m → SaidOk b' k (m.past ds)
  | [], [], _, _, h => h
  | [], _ :: _, _, hd, _ => by simp [drawsFit] at hd
  | _ :: _, [], _, hd, _ => by simp [drawsFit] at hd
  | r :: l, d :: ds, m, hd, h => by
    simp only [drawsFit, Bool.and_eq_true] at hd
    obtain ⟨h1, h2⟩ := hd
    simp only [drawFit, Bool.and_eq_true] at h1
    have e : viewWordsBelowPrime ⟨[⟨[], d⟩], []⟩ = true := by
      simp only [viewWordsBelowPrime, List.all_cons, List.all_nil, Bool.and_true]
      exact h1.1.2
    show SaidOk b' k
      ((⟨m.st.hears d, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩ : Mid W X).past ds)
    refine saidOk_past (b := b) l ds _ h2 ?_
    show viewWordsBelowPrime ⟨m.seen ++ [⟨[], d⟩], []⟩ = true
    exact (okRounds_append _ _).2 ⟨h, e⟩

variable (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)

/-- Items that are open before the sub-protocol and have to be shown again after it. -/
theorem items_again {b : Nat} (ho : ∀ i ∈ (T.row b).owes, i ∈ T.opened b)
    (hR : ∀ i ∈ (T.row b).owes, RidesPastAtS T Said b i) :
    ∀ k s m E s', ThrS T Said b k s m E → T.keeps b s s' →
      T.Items (T.row b).owes k s' m E := by
  intro k s m E s' hA hK ds i hi
  have h0 := thr_item_at T hA.1 (ho i hi) ds
  have h1 := hR i hi k s m E s' [] _ hA hK h0
  rw [add_plain E (thr_tight T hA.1) [] rfl] at h1
  exact h1

end

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.ChainEnd (sealRound)
open VerifiableInference.Desc.K13.Law (placeSeal)
open VerifiableInference.Desc.LinkJoin (batchAt rest9)
open Johnson.Desc.First.Walk.Tied (clearedGives)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- At number 0. -/
theorem frame_owes_front (take : Nat → Bool)
    (hfF : f KindName.frame = keepsFrame P5J.At.links take)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said 0 k m → Said (0 + 1) k m) (hb₀ : b₀ ≠ 0 + 1)
    (hRd : ∀ v s, Rd 0 v s → Rd (0 + 1) v s)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
      Said 0) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said 0 ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said 0 ∧
      ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said 0 := by
  obtain ⟨blk, -, N⟩ := noHouse_start0 h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
    (Said := Said) (fall := fun _ _ _ => none) noHalf said hb₀ hRd
    (fun s h0 => (kpBy_at f (κ := KindName.frame) rfl s s).2 (by
      rw [hfF]
      exact kp_out P5J.At.links take rfl s h0)) rides
  exact ⟨(noHouse_owes N).1, (noHouse_owes N).2.1, (noHouse_owes N).2.2.1⟩

/-- At the frame's step "laid" of segment `l`. -/
theorem frame_owes_laid (take : Nat → Bool)
    (hfF : f KindName.frame = keepsFrame P5J.At.links take) {l : Nat} (hl : l < 25)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said (14 * l + 1) k m → Said (14 * l + 1 + 1) k m)
    (hb₀ : b₀ ≠ 14 * l + 1 + 1) (hRd : ∀ v s, Rd (14 * l + 1) v s → Rd (14 * l + 1 + 1) v s)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
      Said (14 * l + 1)) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (14 * l + 1) ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (14 * l + 1) ∧
      ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (14 * l + 1) := by
  obtain ⟨blk, -, N⟩ := noHouse_laid h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
    (Said := Said) (fall := fun _ _ _ => some "") hl noHalf said hb₀ hRd
    (fun s h0 => (kpBy_at f (κ := KindName.frame) rfl s s).2 (by
      rw [hfF]
      exact kp_laid P5J.At.links take (l := l) rfl rfl s h0))
    (fun _ _ _ _ _ hf => nomatch hf) rides
  exact ⟨(noHouse_owes N).1, (noHouse_owes N).2.1, (noHouse_owes N).2.2.1⟩

/-- At the frame's step after the batching of segment `l`. `htst`: where the step accepts, the
invariant's argument `test` does not fire. `hRd`: `Rd` passes over a step that leaves `rest9`. -/
theorem frame_owes_behind (take : Nat → Bool)
    (hfF : f KindName.frame = keepsFrame P5J.At.links take) {l : Nat} (hl : l < 25)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (htst : ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none)
    (said : ∀ k m, Said (14 * l + IM.nAt l + 3) k m → Said (14 * l + IM.nAt l + 3 + 1) k m)
    (hb₀ : b₀ ≠ 14 * l + IM.nAt l + 3 + 1)
    (hRd : ∀ v s s', Rd (14 * l + IM.nAt l + 3) v s →
      (∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) → Rd (14 * l + IM.nAt l + 3 + 1) v s')
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
      Said (14 * l + IM.nAt l + 3)) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (14 * l + IM.nAt l + 3) ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (14 * l + IM.nAt l + 3) ∧
      ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (14 * l + IM.nAt l + 3) := by
  obtain ⟨Lk, p9, Q9, b₃, b₅, St⟩ := P5J.sits_at h l hl
  have en : batchAt fullLinks P5J.At.ps l + 1 = 14 * l + IM.nAt l + 3 := by
    have e := LPFK9.batch_nAt l hl
    omega
  have hs := behind_seat h St
  rw [en] at hs
  have N := noHouse_behind_seven h H Q test carryX item n₁ n₂ b₀ Vd Rd f w Said
    (fun _ s _ => test l s) hl St take hfF
    (noHalf_of_kind fun g hg => noHalf g hg)
    (fun s rs cols s' n e => htst _ hs s rs cols s' n e) (fun _ e => e)
    (fun v s s' hv hy => by
      rw [en] at hv ⊢
      exact hRd v s s' hv (after_state Lk (after_share_head h hl St.lk St.seg) s s' hy).2.1)
    (by rw [en]; exact hb₀)
    (fun k μ hS => by
      rw [en] at hS ⊢
      exact said k μ hS)
    (by rw [en]; exact rides)
  rw [en] at N
  exact ⟨(noHouse_owes N).1, (noHouse_owes N).2.1, (noHouse_owes N).2.2.1⟩

/-- At the frame's step "cleared" of segment `l`. `hRd`: `Rd` passes over a step after which the
chain is between two segments. `owes`: what the table's row asks for holds after the step. -/
theorem frame_owes_cleared (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    {l : Nat} (hl : l < 25) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said (P1L20.clearIx l) k m → Said (P1L20.clearIx l + 1) k m)
    (hb₀ : b₀ ≠ P1L20.clearIx l + 1)
    (hRd : ∀ v s t, t.atBetween = true → Rd (P1L20.clearIx l) v s →
      Rd (P1L20.clearIx l + 1) v t)
    (owes : ∀ k s m E t,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (P1L20.clearIx l) k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps
        (P1L20.clearIx l) s t →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.Items
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.row
          (P1L20.clearIx l)).owes k t m E)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
      Said (P1L20.clearIx l)) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (P1L20.clearIx l) ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (P1L20.clearIx l) ∧
      ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        (P1L20.clearIx l) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, fr, bL, bB, bC, -, -, hf, -⟩ := hall l hl
  obtain ⟨-, Xl, counts, left, hcl, -⟩ :=
    Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
  obtain ⟨-, -, -, hp, -⟩ := P1L20.places_full hl
  have hKp : ∀ s t, fr.clear s = .ok t → t.failed = none →
      kpBy f (P1L20.clearPlace l) s t := fun s t e h0 =>
    (kpBy_at f (κ := KindName.frame) rfl s t).2 (by
      rw [hfF]
      exact kp_cleared h P5J.At.links hl hfs hf s t e h0)
  obtain ⟨blk, -, N⟩ := noHouse_cleared h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
    (Said := Said) (fall := fun _ _ _ => some "") hl hfs hf noHalf said hb₀
    (fun v s t e hv => by
      rw [hcl] at e
      exact hRd v s t (clearedGives Xl counts left _ _ s t e).1 hv)
    hKp
    (fun k s m E t hA e => by
      have e' := e
      rw [hcl] at e'
      have h0 : t.failed = none :=
        (clearedGives Xl counts left _ _ s t e').2.2.2.2.2.2.1.trans (form_shape hA.1.2.2.1).1
      exact owes k s m E t hA
        ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hp s t).2 (hKp s t e h0)))
    (fun _ _ _ _ _ hf' => nomatch hf') rides
  exact ⟨(noHouse_owes N).1, (noHouse_owes N).2.1, (noHouse_owes N).2.2.1⟩

/-- At the chain's end, number 357. -/
theorem frame_owes_seal (take : Nat → Bool)
    (hfF : f KindName.frame = keepsFrame P5J.At.links take)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (said : ∀ k m ds, Said 357 k m → drawsFit [sealRound] ds = true → Said 358 k (m.past ds))
    (hb₀ : b₀ ≠ 357 + 1) (hRd : ∀ v s, Rd 357 v s → Rd 358 v s)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
      Said 357) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said 357 ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said 357 ∧
      ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
        357 := by
  have N := noHouse_seal357 h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w (Said := Said)
    (fall := fun _ _ _ => some "") noHalf said hb₀ hRd
    (fun s h0 => (kpBy_at f (κ := KindName.frame) rfl s s).2 (by
      rw [hfF]
      exact kp_out P5J.At.links take rfl s h0))
    (fun _ _ _ _ _ _ hf => nomatch hf) rides
  exact ⟨(noHouse_owes N).1, (noHouse_owes N).2.1, (noHouse_owes N).2.2.1⟩

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.saidOk_past
#print axioms ProofFile.Honest.items_again
#print axioms ProofFile.Honest.FirstThread.frame_owes_front
#print axioms ProofFile.Honest.FirstThread.frame_owes_laid
#print axioms ProofFile.Honest.FirstThread.frame_owes_behind
#print axioms ProofFile.Honest.FirstThread.frame_owes_cleared
#print axioms ProofFile.Honest.FirstThread.frame_owes_seal
