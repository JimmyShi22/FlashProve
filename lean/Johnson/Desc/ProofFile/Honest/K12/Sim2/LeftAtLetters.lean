-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clause of the rule at the first chain's last test, at the named first thread.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/LeftAtLetters.lean: onAtRun_at_maker_thread (LeftAtL.lean) where the
rule's invariant at border 354 lies in ThrS (thread₁ h R) (said₁ h R) of AtFullSide/Honest/TheLettersFirst.lean:
the named first thread at the run's own input. Said is said₁, whose words are below the prime by
saidWalk_ok (OkOfWalk.lean); hIM is paid by wordsTied_at_first_thread_paid
(K12/AtFile/LotLScriptPaidBoth.lean). What stays: T with hI, hH, and the list is the caller's to name.

  onAtRun_at_letters   the statement

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). This file's
ground. First kind: hR, hrun: they fail where ready or runC errs: lifted by ready at every k and by the
run's returning under ρ's due test and no silent stop; hρ: ρ and the description alone: public. Second
kind: hR gives that the index is in range and has a trace: a law names the relation. Of neither kind:
h, hA, hf, hH. T is the rule's letter, at the run's coins; hI ties it to the made term, the thread at
the run's own input R.own. What lifts the bar: the order of binders in
RowsSayAtStand.lean's head. The label bars a premise, never a theorem. No property of the
protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.LeftAtL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.OkOfWalk
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLScriptPaidBoth
import AtFullSide.Honest.TheLettersFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (firstScriptAt)
open ProofFile.Honest.Term (matrixInput)
open AtFullSide.Honest AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles (FullSizeMatrix)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

/-- **The clause of the rule at the named first thread.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem onAtRun_at_letters {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hd : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {pl : K2.SwitchPlace} (hf : finishWritten = some pl)
    {H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    {G : Sides hd.description A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B} {ρ : Draws}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit} {r : RunC hd.description}
    (T : ThreadsP hd.description A.B (G.prover H) w₀ rc x k R)
    (hI : ∀ k s m E, T.I₁ 354 k s m E → ThrS (thread₁ hd R) (said₁ hd R) 354 k s m E)
    (hρ : ρ.due hd.description = true)
    (hR : ready hd.description A.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC hd.description A.B (G.prover H) w₀ rc x k ρ = .ok r)
    (hH : (G.prover H).first = A.H.first)
    (Tl : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Thread A.B S ProofFile.Cl (Local FullSizeMatrix IndexCommitterCoins Inst Cells)
      (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst)
    (Sd : Local FullSizeMatrix IndexCommitterCoins Inst Cells → ℕ → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit → Prop)
    (bs : List (Block S ProofFile.Cl)) :
    OnAtRun₁ T ρ r
      ((rowOfJob A.Z (jobOfLot matrixInput OnBytes.HonestTrace.Sz.ref A.Z A.G pl)).lay Tl Sd bs) := by
  obtain ⟨pl', hf', tie⟩ := ProofFile.Honest.K12.LotL.wordsTied_at_first_thread_paid hd matrixInput
    openHonest hA (numbers hd) R.own
  obtain ⟨Bs, base, O⟩ := hd.head.laid.opened
  obtain ⟨-, hG, -⟩ := atPure_ok hA
  have eG : Bs.G₀ = A.G := Option.some.inj (O.blank.symm.trans hG)
  have hfZ : finishAt A.Z A.G = some pl := by
    rw [← eG, finish_at_head hd.head.toAtMg O, hf]
  obtain rfl : pl' = pl := Option.some.inj (hf'.symm.trans hfZ)
  have h0 : ∀ b k m, said₁ hd R b k m → SaidOk b k m := fun b k m a =>
    saidWalk_ok (thread₁ hd R) (fun _ => rfl) b k m a
  exact onAtRun_at_maker_thread hd.head matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    openHonest hA hf T hρ hR hrun hH Tl Sd bs A.H (first hd).script
    (fallsAfterBatching (firstFalls A (first hd).numbers) hd.firstChain)
    (VerifiableInference.Desc.K2.Honest.carryExact A.Z (P5J.At.arr A.Z)) 0 hd.description.t₁
    hd.description.t₂ 339 (ReadyInput hd.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses hd)) R.own rfl (fun v hv y hy => by
      have e : y = ProofFile.startS A.Z v.x.pub := hy
      rw [e, hv]) (said₁ hd R) h0 hI _ rfl
    fun Gp hGp st m₀ E₀ J' hJ c hT he hl Rr ho =>
      tie k st m₀ E₀ _ J' hJ c ⟨hT.1, h0 _ _ _ hT.2⟩ he hl Rr ho Gp hGp

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onAtRun_at_letters
