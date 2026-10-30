-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/TieAtFirst.lean: THE ITEM "tie l" AT THE READS OF EACH OF THE 25 SEGMENTS, AT THE FIRST THREAD OF THE BASE PROVER: hTie of k1_fiveJ_first (AtFullSide/K1/FiveByKind.lean), from exchangeAtS_tie_all (TieAtAll.lean), tieMatS_written (TieMatAtHead.lean) and the form LaysFilling at every segment.

  tieMatS_ok    hF1 at the closed Script, at N := 0, at a Vd that gives okStart
  tie_at_first  the item, from hF2, the second family
  tie_first     the statement: hF2 paid by tieReadsS_base. Left: hSaid, hQ, hI

OF COMPLETENESS's KIND: hI names the input: NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean).
NO PROPERTY IS CLAIMED.
-/
import AtFullSide.K1.TieMatAtHead
import AtFullSide.K1.TieAtAll
import AtFullSide.K1.LaysAtSwitchesPaid
import AtFullSide.K1.ReadsAtBaseAll
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.HonestTrace (Sz ServesAt theTrace)
open ProofFile.Honest.FirstThread
open P5J (AtMgA TS F0T)

variable {W₀ : Type} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **hF1 at the closed Script, at every segment.** hOk: each input that Vd admits passes okStart: it pays
the code switches' public test. hSaid, hI, hV: as in tieMatS_at_head. -/
theorem tieMatS_ok {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop) (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hI : ∀ u ξ C, I.trace A.Z u ξ = some C → ∃ i x,
      C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i x) ∧
        ServesAt (P5J.At.X A.Z) i x) (hV : Vd w → ReadyInput A.F A.H w)
    (hOk : ∀ v, Vd v → (F0T OnBytes.secondHashFunction A.Z Np cF).okStart v.x = true) {l : ℕ} (hl : l < 25) :
    TieMatS (lettersHead h A.H (firstScriptAt I Sz.ref openHonest A cF) test carryX item n₁ n₂ b₀ Vd Rd
        Kp w) Said (P5J.At.cs A.Z) (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) Sz.ref (witBT I A.Z)
      (K1.noL l false) l := by
  refine tieMatS_written hA h _ test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hI hV (N := 0) hl
    (Nat.zero_le _) fun l₀ h₀ => ?_
  rcases Nat.eq_zero_or_pos l₀ with rfl | hp
  · exact ⟨_, _, laysFilling_opening_any h hA Vd 0⟩
  · exact ⟨_, _, laysFilling_switches_paid h hA Vd hOk 0 hp h₀⟩

/-- **hTie of k1_fiveJ_first.** hA, h, parts, hQ, w, Said, hSaid: as there, at S := Sz.ref, Op := openHonest.
hI: on the letter I, paid at matrixInput by trace_at_matrix. hF2: the second family of the item, at each
segment. At an input that does not meet ReadyInput the law is idle. -/
theorem tie_at_first {files : VerifierAndGoals.PublicFiles}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script = firstScriptAt I Sz.ref openHonest A h.firstChain)
    (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hI : ∀ u ξ C, I.trace A.Z u ξ = some C → ∃ i x,
      C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i x) ∧
        ServesAt (P5J.At.X A.Z) i x)
    (hF2 : ∀ l, l < 25 → TieReadsS (firstLetters h parts w) Said (P5J.At.cs A.Z) (P5J.At.arr A.Z)
      (P5J.At.ms A.Z files.lay) (witBT I A.Z) (K3.matsOwn (P5J.At.X A.Z) l) (K1.noL l false) l
      (nReads (P5J.At.X A.Z) l)) :
    ∀ l, l < 25 → ExchangeAtS (firstThread h parts w) Said (K1.noL l false) (.tie l) := by
  obtain ⟨script, numbers⟩ := parts
  dsimp only at hQ
  subst hQ
  intro l hl
  have eF : A.F = h.description :=
    Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.head.laid.value)
  have hV : ReadyInput h.description A.H w → ReadyInput A.F A.H w := fun d => eF ▸ d
  exact exchangeAtS_tie_all hA h.head _ _ _ _ _ _ _ _ _ _ w Said hSaid hI hV hl
    (tieMatS_ok hA h.head _ _ _ _ _ _ _ _ _ w Said hSaid hI hV (fun _ d => d.1) hl) (hF2 l hl)

/-- **hTie of k1_fiveJ_first, whole.** hA, h, parts, hQ, w, Said, hSaid: as there, at S := Sz.ref,
Op := openHonest. hI: on the letter I, paid at matrixInput by trace_at_matrix. -/
theorem tie_first {files : VerifierAndGoals.PublicFiles}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script = firstScriptAt I Sz.ref openHonest A h.firstChain)
    (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hI : ∀ u ξ C, I.trace A.Z u ξ = some C → ∃ i x,
      C.cell = OnBytes.HonestTrace.cellOf (P5J.At.X A.Z) (theTrace (P5J.At.X A.Z) i x) ∧
        ServesAt (P5J.At.X A.Z) i x) :
    ∀ l, l < 25 → ExchangeAtS (firstThread h parts w) Said (K1.noL l false) (.tie l) := by
  refine tie_at_first hA h parts hQ w Said hSaid hI fun l hl => ?_
  obtain ⟨script, numbers⟩ := parts
  dsimp only at hQ
  subst hQ
  exact tieReadsS_base h.head hA (cellsB I A.Z) tokB (otherSendersAt I Sz.ref A h.firstChain)
    (othersApart_first h.head hA) _ _ _ _ _ _ _ _ _ w Said hSaid hl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieMatS_ok
#print axioms ProofFile.Honest.K1.tie_at_first
#print axioms ProofFile.Honest.K1.tie_first
