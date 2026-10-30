-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FormBehindHead.lean: CONDITIONAL.

What is here. THE THREAD's FORM BEHIND THE STEP OF THE MEMBER OF THE LAYERS' OWN ROUNDS (kind K4),
BY ITSELF, at the first chain's thread at the library's own parameters (`lettersHead`), WITH NOTHING
ASKED OF THE THREAD's PARAMETERS b₀, Rd AND Kp. `k4_behind_all` (Law/ElevenHead.lean) ends in the
threads' debt `Behind` (Honest/Thread/Pays.lean): the form behind, what rides behind, and the
member's clause of keeps; it asks hb₀, hKp and hRd, three hypotheses on these parameters. The form
reads none of the three: neither do the thread's other clauses but `rides`, nor the list of members,
nor the member's step. So `k4_behind_all` is called at another thread: the same but for Rd and Kp
that always hold and a border b₀ beyond the one behind the member (k + 2); its first conjunct is the
form at the thread meant. Words: as in Law/ElevenHead.lean.

  `k4_form_behind`   **the form behind the member's step, from h, the member's place, the thread in
      front and the member's accepting step.**
  `k4_form_behind_at`   the same at the number 14 * (2 * g) + 2 + 2, g < 12.
  `k4_form_behindS_at`   the second from the pair of the thread's sentence and what has been said
      (`ThrS`), at every Said.

Limits. CONDITIONAL: on h; `k4_form_behind` besides on A (the member's number, segment and place
stand in the written lists: the library's `atK4_full` has it at each g < 12), the two others on hg.
All three speak only where the thread stands in front of the member and the member's step accepts:
where it stands nowhere they hold emptily. THAT THE THREAD STANDS AT ANY RUN, OR THAT ANY STEP OF
THE MEMBER ACCEPTS, IS NOT SHOWN; of h together with these no example is known to us. Nothing on
what rides behind or on keeps: these stay `k4_behind_all`'s. THE FULL SIZE ALONE, AND THE FORMAT's
EARLIER HASH ALONE; that h holds of any files is not shown here: the side library AtFullSide proves,
with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). IT IS A LAW, NOT A
PART: it rests on modules under Johnson/Goal/: no file that defines a part may build on it; it
states no goal. Nothing on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ElevenHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Road.K4 (AtK4 atK4_full)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h and A. **THE FORM BEHIND THE MEMBER's STEP.** -/
theorem k4_form_behind {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk c s mm E ds y
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (k + 1) c s' y.2 :=
  fun blk hb c s mm E ds y cols s' hT hd hS =>
    (k4_behind_all h H Q test carryX item n₁ n₂ (k + 2) Vd (fun _ _ _ => True)
      (fun _ _ _ => True) w A (by omega) (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial) blk hb
      c s mm E ds y cols s'
      ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1, hT.2.2.2.2.1,
        ⟨fun hle => absurd hle (by omega), trivial⟩, hT.2.2.2.2.2.2⟩ hd hS).1

/-- CONDITIONAL: on h and hg. **THE SAME AT THE MEMBER's NUMBER.** -/
theorem k4_form_behind_at {g : ℕ} (hg : g < 12) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[14 * (2 * g) + 2 +
        2]? = some blk →
      ∀ c s mm E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (14 * (2 * g) + 2 + 2) c s
        mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk c s mm E ds y
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * (2 * g) + 2 + 2 + 1) c s' y.2 := by
  have e : 14 * (2 * g) + 2 + 2 = 28 * g + 4 := by omega
  rw [e]
  exact k4_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (atK4_full g hg)

/-- CONDITIONAL: on h and hg. **THE SAME FROM THE PAIR** of the thread's sentence and what has been
said, at every Said. -/
theorem k4_form_behindS_at (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {g : ℕ}
    (hg : g < 12) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[14 * (2 * g) + 2 +
        2]? = some blk →
      ∀ c s mm E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * (2 * g) + 2 + 2) c s mm E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk c s mm E ds y
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * (2 * g) + 2 + 2 + 1) c s' y.2 :=
  fun blk hb c s mm E ds y cols s' hT hd hS =>
    k4_form_behind_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg blk hb c s mm E ds y cols s'
      hT.1 hd hS

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_form_behind
#print axioms ProofFile.Honest.K4.k4_form_behind_at
#print axioms ProofFile.Honest.K4.k4_form_behindS_at
