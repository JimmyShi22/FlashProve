-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LookTieHead.lean: CONDITIONAL.

What is here. The hypothesis `K4LookTieAt` (Law/ScriptAt.lean) of the tops on the member of the
feed-forward layers' own rounds (sub-protocol K4), at the thread with the library's own values
(`lettersHead`, Honest/Thread/FirstHead.lean), brought down to its three equations. `K4LookTieAt`
says two things: that two readers of the verifier's state find one structure g of what the lookup
has heard, and that g's fields zx, zk and e are what the parameter `look` makes of the challenges
heard. THE FIRST COMES OUT OF THE THREAD: the two readers read two different fields of the state
(`seatS.look`: the field fo; `S.lookHeard?`: the field lookHeard); the test of the public item
`.look m` at a layers' segment (the library's `lookLayB`, Johnson/Desc/First/FillK4.lean) holds that
fo is there and that the two fields are equal, and `two_tests` (Law/LookOfPromise.lean) has that
test out of the thread's open public items. What stays is `K4LookPtsAt`: the three equations, at
whatever `S.lookHeard?` finds. The proof is that call and a case split.

  `K4LookPtsAt`   the three equations. A definition.
  `lookTie_head`   **`K4LookTieAt look Qp s mm`**, from them.

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN: hT
: Thr is a hypothesis. hp (`K4LookPtsAt`): A HYPOTHESIS ON THE PARAMETER `look`, THE STATE AND THE
CHALLENGES HEARD: no witness and no sent value stands in it; Law/LookPtsHead.lean has it from a
sentence on `look` alone. Lh (`LaidK4`, Law/SeatedHead.lean): on public lists and numbers. The side
library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with Lh, hT and hp no example is known to us. THE FULL SIZE ALONE, and the
format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on any
other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. They
come with h and with Law/ElevenHead.lean. A LAW, NOT A PART: no file that defines a part of the
proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ElevenHead
import Johnson.Desc.ProofFile.Honest.K4.Law.LookOfPromise
import Johnson.Desc.ProofFile.Honest.K4.Law.ScriptAt
import Johnson.Desc.ProofFile.Honest.Thread.FormLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (eAll)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.FillK4 (lookLayB)
open VerifiableInference.Desc.Sound (MsgT mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_pub)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- **The three equations of `K4LookTieAt`**, at whatever the state's reader of what the lookup has
heard finds. This defines a hypothesis; the definition claims nothing. -/
def K4LookPtsAt {W X : Type} (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub) (s : TS)
    (m : Mid W X) : Prop :=
  ∀ g, s.lookHeard? = some g →
    (look Q m.st.heard).zx = g.zx ∧ (look Q m.st.heard).zk = g.zk ∧ (look Q m.st.heard).e = g.e

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, hT and hp. **`K4LookTieAt` FROM ITS THREE EQUATIONS, WHERE THE THREAD
STANDS.** -/
theorem lookTie_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hp : K4LookPtsAt look Qp s mm) : K4LookTieAt look Qp s mm := by
  have N := nine_head h Lh
  obtain ⟨_, t2⟩ := two_tests (Dm := h.𝔇) (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
    (mgAll_more_base h.𝔇) N.hH (atK4_of_laid Lh) N.Sx N.Sd
    (fun q hq => thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT hq)
  unfold lookLayB at t2
  split at t2
  · rename_i a ha
    rw [Bool.and_eq_true, decide_eq_true_eq] at t2
    obtain ⟨t3, e⟩ := t2
    cases hfo : a.fo with
    | none => simp [hfo] at t3
    | some g₁ =>
      have h1 : s.lookHeard? = some g₁ := by
        simp only [VerifiableInference.Desc.First.S.lookHeard?, ha]
        rw [← e]
        exact hfo
      have h2 : seatS.look s = some g₁ := by
        simp only [seatS, ha]
        exact hfo
      obtain ⟨b1, b2, b3⟩ := hp g₁ h1
      exact ⟨g₁, h1, h2, b1, b2, b3⟩
  · cases t2

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.lookTie_head
