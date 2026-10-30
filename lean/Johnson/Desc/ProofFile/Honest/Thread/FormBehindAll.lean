-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FormBehindAll.lean: the column `hF` of the gathering
(`owesS_head_form`, GatherHeadForm.lean) at the first chain's invariant at the full size, gathered
from the families of numbers. `FormBehindAtS` (FormShare.lean) is the column at one number: after an
accepting step on the honest prover's messages the part `Form` of the invariant holds at the next
border. Where a lemma of another file proves it under the library's hypothesis `AtMgA` alone, it is
called here. At the other numbers it is a hypothesis, one for each family, so that the statements
list what is still to be proved. No definition.

  1  `noL_lt`, `k3K_lt`   the numbers of K1's later sub-protocols and of K3's lookups in a segment
     other than the output head's
  2  `head_form_k1`, `head_form_w`, `head_form_open`, `head_form_bat`, `head_form_eq`,
     `head_form_shut`, `head_form_k10`, `head_form_k8`, `head_form_k8h`, `head_form_k12`,
     `head_form_k6`, `head_form_k4`, `head_form_k5`, `head_form_k7`, `head_form_k13`   the column at
     205 numbers, whatever is said before the chain
  3  `head_hF_kinds`   the column at all numbers, from the 13 families that are left (153 numbers)
  4  `head_form_k2_link`, `head_form_k2_head`, `head_form_k2_finish`, `head_form_k3`,
     `head_form_k11`   the column at 76 more numbers, where what is said before the chain is
     `SaidOk` (SaidOk.lean)
  5  `head_hF_ok`   the column at all numbers at `SaidOk`, from the five families that are left: the
     77 numbers of the kind `frame`

Called under 2: K1's 52 (K1FormBehind.lean, K1FormBehindEnds.lean, K1FormBehindTwo.lean), K9's 75
(K9FormBehind.lean); and of other authors, in Johnson/Desc/ProofFile/Honest/: K10's 25
(K10/Law/FormBehind.lean), K8's 25 (K8/Law/FormBehind.lean), K4's 12 (K4/Law/FormBehindHead.lean),
K5's 12 (K5/Law/FormBehind.lean), number 354 (K12/Law/FormBehind.lean), number 341
(K6/Law/Behind.lean), number 338 (K7/Law/FormBehind.lean), number 355 (K13/FormBehind.lean). Called
under 4: K2's 25 (K2FormBehind.lean), K3's 50 (K3FormBehind.lean), number 346 (K11FormBehind.lean).

Left as hypotheses of `head_hF_ok`: the frame's 77 numbers in five families. GatherFrames.lean
proves these.

Limits.
  * That an accepting step exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormShare
import Johnson.Desc.ProofFile.Honest.Thread.Numbers358
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.Desc.ProofFile.Honest.Thread.K2FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.K3FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.K11FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.K1FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.K1FormBehindEnds
import Johnson.Desc.ProofFile.Honest.Thread.K9FormBehind
import Johnson.Desc.ProofFile.Honest.K10.Law.FormBehind
import Johnson.Desc.ProofFile.Honest.K8.Law.FormBehind
import Johnson.Desc.ProofFile.Honest.K12.Law.FormBehind
import Johnson.Desc.ProofFile.Honest.K6.Law.Behind
import Johnson.Desc.ProofFile.Honest.K4.Law.FormBehindHead
import Johnson.Desc.ProofFile.Honest.K5.Law.FormBehind
import Johnson.Desc.ProofFile.Honest.K7.Law.FormBehind
import Johnson.Desc.ProofFile.Honest.K13.FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.K1FormBehindTwo
import Johnson.IMR.SendsK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (kindsBeforeBatching blockPlaces)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- The number of a later sub-protocol of K1 in a segment other than the output head's. -/
theorem noL_lt {l : Nat} (hl : l < 24) (d : Bool) :
    VerifiableInference.Desc.K1.noL l d = 14 * l + (if d then 5 else 3) + 2 := by
  show 14 * l + ((if d then 5 else 3) + (if l = 24 then 1 else 0)) + 2 = _
  rw [if_neg (show ¬ l = 24 by omega)]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- At K1's 50 later sub-protocols. -/
theorem head_form_k1 {l : Nat} (hl : l < 25) (d : Bool) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (VerifiableInference.Desc.K1.noL l d) :=
  fun _ hblk _ _ _ _ _ _ _ _ hA _ hS =>
    k1_form_behind_later h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl d hblk hA.1 hS

/-- At number 356. -/
theorem head_form_w :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      356 :=
  fun _ hblk _ _ _ _ _ _ _ _ hA _ hS =>
    k1_form_behind_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hA.1 hS

/-- At a segment's batching. -/
theorem head_form_bat {l : Nat} (hl : l < 25) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + IM.nAt l + 2) :=
  fun _ hblk _ _ _ _ _ _ _ _ hA _ hS =>
    k9_form_behind_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hblk hA.1.2.2.1 hS

/-- At the sub-protocol that writes the batching's sum as one equation. -/
theorem head_form_eq {l : Nat} (hl : l < 25) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + IM.nAt l + 4 + 0) :=
  fun _ hblk _ _ _ _ _ _ _ _ hA _ hS =>
    k9_form_behind_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hblk hA.1 hS

/-- At the sub-protocol that ends a segment's closing. -/
theorem head_form_shut {l : Nat} (hl : l < 25) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + IM.nAt l + 4 + 2) :=
  fun _ hblk _ _ _ _ _ _ _ _ hA _ hS =>
    k9_form_behind_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hblk hA.1.2.2.1 hS

/-- At a segment's closing (K10). -/
theorem head_form_k10 {l : Nat} (hl : l < 25) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + IM.nAt l + 5) :=
  fun blk hblk k s m E ds y cols s' hA _ hS =>
    ProofFile.Honest.K10.k10_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl blk hblk k s m E
      ds y cols s' hA.1 hS

/-- At K8 in a segment other than the output head's. -/
theorem head_form_k8 {l : Nat} (hl : l < 24) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + 4 + 2) :=
  fun blk hblk k s m E ds y cols s' hA _ hS =>
    ProofFile.Honest.K8.k8_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl blk hblk k s m E
      ds y cols s' hA.1 hS

/-- At K8 in the output head's segment, number 343. -/
theorem head_form_k8h :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      343 :=
  fun blk hblk k s m E ds y cols s' hA _ hS =>
    ProofFile.Honest.K8.k8_form_behind_last h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hblk k s m E
      ds y cols s' hA.1 hS

/-- At the proximity test (K12), number 354. -/
theorem head_form_k12 :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      354 :=
  fun blk hblk k s m E ds y cols s' hA _ hS =>
    ProofFile.Honest.K12.k12_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hblk k s m E ds y
      cols s' hA.1 hS

/-- At K6, number 341. The lemma that is called has a hypothesis on `Kp`. It is called at the
condition that always holds, and `head_formBehindAtS_kp` carries the result over to `Kp`. -/
theorem head_form_k6 :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 :=
  head_formBehindAtS_kp h H Q test carryX item n₁ n₂ b₀ Vd Rd (fun _ _ _ => True) w Kp Said
    fun blk hblk k s m E ds y cols s' hA hd hS =>
      (ProofFile.Honest.K6.k6_form_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd (fun _ _ _ => True) w
        (fun _ _ _ => trivial) blk hblk k s m E ds y cols s' hA.1 hd hS).1

/-- At K1's opening, number 2. -/
theorem head_form_open :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      2 :=
  k1_formBehindAtS_two h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said

/-- At K4's 12 sub-protocols. -/
theorem head_form_k4 {g : Nat} (hg : g < 12) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * (2 * g) + 2 + 2) :=
  ProofFile.Honest.K4.k4_form_behindS_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hg

/-- At K5's 12 sub-protocols. -/
theorem head_form_k5 {g : Nat} (hg : g < 12) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * (2 * g + 1) + 2 + 2) :=
  fun blk hblk k s m E ds y cols s' hA _ hS =>
    ProofFile.Honest.K5.k5_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg blk hblk k s m E
      ds y cols s' hA.1 hS

/-- At K7, number 338. -/
theorem head_form_k7 :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      338 :=
  fun blk hblk k s m E ds y cols s' hA _ hS =>
    ProofFile.Honest.K7.k7_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hblk k s m E ds y
      cols s' hA.1 hS

/-- At K13, number 355. -/
theorem head_form_k13 :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      355 :=
  fun blk hblk k s m E ds y cols s' hA _ hS =>
    ProofFile.Honest.K13.k13_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hblk k s m E ds y
      cols s' hA.1 hS

/-- **The column `hF`, from the families that are left.** -/
theorem head_hF_kinds
    (hfront : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      0)
    (hlaid : ∀ l, l < 25 →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + 1))
    (hbehind : ∀ l, l < 25 →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + IM.nAt l + 3))
    (hcleared : ∀ l, l < 25 →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + IM.nAt l + 7))
    (hseal : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      357)
    (hk2 : ∀ l, 1 ≤ l → l < 24 →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + 0 + 2))
    (hk2h : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      339)
    (hk2f : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      353)
    (hk3c : ∀ l, l < 24 →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + 1 + 2))
    (hk3d : ∀ l, l < 24 →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + 6 + 2))
    (hk3ch : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      340)
    (hk3dh : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      345)
    (hk11 : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      346) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      b := by
  intro b hb
  have hb' : b < cF.blocksInOrder.length := hb
  rw [head_len h] at hb'
  refine all_numbers
    (FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said)
    hfront hlaid ?_ ?_ hk2f (head_form_k12 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said)
    (head_form_k13 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said)
    (head_form_w h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said) hseal b hb'
  · intro l hl i hi
    by_cases h24 : l = 24
    · subst h24
      rw [nAt_head] at hi
      have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
        omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact head_form_k7 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
      · exact hk2h
      · exact hk3ch
      · exact head_form_k6 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
      · exact head_form_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
          (l := 24) (by decide) false
      · exact head_form_k8h h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
      · exact head_form_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
          (l := 24) (by decide) true
      · exact hk3dh
      · exact hk11
    · have hl' : l < 24 := by omega
      rw [nAt_lt hl'] at hi
      have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      have k1 : ∀ d : Bool,
          FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
            (14 * l + (if d then 5 else 3) + 2) := by
        intro d
        rw [← noL_lt hl' d]
        exact head_form_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl d
      obtain ⟨g, hg, hgl⟩ : ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) :=
        ⟨l / 2, by omega, by omega⟩
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · by_cases l0 : l = 0
        · subst l0
          exact head_form_open h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
        · exact hk2 l (by omega) hl'
      · exact hk3c l hl'
      · rcases hgl with rfl | rfl
        · exact head_form_k4 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hg
        · exact head_form_k5 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hg
      · exact k1 false
      · exact head_form_k8 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl'
      · exact k1 true
      · exact hk3d l hl'
  · intro l hl j j2 j7
    have hc : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact head_form_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl
    · exact hbehind l hl
    · exact head_form_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl
    · exact head_form_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl
    · exact head_form_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl
    · exact hcleared l hl

/-! ## At `SaidOk` -/

/-- The number of a lookup (K3) in a segment other than the output head's. -/
theorem k3K_lt {l : Nat} (hl : l < 24) (d : Bool) :
    VerifiableInference.OnPublicFiles.k3K l d = 14 * l + (if d then 6 else 1) + 2 := by
  show 14 * l + ((if d then 6 else 1) + (if l = 24 then 1 else 0)) + 2 = _
  rw [if_neg (show ¬ l = 24 by omega)]
  rfl

/-- At K2 at the first place of a segment from 1 to 23. -/
theorem head_form_k2_link {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (14 * l + 0 + 2) := by
  intro blk hblk k s m E ds y cols s' hA _ hS
  have hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[0]? = some KindName.K2 := by
    have hl0 : (l == 0) = false := beq_eq_false_iff_ne.2 (by omega)
    rw [hl0]
    unfold IM.subAt
    rw [if_neg (by omega)]
    split <;> rfl
  exact k2_form_behind_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk)
    (by rw [head_place_hear h (by omega) hk hblk]) hblk hA hS

/-- At K2 in the output head's segment, number 339. -/
theorem head_form_k2_head :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      339 := by
  intro blk hblk k s m E ds y cols s' hA _ hS
  have hb' : cF.blocksInOrder[14 * 24 + 1 + 2]? = some blk := hblk
  exact k2_form_behind_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk)
    (by rw [head_place_hear h (l := 24) (i := 1) (k := .K2) (by decide) rfl hb']) hblk hA hS

/-- At K2 after the last segment, number 353. -/
theorem head_form_k2_finish :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      353 := by
  intro blk hblk k s m E ds y cols s' hA _ hS
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk
  have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
  have hp' := hp
  rw [← e', IM.place_353] at hp'
  exact k2_form_behind_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp
    (by rw [← Option.some.inj hp']) hblk hA hS

/-- At K3's 50 lookups. -/
theorem head_form_k3 {l : Nat} (hl : l < 25) (d : Bool) :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (VerifiableInference.OnPublicFiles.k3K l d) := by
  intro blk hblk k s m E ds y cols s' hA _ hS
  cases d
  · exact k3_form_behind_calls h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hblk hA hS
  · exact k3_form_behind_digits h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hblk hA hS

/-- At the merge (K11), number 346. -/
theorem head_form_k11 :
    FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      346 :=
  fun _ hblk _ _ _ _ _ _ _ _ hA _ hS =>
    k11_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hA hS

/-- **The column `hF` at `SaidOk`, from the families that are left there.** -/
theorem head_hF_ok
    (hfront : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      0)
    (hlaid : ∀ l, l < 25 →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (14 * l + 1))
    (hbehind : ∀ l, l < 25 →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (14 * l + IM.nAt l + 3))
    (hcleared : ∀ l, l < 25 →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (14 * l + IM.nAt l + 7))
    (hseal : FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      357) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      FormBehindAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      b :=
  head_hF_kinds h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w SaidOk hfront hlaid hbehind hcleared
    hseal
    (fun l h1 h24 => head_form_k2_link h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w h1 h24)
    (head_form_k2_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_form_k2_finish h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (fun l hl => by
      have e := k3K_lt hl false
      have t := head_form_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (l := l) (by omega) false
      rw [e] at t
      exact t)
    (fun l hl => by
      have e := k3K_lt hl true
      have t := head_form_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (l := l) (by omega) true
      rw [e] at t
      exact t)
    (head_form_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (l := 24) (by decide) false)
    (head_form_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (l := 24) (by decide) true)
    (head_form_k11 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.noL_lt
#print axioms ProofFile.Honest.FirstThread.head_form_k1
#print axioms ProofFile.Honest.FirstThread.head_form_w
#print axioms ProofFile.Honest.FirstThread.head_form_bat
#print axioms ProofFile.Honest.FirstThread.head_form_eq
#print axioms ProofFile.Honest.FirstThread.head_form_shut
#print axioms ProofFile.Honest.FirstThread.head_form_k10
#print axioms ProofFile.Honest.FirstThread.head_form_k8
#print axioms ProofFile.Honest.FirstThread.head_form_k8h
#print axioms ProofFile.Honest.FirstThread.head_form_k12
#print axioms ProofFile.Honest.FirstThread.head_form_k6
#print axioms ProofFile.Honest.FirstThread.head_form_open
#print axioms ProofFile.Honest.FirstThread.head_form_k4
#print axioms ProofFile.Honest.FirstThread.head_form_k5
#print axioms ProofFile.Honest.FirstThread.head_form_k7
#print axioms ProofFile.Honest.FirstThread.head_form_k13
#print axioms ProofFile.Honest.FirstThread.head_hF_kinds
#print axioms ProofFile.Honest.FirstThread.k3K_lt
#print axioms ProofFile.Honest.FirstThread.head_form_k2_link
#print axioms ProofFile.Honest.FirstThread.head_form_k2_head
#print axioms ProofFile.Honest.FirstThread.head_form_k2_finish
#print axioms ProofFile.Honest.FirstThread.head_form_k3
#print axioms ProofFile.Honest.FirstThread.head_form_k11
#print axioms ProofFile.Honest.FirstThread.head_hF_ok
