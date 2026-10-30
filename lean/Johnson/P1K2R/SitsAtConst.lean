-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SitsAtConst.lean: AT EVERY PLACE OF THE CODE SWITCH IN THE COMPOSED MEANING's
    CONSTANT's OWN LIST OF PLACES THE SUB-PROTOCOL THAT THE HEAD's CHAIN HOLDS THERE SITS ON THE
    KIND's OWN AT THE NUMBERS AT WHICH THE SENTENCE ON THE CARRIED CLAIM IS SPENT (`ProofFile.pAtK2 Zp
    m`), BEHIND ONE DOOR THAT LEAVES WHAT `Left` NAMES AND HANDS ON NO MARKED STATE; AND THE FIRST
    THREE CLAUSES OF WHAT IS OWED AT A PLACE STAND AT THESE NUMBERS. One definition, three theorems.
    A law file: no sub-protocol imports it.

Why. Johnson/P1K2R/ThreeAtConst.lean has the three clauses at "some numbers p". The fourth clause
    (`K2AllOwes`) speaks of the numbers `pAt m` of the sentence on the carried claim. They must be
    one.

What is said.
  `mOf i`: the carried claim's segment at the place number i: l - 1 at 14 l + 2; 23 at 339; 24 at
      353.
  `k02_sitsU_pAt_at`: under the head `P5J.AtMg` at the second hash function, the named test
      `spotsFitB Zp` (Johnson/Top/H0/K2Caller/PAtSeated.lean) and "the request's shape has 25
      segments": at every place i of the kind: the head's chain holds B at i, `Sits B (codeSwitchKind
      (ProofFile.pAtK2 Zp (mOf i))) enter leave`, `LeftDoor enter leave`, `EndsUnmarked leave`. CALLS:
      `k02_sits_pAt` (Johnson/Top/H0/K2Caller/SitsAtP.lean) with its three doors; our `leftDoor_*`
      (Johnson/P1K2R/SitsLeft.lean) and `ends_*` (Johnson/P1K2R/SitsNoMark.lean) at them;
      `IM.Open.unique`, `IM.back_numbers`, `k2_spots` as in ThreeAtConst.lean.
  `k2_three_pAt_at_const`: so the three clauses, with he and hk, at p := `ProofFile.pAtK2 Zp (mOf i)`.
  `mOf_link`: mOf (14 l + 0 + 2) = l - 1.

Limits. THE TEST `spotsFitB` IS A PREMISE (by its owner's page it ran true once at the full size);
    so is "25 segments". THE FOURTH CLAUSE IS NOT TOUCHED. A member of the head is proved at `storedPublicFiles`
    and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.ThreeAtConst
import Johnson.Top.H0.K2Caller.SitsAtP

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes.Maker Iop
open VerifiableInference.Desc (Block Chain Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind ownPiece)
open VerifiableInference.Desc.First.K2Caller (k2Q spotsFitB)
open H2K.JointK (Sits)
open _root_.Run (ckP)
open ProofFile (Cl)

/-- The carried claim's segment at the place number i. -/
def mOf (i : ℕ) : ℕ := if i = 353 then 24 else if i = 339 then 23 else i / 14 - 1

theorem mOf_link (l : ℕ) (h1 : 1 ≤ l) (h24 : l < 24) : mOf (14 * l + 0 + 2) = l - 1 := by
  unfold mOf
  rw [if_neg (by omega), if_neg (by omega)]
  omega

/-- **At the sentence's own numbers, behind one door, at every place of the kind.** -/
theorem k02_sitsU_pAt_at {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np :
                  H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (hsp :
                                    spotsFitB Zp = true) (h25 : Zp.s₀.check.frame.shape.link.length = 25) (i : ℕ) (a : Place) (ha :
                                    P5J.At.ps[i]? = some a) (hk : a.kind = KindName.K2) :
    ∃ (B : Block S Cl) (enter : S → Except String S) (leave : S → S → Except String S), cF.blocksInOrder[i]?
        = some B ∧ Sits B (codeSwitchKind (ProofFile.pAtK2 Zp (mOf i)) : Block S Unit) enter leave ∧ LeftDoor enter
        leave ∧ EndsUnmarked leave := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Z', Bs', base', c', A', B', O', H⟩ := k02_sits_pAt h.scope h.reads h.laid.value
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := O.unique O'
  obtain ⟨h1, h2, h3⟩ := H hsp h25
  rcases k2_spots i a ha hk with ⟨l, a1, a24, rfl⟩ | rfl | rfl
  · obtain ⟨b, hb, hX⟩ := h1 l a1 a24
    obtain ⟨-, fs, f, hfs, hf, hS⟩ := hX (flat_planOk O h.laid.planOk b (List.mem_of_getElem? hb))
    rw [mOf_link l a1 a24]
    exact ⟨b, _, _, hb, hS, leftDoor_opened hfs hf (by omega), ends_opened f⟩
  · obtain ⟨b, hb, hX⟩ := h2
    obtain ⟨-, HP, -, hS⟩ := hX (flat_planOk O h.laid.planOk b (List.mem_of_getElem? hb))
    exact ⟨b, _, _, hb, hS, leftDoor_head HP, ends_head HP⟩
  · obtain ⟨b, hb, hX⟩ := h3
    obtain ⟨-, hS⟩ := hX (back_planOk O h.laid.planOk (List.mem_of_getElem? hb))
    exact ⟨_, _, _, (IM.back_numbers h.scope h.reads O).1 0 b hb, hS.same _ rfl rfl fun e =>
        (Bool.and_eq_true _ _ ▸ e : _ ∧ _).1, leftDoor_finish, ends_finish⟩

/-- **The first three clauses at the sentence's own numbers.** -/
theorem k2_three_pAt_at_const {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np
                  : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (hsp :
                                    spotsFitB Zp = true) (h25 : Zp.s₀.check.frame.shape.link.length = 25) (L : P5J.Free
                                    OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (q₁ : (P5J.F0T
                                                OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁) (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np
                                                                     cF).shared.blocksInOrder = L.c₂ :: L.k₂) (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ ::
                                                                              L.k₃) (i : ℕ) (q) (a : Place) (hq : (h.row L)[i]? = some q) (ha : P5J.At.ps[i]? = some a) (hk :
                                                                              a.kind = KindName.K2) :
    ∃ (B : Block S Cl) (enter : S → Except String S) (leave : S → S → Except String S) (d₁ d₂ : RDT)
        (extq : _), cF.blocksInOrder[i]? = some B ∧ Sits B (codeSwitchKind (ProofFile.pAtK2 Zp (mOf i)) : Block S Unit) enter
        leave ∧ LeftDoor enter leave ∧ q = k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base
        d₁ d₂ extq ∧ (∀ a τ b, (ownPiece (k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base
        d₁ d₂ extq) B (fun _ _ w => w) (k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base d₁
        d₂ extq).err).ior.red.out a τ = some b → a.1.failed = none) ∧ [d₁, d₂].map (·.entry) =
        (VerifiableInference.Desc.First.K2.rounds (ProofFile.pAtK2 Zp (mOf i))).map (·.entry) ∧ ∀ d ∈ [d₁,
              d₂], Fmt.kindOf d.entry.name = some d.kind := by
  obtain ⟨B, enter, leave, hB, hS, hD, hE⟩ := k02_sitsU_pAt_at h hsp h25 i a ha hk
  have hi : i < 357 := by
    rcases k2_spots i a ha hk with ⟨l, _, _, rfl⟩ | rfl | rfl <;> omega
  obtain ⟨d₁, d₂, extq, e, he, hkk⟩ := k2_written_at_row h L q₁ q₂ q₃ i q hq hi B hB _ hS.rounds
  exact ⟨B, enter, leave, d₁, d₂, extq, hB, hS, hD, e, k2_unmarked_at _ B enter leave hS hD hE _ _
      d₁ d₂ extq, he, hkk⟩

end P1K2

#print axioms P1K2.mOf_link
#print axioms P1K2.k02_sitsU_pAt_at
#print axioms P1K2.k2_three_pAt_at_const
