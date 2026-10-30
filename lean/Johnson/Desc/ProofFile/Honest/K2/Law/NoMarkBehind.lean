-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/NoMarkBehind.lean: the kind "the code switch" (K2): UNDER THE
HEAD ALONE, AT EVERY PLACE OF THE KIND ON THE FIRST CHAIN: BEHIND A YES OF THE PLACE's BLOCK THE
STATE BEARS NO MARK. NOTHING IS ASKED OF THE STATE IN FRONT. Two statements with their proofs; no
definition. A joining of the library's theorems.

  `k2_sits_of_head`   the head's chain's own block at a place of the kind sits on the kind's own
                    block behind one door, whose way out hands on no marked state: the library's
                    `k02_sitsU_pAt_at` (Johnson/P1K2R/SitsAtConst.lean) with its two named
                    premises paid from the head, as Johnson/P1K2R/LastLine.lean and
                    LastLineTests.lean pay them
  `k2_noMark_behind`   so a yes of that block's step leaves no mark behind

Limits. THE HEAD IS A LONG CONDITION OF ITS OWN. No example of the head is shown here; the library's
`head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean) has one under four
premises on the three public files.


The line that strikes an instance below stands in the imported file too. Nothing on any property.
-/
import Johnson.P1K2R.LastLineOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.First.K2Caller
open H2K.JointK (Sits)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head alone: the place's block sits on the kind's own, behind one door.** -/
theorem k2_sits_of_head (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) {k : Nat}
    {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) {B : Block VerifiableInference.Desc.First.S Cl}
    (hB : cF.blocksInOrder[k]? = some B) :
    ∃ (enter : VerifiableInference.Desc.First.S → Except String VerifiableInference.Desc.First.S)
      (leave : VerifiableInference.Desc.First.S → VerifiableInference.Desc.First.S →
        Except String VerifiableInference.Desc.First.S),
      Sits B (VerifiableInference.Desc.First.K2.codeSwitchKind (ProofFile.pAtK2 Zp (P1K2.mOf k)) :
        Block VerifiableInference.Desc.First.S Unit) enter leave ∧
      P1K2.LeftDoor enter leave ∧ P1K2.EndsUnmarked leave := by
  have hp := P5J.pins_of_laid Hd.toAtMg.scope Hd.toAtMg.laid
  obtain ⟨B', enter, leave, hB', hS, hL, hE⟩ := P1K2.k02_sitsU_pAt_at Hd.toAtMg
    (H2K12.spots_atAll Hd hp.2) (P1K2.links25_atAll Hd) k pl ha hk
  obtain rfl : B' = B := Option.some.inj (hB'.symm.trans hB)
  exact ⟨enter, leave, hS, hL, hE⟩

/-- **No mark behind a yes.** -/
theorem k2_noMark_behind (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) {k : Nat}
    {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[k]? = some pl)
    (hk : pl.kind = KindName.K2) {B : Block VerifiableInference.Desc.First.S Cl}
    (hB : cF.blocksInOrder[k]? = some B) {ft : Nat} {s s' : VerifiableInference.Desc.First.S}
    (hy : IM.Yes ft B s s') : s'.failed = none := by
  obtain ⟨enter, leave, hS, -, hE⟩ := k2_sits_of_head Hd ha hk hB
  obtain ⟨rs, cols, n, hy⟩ := hy
  obtain ⟨t, t', -, -, e₃⟩ := hS.step ft s s' rs cols n hy
  exact hE s t' s' e₃

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.k2_sits_of_head
#print axioms ProofFile.Honest.K2.Law.k2_noMark_behind
