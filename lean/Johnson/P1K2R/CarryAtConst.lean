-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K2R/CarryAtConst.lean: the code switch: THREE FIELDS OF THE KIND's NAMED CONDITION
(`K2AllOwes`: Johnson/Top/H0/K2Ties/Assembly.lean), AT THE CLOSED CONSTANT's TERMS: those on the
carried claim: its table of typed structures, its sentence in the composed meaning, its way in.
The letters are laid so: rowAt := `ProofFile.rowAtK2 Zp.pol Z.lay Zp.KL` · pAt := `ProofFile.pAtK2 Zp` · door
:= `doorZ Zp` · the frame := the laid data's. A join; nothing is evaluated but one closed fact.

Main names:
  `hrow_const`: where the named test `tableWrittenB` accepts, the table's entry m is the written
    table's.
    `hcar_const`: under the head: the carried claim at these letters IS the composed meaning's field
    carry at the constant (`mgAll_carry`; `At.cr1` is `carryAtZ`).
  `stand25_full`: BY LEAN's KERNEL: at the 25 numbers of the kind's places the written list's
    place stands between two links, but at the output head's, where it stands in front of the
    head. `stand25_other`: a negative test: one number further on the sentence fails at the first
    place.
  `hdoor_const`: under the table's promise, at a state without a mark: what the way in lets in is
    what `doorZ` hands: at each of the three sorts of place.
Limits. The way in's three sorts are a premise, in the words of the list that hands them.
`tableWrittenB` is a named test that the sealed verifier does not ask. A member of the head is
proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). Nothing on soundness.
On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.DoorOfPromise
import Johnson.Top.H0.K2Caller.TableWritten
import Johnson.Top.H0.Opts.WholeOfLaid
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (standAt)

/-- **hrow**: the table's entry is the written one. -/
theorem hrow_const {pol lay KL : ByteArray} (hT : tableWrittenB pol lay KL = true) {m : ℕ}
    {r : SwRow} (hr : tableFullLit[m]? = some r) : ProofFile.rowAtK2 pol lay KL m = some r :=
  (tableWritten_says hT m).trans hr

/-- The first chain's frame at the laid data. -/
abbrev frD (D : WholeD) : Frame :=
  VerifiableInference.Desc.Sound.frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))
    (D.at frS.P.T.a).key₁ 0

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 1000000 in
/-- **hcar**: the carried claim at these letters is the composed meaning's field at the constant. -/
theorem hcar_const (Hd : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) (m : ℕ) :
    ∀ z, ∀ s y w, carryK2 (ProofFile.rowAtK2 Zp.pol Z.lay Zp.KL) (ProofFile.pAtK2 Zp) (doorZ Zp)
      (K2.orcY (frD D).all
        (frD D).key)
      (fun r H => smpK2 r H) m (z, s) y w →
      (mgAll (Hd.toAtMg.𝔇 Hd.𝔇) mgBase).carry m (z, s) y w := by
  intro z s y w h
  have hW := P1M2.wholeAt_of_laid Hd.toAtMg.laid
  have ea := ProofFile.Law.allAt_of hW
  have ek := ProofFile.Law.keyAt_of hW
  have e : (Hd.toAtMg.𝔇 Hd.𝔇).cr1 = carryAtZ Zp Z.lay := rfl
  rw [mgAll_carry, e]
  unfold carryAtZ
  rw [ea, ek]
  exact h

end

/-- The number of the place whose switch opens group m + 1. -/
def noAt (m : ℕ) : ℕ := if m < 23 then 14 * (m + 1) + 2 else if m = 23 then 339 else 353

/-- A test: where the written list's place number `noAt m` stands. -/
def stand25B (d : ℕ) : Bool :=
  (List.range 25).all fun m =>
    (P5J.At.ps[noAt m + d]?).map (standAt P5J.fullLinks) ==
      some (if m = 23 then .headFront else .between)

set_option maxRecDepth 1000000 in
theorem stand25_full : stand25B 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one number further on. -/
theorem stand25_other : stand25B 1 = false := by decide +kernel

theorem stand_at25 {m : ℕ} (hm : m < 25) :
    ∃ p, P5J.At.ps[noAt m]? = some p ∧
      standAt P5J.fullLinks p = if m = 23 then .headFront else .between := by
  have h := List.all_eq_true.1 stand25_full m (List.mem_range.2 hm)
  rw [Nat.add_zero, beq_iff_eq, Option.map_eq_some_iff] at h
  exact h

/-- **hdoor**: what the way in lets in is what the carried claim's door hands. -/
theorem hdoor_const {P W : Type} {F : Frame} (N : VerifiableInference.Desc.First.Numbers)
    (Mg : VerifiableInference.Desc.First.Meaning P W) (Zp : ProofFile.Pub) {m : ℕ}
    {enter : VerifiableInference.Desc.First.S → Except String VerifiableInference.Desc.First.S}
    (w : (m < 23 ∧ (ProofFile.pAtK2 Zp m).stands = .link ∧ ∀ s t, enter s = .ok t → t = s) ∨
      (m = 23 ∧ (ProofFile.pAtK2 Zp m).stands = .head ∧ ∀ s t, enter s = .ok t → t = s) ∨
      (m = 24 ∧ (ProofFile.pAtK2 Zp m).stands = .finish ∧
        ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t)) :
    ∀ (z : P) (a : VerifiableInference.Desc.First.S × F.E.Str),
      onQ N Mg P5J.fullLinks P5J.At.ps (fun s => (z, s)) (noAt m) a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → doorZ Zp m a.1 = some t := by
  intro z a ha hm t he
  have h25 : m < 25 := by rcases w with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  obtain ⟨p, hp, hst⟩ := stand_at25 h25
  have hd : doorZ Zp m a.1 = ProofFile.doorAtK2 Zp m a.1 := by
    refine doorZ_of_promise N Mg P5J.fullLinks P5J.At.ps (fun s => (z, s)) (noAt m) Zp m a ha hm p
      hp ?_
    rcases w with ⟨h, e, -⟩ | ⟨h, -, -⟩ | ⟨h, e, -⟩
    · exact Or.inl ⟨by rw [hst, if_neg (by omega)], by rw [e]; exact fun c => by cases c⟩
    · exact Or.inr (by rw [hst, if_pos h])
    · exact Or.inl ⟨by rw [hst, if_neg (by omega)], by rw [e]; exact fun c => by cases c⟩
  rw [hd]
  unfold ProofFile.doorAtK2
  rcases w with ⟨-, e, f⟩ | ⟨-, e, f⟩ | ⟨-, e, f⟩
  · rw [e, f _ _ he]
  · rw [e, f _ _ he]
  · rw [e]
    show (K2.finishFrontQ a.1).toOption = some t
    rw [f _ _ he]
    rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hrow_const
#print axioms VerifiableInference.Desc.First.K2Caller.hcar_const
#print axioms VerifiableInference.Desc.First.K2Caller.stand25_full
#print axioms VerifiableInference.Desc.First.K2Caller.stand25_other
#print axioms VerifiableInference.Desc.First.K2Caller.stand_at25
#print axioms VerifiableInference.Desc.First.K2Caller.hdoor_const
