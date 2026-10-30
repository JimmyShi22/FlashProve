-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyInv0Meant.lean: at the full size, at an instance with its stored strings and
polynomials (`Meant`, Johnson/Prover/Link/LinkYesStm.lean): the batched claim holds of the written
state, and so the invariant of the induction over the stages of the proximity test (`BodyInv`)
holds in front of the first stage without that premise.

Main names (namespace `Johnson.Prover.Link.Full`).
  `front0_full`   `Meant` · the six sub-protocols in front of the test accept the written rounds and
      stored columns · the link's seats · the statement in order · the count of the group's open
      rows: then whatever row the batching combines, the claim holds at the written state's
      message
  `bodyInv0_meant`   `bodyInv0_full` (Johnson/Prover/Link/BodyInv0Full.lean) with that premise paid

By: `door_full` (Johnson/Prover/Link/DoorFull.lean), `front_at` (Johnson/Prover/Link/FrontAt.lean),
`stored_full` (Johnson/Prover/Link/FrontStored.lean), `layout_eq` (Johnson/Desc/Means/Layout.lean).

Limits. Every premise is asked. The full size alone. Nothing on soundness; nothing on what a value
that is sent discloses or does not disclose.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyInv0Full
import Johnson.Prover.Link.FrontAt
import Johnson.Prover.Link.FrontStored

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link.Full
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Desc.K15 (St P15 frP frontBlock blocksOrV first t12Of p12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open OnBytes.Flat (dsFull RecFull)
open TypedOracleCompiler.Run.PQ (drawnSL uL)
open _root_.Run (ckP)
open _root_.Run.PQ (SgX)
open _root_.Iop (Rho twoExternalStrings)

section
variable (rr : RecFull × RecFull) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
  (M₀ M₁ : (Fin frS.P.v → Bool) → frS.Co → GE) (hM : Meant rr y M₀ M₁) (C : LCoins)
  (ρ : Rho (uL (ckP .two) dsFull)) (d' : St) (G' : Group)
  (h6 : foldBlocks 0 (frontBlock frP :: blocksOrV frP) (first frP.codes (keysOf rr))
    (lFront frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
    (lStoredCols frP frS (linOf rr y M₀ M₁) (drawsOf (drawnSL (ckP .two) dsFull ρ))) =
    .ok (d', [], []))
  (hS : LinkSeats frP.par d' G') (ho : InOrder d'.st)
  (hn : G'.rows.size =
    2 * frP.S.table.answers + (frP.S.columnsFirst + frP.S.columnsFurther) + 1)

include hM h6 hS ho hn

/-- **The batched claim holds of the written state.** -/
theorem front0_full (row : GroupRow)
    (hrow : Bat.combine (begun d'.st d'.loc.g G') d'.loc.g
      ⟨layoutOf d'.st G', runRows d'.st G'⟩
      (drawnOf (noDigest ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩)) = some row) :
    (Slf.idf (E := GE) (J := (frS.sg 97).cIn.J)).Holds (stmG (frS.sg 97) row)
      (μOf (frS.sg 97) (lPS frP frS (linOf rr y M₀ M₁) C
        (drawsOf (drawnSL (ckP .two) dsFull ρ)))) := by
  obtain ⟨-, f0, r0, -, -, hcut, -⟩ := cuts_full
  obtain ⟨-, -, -, XR, DR, hR, e, -⟩ := door_full (keysOf rr) rfl rfl [] d' G' _ _ _ _ h6 hS ho hn
    (((laidOf pF).take 1).map (·.1)) hcut
  have hG : d'.st.groups[XR.group]? = some G' := by
    rw [e]
    exact hS.group
  have hrow' : Bat.combine (begun d'.st XR.group G') XR.group
      ⟨layoutOf d'.st G', runRows d'.st G'⟩
      (drawnOf (noDigest ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩)) = some row := by
    rw [e]
    exact hrow
  exact front_at rr y M₀ M₁ hM C ρ _ _ d' _ _ _ _ XR DR hR rfl (stored_full rr y M₀ M₁ _) G'
    (layoutOf d'.st G') _ row hG (layout_eq _ _ _ hG) hrow'

/-- **`BodyInv` in front of the first stage**, the claim's premise paid. -/
theorem bodyInv0_meant :
    ∃ row,
      (guardedProximityTestParts.front pF).decide (t12Of d') [] [] = .ok (t12Of d') ∧
      (guardedProximityTestParts.bat pF (((laidOf pF).take 1).map (·.1))).decide (t12Of d')
        [noDigest ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩] [] =
        .ok (batT (t12Of d') G' row) ∧
      (guardedProximityTestParts.group (batT (t12Of d') G' row)).any (firstFits curF) = true ∧
      lT frP frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)) =
        batT (t12Of d') G' row ∧
      BodyInv pF C.body (PlanAll pF) (drawsOf (drawnSL (ckP .two) dsFull ρ))
        (nxtF :: pF.nums.stages.drop 2) 0 curF ((laidOf pF).drop 1) 6 (batT (t12Of d') G' row)
        (lPS frP frS (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (lCol frP frS (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ))) :=
  bodyInv0_full (linOf rr y M₀ M₁) C ρ rfl rfl d' G' h6 hS ho hn
    (front0_full rr y M₀ M₁ hM C ρ d' G' h6 hS ho hn)

end

end Johnson.Prover.Link.Full
