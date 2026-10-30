-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyInv0Full.lean: at the full size, the invariant of the induction over the
stages of the proximity test (`BodyInv`, Johnson/Prover/Link/BodyInv.lean) holds in front of the
first stage, at the state behind the batching, at the values that every run samples.

Main names (namespace `Johnson.Prover.Link.Full`).
  `fr_first`, `fr_rest`   two names for the plan's first stage, and for those behind it, are one
  `fitFrom_run5`   at every run the sampled values from round 5 ("BAT") on fit the test's rounds
  `asked_bat`, `fitB_run`   "BAT" asks no item but roots; so its one round fits
  `bodyInv0_full`   the six sub-protocols in front of the test accept the written rounds and stored
      columns · the link's seats · the statement in order · the count of the group's open rows ·
      the batched claim holds of the written state (a premise): then the front's and the batching's
      parts accept, the group behind the batching fits the first stage (`firstFits`), `lT` is the
      written state behind the batching, and `BodyInv` holds there

An assembly of calls. A limit is raised: `maxRecDepth` at `asked_bat`, a closed fact that Lean's
kernel decides.

Limits. Every premise is asked; that the batched claim holds of the written state is a premise
here. The full size alone. Nothing on soundness; nothing on what a value that is sent discloses or
does not disclose.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyCloseB
import Johnson.Prover.Link.BodyAtFull
import Johnson.Prover.Link.LinkJoinB
import Johnson.Prover.Link.LinkWidths
import Johnson.Prover.Link.DoorSeam
import Johnson.Prover.Link.DoorCodes
import Johnson.Prover.Link.StepPlanFull
import Johnson.Prover.Link.FormCuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link.Full
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Desc.K15 (St P15 frP frontBlock blocksOrV first t12Of p12Of linkDeclaredRounds)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf laidS)
open OnBytes.Flat (dsFull)
open TypedOracleCompiler.Run.PQ (RD drawnSL uL)
open _root_.Run (ckP)
open _root_.Iop (Rho)

/-- Two names for the plan's first stage are one. -/
theorem fr_first : frFirst = curF :=
  (List.cons.inj (fr_cons.symm.trans stages_two_full)).1

/-- Two names for the stages behind it are one. -/
theorem fr_rest : frRest = nxtF :: pF.nums.stages.drop 2 :=
  (List.cons.inj (fr_cons.symm.trans stages_two_full)).2

/-- **At every run the sampled values from round 5 on fit the test's rounds.** -/
theorem fitFrom_run5 (ρ : Rho (uL (ckP .two) dsFull)) :
    FitFrom (drawsOf (drawnSL (ckP .two) dsFull ρ)) (laidOf pF) 5 :=
  fun n d hd => by
    obtain ⟨_, _, h5⟩ := decls_split frP plan_full.1
    have hdec : (linkDeclaredRounds frP)[5 + n]? = some d.1 := by
      rw [decls_test frP (_root_.Desc.K15.test_planOk frP _ _ (_root_.Desc.K15.descV_planOk frP _ _
        _root_.Desc.K15.planOk_full)), List.getElem?_append_right (by rw [h5]; omega), h5,
        List.getElem?_map]
      have e : 5 + n - 5 = n := by omega
      have hd' : (laidOf (p12Of frP))[n]? = some d := hd
      rw [e, hd']
      rfl
    obtain ⟨Dn, hDn, hR⟩ := forall₂_get (roundFits_run (linkDeclaredRounds frP) dsFull fr_isOf2 fr_nz ρ)
      (5 + n) d.1 hdec
    have e : drawsOf (drawnSL (ckP .two) dsFull ρ) (5 + n) = Dn := by
      unfold drawsOf
      rw [List.getD_eq_getElem?_getD, hDn]
      rfl
    rw [e]
    exact ⟨hR, ltE_drawnSL dsFull ρ Dn (List.mem_of_getElem? hDn)⟩

set_option maxRecDepth 100000 in
/-- "BAT" asks no item but roots. -/
theorem asked_bat : ((laidOf pF).take 1).map asked = [[]] := by decide +kernel

/-- **The one round of "BAT" fits.** -/
theorem fitB_run (ρ : Rho (uL (ckP .two) dsFull)) :
    roundsFit (((laidOf pF).take 1).map (·.1))
      [⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩] = true :=
  roundsFit_sorts ((laidOf pF).take 1) 5 _ ((fitFrom_run5 ρ).take 1) asked_bat fun n r h => by
    match n, h with
    | 0, h => cases h; rfl
    | _ + 1, h => cases h

/-- **`BodyInv` in front of the first stage, at the full size.** -/
theorem bodyInv0_full (X : LIn frS) (C : LCoins) (ρ : Rho (uL (ckP .two) dsFull))
    (hi0 : X.keys.1.item = 0) (hi1 : X.keys.2.item = 1) (d' : St) (G' : Group)
    (h6 : foldBlocks 0 (frontBlock frP :: blocksOrV frP) (first frP.codes X.keys)
      (lFront frS 97 X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (lStoredCols frP frS X (drawsOf (drawnSL (ckP .two) dsFull ρ))) = .ok (d', [], []))
    (hS : LinkSeats frP.par d' G') (ho : InOrder d'.st)
    (hn : G'.rows.size =
      2 * frP.S.table.answers + (frP.S.columnsFirst + frP.S.columnsFurther) + 1)
    (HF : ∀ row, Bat.combine (begun d'.st d'.loc.g G') d'.loc.g
        ⟨layoutOf d'.st G', runRows d'.st G'⟩
        (drawnOf (noDigest ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩)) = some row →
      (Slf.idf (E := GE) (J := (frS.sg 97).cIn.J)).Holds (stmG (frS.sg 97) row)
        (μOf (frS.sg 97) (lPS frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ))))) :
    ∃ row,
      (guardedProximityTestParts.front pF).decide (t12Of d') [] [] = .ok (t12Of d') ∧
      (guardedProximityTestParts.bat pF (((laidOf pF).take 1).map (·.1))).decide (t12Of d')
        [noDigest ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩] [] =
        .ok (batT (t12Of d') G' row) ∧
      (guardedProximityTestParts.group (batT (t12Of d') G' row)).any (firstFits curF) = true ∧
      lT frP frS 97 X C (drawsOf (drawnSL (ckP .two) dsFull ρ)) = batT (t12Of d') G' row ∧
      BodyInv pF C.body (PlanAll pF) (drawsOf (drawnSL (ckP .two) dsFull ρ))
        (nxtF :: pF.nums.stages.drop 2) 0 curF ((laidOf pF).drop 1) 6 (batT (t12Of d') G' row)
        (lPS frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (lCol frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ))) := by
  obtain ⟨-, f0, r0, -, hbc, hcut, -⟩ := cuts_full
  obtain ⟨H, B, F, -⟩ := door_full X.keys hi0 hi1 [] d' G' _ _ _ _ h6 hS ho hn
    (((laidOf pF).take 1).map (·.1)) hcut
  obtain ⟨row, hc, hb⟩ := bat5_yes H _ B hbc [⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩]
    (fitB_run ρ)
  have hf := front5_yes B.pass H.group F
  obtain ⟨T, I, -⟩ := formInv0_closed X.keys hi0 hi1 d' G' _ _ _ _ h6 hS ho _ row hc
    (lCol frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
    (length_lCol frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
  have hh0 : (sgOf curF).h = 0 := by
    rw [seam_sg]
  refine ⟨row, hf, hb, group_batT H row, lT_eq frP frS 97 X C _ d' _ h6 hf hb, ⟨?_, ?_⟩,
    fitFrom_run ρ, row, _, _, _, _, _, T, I, ?_, ?_, ?_⟩
  · rw [codes_full X.keys hi0 hi1 d' G' _ _ _ _ h6 row]
    exact planFrom_full_cons
  · have h := fr_sortsL
    rw [fr_first, fr_rest] at h
    exact h
  · have h := HF row hc
    rw [stmG_eq] at h
    rw [I.layK, I.layH]
    exact seam_sg ▸ h
  · show (fun _ => packedN (sg0 frP) (C.body.W (sg0 frP) 0) 0) = _
    rw [sg0_eq frP curF _ stages_two_full]
    funext b
    exact (packedN_row (sgOf curF) hh0 _ b).symm
  · exact colIs_first_full X.keys hi0 hi1 d' G' _ _ _ _ h6 hS row _ _ _ _ C.tN _ C.ψN rfl rfl

end Johnson.Prover.Link.Full
