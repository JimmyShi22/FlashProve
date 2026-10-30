-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Caller.lean: who calls the library's proved batching at kind K13's place: the
caller, made of the plan's numbers and of the public record in front of the place. Definitions, and
statements with their proofs.
Main names:
  `callerAt P s`: the library's parameters (`Cb.BattPar`): the matrix has the plan's number of rows
    and column variables; the claims are the rows of the record's pile.
  `freshAt P s`: the mask entries that the text takes for the hiding polynomial at that record.
  `callerAt_ok`, `callerAt_hAt`: the library's two conditions hold of it; so its batching is
    knowledge sound there (`Cb.Pv.BattShort.HAt`).
  `callerAt_in`: what the library's joint in front says at that caller: all rows on the table are
    true.
  `battCallerAt`, `battCallerAt_mem`, `battCallerAt_good`: the same as a caller of the family of a
    written proof file (`KObj.KBattShortF`, Johnson/Top/Fam/BattShort.lean).
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/Fit.lean names; of the ground: `takeMasksP`.

What is not claimed. Three letters of `battCallerAt` are not fixed by the public record: the
signature Sg of the committed messages, the reading rdM of a matrix and of mask entries off these
messages, and the outer oracles Ex. The joint that goes along is the trivial one.

-/
import Johnson.Desc.K13.Law.Good
import Johnson.Top.Fam.BattShort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.OnPublicFiles (BattCaller BattOK)

/-- **The caller at the place**, of the plan's numbers and the public record. -/
noncomputable abbrev callerAt (P : Where) (s : S) : BattPar GE :=
  parOf ρg P.lin.matrixRows P.lin.kCol s.out.pending

/-- The mask entries that the text takes at that record; none where the ledger refuses. -/
def freshAt (P : Where) (s : S) : List Slot :=
  ((takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol)).map fun t =>
    t.1.map fun i => (⟨s.out.indexMasks, i⟩ : Slot)).getD []

/-- The library's two conditions hold of it. -/
theorem callerAt_ok (P : Where) (s : S) : 2 ≤ (callerAt P s).n ∧ (callerAt P s).Z.OK :=
  ⟨le_refl 2, ok_powers GE s.out.pending.length⟩

/-- So the library's batching is knowledge sound at it. -/
theorem callerAt_hAt (P : Where) (s : S) : Cb.Pv.BattShort.HAt (callerAt P s) :=
  Cb.Pv.BattShort.hAt _ (callerAt_ok P s).1 (callerAt_ok P s).2

/-- **What the library's joint in front says at that caller.** -/
theorem callerAt_in (P : Where) (s : S) (hs : s.rows = s.out.pending)
    (w : Wit GE P.lin.matrixRows P.lin.kCol) :
    (callerAt P s).InHolds (targets ρg s.out.pending, ())
        (msgOf ρg w s.out.pending (freshAt P s)) ↔
      ∀ r ∈ s.rows, Holds ρg w r := by
  rw [hs]
  exact inHolds_iff GE ρg _ _ w _ _

/-- The same as a caller of the family of a written proof file. -/
noncomputable def battCallerAt (P : Where) (s : S) (Ex : ExtSpec) (Sg : Sig GE)
    (rdM : Sg.Msg → Wit GE P.lin.matrixRows P.lin.kCol) : BattCaller GE where
  B := callerAt P s
  Ex := Ex
  Kc := Unit
  Wp := Unit
  Sg := Sg
  A0 := ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩
  msg := fun m => msgOf ρg (rdM m) s.out.pending (freshAt P s)

/-- It is a member of the family. -/
theorem battCallerAt_mem (P : Where) (s : S) (Ex : ExtSpec) (Sg : Sig GE)
    (rdM : Sg.Msg → Wit GE P.lin.matrixRows P.lin.kCol) :
    KObj.KBattShortF.mem (battCallerAt P s Ex Sg rdM) := fun c hc => by
  rw [List.mem_singleton.1 hc]
  exact callerAt_ok P s

/-- So the family's block at it is good. -/
theorem battCallerAt_good (P : Where) (s : S) (Ex : ExtSpec) (Sg : Sig GE)
    (rdM : Sg.Msg → Wit GE P.lin.matrixRows P.lin.kCol) :
    (KObj.KBattShortF.blk (battCallerAt P s Ex Sg rdM)).Good :=
  KObj.KBattShortF_good _ (battCallerAt_mem P s Ex Sg rdM)

end VerifiableInference.Desc.K13.Law
