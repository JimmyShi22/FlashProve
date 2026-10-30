-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/K10Defaults.lean (kind K10): TERMS FOR FOUR FREE LETTERS OF K10's
ASSEMBLED LAW: a default sample, two default witnesses, and the trivial joint beside. Definitions,
two statements and their proofs.

Why. At the closed constant's letters Lean's search for `Nonempty` of these types runs out of its
bound (a timeout at `typeclass`); at letters it answers at once. So the terms are made here, at
letters, and called there.
  `smp0 cs lo`: a sample for every message of the list. IT IS READ: the map `faK10` (FaK10.lean,
    beside this file, line 93) lays `(smp (z, a.1) i).getD (σ₀ i)`: the default stands at message i
    just where the reader smp gives nothing. So the arbitrary default does no harm only where the
    reader gives something at every member. WHERE THAT IS SHOWN: `smpDrawn_seed`
    (Johnson/Desc/First/Link/Law/DrawnSeed.lean): where the statement holds the seed (`K1.SeedIs`),
    the drawn reader gives some sample; it is spent in `owes_of_shapes` (TiedOfShapes.lean there),
    which `tied_of_shapes` calls: beneath the first tie, whose premise seed gives `SeedIs` at every
    member.
  `wit0 cs lo`: a witness with nothing beside. `brw0 ..`: the second default witness, where nothing
    is kept beside. In FaK10.lean's code these two letters stand in binders, in the caller's term
    (its notation CK) and as arguments handed on; the map's body does not name them. Where the
    library's `foldCaller` reads them has not been looked at.
Each of the three is picked by choice out of a type that Lean's instances show inhabited: WITHOUT
CODE.
  `joint0 ..`: the trivial joint beside: the library's `Sig.pred` at True, True, over Unit, with no
    further oracle. `joint0_on`: its promise holds at ((), ()). `joint0_relR`: so does its relaxed
    relation, at every witness.
Limits. Defaults. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.K10TwoAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR
open Prob Run KObj Johnson.Pack Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open OnBytes.Means (InOrder)
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart rowSays wordsAtFirst laysSeats)


/-- A default sample. -/
noncomputable def smp0 (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) : (sigOf cs lo).Smp :=
  Classical.choice inferInstance

/-- A default witness, with nothing beside. -/
noncomputable def wit0 (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) :
    (sigOf cs lo).Wit × Unit :=
  Classical.choice inferInstance

/-- The second default witness, where nothing is kept beside. -/
noncomputable def brw0 (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) (gs : GroupSize)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 →
      cMain cs (lo.get i).1 = (stageOf gs 219).C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 →
      cMask cs (lo.get i).1 = (stageOf gs 219).Z)
    (B : Type) [Fintype B] (n : ℕ)
    (num : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n) :
    LdBrW (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G ((groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ).sizeB (fun _ => False) (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ) B) (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo
      (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n
      num)).kp Unit :=
  Classical.choice inferInstance

/-- The trivial joint beside. -/
noncomputable def joint0 (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) (gs : GroupSize)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 →
      cMain cs (lo.get i).1 = (stageOf gs 219).C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 →
      cMask cs (lo.get i).1 = (stageOf gs 219).Z)
    (B : Type) [Fintype B] (n : ℕ)
    (num : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n) :
    Rels Unit Unit extNone (((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ).sizeB (fun _ => False) (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV
      (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).Msg ×
      Unit) :=
  ((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).sizeB (fun _ => False)
    (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs lo (stageOf gs
    219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))) (ZV
    (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).pred (St := Unit) (Wp := Unit)
    (fun _ _ _ => True) (fun _ _ _ => True)

theorem joint0_on (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) (gs : GroupSize)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 →
      cMain cs (lo.get i).1 = (stageOf gs 219).C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 →
      cMask cs (lo.get i).1 = (stageOf gs 219).Z)
    (B : Type) [Fintype B] (n : ℕ)
    (num : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n) :
    (joint0 cs lo gs kb hM hZ B n num).on ((), ()) :=
  trivial

theorem joint0_relR (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ)) (gs : GroupSize)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 →
      cMain cs (lo.get i).1 = (stageOf gs 219).C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 →
      cMask cs (lo.get i).1 = (stageOf gs 219).Z)
    (B : Type) [Fintype B] (n : ℕ)
    (num : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n)
    (w : ((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).sizeB (fun _ =>
      False) (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs lo
      (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).Msg × Unit) :
    (joint0 cs lo gs kb hM hZ B n num).relR ((), ()) w :=
  trivial

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.joint0_on
#print axioms VerifiableInference.Desc.First.Close.joint0_relR
