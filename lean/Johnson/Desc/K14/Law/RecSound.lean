-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/RecSound.lean: the joined law of the constraints (rec_gamma) in the linear
claim's shared rounds, and the law tried on two functions that are no verifier's.

No challenge is drawn at the place "(rec_gamma)", so the law has no count. Its first half: where the
place says yes and the state reaches the test on G_u, if all constraints on G_u hold of words, then
at every seed of the record the folded row's own sample is the fold of the rows' answers (RecAt).
Its second half: where the three clauses hold, o_u can join G_u and the constraints can be made and
added, the place says yes.
Main names: RecAt, RecSoundOf, YesRecOf, RecLawOf, recSound, rec_yes, recLaw, not_recLawOf_yes,
not_recLawOf_no.

What is not claimed. Nothing on the record's answers being those of the encoded index, or on the
equations pinning the folded row. The small instances are no instances of a release.

-/
import Johnson.Desc.K14.Law.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground

variable {K : Type} [Field K] (ρ : Reading K)

/-- (rec_gamma)'s equation at a seed of the record with its number. -/
def RecAt (p : Par) (d : St) (m : Words K) (x : SampleSeed × Nat) : Prop :=
  RecEq p.S.fold.index (x.1.z.map ρ.val) (ρ.val x.1.beta) (fun t => ρ.val (thetaE t)) x.2
    (fun r => ρ.val ((weights p.S d.loc).getD r zeroE))
    (fun k => ρ.val (d.loc.key.record.getD k zeroE))
    (fun k => m d.loc.oU.oracle .main (d.loc.oU.lay.index k))

/-- The law's first half, of any function in the place of "(rec_gamma)". e: the state at the test on
G_u. -/
def RecSoundOf (lr : Par → St → List Fmt.RoundView → Option St) : Prop :=
  ∀ (p : Par) (d d' e : St) (rs : List Fmt.RoundView) (m : Words K), lr p d rs = some d' →
    Reaches d' e d.loc.gU → Means.AllSay ρ e.st (rowsOn e d.loc.gU) m →
    p.S.fold.index.ok = true → PlacedU e.st p.S.fold d.loc.oU →
    ∀ x ∈ d.loc.key.seeds.zipIdx, RecAt ρ p d m x

/-- The law's second half: where the clauses hold, o_u can join and the constraints can be made and
added, the function says yes. -/
def YesRecOf (lr : Par → St → List Fmt.RoundView → Option St) : Prop :=
  ∀ (p : Par) (d d1 d' : St) (rs : List Fmt.RoundView) (rows : List Row),
    ok (laysRecL p d.loc) = true → joinP d d.loc.gU d.loc.oU.oracle false = some d1 →
    recRows p d.loc = some rows → addRowsP d1 d.loc.gU rows = some d' → lr p d rs = some d'

/-- The joined law of (rec_gamma), of any function in the place of "(rec_gamma)". -/
def RecLawOf (lr : Par → St → List Fmt.RoundView → Option St) : Prop := RecSoundOf ρ lr ∧ YesRecOf lr

/-- **The law's first half**: LAYS and MEANS joined. -/
theorem recSound : RecSoundOf ρ laysRec :=
  fun p d d' e rs m h hR hs hi hP => recSays ρ p d d' e rs e.st m h hR.later hs hi hP

/-- "(rec_gamma)" says yes where its clauses hold and its writes go through. -/
theorem rec_yes : YesRecOf laysRec := by
  intro p d d1 d' rs rows h0 h1 h2 h3
  have e : laysRec p d rs = (guard (ok (laysRecL p d.loc) = true) : Option Unit).bind fun _ =>
      (joinP d d.loc.gU d.loc.oU.oracle false).bind fun d1 =>
        (recRows p d.loc).bind fun rows => addRowsP d1 d.loc.gU rows := rfl
  rw [e, h1, h2]
  simp [guard, h0, h3]

/-- **The joined law of (rec_gamma).** -/
theorem recLaw : RecLawOf ρ laysRec := ⟨recSound ρ, rec_yes⟩

/-! ## Two small instances -/

/-- A code with four message entries; a table of one row with one answer. -/
def tinyRS : LinShape :=
  { tinyS with fold := { tinyS.fold with
      index := { code := ⟨3, 4, 0⟩, v := 0, answers := 1, saltBytes := 40 } } }

@[inherit_doc tinyRS]
def tinyRP : Par := { samples := 0, firstTree := 0, S := tinyRS, key := {}, entries := [] }

/-- Two messages over that code; no group. -/
def tinyRT : Statement :=
  { codes := { base := #[⟨3, 4, 0⟩, ⟨3, 4, 0⟩], mask := #[] },
    oracles :=
      #[{ shape := { code := 0, mainRows := 1 } }, { shape := { code := 1, mainRows := 1 } }],
    groups := #[] }

/-- A record with one seed and the answer 1. -/
def tinyRD : St :=
  { st := tinyRT, book := { trees := #[], place := #[] }, roots := 0, opened := [],
    loc := { gU := 0, gOmega := 1,
             oU := { oracle := 1, lay := { rowBits := 0, placeBits := 2, rowsHigh := false } },
             key := { record := #[oneE], seeds := [⟨[zeroE, zeroE], oneE⟩] } } }

/-- The small table's shape meets its conditions. -/
theorem tinyR_ok : tinyRP.S.fold.index.ok = true := by decide

/-- At the small instance o_u has its table. -/
theorem tinyR_placed : PlacedU tinyRT tinyRP.S.fold tinyRD.loc.oU :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- At words that are 0 the equation fails: the fold of the answers is 1. -/
theorem tinyR_never : ¬ RecAt ρ tinyRP tinyRD (fun _ _ _ => 0) (⟨[zeroE, zeroE], oneE⟩, 0) := by
  have hw : weights tinyRP.S tinyRD.loc = #[oneE] := rfl
  have hr : tinyRD.loc.key.record = #[oneE] := rfl
  have hn : tinyRP.S.fold.index.rows = 1 := rfl
  unfold RecAt RecEq
  rw [hw, hr, hn]
  simp [ρ.one]

/-- A function that says yes to all and lays nothing does not meet the law's first half. -/
theorem not_recSoundOf_yes : ¬ RecSoundOf ρ fun _ d _ => some d := by
  intro h
  refine tinyR_never ρ (h tinyRP tinyRD tinyRD tinyRD [] (fun _ _ _ => 0) rfl (Reaches.refl _ _)
    ?_ tinyR_ok tinyR_placed _ (by simp [tinyRD]))
  intro r hr
  simp [rowsOn, tinyRD, tinyRT] at hr

/-- A state in which o_u is sampled and has not yet joined G_u; the record is empty. -/
def tinyJ : St :=
  { tinyD with st := { tinyT with
      oracles :=
        #[{ shape := { code := 0, mainRows := 1 } },
          { shape := { code := 1, mainRows := 1 }, sampled := true },
          { shape := { mainRows := 0, maskRows := 1 } }],
      groups := #[{ code := 1, members := #[2] }, { code := 0, members := #[0, 2] }] } }

/-- The three clauses hold there. -/
theorem tinyJ_clauses : ok (laysRecL tinyLP tinyJ.loc) = true := by decide

/-- o_u can join G_u there. -/
theorem tinyJ_join : (joinP tinyJ 0 1 false).isSome = true := by
  have h : ok (joinL tinyJ.st 0 1 false) = true := by
    simp [ok, joinL, VerifiableInference.Desc.Ground.has, tinyJ, tinyD, tinyT]
  unfold joinP
  rw [if_pos h]
  rfl

/-- No constraint is added to a group that is there and not under test. -/
theorem addRowsP_nil (d : St) (g : Nat) (h : ok (rowsL d.st g) = true) :
    addRowsP d g [] = some d := by
  unfold addRowsP
  rw [if_pos h]
  rfl

/-- A function that says no to all does not meet the law's second half. -/
theorem not_yesRecOf_no : ¬ YesRecOf fun _ _ _ => none := by
  intro h
  obtain ⟨d1, hd⟩ := Option.isSome_iff_exists.1 tinyJ_join
  have h0 : ok (rowsL d1.st 0) = true := by
    unfold joinP at hd
    split at hd
    · simp only [Option.map_eq_some_iff] at hd
      obtain ⟨G, hG, rfl⟩ := hd
      have : G = { code := 1, members := #[2] } := by
        simpa [tinyJ, tinyD, tinyT] using hG.symm
      subst this
      simp [ok, rowsL, VerifiableInference.Desc.Ground.has, withMessageInGroup, tinyJ, tinyD, tinyT]
    · cases hd
  have := h tinyLP tinyJ d1 d1 [] [] tinyJ_clauses hd rfl (addRowsP_nil d1 0 h0)
  cases this

/-- Neither function meets the joined law. -/
theorem not_recLawOf_yes : ¬ RecLawOf ρ fun _ d _ => some d :=
  fun h => not_recSoundOf_yes ρ h.1

@[inherit_doc not_recLawOf_yes]
theorem not_recLawOf_no : ¬ RecLawOf ρ fun _ _ _ => none :=
  fun h => not_yesRecOf_no h.2

end Desc.K14.Law
