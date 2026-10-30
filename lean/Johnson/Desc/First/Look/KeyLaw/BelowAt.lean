-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/BelowAt.lean: THE TYPED LOOKUP'S ERRORS, CARRIED ALONG THE MAPS TO
THE WRITTEN ROUNDS, ARE BELOW THE PLANNER'S TARGET: as shares of the written rounds' verifier
messages they are at most 2⁻¹ ^ target, round by round, at every face and every setting at which
the planner's own rounds for the lookup hold.

How. Maps.below_held (OnBytes/Flat/CarrySBelow.lean) asks two things of the planner's rounds. They
hold the written rounds pair by pair: the written rounds have the planner's entries (AsDeclared,
MadeAt.lean), and the planner's rounds pass the two tests named below. Each typed count is at most
the planner's number for its round: the typed lookup's errors are covered by the planner's list
(lamS_covered, OnBytes/Tie/Pv/KeyLookup/LamBelow.lean), and a typed round has no more values than
the written round draws.

Main names:
  list_size: the planner's list at the face's size is its list at the typed lookup's size.
  nVals_plain: the number of values that a round without positions, matrix entries, seeds and
    sealing draws.
  valsLe_fits, marks_mapsT: the two small facts that Maps.below_held wants.
  below_of_list: the bound at any typed shape with readers whose errors the planner's list covers.
  LookHeld s f: the setting has the format's field and degree 3, and the rounds that the planner's
    routine makes for the face's size, at the scope "once", pass sideR and hold at the target.
  lam_below: THE BOUND.

Limits. Left as premises, all on public numbers: the setting has the format's field and degree 3 ·
the planner's routine for the lookup ends well at the scope "once" · each of its rounds passes sideR
(the logarithm of positions is at most 64; no more elements that are never 0 than elements; work +
66 ≤ target where an element is drawn) · each of its rounds holds at the target, work counted
(roundHolds). Nothing here says that a key's plan holds these rounds. The target counts a round's
proof of work. A bound round by round, no sum.

-/
import OnBytes.Flat.CarrySBelow
import OnBytes.Flat.CountsCovered
import OnBytes.Flat.HeldAll
import OnBytes.Slice.NoWorkRatesRound
import OnBytes.Tie.Pv.KeyLookup.LamBelow
import Johnson.Desc.First.Look.KeyLaw.MadeAt
import Johnson.Desc.First.Look.KeyLaw.MeetsAt
import Johnson.Desc.First.Look.KeyLaw.Plan

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.K3.KeyLaw
open Iop Prob _root_.Run _root_.Run.PQ OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open OnBytes.Flat
open Cb.Pv (Fits Covered valuesOf)
open Lk6 (sizeOfPub)
open Fo.Peel (MeetsT)
open OnBytes.Flat.Held (sideR held_list)

/-! ## The planner's list -/

theorem list_congr (s : Setting) {x x' : LookupSize} (h1 : x.shifted = x'.shifted) (h2 : x.d = x'.d)
    (h3 : x.mu = x'.mu) (h4 : lookupLive x = lookupLive x') (h5 : lookupParts x = lookupParts x') :
    lookupList s x = lookupList s x' := by
  unfold lookupList
  rw [h1, h2, h3, h4, h5]

/-- The planner's list at the face's size is its list at the typed lookup's size. -/
theorem list_size (s : Setting) (A : Lk6.Dat GE) (st : A.St) (f : Face) (hf : FaceIs A st f)
    (hok : f.ok = true) (hadm : A.toPub.Adm Cb.Gl.p) :
    lookupList s f.size = lookupList s (sizeOfPub A.toPub) := by
  unfold Face.ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, k2⟩, k3⟩, -⟩, k5⟩, -⟩, -⟩, -⟩, -⟩ := hok
  have hne : f.parts ≠ [] := by
    intro h0
    rw [h0] at k5
    cases k5
  refine list_congr s hf.noShift hf.d hf.mu ?_ ?_
  · rw [live_size k2 k3, hf.planes]
    simp [lookupLive, sizeOfPub, Lk6.adm_pl hadm]
  · rw [parts_size hne, hf.parts]
    simp [lookupParts, sizeOfPub, Lk6.adm_parts hadm]

/-! ## The numbers of values -/

theorem nVals_repNZ (n : ℕ) (rest : List Fmt.Draw) :
    nVals (List.replicate n Fmt.Draw.elemNZ ++ rest) =
      (Fmt.Fld.two.p ^ 3 - 1) ^ n * nVals rest := by
  induction n with
  | zero => rw [pow_zero, one_mul]; rfl
  | succ n ih =>
      show (Fmt.Fld.two.p ^ 3 - 1) * nVals (List.replicate n Fmt.Draw.elemNZ ++ rest) = _
      rw [ih]
      generalize Fmt.Fld.two.p ^ 3 - 1 = Q
      rw [pow_succ, mul_comm (Q ^ n) Q, mul_assoc]

/-- The number of values that a round without positions, matrix entries, seeds and sealing draws. -/
theorem nVals_plain (e : Fmt.Entry) (k : Fmt.Kind) (hp : e.poss = 0) (ht : e.trits = 0)
    (h1 : k ≠ .sealed) (h2 : k ≠ .seeds) : nVals (Fmt.dsOf e k) =
      Fintype.card GE ^ (e.drawE - e.drawNZ) * (Fintype.card GE - 1) ^ e.drawNZ := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [hp, ht, if_neg h2, if_neg h1, List.replicate_zero, List.nil_append, List.append_assoc,
    nVals_repE, nVals_repNZ, card_GE]
  have e0 : nVals [Fmt.Draw.trits 0] = 1 := rfl
  rw [e0, mul_one]

/-- A planned round's number of values, against its entry's draws. -/
theorem vals_round (s : Setting) (c : Scope) (q : ℕ) (hq : 2 ≤ q) : ∀ y : RoundSpec,
    0 < valuesOf q y ∧ valuesOf q y ≤
      q ^ ((y.round s c).entry.drawE - (y.round s c).entry.drawNZ) *
        (q - 1) ^ (y.round s c).entry.drawNZ
  | .said _ _ _ d _ _ _ =>
    ⟨Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega)), by
      show (q - 1) ^ d.drawNZ * q ^ (d.drawE - d.drawNZ) ≤
        q ^ (d.drawE - d.drawNZ) * (q - 1) ^ d.drawNZ
      rw [Nat.mul_comm]⟩
  | .silent _ _ _ => ⟨Nat.one_pos, Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))⟩
  | .record _ _ _ => ⟨Nat.one_pos, Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))⟩

/-- Typed rounds that fit the planner's list have no more values than written rounds that draw at
least the planner's numbers. -/
theorem valsLe_fits (q : ℕ) : ∀ (ds : List RD) (s' : Iop.Shape) (ε : Err s')
    (ys : List RoundSpec),
    List.Forall₂ (Fits q) (ε.toList.zip s'.chalList) ys →
    List.Forall₂ (fun (d : RD) y => 0 < valuesOf q y ∧
      valuesOf q y ≤ nVals (Fmt.dsOf d.entry d.kind)) ds ys → Held.ValsLe ds s'
  | [], [], _, _, _, _ => trivial
  | d :: ds, r' :: s', (e, ε), _, h, g => by
    have h' : List.Forall₂ (Fits q)
        ((e, Fintype.card r'.Chal) :: ε.toList.zip (Iop.Shape.chalList s')) _ := h
    cases h' with
    | cons h1 t1 =>
      cases g with
      | cons g1 g2 =>
        have e1 : valuesOf q _ = Fintype.card r'.Chal := h1.1
        exact ⟨e1 ▸ g1.1, e1 ▸ g1.2, valsLe_fits q ds s' ε _ t1 g2⟩
  | [], r' :: s', (e, ε), _, h, g => by
    have h' : List.Forall₂ (Fits q)
        ((e, Fintype.card r'.Chal) :: ε.toList.zip (Iop.Shape.chalList s')) _ := h
    cases h' with
    | cons _ _ => cases g
  | _ :: _, [], _, _, h, g => by
    have h' : List.Forall₂ (Fits q) [] _ := h
    cases h'
    cases g

/-- The maps of a list of readers skip no round. -/
theorem marks_mapsT : ∀ (ds : List RDT) (s' : Iop.Shape) (sp : List Tw.RSp)
    (R : Fo.Peel.Rds s' sp) (h : ds.length = sp.length),
    (Fo.Peel.mapsT ds s' sp R h).marks = (ds.map toRD).map fun _ => true
  | [], [], [], _, _ => rfl
  | _ :: ds, _ :: s', _ :: sp, R, h =>
    congrArg (true :: ·) (marks_mapsT ds s' sp R.2 (Nat.succ.inj h))
  | [], _ :: _, _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], [], _, h => absurd h (by simp)
  | _, [], _ :: _, R, _ => nomatch R
  | _, _ :: _, [], R, _ => nomatch R

/-! ## The written rounds -/

theorem declared_entries : ∀ (ds : List RDT) (es : List Fmt.Entry),
    List.Forall₂ AsDeclared ds es → (ds.map toRD).map (·.entry) = es
  | _, _, .nil => rfl
  | _, _, .cons h t => congrArg₂ List.cons h.1 (declared_entries _ _ t)

theorem draws_enough (s : Setting) (c : Scope) : ∀ (ds : List RDT) (ys : List RoundSpec)
    (xs : List Shape), List.Forall₂ AsDeclared ds (ys.map fun y => (y.round s c).entry) →
    List.Forall₂ MadeOf ds xs →
    List.Forall₂ (fun (d : RD) y => 0 < valuesOf (Fintype.card GE) y ∧
      valuesOf (Fintype.card GE) y ≤ nVals (Fmt.dsOf d.entry d.kind)) (ds.map toRD) ys
  | [], [], _, _, _ => .nil
  | d :: ds, y :: ys, _, .cons h t, .cons m u => by
    refine .cons ?_ (draws_enough s c ds ys _ t u)
    have v := vals_round s c (Fintype.card GE) Fintype.one_lt_card y
    have e1 : d.entry.poss = 0 := congrArg Fmt.Entry.poss m.entry
    have e2 : d.entry.trits = 0 := congrArg Fmt.Entry.trits m.entry
    refine ⟨v.1, ?_⟩
    show _ ≤ nVals (Fmt.dsOf d.entry d.kind)
    rw [nVals_plain d.entry d.kind e1 e2 m.notSealed m.notSeeds, h.1]
    exact v.2

/-! ## The bound -/

/-- The bound at any typed shape with readers whose errors the planner's list ys fits and covers. -/
theorem below_of_list {s' : Iop.Shape} (rd : Lk6.Flat.RdS GE s') (ε : Err s') (s : Setting)
    (hp : s.p = 2 ^ 64 - 2 ^ 32 + 1) (hdg : s.degree = 3) (ys : List RoundSpec)
    (hcov : List.Forall₂ (Covered s .once) (ε.toList.zip s'.chalList) ys)
    (hfit : List.Forall₂ (Fits (Fintype.card GE)) (ε.toList.zip s'.chalList) ys)
    (hside : (ys.map (·.round s .once)).all (sideR s.target) = true)
    (hholds : (ys.map (·.round s .once)).all (roundHolds s (capped s)) = true) (ds : List RDT)
    (xs : List Shape) (hmade : List.Forall₂ MadeOf ds xs)
    (hd : List.Forall₂ AsDeclared ds (ys.map fun y => (y.round s .once).entry))
    (hl : ds.length = (rd.fms.map spOf).length) :
    Err.Below ((mapsOf rd ds hl).err ε) ((2 : ℝ≥0∞)⁻¹ ^ s.target) := by
  refine Maps.below_held s _ (ys.map (·.round s .once)) ε
    (held_list s hp hdg _ _ ?_ hside hholds) ?_
  · rw [declared_entries ds _ hd, List.map_map]
    rfl
  · have hm : (mapsOf rd ds hl).marks = (ds.map toRD).map fun _ => true :=
      marks_mapsT ds _ _ _ _
    rw [hm]
    exact Held.countsL_all s .once (ds.map toRD) s' ε ys hcov
      (valsLe_fits (Fintype.card GE) (ds.map toRD) s' ε ys hfit (draws_enough s .once ds ys xs hd
        hmade))

/-- The setting's number of elements is the field's. -/
theorem cardE_eq (s : Setting) (hp : s.p = 2 ^ 64 - 2 ^ 32 + 1) (hdg : s.degree = 3) :
    s.cardE = Fintype.card GE := by
  have e0 : (2 ^ 64 - 2 ^ 32 + 1 : ℕ) = Fmt.Fld.two.p := by decide +kernel
  unfold Setting.cardE
  rw [hp, hdg, card_GE, e0]

/-- **The planner's own rounds for the lookup hold.** On public numbers alone. -/
def LookHeld (s : Setting) (f : Face) : Prop :=
  s.p = 2 ^ 64 - 2 ^ 32 + 1 ∧ s.degree = 3 ∧ ∀ Q : Planned,
    finish s .once (planLookup f.size) = .ok Q →
      Q.rounds.all (sideR s.target) = true ∧ Q.rounds.all (roundHolds s (capped s)) = true

/-- **The typed lookup's errors along the maps are below the planner's target.** -/
theorem lam_below (A : Lk6.Dat GE) (st : A.St) (P : Lk6.Pl A) (Ex : ExtSpec) (f : Face)
    (hf : FaceIs A st f) (hok : f.ok = true) (hadm : A.toPub.Adm Cb.Gl.p) (s : Setting)
    (hp : s.p = 2 ^ 64 - 2 ^ 32 + 1) (hdg : s.degree = 3) (Q : Planned)
    (hfin : finish s .once (planLookup f.size) = .ok Q)
    (hside : Q.rounds.all (sideR s.target) = true)
    (hholds : Q.rounds.all (roundHolds s (capped s)) = true) (ds : List RDT)
    (hd : List.Forall₂ AsDeclared ds (Q.rounds.map (·.entry)))
    (hl : ds.length = ((Lk6.lamS_runs A P Ex).rd.fms.map spOf).length) :
    Err.Below ((mapsOf (Lk6.lamS_runs A P Ex).rd ds hl).err (A.lamS P Ex).e)
      ((2 : ℝ≥0∞)⁻¹ ^ s.target) := by
  obtain ⟨-, hr, hg⟩ := finish_rounds (runs_lookup f.size) hfin
  have hls := list_size s A st f hf hok hadm
  rw [hls] at hr hg
  have hq := cardE_eq s hp hdg
  have he : entriesG s .once f = some (Q.rounds.map (·.entry)) := by
    unfold entriesG
    rw [hfin]
  have hmade := made_along s .once f _ hf.noShift hok he ds hd
  rw [hr] at hd hside hholds
  rw [List.map_map] at hd
  exact below_of_list (Lk6.lamS_runs A P Ex).rd (A.lamS P Ex).e s hp hdg _
    (Lk6.lamS_covered Cb.Gl.p A P Ex s hadm hq hg) (Lk6.lamS_fits Cb.Gl.p A P Ex s hadm hq) hside
    hholds ds _ hmade hd hl

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.list_size
#print axioms VerifiableInference.Desc.K3.KeyLaw.nVals_plain
#print axioms VerifiableInference.Desc.K3.KeyLaw.valsLe_fits
#print axioms VerifiableInference.Desc.K3.KeyLaw.marks_mapsT
#print axioms VerifiableInference.Desc.K3.KeyLaw.below_of_list
#print axioms VerifiableInference.Desc.K3.KeyLaw.lam_below
