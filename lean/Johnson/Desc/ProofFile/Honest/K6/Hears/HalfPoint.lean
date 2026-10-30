-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Hears/HalfPoint.lean: at the honest side's letters the lookup's
point on the positions has lt coordinates, at every list of challenges. Statements and proofs on the
honest side's makers of points (Honest/K6/Wit.lean, Honest/K3/Heard.lean) and on the verifier's
maker of letters (`fromLookup`, Johnson/Desc/Kinds/HeadIn.lean). No goal is stated.

WHAT IT IS NOT. LENGTHS ALONE: that the two sides' points are one, coordinate by coordinate, is not
said: a statement on values would need that tie. CONDITIONAL: `zt_size_half` and `zt_size_given` on
the test "the key points' lengths" (`headPointsFit`) accepting, the second besides on public numbers
p that have the shape's sizes; `pointsFit_of_fitsB` on `headFitsB`; `zt_sizes_meet` on `headFitsB`,
on a return of `given` and on the tests on the plan: that any of these holds at any public files or
at any state is not shown here. The first five lemmas have no premise: they are facts on the lengths
of arrays. No state of a run, no value of a witness, no measure.

  `keyPt_size`, `zx_size`, `zk_size_free`   a key tree's point behind n levels has n coordinates;
                    the lookup's point has min dT v; a call's key point has as many at every two
                    lists: whatever was heard
  `lookup_sizes_free`   **the lengths of the lookup's point and of each call's key point hang on the
                    public numbers alone**
  `last_size`       the last n coordinates of a point are min n of its size
  `zt_size_half`, `zt_size_given`   **where the test accepts, zt has lt coordinates at the honest
                    side's letters, at every list of challenges**
  `pointsFit_of_fitsB`   the lot's own premise, `headFitsB`, gives the test
  `zt_sizes_meet`   **the two sides' zt have as many coordinates**: the honest side's at every list,
                    and the letters' that `given` returns at a state

Why. Honest/K6/Hears/NoPoint.lean (not in the library) carries "these rounds are heard" from one
choice of the lookup's letters to another with as many coordinates of zt. At the letters that the
verifier's text takes off its state the library has that number (`zt_size_at`). At the honest side's
letters the test "the key points' lengths" of Honest/K6/Wit.lean tries labelled challenges only. An
unheard round is read as 0 by the makers, which changes no length. That lt is at most the length of
the lookup's point comes out of the test's acceptance, not out of the shape: the first call's line
says that its key point has lJ + lt coordinates and ends as the lookup's point ends. This file
stands over Honest/K6/Wit.lean, with what that imports, and Honest/K3/Heard.lean. No file of the
folder lean/Johnson/Goal/ is imported by this one, nor, by a walk over the import lines, by any file
beneath it. Called: `layBack_size` (Johnson/Desc/First/ProdV/LevelKit.lean), `zt_size_at`
(Johnson/Desc/Kinds/Law/WeightTwinAt.lean), `given_ok` (Law/FromGiven.lean).
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Wit
import Johnson.Desc.First.ProdV.LevelKit
import Johnson.Desc.Kinds.Law.WeightTwinAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6.Hears
open OnBytes (E)
open VerifiableInference.Desc.Kinds

/-- A key tree's point behind n levels has n coordinates, whatever was heard. -/
theorem keyPt_size (f : K3.LFace) (base : Nat) (heard : List Fmt.Drawn)
    (i n : Nat) : ((K3.ptsOf f base heard).keyPt i n).size = n := by
  cases n with
  | zero => rfl
  | succ m =>
    show (#[_] ++ VerifiableInference.Desc.First.ProdV.layBack m _ _).size = m + 1
    rw [Array.size_append, VerifiableInference.Desc.First.ProdV.layBack_size]
    simp
    omega

/-- The lookup's point has min dT v coordinates, whatever was heard. -/
theorem zx_size (h : OnBytes.Model.Forest.Shape) (base : Nat) (heard : List Fmt.Drawn) :
    (K3.keyPtsAt h base heard).zx.size = min h.dT h.v := by
  show (((K3.ptsOf _ base heard).keyPt 0 h.v).extract 0 h.dT).size = _
  rw [Array.size_extract, keyPt_size]
  omega

/-- A call's key point has as many coordinates at every two lists. -/
theorem zk_size_free (h : OnBytes.Model.Forest.Shape) (base : Nat) (heard heard' : List Fmt.Drawn)
    (c : Nat) : ((K3.keyPtsAt h base heard).zk.getD c #[]).size =
      ((K3.keyPtsAt h base heard').zk.getD c #[]).size := by
  unfold K3.keyPtsAt K3.keyPtsOf
  by_cases hc : c < h.NC
  · simp [Array.getD, hc, keyPt_size]
  · simp [Array.getD, hc]

/-- **THE LENGTHS OF THE LOOKUP's POINT AND OF EACH CALL's KEY POINT HANG ON THE PUBLIC NUMBERS
ALONE**: they are the same at every two lists of challenges. -/
theorem lookup_sizes_free (N : HeadWhere) (front front' : List Fmt.Drawn) :
    (headLookupOf N front).1.size = (headLookupOf N front').1.size ∧
      ∀ c, ((headLookupOf N front).2 c).size = ((headLookupOf N front').2 c).size := by
  unfold headLookupOf
  cases N.look with
  | none => exact ⟨rfl, fun _ => rfl⟩
  | some x =>
    refine ⟨?_, fun c => zk_size_free x.1 x.2 front front' c⟩
    show (K3.keyPtsAt x.1 x.2 front).zx.size = (K3.keyPtsAt x.1 x.2 front').zx.size
    rw [zx_size, zx_size]

/-- The last n coordinates of a point. -/
theorem last_size (z : Point) (n : Nat) : (z.last n).size = min n z.size := by
  unfold Point.last
  rw [Array.size_extract]
  omega

/-- **WHERE THE TEST "the key points' lengths" ACCEPTS, THE LOOKUP's POINT ON THE POSITIONS HAS lt
COORDINATES AT THE HONEST SIDE's LETTERS, AT EVERY LIST OF CHALLENGES.** The test tries labelled
challenges; floor: any. -/
theorem zt_size_half (N : HeadWhere) (hfit : headPointsFit N = true) (floor : Nat)
    (front : List Fmt.Drawn) :
    letI : Head.Sizes := (Head.parOf N.shape 0).sizes
    ((Head.fromLookup floor (headLookupOf N front).1 (headLookupOf N front).2).norm.zt).size =
      Norm.lt := by
  letI : Head.Sizes := (Head.parOf N.shape 0).sizes
  show ((headLookupOf N front).1.last Norm.lt).size = Norm.lt
  rw [last_size]
  unfold headPointsFit at hfit
  cases hl : N.look with
  | none =>
    rw [hl] at hfit
    cases hfit
  | some x =>
    rw [hl] at hfit
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hfit
    have h0 := hfit (([.inl .remLow, .inl .remHigh, .inr .marginTop] : List Head.PlaceKey), 0)
      (by simp [Head.callList, List.zipIdx])
    obtain ⟨a, b⟩ := h0
    have b' := congrArg Array.size b
    rw [last_size, last_size, a] at b'
    have e := (lookup_sizes_free N front (headLabels (x.2 + headLookRounds x.1))).1
    have e' : (headLookupOf N (headLabels (x.2 + headLookRounds x.1))).1 =
        (headLookupAt x.1 x.2 (headLabels (x.2 + headLookRounds x.1))).1 := by
      unfold headLookupOf
      rw [hl]
    rw [e, e']
    omega

/-- The same at the letters that the honest side's small input makes, for public numbers p with the
sizes of the shape. -/
theorem zt_size_given (N : HeadWhere) (hfit : headPointsFit N = true) (request : Head.Request)
    (y : Nat) (c : Cells) (Wh : Nat → Nat → Int) (p : Head.Par)
    (hp : p.sizes = (Head.parOf N.shape 0).sizes) (front : List Fmt.Drawn) :
    letI : Head.Sizes := p.sizes
    (((headAskOf N request y c Wh).given p front).normIn.zt).size = Norm.lt := by
  have h := zt_size_half N hfit p.floor front
  rw [← hp] at h
  exact h

/-- The lot's own premise gives the test. -/
theorem pointsFit_of_fitsB (Z : Pub) (G : Ground) (h : headFitsB Z G = true) :
    headPointsFit (headWhereOf Z G) = true := by
  unfold headFitsB headFits headFitsOn at h
  simp only [List.all_cons, List.all_append, List.all_nil, Bool.and_eq_true, Bool.and_true] at h
  exact h.2.2.2.2.2.1

/-- **THE TWO SIDES' zt HAVE AS MANY COORDINATES**: the premise of `hears_free` (Hears/NoPoint.lean)
at the honest side's letters, at any list of challenges, and at the letters that `given` returns at
a state. -/
theorem zt_sizes_meet (Z : Pub) (G : Ground) (hfit : headFitsB Z G = true) (request : Head.Request)
    (y : Nat) (c : Cells) (Wh : Nat → Nat → Int) (front : List Fmt.Drawn)
    {s : VerifiableInference.Desc.First.S} {g : Head.Given}
    (hg : Head.given (Head.parOf G.W.hS (Head.Law.workOf G.W))
      (Head.seatAt G.W.hS (Head.Law.readsOf G.W)) s = .ok g)
    (hplan : (Head.parOf G.W.hS (Head.Law.workOf G.W)).ok = true) :
    (((headAskOf (headWhereOf Z G) request y c Wh).given (headParAt G) front).normIn.zt).size =
      (g.normIn.zt).size := by
  have e1 := zt_size_given (headWhereOf Z G) (pointsFit_of_fitsB Z G hfit) request y c Wh
    (headParAt G) rfl front
  have e2 := Head.Law.Came.zt_size_at G.W hg hplan
  obtain ⟨_, _, _, _, _, rfl⟩ := Head.Law.Came.given_ok _ _ _ _ hg
  exact e1.trans e2.symm

#print axioms keyPt_size
#print axioms zx_size
#print axioms zk_size_free
#print axioms lookup_sizes_free
#print axioms last_size
#print axioms zt_size_half
#print axioms zt_size_given
#print axioms pointsFit_of_fitsB
#print axioms zt_sizes_meet

end ProofFile.Honest.K6.Hears
