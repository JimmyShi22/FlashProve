-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotHeardAtKeys.lean: THE BODY OF HeardOfFold (E2E/FirstHEval.lean), in scope: the verifier's state that the
first sixteen sub-protocols of the key file's first chain leave, from the chain's start, over the rounds seen, holds its
claims on the lookups' keys at the points that the prover makes of these rounds' challenges (keyPoints,
E2E/KeyFirstSends.lean), at every list of rounds on which the fold returns and every list of challenges behind.

  one_bare, seg_bare   the two readers do not see the sealed digest
  point_of_heard  FROM A HEARING TO THE PROVER's POINT: where the claims are keyClaims of a hearing on the lookup's own rounds,
                  which begin at number o of the rounds seen, and the two counts of rounds agree at part p: the prover's
                  point of part p at base o is the claim's point
  take16, looks_sourced, len_zero, base_sourced   in scope: the first sixteen; the two lookups; the numbers
  heardAtKeys_of_fold   THE BODY

By what. The verifier's side: heard_pts (E2E/LotHeardText.lean: the general text, part by part) and front_heard
(E2E/LotHeardWalk.lean: the walk over the fold). The prover's side: elemAt_all, varChals_all (Honest/K3/HeardLaw.lean). That
the two count the rounds alike: pos_full, base_full (E2E/LotHeardClosed.lean), by the kernel at the written sizes.

Limits. In scope, at the written sizes. Where the fold returns: that it returns on any rounds is not shown. The claims'
points alone: nothing on their weights, masks or targets. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotHeardWalk
import E2E.LotHeardClosed
import E2E.FirstHPile
import E2E.KeyRangesFront

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open OnBytes
open VerifiableInference.Desc (Block OpenedColumn noDigest foldBlocks)
open VerifiableInference.Desc.K3 (faceOfLkp keyClaims)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces Lookup lookupsOf lookupPlace)
open H2K.JointK (keyFirstPre keyFirstPost rngEntry keyFirst_cut)
open AtPublicFiles.KeyThread (D pre_length)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (six_sourced)
open AtPublicFiles.KeyBook (places_named fullFirst)
open AtPublicFiles.KeyValues (keyPoints oneOf faceAt baseAt lookAt blocksOf placeAt)
open AtPublicFiles.Key (keyClaims_at)
open Johnson.RunOne.Sound (rowsOf)
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest.K3 (e1 one seg allOf elemAt_all varChals_all ptsOf behind varChals elemAt roundAt
  firstRound)

theorem e1_bare (rs : List Fmt.RoundView) : (rs.map noDigest).map e1 = rs.map e1 := by
  rw [List.map_map]
  rfl

theorem one_bare (rs : List Fmt.RoundView) (a : Nat) : one (rs.map noDigest) a = one rs a := by
  unfold ProofFile.Honest.K3.one
  rw [e1_bare]

theorem seg_bare (rs : List Fmt.RoundView) (a n : Nat) : seg (rs.map noDigest) a n = seg rs a n := by
  unfold ProofFile.Honest.K3.seg
  rw [e1_bare]

/-- **From a hearing to the prover's point.** -/
theorem point_of_heard {set : Params.Setting} {i : Nat} {x : Lookup} {seen : List Fmt.RoundView}
    {tail : List Fmt.Drawn} {o : Nat} {keys : List Lkp.Keys}
    (H : HeardOn set i x (seen.drop o) keys) (hsft : (faceOfLkp x).shifted = false) (p k : Nat)
    (hp : p < (faceOfLkp x).parts.length) (hv : (faceOfLkp x).parts.getD p 0 = k + 1)
    (h1 : firstRound (faceOfLkp x) (.key p k) =
      oKeys (faceOfLkp x) + offK (faceOfLkp x).parts p + Kr 0 0 k)
    (h2 : firstRound (faceOfLkp x) (.keyLine p k) =
      oKeys (faceOfLkp x) + offK (faceOfLkp x).parts p + Kr 0 0 k + k + 3) :
    ((ptsOf (faceOfLkp x) o (seen.map (·.drawn) ++ tail)).keyPt p (k + 1)).toList.reverse =
      (keys.getD p default).point := by
  obtain ⟨F, home, g, es, F₀, G, hk, hh⟩ := H
  have hh' : VerifiableInference.Desc.K3.KeyLaw.hearE (faceOfLkp x) es F₀
      ((((seen.drop o).take (lenOf set i x))).map noDigest) = some (g, G) := hh
  obtain ⟨a, b⟩ := heard_pts hsft hh' p k hp hv
  obtain ⟨hlen, -⟩ := VerifiableInference.Desc.K3.KeyLaw.heard_keys hsft hh'
  rw [one_bare, seg_bare] at a
  rw [List.length_map, Kr_snoc] at b
  simp only [Nat.zero_add] at b
  -- the rounds seen, cut at the lookup's own
  have ho : o ≤ seen.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (Nat.le_of_lt (Nat.lt_of_not_le hc)), List.take_nil,
      List.length_nil] at b
    have : oKeys (faceOfLkp x) = 1 + 3 * ((faceOfLkp x).planes - 1) +
        3 * ((faceOfLkp x).parts.length - 1) + 1 := rfl
    omega
  have hall : seen.map (·.drawn) ++ tail =
      allOf ((seen.take o).map (·.drawn)) ((seen.drop o).take (lenOf set i x))
        (((seen.drop o).drop (lenOf set i x)).map (·.drawn) ++ tail) := by
    unfold allOf
    rw [← List.append_assoc, ← List.map_append, ← List.map_append, List.append_assoc,
      List.take_append_drop, List.take_append_drop]
  have hfl : ((seen.take o).map (·.drawn)).length = o := by
    rw [List.length_map, List.length_take, Nat.min_eq_left ho]
  -- the prover's point
  have hP : (ptsOf (faceOfLkp x) o (seen.map (·.drawn) ++ tail)).keyPt p (k + 1) =
      (g.keys.getD p (#[], {})).1 := by
    show behind k ((faceOfLkp x).orders p k)
        (varChals (faceOfLkp x) o (seen.map (·.drawn) ++ tail) (.key p k) k)
        (elemAt (seen.map (·.drawn) ++ tail) (roundAt (faceOfLkp x) o (.keyLine p k))) = _
    have v1 := varChals_all (faceOfLkp x) ((seen.take o).map (·.drawn))
      (((seen.drop o).drop (lenOf set i x)).map (·.drawn) ++ tail)
      ((seen.drop o).take (lenOf set i x)) (.key p k) _ k h1 (by omega)
    have v2 := elemAt_all ((seen.take o).map (·.drawn))
      (((seen.drop o).drop (lenOf set i x)).map (·.drawn) ++ tail)
      ((seen.drop o).take (lenOf set i x))
      (oKeys (faceOfLkp x) + offK (faceOfLkp x).parts p + Kr 0 0 k + k + 3) (by omega)
    rw [hfl] at v1 v2
    rw [a, hall]
    unfold roundAt
    rw [h2, v1, v2]
  -- the claim's point
  obtain ⟨-, hat⟩ := keyClaims_at x F home g keys hk
  have hpg : p < g.keys.length := by rw [hlen]; exact hp
  obtain ⟨y, hy⟩ := hat p _ (List.getElem?_eq_getElem hpg)
  rw [hP, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hy,
    List.getElem?_eq_getElem hpg]
  rfl

/-- A list cut behind n members: its first n + 1. -/
theorem take_cut {α : Type} (l pre post : List α) (a : α) (n : Nat) (h : l = pre ++ a :: post)
    (hn : pre.length = n) : l.take (n + 1) = pre ++ [a] := by
  subst h
  subst hn
  rw [List.take_length_add_append]
  rfl

section
variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- In scope the first sixteen are what stands in front of the ranges' test, and that test. -/
theorem take16 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (D Xs N Pl).first.blocksInOrder.take 16 =
      keyFirstPre (oneOf Xs) Xs.Y.D.1 Xs.Y.told.1 Xs.set N ++ [rngEntry (oneOf Xs) N] := by
  have hc : (D Xs N Pl).first.blocksInOrder = _ :=
    keyFirst_cut (oneOf Xs) Xs.Y.D.1 Xs.Y.told.1 Xs.set N
  have hl : (keyFirstPre (oneOf Xs) Xs.Y.D.1 Xs.Y.told.1 Xs.set N).length = 15 :=
    pre_length scope hs.named
  exact take_cut _ _ _ _ 15 hc hl

/-- In scope the lookups are the written sizes' two. -/
theorem looks_sourced (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    lookupsOf (oneOf Xs) = [looksF.getD 0 default, looksF.getD 1 default] := by
  have h6 := six_sourced hs scope
  have e : lookupsOf (oneOf Xs) = looksF := by
    unfold lookupsOf looksF
    rw [(h6.ranges : (oneOf Xs).ranges = keyFull.ranges.x),
      (h6.lin : (oneOf Xs).lin = keyFull.once.shape)]
    rfl
  rw [e]
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 looks_two
  rw [hab]
  rfl

/-- In scope the first lookup has 9,581 rounds. -/
theorem len_zero (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    lenOf Xs.set 0 (looksF.getD 0 default) = 9581 := by
  have hr := (places_named scope hs.named).1
  have hc : (keyFileDescription Xs N Pl).first.blocksInOrder = _ :=
    keyFirst_cut (oneOf Xs) Xs.Y.D.1 Xs.Y.told.1 Xs.set N
  rw [hc, pre_two _ _ _ _ _ (looks_sourced hs scope)] at hr
  have h4 := (congrArg (fun l => (l[4]?).map (·.2)) hr).trans base_full.2.2
  have h5 : some (lenOf Xs.set 0 (looksF.getD 0 default)) = some 9581 := h4
  exact Option.some.inj h5

/-- In scope the prover's two bases. -/
theorem base_sourced (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    baseAt Xs N 0 = 4 ∧ baseAt Xs N 1 = 9585 := by
  have hr : rowsOf (blocksOf Xs N) = fullFirst := (places_named scope hs.named).1
  unfold baseAt
  rw [rif_rows, rif_rows, hr]
  exact ⟨by rw [show placeAt 0 = ⟨1, some 0, 2, .K3⟩ from rfl, base_full.1]; rfl,
    by rw [show placeAt 1 = ⟨1, some 1, 2, .K3⟩ from rfl, base_full.2.1]; rfl⟩

/-- **THE BODY OF HeardOfFold, in scope.** -/
theorem heardAtKeys_of_fold (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (x : Xi)
    (seen : List Fmt.RoundView) (cols : List OpenedColumn) (s : FirstState) (r : List Fmt.RoundView) (c : List OpenedColumn)
    (h : foldBlocks 0 ((D Xs N Pl).first.blocksInOrder.take 16) ((D Xs N Pl).start₁ x) seen cols =
      .ok (s, r, c)) (tail : List Fmt.Drawn) :
    HeardAtKeys Xs N (seen.map (·.drawn) ++ tail) s := by
  have h6 := six_sourced hs scope
  have hlk := looks_sourced hs scope
  rw [take16 hs scope] at h
  obtain ⟨k0, k1, hk, H0, H1⟩ := front_heard _ _ _ _ _ 0 hlk h rfl rfl
  rw [len_zero hs scope] at H1
  obtain ⟨b0, b1⟩ := base_sourced hs scope
  have hk' : s.base.keys = [k0, k1] := hk
  have hr : (oneOf Xs).ranges = keyFull.ranges.x := h6.ranges
  intro i p hi hp
  rw [hr] at hi hp
  have hi2 : i < 2 := by
    have e : keyFull.ranges.x.lookups.length = 2 :=
      VerifiableInference.Desc.K3.KeyLaw.held_full_two
    omega
  have hface : faceAt Xs i = faceF i := by
    unfold faceAt lookAt faceF
    rw [hlk]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rfl
    · rfl
  obtain ⟨hsft, hpl⟩ := face_plain i hi2
  rw [hpl] at hp
  obtain ⟨hv1, p1, p2⟩ := pos_full i hi2 p hp
  obtain ⟨k, hk1⟩ : ∃ k, (faceF i).parts.getD p 0 = k + 1 := ⟨_, (Nat.sub_add_cancel hv1).symm⟩
  rw [hk1, Nat.add_sub_cancel] at p1 p2
  unfold keyPoints
  rw [hface, hk1, hk']
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · rw [b0]
    exact point_of_heard H0 hsft p k hp hk1 p1 p2
  · rw [b1]
    exact point_of_heard H1 hsft p k hp hk1 p1 p2

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.point_of_heard
#print axioms AtPublicFiles.FirstH.Lots.take16
#print axioms AtPublicFiles.FirstH.Lots.looks_sourced
#print axioms AtPublicFiles.FirstH.Lots.len_zero
#print axioms AtPublicFiles.FirstH.Lots.base_sourced
#print axioms AtPublicFiles.FirstH.Lots.heardAtKeys_of_fold
