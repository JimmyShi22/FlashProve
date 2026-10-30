-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3ParOfLawsProofs.lean: the entry file. Under the hypothesis of the statement of
Fmt/M3ParOfLaws.lean, what `parOf` of Fmt/M3ParOf.lean reads out of the parameters is what was
spelled into them. That is the sizes and the number of salt bytes in a leaf of a stored table.
This file has the proof of this statement. The head of
Fmt/M3ParOfLaws.lean says what these nouns mean.

1. What the file contains. Proofs. No Mathlib.
   The item "the link".
   - `cat_append`, `cat_flat`: joining (`cat`) a list of words that is made of parts gives the same
     bytes as joining each part and then joining the results.
   - `undoes_14`, `link_whole`: under the hypotheses of their statements, the reader undoes the
     spelling. The spelling is fourteen words, then a list of entries of four words each, then a
     word. The laws of readers are in Fmt/Rules1Laws.lean.
   - `link_bytes`: the words that Fmt/M3Items.lean lists for the item, written as bytes, are that
     spelling, at `head14` and `later4`.
   The plan. Both lemmas assume that `P.stages` is not empty.
   - `link_entry` says which entry of the plan has the name "LINK".
   - `poss_back`: the numbers of positions in the plan's entries "CS", and then in its entry
     "BASE", are those of the stages. The proof uses `later_poss` of Fmt/M1ParOfLawsProofs.lean,
     because the rounds of the proximity test are the first toy's.
   `value_codes`, `value_link`: the two items by their names.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems. `par_back` (statement and hypothesis: Fmt/M3ParOfLaws.lean).

   `par_back`: The proof uses the lemmas above and the first toy's lemmas on the list that has each
     code once (`noIn_get`, `mem_onceL`, `stages_of`). The first stage is read back because
     `Par.small` requires that it is the group.






4. What is not claimed. See Fmt/M3ParOfLaws.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M3ParOfLaws
import Fmt.M1ParOfLawsProofs

namespace Fmt
namespace M3
open Fmt.M1 Fmt.M2

theorem cat_append (a b : List ByteArray) : cat (a ++ b) = cat a ++ cat b := by
  induction a with
  | nil => rw [List.nil_append, cat_nil, ByteArray.empty_append]
  | cons x a ih => rw [List.cons_append, cat_cons, cat_cons, ih, ByteArray.append_assoc]

theorem cat_flat {α : Type} (l : List α) (f : α → List Nat) :
    cat ((l.flatMap f).map u64n) = cat (l.map fun s => cat ((f s).map u64n)) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, List.map_append, cat_append, ih, List.map_cons, cat_cons]

/-- fourteen words -/
theorem undoes_14 :
    Undoes (rdMany rdWord 14) (fun l : List UInt64 => cat (l.map u64)) fun l => l.length = 14 := by
  intro l hl pre post
  have a := undoes_many undoes_word l (fun _ _ => trivial) pre post
  rw [hl] at a
  exact a

/-- the item's spelling, cut as the reader cuts it -/
def spLink (x : List UInt64 × List (Nat × Nat × Nat × Nat) × UInt64) : ByteArray :=
  pair (fun l : List UInt64 => cat (l.map u64)) (pair (list sp4) u64) x

theorem link_whole (hd : List UInt64) (ss : List (Nat × Nat × Nat × Nat)) (w : UInt64)
    (h0 : hd.length = 14) (h1 : ss.length < 2 ^ 64)
    (h2 : ∀ s ∈ ss, s.1 < 2 ^ 64 ∧ s.2.1 < 2 ^ 64 ∧ s.2.2.1 < 2 ^ 64 ∧ s.2.2.2 < 2 ^ 64) :
    whole rdLink (spLink (hd, ss, w)) = some (hd, ss, w) :=
  whole_of_undoes (undoes_pair
      undoes_14 (undoes_pair (undoes_list undoes_stage4 fun s _ => sp4_size s) undoes_word))
    (hd, ss, w) ⟨h0, ⟨h1, h2⟩, trivial⟩

/-- the fourteen words of sizes -/
def head14 (P : Par) (tsalt : Nat) : List Nat :=
  [P.T.a, P.T.l, P.T.r, P.v, P.s, tsalt, P.nu0, P.nuj, noIn (baseCodes P false) P.C,
    noIn (maskCodes P) P.Z, P.R, if P.high then 1 else 0, 0, 1]

def later4 (P : Par) : List (Nat × Nat × Nat × Nat) :=
  (P.stages.drop 1).map fun s => (noIn (baseCodes P false) s.C, noIn (maskCodes P) s.Z, s.k, s.h)

theorem link_bytes (P : Par) (tsalt : Nat) :
    linkBytes P false false tsalt = spLink ((head14 P tsalt).map UInt64.ofNat, later4 P, 1) := by
  have e : linkWords P false false tsalt =
      head14 P tsalt ++ [P.stages.length - 1] ++
        ((P.stages.drop 1).flatMap fun s =>
          [noIn (baseCodes P false) s.C, noIn (maskCodes P) s.Z, s.k, s.h]) ++ [1] := by
    simp [linkWords, head14]
  unfold linkBytes
  rw [e]
  simp only [List.map_append, cat_append, cat_flat]
  simp only [spLink, pair, list, later4, List.length_map, List.length_drop,
    List.map_map, ByteArray.append_assoc]
  rfl

theorem base_codes (P : Par) : baseCodes P false = onceL (P.stages.map (·.C)) := by simp [baseCodes]

theorem link_entry (P : Par) (nonceB : Nat) (h : P.stages ≠ []) :
    (planOf P nonceB).entries.find? (·.name == "LINK") =
      some (rLink P.work (P.nu0 + P.nuj) P.T.a).entry := by
  obtain ⟨s, rest, e⟩ : ∃ s rest, P.stages = s :: rest := by
    cases hs : P.stages with
    | nil => exact absurd hs h
    | cons s rest => exact ⟨s, rest, rfl⟩
  show ((roundsOf P).map (·.entry)).find? (·.name == "LINK") = _
  simp only [roundsOf, e]
  rfl

theorem poss_back (P : Par) (nonceB : Nat) (h : P.stages ≠ []) :
    possOf (planOf P nonceB) = P.stages.map (·.t) := by
  obtain ⟨s, rest, e⟩ : ∃ s rest, P.stages = s :: rest := by
    cases hs : P.stages with
    | nil => exact absurd hs h
    | cons s rest => exact ⟨s, rest, rfl⟩
  show possUnder "CS" (roundsOf P) ++ possUnder "BASE" (roundsOf P) = _
  simp only [roundsOf, e, possUnder_append]
  have c1 : possUnder "CS"
        [rLinkPoint P.v, rSeedN (P.aR + P.aP), rAnswers 2, rLink P.work (P.nu0 + P.nuj) P.T.a,
          rLinkPhi P.aPhi, rBatN (nRows P)] = [] := rfl
  have c2 : possUnder "BASE"
        [rLinkPoint P.v, rSeedN (P.aR + P.aP), rAnswers 2, rLink P.work (P.nu0 + P.nuj) P.T.a,
          rLinkPhi P.aPhi, rBatN (nRows P)] = [] := rfl
  rw [c1, c2, List.nil_append, List.nil_append]
  exact later_poss P.work rest 0 (width0 P) s

theorem value_codes (P : Par) (cfg : ByteArray) (nonceB tsalt : Nat) :
    (theParams P cfg nonceB tsalt).valueOf nameCodes =
      some (codesBytes (baseCodes P false) (maskCodes P)) := by
  have h2 : (nameCodes == nameCodes) = true := by decide
  simp only [theParams, Params.valueOf, itemsOf, List.find?_cons, h2, Option.map_some]

theorem value_link (P : Par) (cfg : ByteArray) (nonceB tsalt : Nat) :
    (theParams P cfg nonceB tsalt).valueOf nameLink = some (linkBytes P false false tsalt) := by
  have h1 : (nameCodes == nameLink) = false := by decide
  have h2 : (nameLink == nameLink) = true := by decide
  simp only [theParams, Params.valueOf, itemsOf, List.find?_cons, h1, h2, Option.map_some]

theorem par_back : Spec.par_back := by
  intro P cfg nonceB tsalt hs
  obtain ⟨s0, rest, e⟩ : ∃ s rest, P.stages = s :: rest := by
    cases h : P.stages with
    | nil => simp [Par.small, h] at hs
    | cons s rest => exact ⟨s, rest, rfl⟩
  have hne : P.stages ≠ [] := by rw [e]; exact List.cons_ne_nil _ _
  simp only [Par.small, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Stage.small, Code.small] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hT, hv⟩, hss⟩, hts⟩, hn0⟩, hnj⟩, hR⟩, hlen⟩, hall⟩, hfirst⟩ := hs
  rw [e] at hfirst
  simp only [Bool.and_eq_true, beq_iff_eq] at hfirst
  obtain ⟨⟨⟨hC, hZ⟩, hk⟩, hh⟩ := hfirst
  generalize hcm : baseCodes P false = cm
  generalize hcz : maskCodes P = cz
  have hcm' : onceL (P.stages.map (·.C)) = cm := by rw [← hcm, base_codes]
  have hcz' : onceL (P.stages.map (·.Z)) = cz := hcz
  have lm : cm.length ≤ P.stages.length := by
    rw [← hcm']; simpa using length_onceL (P.stages.map (·.C))
  have lz : cz.length ≤ P.stages.length := by
    rw [← hcz']; simpa using length_onceL (P.stages.map (·.Z))
  have mm : ∀ s ∈ P.stages, s.C ∈ cm ∧ s.Z ∈ cz := fun s hs => by
    rw [← hcm', ← hcz', mem_onceL, mem_onceL]
    exact ⟨List.mem_map.2 ⟨s, hs, rfl⟩, List.mem_map.2 ⟨s, hs, rfl⟩⟩
  have om : okCodes cm := ⟨by omega, fun c hc => by
    rw [← hcm', mem_onceL] at hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hc
    have := hall s hs
    exact ⟨this.1.1.1.1.1, this.1.1.1.1.2, this.1.1.1.2⟩⟩
  have oz : okCodes cz := ⟨by omega, fun c hc => by
    rw [← hcz', mem_onceL] at hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hc
    have := hall s hs
    exact ⟨this.1.1.2.1.1, this.1.1.2.1.2, this.1.1.2.2⟩⟩
  have m0 : s0 ∈ P.stages := by rw [e]; exact List.mem_cons_self
  have mC : P.C ∈ cm := hC ▸ (mm s0 m0).1
  have mZ : P.Z ∈ cz := hZ ▸ (mm s0 m0).2
  have a1 : ((theParams P cfg nonceB tsalt).valueOf nameCodes).bind (whole rdCodes) =
      some (cm, cz) := by
    rw [value_codes, hcm, hcz, Option.bind_some]; exact codes_back cm cz om oz
  have a2 : ((theParams P cfg nonceB tsalt).valueOf nameLink).bind (whole rdLink) =
      some ((head14 P tsalt).map UInt64.ofNat, later4 P, 1) := by
    rw [value_link, link_bytes, Option.bind_some]
    refine link_whole _ _ _
      (by simp only [head14, List.map_cons, List.map_nil, List.length_cons, List.length_nil])
      (by simp only [later4, List.length_map, List.length_drop]; omega) fun x hx => ?_
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    have hs' : s ∈ P.stages := List.mem_of_mem_drop hs
    have b1 := noIn_lt cm s.C (mm s hs').1
    have b2 := noIn_lt cz s.Z (mm s hs').2
    have := hall s hs'
    rw [hcm, hcz]
    exact ⟨by show noIn cm s.C < _; omega, by show noIn cz s.Z < _; omega, this.1.2, this.2⟩
  have a3 : (theParams P cfg nonceB tsalt).plan.entries.find? (·.name == "LINK") =
      some (rLink P.work (P.nu0 + P.nuj) P.T.a).entry :=
    link_entry P nonceB hne
  have a6 : possOf (theParams P cfg nonceB tsalt).plan = s0.t :: rest.map (·.t) := by
    have := poss_back P nonceB hne
    rw [e] at this
    exact this
  have l4 : later4 P = rest.map fun s => (noIn cm s.C, noIn cz s.Z, s.k, s.h) := by
    simp only [later4, e, List.drop_succ_cons, List.drop_zero, hcm, hcz]
  have nC := noIn_lt cm P.C mC
  have nZ := noIn_lt cz P.Z mZ
  unfold parOf
  rw [a1, a2, a3]
  simp only [head14, List.map_cons, List.map_nil, hcm, hcz, a6, l4]
  rw [toNat_ofNat_lt _ (by omega : noIn cm P.C < 2 ^ 64),
    toNat_ofNat_lt _ (by omega : noIn cz P.Z < 2 ^ 64), noIn_get cm P.C mC, noIn_get cz P.Z mZ]
  have hhi : (UInt64.ofNat (if P.high = true then 1 else 0) == 0 || P.high) = true := by
    cases P.high <;> decide
  have hhi' : (UInt64.ofNat (if P.high = true then 1 else 0) == 1) = P.high := by
    cases P.high <;> decide
  have c0 : (UInt64.ofNat 0 == 0) = true := by decide
  have c1 : (UInt64.ofNat 1 == 1) = true := by decide
  have c2 : ((1 : UInt64) == 1) = true := by decide
  have mr : ∀ s ∈ rest, s.C ∈ cm ∧ s.Z ∈ cz := fun s hs =>
    mm s (by rw [e]; exact List.mem_cons_of_mem _ hs)
  simp only [c0, c1, c2, hhi', hhi, List.length_map, beq_self_eq_true, Bool.and_self, if_true,
    stages_of cm cz rest mr, allSome_map, Option.map_some, toNat_ofNat_lt _ hT.1.1,
    toNat_ofNat_lt _ hT.1.2, toNat_ofNat_lt _ hT.2, toNat_ofNat_lt _ hv, toNat_ofNat_lt _ hss,
    toNat_ofNat_lt _ hn0, toNat_ofNat_lt _ hnj, toNat_ofNat_lt _ hR, toNat_ofNat_lt _ hts]
  have es : ({ C := P.C, Z := P.Z, k := 1 + clog P.R, h := 0, t := s0.t } : Stage) :: rest =
      P.stages := by
    rw [e, ← hC, ← hZ, ← hk, ← hh]
  rw [es]
  rfl

end M3
end Fmt
