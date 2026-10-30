-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2ParOfLawsProofs.lean: the second toy. This file proves the three statements of
Fmt/M2ParOfLaws.lean: under their hypotheses, the sizes and the description come back from the
parameter bytes.

The head of Fmt/M2ParOfLaws.lean says what the toy, the sizes, a description and spelling are.

1. What the file contains. Proofs, with a few definitions to state lemmas with. No Mathlib.
   The item "the chain of links". undoes_n (a fixed number of words), sp6, undoes_link1 (a link: a
   word, and a list of six words each), chain_whole (under the hypotheses of its statement, the
   reader undoes the spelling; the laws of readers are in Fmt/Rules1Laws.lean).
   The plan. link_poss, links_poss: no round of the frame (`linkRounds`, Fmt/M2Plan.lean) is called
   "CS" or "BASE". poss_back: so, with at least one stage (`h`), the positions under these names are
   those of the last test's stages (later_poss, Fmt/M1ParOfLawsProofs.lean). link_loc, loc_back:
   with at least one link and at least one stage (`hl`, `h`) the plan's first "LOC" has the frame's
   positions (`P.t`) and the bits of work.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   par_back   The links that are read are this toy's by definition: `linksRead` (Fmt/M2ParOf.lean)
     is made from `msgsOf`, as the spelling is. The first stage is not written in the item; it comes
     back because `Par.small` asks that it is the last group's.
   read_back, spec_back   (statements and hypotheses: Fmt/M2ParOfLaws.lean)

4. What is not claimed. See Fmt/M2ParOfLaws.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M2ParOfLaws
import Fmt.M1ParOfLawsProofs

namespace Fmt
namespace M2
open Fmt.M1

theorem undoes_n (n : Nat) :
    Undoes (rdMany rdWord n) (fun l : List UInt64 => cat (l.map u64)) fun l => l.length = n := by
  intro l hl pre post
  have a := undoes_many undoes_word l (fun _ _ => trivial) pre post
  rw [hl] at a
  exact a

/-- The spelling of a list of words; it is used for a message's six words. -/
def sp6 (l : List UInt64) : ByteArray := cat (l.map u64)

theorem sp6_size (l : List UInt64) (h : l.length = 6) : 1 ≤ (sp6 l).size := by
  match l, h with
  | [a, b, c, d, e, f], _ => simp only [sp6, List.map_cons, List.map_nil, cat_cons, cat_nil, ByteArray.size_append, size_u64]; omega

/-- The spelling of a link, cut as the reader cuts it. -/
def spLink1 (x : UInt64 × List (List UInt64)) : ByteArray := pair u64 (list sp6) x

def okLink1 (x : UInt64 × List (List UInt64)) : Prop :=
  True ∧ x.2.length < 2 ^ 64 ∧ ∀ l ∈ x.2, l.length = 6

theorem undoes_link1 : Undoes rdLink1 spLink1 okLink1 :=
  undoes_pair undoes_word (undoes_list (undoes_n 6) fun l h => sp6_size l h)

theorem link1_size (x : UInt64 × List (List UInt64)) : 1 ≤ (spLink1 x).size := by
  simp only [spLink1, pair, ByteArray.size_append, size_u64]; omega

/-- The spelling of the item "the chain of links", cut as the reader cuts it. -/
def spChain (x : List UInt64 × List (UInt64 × List (List UInt64)) × List UInt64 ×
      List (Nat × Nat × Nat × Nat) × UInt64) : ByteArray :=
  pair (fun l : List UInt64 => cat (l.map u64))
    (pair (list spLink1) (pair (fun l : List UInt64 => cat (l.map u64)) (pair (list sp4) u64))) x

theorem chain_whole (a : List UInt64) (ls : List (UInt64 × List (List UInt64))) (b : List UInt64)
    (ss : List (Nat × Nat × Nat × Nat)) (w : UInt64) (ha : a.length = 2) (h1 : ls.length < 2 ^ 64)
    (h2 : ∀ x ∈ ls, okLink1 x) (hb : b.length = 2) (h3 : ss.length < 2 ^ 64)
    (h4 : ∀ s ∈ ss, s.1 < 2 ^ 64 ∧ s.2.1 < 2 ^ 64 ∧ s.2.2.1 < 2 ^ 64 ∧ s.2.2.2 < 2 ^ 64) :
    whole rdChain (spChain (a, ls, b, ss, w)) = some (a, ls, b, ss, w) :=
  whole_of_undoes (undoes_pair (undoes_n 2)
      (undoes_pair (undoes_list undoes_link1 fun x _ => link1_size x)
        (undoes_pair (undoes_n 2)
          (undoes_pair (undoes_list undoes_stage4 fun s _ => sp4_size s) undoes_word))))
    (a, ls, b, ss, w) ⟨ha, ⟨h1, h2⟩, hb, ⟨h3, h4⟩, trivial⟩

def later4 (P : Par) : List (Nat × Nat × Nat × Nat) :=
  (P.stages.drop 1).map fun s =>
    (noIn (onceL (P.stages.map (·.C))) s.C, noIn (onceL (P.stages.map (·.Z))) s.Z, s.k, s.h)

theorem msg_bytes (m : Mem) (moment life : Nat) :
    linkMsgBytes m moment life = sp6 ((msgWords m moment life).map UInt64.ofNat) := by
  simp only [linkMsgBytes, sp6, msgWords, u64n, List.map_cons, List.map_nil]

theorem link_bytes (L i : Nat) :
    linkBytes 0 (msgsOf L (i + 1)) =
      spLink1 (0, (msgsOf L (i + 1)).map fun x => (msgWords x.1 x.2.1 x.2.2).map UInt64.ofNat) := by
  have e : (msgsOf L (i + 1)).map (fun x => linkMsgBytes x.1 x.2.1 x.2.2) =
      ((msgsOf L (i + 1)).map fun x => (msgWords x.1 x.2.1 x.2.2).map UInt64.ofNat).map sp6 := by
    rw [List.map_map]
    exact List.map_congr_left fun x _ => msg_bytes x.1 x.2.1 x.2.2
  simp only [linkBytes, e, spLink1, pair, list, List.length_map, ByteArray.append_assoc]
  rfl

theorem chain_bytes (P : Par) :
    chainBytes P =
      spChain ([UInt64.ofNat (noIn (onceL (P.stages.map (·.C))) P.C),
            UInt64.ofNat (noIn (onceL (P.stages.map (·.Z))) P.Z)],
          linksRead P.links, [0, 1], later4 P, 1) := by
  have e : (List.range P.links).map (fun i => linkBytes 0 (msgsOf P.links (i + 1))) =
      (linksRead P.links).map spLink1 := by
    simp only [linksRead, List.map_map]
    exact List.map_congr_left fun i _ => link_bytes P.links i
  simp only [chainBytes, e]
  simp only [spChain, pair, list, linksRead, List.length_map, List.length_range, List.map_cons,
    List.map_nil, cat_cons, cat_nil, ByteArray.append_assoc, ByteArray.append_empty, stagesBytes,
    later4, choicesBytes, bool, u64n, List.map_map]
  rfl

/-! the plan -/

theorem link_poss (n : String) (h : n = "CS" ∨ n = "BASE") (P : Par) (m : Nat) :
    possUnder n (linkRounds P m) = [] := by
  rcases h with rfl | rfl
  · simp only [linkRounds, possUnder_append, possUnder_rep "CS" P.V (rTwo "PSC round") (by decide), possUnder_rep "CS" (kOf (memsOf P.links m)) (rTwo "FOLD round") (by decide)]; rfl
  · simp only [linkRounds, possUnder_append, possUnder_rep "BASE" P.V (rTwo "PSC round") (by decide), possUnder_rep "BASE" (kOf (memsOf P.links m)) (rTwo "FOLD round") (by decide)]; rfl

theorem links_poss (n : String) (h : n = "CS" ∨ n = "BASE") (P : Par) (l : List Nat) :
    possUnder n (l.flatMap fun i => linkRounds P (i + 1)) = [] := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.flatMap_cons, possUnder_append, link_poss n h, ih]; rfl

theorem poss_back (P : Par) (nonceB : Nat) (h : P.stages ≠ []) :
    possOf (planOf P nonceB) = P.stages.map (·.t) := by
  obtain ⟨s, rest, e⟩ : ∃ s rest, P.stages = s :: rest := by
    cases hs : P.stages with
    | nil => exact absurd hs h
    | cons s rest => exact ⟨s, rest, rfl⟩
  show possUnder "CS" (roundsOf P) ++ possUnder "BASE" (roundsOf P) = _
  simp only [roundsOf, e, possUnder_append,
    links_poss "CS" (Or.inl rfl), links_poss "BASE" (Or.inr rfl)]
  have c1 : possUnder "CS" [rSeedN (seedOfGroup P 1), rAnswers (nAns P 1)] = [] := rfl
  have c2 : possUnder "BASE" [rSeedN (seedOfGroup P 1), rAnswers (nAns P 1)] = [] := rfl
  have c3 : possUnder "CS" [rBatN (nRowsAt P (P.links + 1))] = [] := rfl
  have c4 : possUnder "BASE" [rBatN (nRowsAt P (P.links + 1))] = [] := rfl
  rw [c1, c2, c3, c4]
  simp only [List.nil_append, List.append_nil]
  exact later_poss P.work rest P.links _ s

theorem firstUnder_append_some
    (n : String) (a b : List Round) (x : Entry) (h : firstUnder n a = some x) :
    firstUnder n (a ++ b) = some x := by
  simp only [firstUnder, List.map_append, List.find?_append] at h ⊢
  rw [h]; rfl

theorem link_loc (P : Par) (m : Nat) :
    ∃ x, firstUnder "LOC" (linkRounds P m) = some x ∧ x.poss = P.t ∧ x.work = P.work := by
  refine ⟨(rLoc P.work P.t P.C.a (nAns P (m + 1)) (m - 1) (widthOf (memsOf P.links m) 1)).entry, ?_,
    rfl, rfl⟩
  simp only [linkRounds]
  rw [firstUnder_append_none _ _ _ ?_]
  · rfl
  · rw [firstUnder_append_none _ _ _ ?_]
    · exact firstUnder_rep "LOC" _ (rTwo "FOLD round") (by decide)
    · rw [firstUnder_append_none _ _ _ ?_]
      · rfl
      · rw [firstUnder_append_none _ _ _ ?_]
        · rfl
        · rw [firstUnder_append_none _ _ _ rfl]
          exact firstUnder_rep "LOC" _ (rTwo "PSC round") (by decide)

theorem loc_back (P : Par) (nonceB : Nat) (h : P.stages ≠ []) (hl : 1 ≤ P.links) :
    ∃ x,
      (planOf P nonceB).entries.find? (·.name == "LOC") = some x ∧
      x.poss = P.t ∧
      x.work = P.work := by
  obtain ⟨s, rest, e⟩ : ∃ s rest, P.stages = s :: rest := by
    cases hs : P.stages with
    | nil => exact absurd hs h
    | cons s rest => exact ⟨s, rest, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, P.links = n + 1 := ⟨P.links - 1, by omega⟩
  obtain ⟨x, h1, h2, h3⟩ := link_loc P 1
  refine ⟨x, ?_, h2, h3⟩
  show firstUnder "LOC" (roundsOf P) = _
  simp only [roundsOf, e]
  have r1 : (List.range P.links).flatMap (fun i => linkRounds P (i + 1)) =
      linkRounds P 1 ++ ((List.range n).map (· + 1)).flatMap (fun i => linkRounds P (i + 1)) := by
    rw [hn, List.range_succ_eq_map, List.flatMap_cons]
  rw [r1]
  refine firstUnder_append_some _ _ _ _ (firstUnder_append_some _ _ _ _ ?_)
  rw [firstUnder_append_none _ _ _ rfl]
  exact firstUnder_append_some _ _ _ _ h1

theorem value_codes (P : Par) (cfg : ByteArray) (nonceB : Nat) :
    (theParams P cfg nonceB).valueOf nameCodes =
      some (codesBytes (onceL (P.stages.map (·.C))) (onceL (P.stages.map (·.Z)))) := by
  have h2 : (nameCodes == nameCodes) = true := by decide
  simp only [theParams, Params.valueOf, itemsOf, List.find?_cons, h2, Option.map_some, codesItem]

theorem value_links (P : Par) (cfg : ByteArray) (nonceB : Nat) :
    (theParams P cfg nonceB).valueOf nameLinks = some (chainBytes P) := by
  have h1 : (nameCodes == nameLinks) = false := by decide
  have h2 : (nameLinks == nameLinks) = true := by decide
  simp only [theParams, Params.valueOf, itemsOf, List.find?_cons, h1, h2, Option.map_some]

theorem links_ok (L : Nat) : ∀ x ∈ linksRead L, okLink1 x := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
  refine ⟨trivial, ?_, ?_⟩
  · simp [msgsOf]
  · intro l hl
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hl
    simp [msgWords]

theorem par_back : Spec.par_back := by
  intro P cfg nonceB hs
  obtain ⟨s0, rest, e⟩ : ∃ s rest, P.stages = s :: rest := by
    cases h : P.stages with
    | nil => simp [Par.small, h] at hs
    | cons s rest => exact ⟨s, rest, rfl⟩
  have hne : P.stages ≠ [] := by rw [e]; exact List.cons_ne_nil _ _
  simp only [Par.small, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Stage.small, Code.small] at hs
  obtain ⟨⟨⟨⟨hl1, hl2⟩, hlen⟩, hall⟩, hfirst⟩ := hs
  rw [e] at hfirst
  simp only [Bool.and_eq_true, beq_iff_eq] at hfirst
  obtain ⟨⟨⟨hC, hZ⟩, hk⟩, hh⟩ := hfirst
  generalize hcm : onceL (P.stages.map (·.C)) = cm
  generalize hcz : onceL (P.stages.map (·.Z)) = cz
  have lm : cm.length ≤ P.stages.length := by
    rw [← hcm]; simpa using length_onceL (P.stages.map (·.C))
  have lz : cz.length ≤ P.stages.length := by
    rw [← hcz]; simpa using length_onceL (P.stages.map (·.Z))
  have mm : ∀ s ∈ P.stages, s.C ∈ cm ∧ s.Z ∈ cz := fun s hs => by
    rw [← hcm, ← hcz, mem_onceL, mem_onceL]
    exact ⟨List.mem_map.2 ⟨s, hs, rfl⟩, List.mem_map.2 ⟨s, hs, rfl⟩⟩
  have om : okCodes cm := ⟨by omega, fun c hc => by
    rw [← hcm, mem_onceL] at hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hc
    have := hall s hs
    exact ⟨this.1.1.1.1.1, this.1.1.1.1.2, this.1.1.1.2⟩⟩
  have oz : okCodes cz := ⟨by omega, fun c hc => by
    rw [← hcz, mem_onceL] at hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hc
    have := hall s hs
    exact ⟨this.1.1.2.1.1, this.1.1.2.1.2, this.1.1.2.2⟩⟩
  have m0 : s0 ∈ P.stages := by rw [e]; exact List.mem_cons_self
  have mC : P.C ∈ cm := hC ▸ (mm s0 m0).1
  have mZ : P.Z ∈ cz := hZ ▸ (mm s0 m0).2
  have a1 : ((theParams P cfg nonceB).valueOf nameCodes).bind (whole rdCodes) = some (cm, cz) := by
    rw [value_codes, hcm, hcz, Option.bind_some]; exact codes_back cm cz om oz
  have a2 : ((theParams P cfg nonceB).valueOf nameLinks).bind (whole rdChain) =
      some ([UInt64.ofNat (noIn cm P.C), UInt64.ofNat (noIn cz P.Z)], linksRead P.links,
          [0, 1], later4 P, 1) := by
    rw [value_links, chain_bytes, Option.bind_some, hcm, hcz]
    refine chain_whole _ _ _ _ _ rfl
      (by simp only [linksRead, List.length_map, List.length_range]; exact hl2) (links_ok P.links)
      rfl (by simp only [later4, List.length_map, List.length_drop]; omega) fun x hx => ?_
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    have hs' : s ∈ P.stages := List.mem_of_mem_drop hs
    have b1 := noIn_lt cm s.C (mm s hs').1
    have b2 := noIn_lt cz s.Z (mm s hs').2
    have := hall s hs'
    rw [hcm, hcz]
    exact ⟨by show noIn cm s.C < _; omega, by show noIn cz s.Z < _; omega, this.1.2, this.2⟩
  obtain ⟨loc, a3, a4, a5⟩ := loc_back P nonceB hne hl1
  have a3' : (theParams P cfg nonceB).plan.entries.find? (·.name == "LOC") = some loc := a3
  have a6 : possOf (theParams P cfg nonceB).plan = s0.t :: rest.map (·.t) := by
    have := poss_back P nonceB hne
    rw [e] at this
    exact this
  have l4 : later4 P = rest.map fun s => (noIn cm s.C, noIn cz s.Z, s.k, s.h) := by
    simp only [later4, e, List.drop_succ_cons, List.drop_zero]
    rw [← e, hcm, hcz]
  have nC := noIn_lt cm P.C mC
  have nZ := noIn_lt cz P.Z mZ
  have ll : (linksRead P.links).length = P.links := by
    simp only [linksRead, List.length_map, List.length_range]
  unfold parOf
  rw [a1, a2, a3']
  simp only [a6, l4]
  rw [toNat_ofNat_lt _ (by omega : noIn cm P.C < 2 ^ 64),
    toNat_ofNat_lt _ (by omega : noIn cz P.Z < 2 ^ 64), noIn_get cm P.C mC, noIn_get cz P.Z mZ]
  have mr : ∀ s ∈ rest, s.C ∈ cm ∧ s.Z ∈ cz := fun s hs =>
    mm s (by rw [e]; exact List.mem_cons_of_mem _ hs)
  simp only [ll, List.length_map, beq_self_eq_true, Bool.and_self, if_true, stages_of cm cz rest mr,
    allSome_map, Option.map_some, a4, a5]
  have es : ({ C := P.C, Z := P.Z, k := kOf (memsOf P.links (P.links + 1)),
               h := 0, t := s0.t } : Stage) :: rest = P.stages := by
    rw [e, ← hC, ← hZ, ← hk, ← hh]
  rw [es]
  rfl

theorem params_of (P : Par) (cfg : ByteArray) (nonceB : Nat) :
    (specOf P cfg (itemsOf P) nonceB).params = (theParams P cfg nonceB).bytes := rfl

theorem read_back : Spec.read_back := by
  intro P cfg nonceB hs hf
  rw [params_of, params_back _ hf]
  exact par_back P cfg nonceB hs

theorem spec_back : Spec.spec_back := by
  intro P cfg nonceB hs hf hok
  unfold specFrom
  rw [params_of, params_back _ hf]
  simp only [Option.bind_some, par_back P cfg nonceB hs]
  have e1 : specOf P (theParams P cfg nonceB).cfg
        (theParams P cfg nonceB).others (theParams P cfg nonceB).plan.nonce =
      specOf P cfg (itemsOf P) nonceB := rfl
  have e2 : fitsPlan (theParams P cfg nonceB) P = true := samePlan_self _
  rw [e1, e2, hok, params_of]
  simp

end M2
end Fmt
