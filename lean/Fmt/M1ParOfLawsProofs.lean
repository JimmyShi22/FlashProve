-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1ParOfLawsProofs.lean: the first toy. The sizes are read back out of the parameter bytes of
their own description, for all sizes within bounds whose parameters fit (`Params.fit`). The proofs
of `par_back`, `read_back` and `spec_back` of Fmt/M1ParOfLaws.lean.

The words (sizes, description, parameter bytes, items) are told in the head of Fmt/M1ParOfLaws.lean.
An entry is a round's row in the plan (`Entry`, Fmt/Plan.lean); "ZERO", "CS" and "BASE" are names of
entries of this toy's plan (Fmt/M1Plan.lean).

1. What the file contains. Proofs, and four small definitions for them (`okCodes`, `sp4`,
`possUnder`, `firstUnder`). No Mathlib.
   `undoes_code`, `codes_back`: the item "codes": two lists of codes are read back (`okCodes`).
   `undoes_stage4`, `stages_back`: the item on the stages: a list of four words each is read back,
     if the list has fewer than 2^64 entries and every word is below 2^64 (`h1`, `h2`).
   `mem_onceL`, `length_onceL`: the list in which each code stands once has the same members and is
     no longer.
   `noIn_get`, `noIn_lt`: a member's number in a list leads back to it, and is below the list's
     length. So a code's number is below the number of stages: main codes and mask codes have a list
     each, with at most one code for a stage. No further bound is needed.
   `possUnder`, `later_poss`, `poss_back`: for sizes with a stage (`h` of `poss_back`), the
     positions under "CS", then under "BASE", are the stages' numbers of positions, in order (also
     for one stage, where there is no "CS").
   `firstUnder`, `later_base`, `base_back`: for sizes with a stage (`h`), the first entry "BASE" has
     the sizes' bits of work. `zero_back`: for sizes with a stage (`h`), the first entry "ZERO"
     draws K elements (also for K = 0).
   `allSome_map`, `stages_of`: every stage comes back from its four words, its positions and the two
     lists, if these lists hold its codes (`h`).

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems. `par_back`, `read_back`, `spec_back` (statements and hypotheses:
Fmt/M1ParOfLaws.lean).
   `par_back`: the sizes out of their own plan and items.
   `read_back`: the sizes out of their description's parameter bytes (by `params_back` of
     Fmt/ParamsReadLawsProofs.lean).
   `spec_back`: the sizes and the description out of these bytes.

4. What is not claimed. See Fmt/M1ParOfLaws.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1ParOfLaws
import Fmt.ParamsReadLawsProofs

namespace Fmt
namespace M1

theorem code_bytes (c : Code) : c.bytes = cat (([c.a, c.l, c.r].map UInt64.ofNat).map u64) := by
  simp only [Code.bytes, u64n, List.map_cons, List.map_nil, cat_cons, cat_nil,
    ByteArray.append_assoc, ByteArray.append_empty]

theorem undoes_code :
    Undoes rdCode Code.bytes fun c => c.a < 2 ^ 64 ∧ c.l < 2 ^ 64 ∧ c.r < 2 ^ 64 := by
  intro c hc pre post
  rw [code_bytes]
  have a := undoes_many undoes_word ([c.a, c.l, c.r].map UInt64.ofNat) (fun _ _ => trivial) pre post
  have hl : ([c.a, c.l, c.r].map UInt64.ofNat).length = 3 := rfl
  rw [hl] at a
  unfold rdCode
  rw [a]
  simp only [List.map_cons, List.map_nil, toNat_ofNat_lt _ hc.1,
    toNat_ofNat_lt _ hc.2.1, toNat_ofNat_lt _ hc.2.2]

theorem code_size (c : Code) : 1 ≤ c.bytes.size := by
  simp only [Code.bytes, u64n, ByteArray.size_append, size_u64]; omega

/-- a list of codes within the bounds -/
def okCodes (l : List Code) : Prop :=
  l.length < 2 ^ 64 ∧ ∀ c ∈ l, c.a < 2 ^ 64 ∧ c.l < 2 ^ 64 ∧ c.r < 2 ^ 64

theorem codes_back (A B : List Code) (hA : okCodes A) (hB : okCodes B) :
    whole rdCodes (codesBytes A B) = some (A, B) := by
  have h := whole_of_undoes
    (undoes_pair (undoes_list undoes_code fun c _ => code_size c)
      (undoes_list undoes_code fun c _ => code_size c))
    (A, B) ⟨hA, hB⟩
  have e : pair (list Code.bytes) (list Code.bytes) (A, B) = codesBytes A B := by
    simp only [pair, list, codesBytes, ByteArray.append_assoc]
  rw [e] at h
  exact h

/-- the spelling of a stage's four words -/
def sp4 (s : Nat × Nat × Nat × Nat) : ByteArray := cat ([s.1, s.2.1, s.2.2.1, s.2.2.2].map u64n)

theorem undoes_stage4 :
    Undoes rdStage4 sp4 fun s =>
      s.1 < 2 ^ 64 ∧ s.2.1 < 2 ^ 64 ∧ s.2.2.1 < 2 ^ 64 ∧ s.2.2.2 < 2 ^ 64 := by
  intro s hs pre post
  have e : sp4 s = cat (([s.1, s.2.1, s.2.2.1, s.2.2.2].map UInt64.ofNat).map u64) := by
    simp only [sp4, u64n, List.map_cons, List.map_nil]
  rw [e]
  have a := undoes_many undoes_word ([s.1, s.2.1, s.2.2.1, s.2.2.2].map UInt64.ofNat)
    (fun _ _ => trivial) pre post
  have hl : ([s.1, s.2.1, s.2.2.1, s.2.2.2].map UInt64.ofNat).length = 4 := rfl
  rw [hl] at a
  unfold rdStage4
  rw [a]
  simp only [List.map_cons, List.map_nil, toNat_ofNat_lt _ hs.1, toNat_ofNat_lt _ hs.2.1,
    toNat_ofNat_lt _ hs.2.2.1, toNat_ofNat_lt _ hs.2.2.2]

theorem sp4_size (s : Nat × Nat × Nat × Nat) : 1 ≤ (sp4 s).size := by
  simp only [sp4, u64n, List.map_cons, List.map_nil, cat_cons, cat_nil, ByteArray.size_append, size_u64]; omega

theorem stages_back (l : List (Nat × Nat × Nat × Nat)) (h1 : l.length < 2 ^ 64)
    (h2 : ∀ s ∈ l, s.1 < 2 ^ 64 ∧ s.2.1 < 2 ^ 64 ∧ s.2.2.1 < 2 ^ 64 ∧ s.2.2.2 < 2 ^ 64) :
    whole rdStages (stagesBytes l) = some l :=
  whole_of_undoes (undoes_list undoes_stage4 fun s _ => sp4_size s) l ⟨h1, h2⟩

/-! the list in which each code stands once -/

theorem mem_onceL (l : List Code) (x : Code) : x ∈ onceL l ↔ x ∈ l := by
  induction l with
  | nil => simp [onceL]
  | cons c l ih =>
    simp only [onceL, List.mem_cons, List.mem_filter, ih, bne_iff_ne, ne_eq]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.1
    · rintro (h | h)
      · exact Or.inl h
      · by_cases e : x = c
        · exact Or.inl e
        · exact Or.inr ⟨h, e⟩

theorem length_onceL (l : List Code) : (onceL l).length ≤ l.length := by
  induction l with
  | nil => simp [onceL]
  | cons c l ih =>
    simp only [onceL, List.length_cons]
    have := List.length_filter_le (fun y => y != c) (onceL l)
    omega

theorem noIn_get (L : List Code) (x : Code) (h : x ∈ L) : L[noIn L x]? = some x := by
  unfold noIn
  induction L with
  | nil => simp at h
  | cons c L ih =>
    rw [List.idxOf_cons]
    by_cases e : c = x
    · simp [e]
    · have hx : x ∈ L := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm e
        · exact h
      have hb : (c == x) = false := by simp [e]
      rw [hb]
      simp only [cond_false, List.getElem?_cons_succ]
      exact ih hx

theorem noIn_lt (L : List Code) (x : Code) (h : x ∈ L) : noIn L x < L.length :=
  List.idxOf_lt_length_of_mem h

/-! what parOf reads off the plan -/

/-- the numbers of positions of the entries under the name `n`, in their order -/
def possUnder (n : String) (l : List Round) : List Nat :=
  ((l.map (·.entry)).filter (·.name == n)).map (·.poss)

theorem possUnder_append (n : String) (a b : List Round) :
    possUnder n (a ++ b) = possUnder n a ++ possUnder n b := by
  simp only [possUnder, List.map_append, List.filter_append]

theorem possUnder_rep (n : String) (k : Nat) (r : Round) (h : (r.entry.name == n) = false) :
    possUnder n (List.replicate k r) = [] := by
  simp only [possUnder, List.map_replicate, List.filter_replicate, h,
    Bool.false_eq_true, if_false, List.map_nil]

theorem later_poss (work : Nat) (rest : List Stage) :
    ∀ (tree W : Nat) (old : Stage), possUnder "CS" (laterRounds work tree W old rest) ++
        possUnder "BASE" (laterRounds work tree W old rest) =
      (old :: rest).map (·.t) := by
  induction rest with
  | nil => intro tree W old; rfl
  | cons new rest ih =>
    intro tree W old
    have h := ih (tree + 1) (wMid new) new
    simp only [laterRounds, possUnder_append,
      possUnder_rep "CS" old.k (rTwo "FOLD round") (by decide),
      possUnder_rep "BASE" old.k (rTwo "FOLD round") (by decide)]
    have c1 : possUnder "CS" [rEps "FOLD epsilon"] = [] := rfl
    have c2 : possUnder "BASE" [rEps "FOLD epsilon"] = [] := rfl
    have c3 : possUnder "CS" [rSeed new, rCs work old tree W] = [old.t] := rfl
    have c4 : possUnder "BASE" [rSeed new, rCs work old tree W] = [] := rfl
    rw [c1, c2, c3, c4]
    simp only [List.nil_append, List.append_nil, List.cons_append, List.map_cons] at h ⊢
    rw [h]

theorem head_poss (n : String) (K : Nat) (s : Stage) (h : n = "CS" ∨ n = "BASE") :
    possUnder n (headRounds K s) = [] := by
  rcases h with rfl | rfl
  · simp only [headRounds, possUnder_append, possUnder_rep "CS" K (rTwo "PSC round") (by decide)]; rfl
  · simp only [headRounds, possUnder_append, possUnder_rep "BASE" K (rTwo "PSC round") (by decide)]; rfl

theorem poss_back (P : Par) (nonceB : Nat) (h : P.stages ≠ []) :
    possOf (planOf P nonceB) = P.stages.map (·.t) := by
  obtain ⟨s, rest, e⟩ : ∃ s rest, P.stages = s :: rest := by
    cases hs : P.stages with
    | nil => exact absurd hs h
    | cons s rest => exact ⟨s, rest, rfl⟩
  show possUnder "CS" (roundsOf P) ++ possUnder "BASE" (roundsOf P) = _
  simp only [roundsOf, e, possUnder_append, head_poss "CS" P.K s (Or.inl rfl),
    head_poss "BASE" P.K s (Or.inr rfl), List.nil_append]
  exact later_poss P.work rest 0 (wFirst s) s

/-- the first entry under the name `n` -/
def firstUnder (n : String) (l : List Round) : Option Entry := (l.map (·.entry)).find? (·.name == n)

theorem firstUnder_append_none (n : String) (a b : List Round) (h : firstUnder n a = none) :
    firstUnder n (a ++ b) = firstUnder n b := by
  simp only [firstUnder, List.map_append, List.find?_append] at h ⊢
  rw [h]; rfl

theorem firstUnder_rep (n : String) (k : Nat) (r : Round) (h : (r.entry.name == n) = false) :
    firstUnder n (List.replicate k r) = none := by
  simp only [firstUnder, List.map_replicate, List.find?_replicate, h,
    Bool.false_eq_true, if_false, ite_self]

theorem later_base (work : Nat) (rest : List Stage) :
    ∀ (tree W : Nat) (old : Stage),
      ∃ e, firstUnder "BASE" (laterRounds work tree W old rest) = some e ∧ e.work = work := by
  induction rest with
  | nil => intro tree W old; exact ⟨(rBase work old tree).entry, rfl, rfl⟩
  | cons new rest ih =>
    intro tree W old
    obtain ⟨e, h1, h2⟩ := ih (tree + 1) (wMid new) new
    refine ⟨e, ?_, h2⟩
    simp only [laterRounds]
    rw [firstUnder_append_none _ _ _ ?_, h1]
    rw [firstUnder_append_none _ _ _ ?_]
    · rfl
    · rw [firstUnder_append_none _ _ _ rfl]
      exact firstUnder_rep "BASE" old.k (rTwo "FOLD round") (by decide)

theorem base_back (P : Par) (nonceB : Nat) (h : P.stages ≠ []) :
    ∃ e, (planOf P nonceB).entries.find? (·.name == "BASE") = some e ∧ e.work = P.work := by
  obtain ⟨s, rest, e⟩ : ∃ s rest, P.stages = s :: rest := by
    cases hs : P.stages with
    | nil => exact absurd hs h
    | cons s rest => exact ⟨s, rest, rfl⟩
  obtain ⟨x, h1, h2⟩ := later_base P.work rest 0 (wFirst s) s
  refine ⟨x, ?_, h2⟩
  show firstUnder "BASE" (roundsOf P) = _
  simp only [roundsOf, e]
  rw [firstUnder_append_none _ _ _ ?_, h1]
  simp only [headRounds]
  rw [firstUnder_append_none _ _ _ ?_]
  · rfl
  · rw [firstUnder_append_none _ _ _ rfl]
    exact firstUnder_rep "BASE" P.K (rTwo "PSC round") (by decide)

theorem zero_back (P : Par) (nonceB : Nat) (h : P.stages ≠ []) :
    (planOf P nonceB).entries.find? (·.name == "ZERO") = some (rZero P.K).entry := by
  obtain ⟨s, rest, e⟩ : ∃ s rest, P.stages = s :: rest := by
    cases hs : P.stages with
    | nil => exact absurd hs h
    | cons s rest => exact ⟨s, rest, rfl⟩
  show firstUnder "ZERO" (roundsOf P) = _
  simp only [roundsOf, e, headRounds]
  rfl

/-! the stages -/

theorem allSome_map {α : Type} (l : List α) : allSome (l.map some) = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, allSome, ih, Option.map_some]

theorem stages_of (cm cz : List Code) (l : List Stage) (h : ∀ s ∈ l, s.C ∈ cm ∧ s.Z ∈ cz) :
    ((l.map fun s => (noIn cm s.C, noIn cz s.Z, s.k, s.h)).zip (l.map (·.t))).map
        (stageOf (cm, cz)) = l.map some := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have hs := h s (by simp)
    simp only [List.map_cons, List.zip_cons_cons]
    rw [ih fun x hx => h x (by simp [hx])]
    have e : stageOf (cm, cz) ((noIn cm s.C, noIn cz s.Z, s.k, s.h), s.t) = some s := by
      simp only [stageOf, noIn_get cm s.C hs.1, noIn_get cz s.Z hs.2]
    rw [e]

theorem par_back : Spec.par_back := by
  intro P cfg nonceB hs
  simp only [Par.small, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    decide_eq_true_eq, List.all_eq_true, Stage.small, Code.small] at hs
  obtain ⟨⟨h0, h1⟩, h2⟩ := hs
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
    have := h2 s hs
    exact ⟨this.1.1.1.1.1, this.1.1.1.1.2, this.1.1.1.2⟩⟩
  have oz : okCodes cz := ⟨by omega, fun c hc => by
    rw [← hcz, mem_onceL] at hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hc
    have := h2 s hs
    exact ⟨this.1.1.2.1.1, this.1.1.2.1.2, this.1.1.2.2⟩⟩
  have a1 : ((theParams P cfg nonceB).valueOf nameCodes).bind (whole rdCodes) = some (cm, cz) := by
    have : (theParams P cfg nonceB).valueOf nameCodes = some (codesBytes cm cz) := by
      rw [← hcm, ← hcz]; rfl
    rw [this]; exact codes_back cm cz om oz
  have a2 : ((theParams P cfg nonceB).valueOf nameStages).bind (whole rdStages) =
      some (P.stages.map fun s => (noIn cm s.C, noIn cz s.Z, s.k, s.h)) := by
    have : (theParams P cfg nonceB).valueOf nameStages =
        some (stagesBytes (P.stages.map fun s => (noIn cm s.C, noIn cz s.Z, s.k, s.h))) := by
      rw [← hcm, ← hcz]; rfl
    rw [this]
    refine stages_back _ (by simpa using h1) fun x hx => ?_
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    have b1 := noIn_lt cm s.C (mm s hs).1
    have b2 := noIn_lt cz s.Z (mm s hs).2
    have := h2 s hs
    exact ⟨by show noIn cm s.C < _; omega, by show noIn cz s.Z < _; omega, this.1.2, this.2⟩
  have a3 : (theParams P cfg nonceB).plan.entries.find? (·.name == "ZERO") =
      some (rZero P.K).entry :=
    zero_back P nonceB h0
  obtain ⟨bs, a4, a5⟩ := base_back P nonceB h0
  have a4' : (theParams P cfg nonceB).plan.entries.find? (·.name == "BASE") = some bs := a4
  have a6 : possOf (theParams P cfg nonceB).plan = P.stages.map (·.t) := poss_back P nonceB h0
  unfold parOf
  rw [a1, a2, a3, a4']
  simp only [a6, List.length_map, beq_self_eq_true, if_true, stages_of cm cz P.stages mm,
    allSome_map, Option.map_some, a5]
  rfl

theorem params_of (P : Par) (cfg : ByteArray) (nonceB : Nat) :
    (specOf P cfg (itemsOf P) nonceB).params = (theParams P cfg nonceB).bytes := rfl

theorem read_back : Spec.read_back := by
  intro P cfg nonceB hs hf
  rw [params_of, params_back _ hf]
  exact par_back P cfg nonceB hs

theorem samePlan_self (A : Plan) : samePlan A A = true := by
  simp only [samePlan, beq_self_eq_true, Bool.and_self]

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
  simp only [decide_true, Bool.and_self, if_true]

end M1
end Fmt
