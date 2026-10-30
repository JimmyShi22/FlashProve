-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/PartsAll.lean: THE TWO FILLINGS OF A LOOKUP'S SUMMANDS
YIELD THE SAME LISTS AT EVERY STAGE OF THE ROW, AT ANY NUMBER OF PARTS OF KEYS. CONDITIONAL, on the
four premises below. The theorem in two forms, two definitions of premises, the lemmas on the two
stages that are new.

The two fillings: `fastJobs f row` (Honest/K3/JobsFast.lean), which folds tables of the program's
elements, and `Parts.specJobsPAt f row pads` (Honest/K3/Parts/Jobs.lean), which reads the summands
off the specification, each part's tree at data of its own. `stages_agreeP` says of them what
`stages_agree` (Honest/K3/FastLaw/All.lean) says at one part: at every stage of the row that is a
masked sumcheck the three functions give the same lists OF WORDS: the round polynomial behind fewer
challenges than the stage has variables; the polynomial in Y and the end values behind as many.

THE PREMISES, each a hypothesis of the theorem:
  SizedP f p        every part has at least 2 keys; from 2 to 2 ^ mu planes (SO SOME PLANES MAY BE
                    UNREAL); the shift's words below the prime (at a face without a shift the
                    points' shift is the program's 0)
  FactorFits f row pads p   as at one part (Honest/K3/FastLaw/Tie.lean); SPENT AT THE TIE'S FIRST
                    STEP ALONE: `stage_agreeP` asks it there and nowhere else
  PtsSizedP f p     each point has as many coordinates as its stage has variables, at every part
  the orders        the face's order at each level of each part's tree lists that level's variables,
                    each once

How. Honest/K3/FastLaw/PartsTurn.lean turns every stage but two into a stage at one part; there the
one-part theorems are spent. New here: a part's root and the product of the roots from a part on,
read (`root_read`, `rest_read`); the parts' step (`split_endsP`, `split_inYP`); the tie's first step
at the product of all roots (`tie0_endsP`, `tie0_inYP`).

Limits. WHETHER THE PREMISES HOLD AT THE KEY FILE'S TWO FACES IS NOT SHOWN HERE. Nothing at other
lengths of the lists of challenges. Nothing says that either filling is right.
Nothing on any property of the protocol.

-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.PartsTurn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E addE subE mulE zeroE oneE okE)
open OnBytes.Slice (readE readV readE_mul readE_add readE_sub readE_one readE_zero)
open OnBytes.HonestTrace.Look (sqMul addP)
open ProofFile.Honest.K3.Parts (specJobsPAt dataP restFrom splitJob tieTop split_ends)

/-! ## 1 The premises -/

/-- **The premise on numbers and points, at parts.** -/
structure SizedP (f : LFace) (p : Pts) : Prop where
  one : ∀ v ∈ f.parts, 1 ≤ v
  two : 2 ≤ f.planes
  fit : f.planes ≤ 2 ^ f.mu
  theta : okE p.theta = true

/-- **The premise on the points' sizes, at parts.** -/
structure PtsSizedP (f : LFace) (p : Pts) : Prop where
  key : ∀ y ∈ f.parts.zipIdx, ∀ m < y.1, (p.keyPt y.2 m).size = m
  tab : ∀ l ≤ f.d, (p.tabPt l).size = f.mu + l
  zero : p.zeroPt.size = f.mu + f.d

/-- A member of the numbered list of parts: the part's size stands at its number. -/
theorem zip_facts {l : List Nat} {y : Nat × Nat} (hy : y ∈ l.zipIdx) :
    y.2 < l.length ∧ l.getD y.2 0 = y.1 := by
  obtain ⟨a, i⟩ := y
  have h := List.mem_zipIdx_iff_getElem?.1 hy
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 h
  exact ⟨hi, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩

section
variable {f : LFace} {p : Pts}

theorem sized_one (H : SizedP f p) : Sized (oneF f) 1 p :=
  ⟨rfl, Nat.le_refl _, H.two, H.fit, H.theta⟩

theorem sized_turn (H : SizedP f p) {i : Nat} (hi : i < f.parts.length) :
    Sized (turnF f i) (f.parts.getD i 0) (turnP p i) :=
  ⟨rfl, H.one _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi), H.two, H.fit,
    H.theta⟩

end

/-! ## 2 Products -/

theorem foldl_mul_read : ∀ (l : List E) (a : E),
    readE (l.foldl mulE a) = readE a * (l.map readE).prod
  | [], a => by simp
  | x :: l, a => by
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [foldl_mul_read l, readE_mul]
    ring

theorem foldl_mul_ok (l : List E) : ∀ a : E, okE a = true → okE (l.foldl mulE a) = true := by
  induction l with
  | nil => exact fun _ h => h
  | cons x l ih =>
    intro a _
    rw [List.foldl_cons]
    exact ih (mulE a x) (ok_mul a x)

theorem restFrom_prod (z : Nat → KE) : ∀ k i,
    restFrom z k i = ((List.range k).map fun j => z (i + j)).prod
  | 0, _ => rfl
  | k + 1, i => by
    have e : (fun j => z (i + 1 + j)) = ((fun j => z (i + j)) ∘ Nat.succ) := by
      funext j
      show z (i + 1 + j) = z (i + (j + 1))
      congr 1
      omega
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, ← e,
      ← restFrom_prod z k (i + 1)]
    rfl

/-! ## 3 The roots -/

section
variable (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden) (p : Pts)

/-- **CONDITIONAL ON `SizedP f p`, at a part that there is: part i's root, read.** Member of the
premise: Honest/K3/FastLaw/PartsGuards.lean [not in this library]. -/
theorem root_read (H : SizedP f p) {i : Nat} (hi : i < f.parts.length) :
    readE ((srcAt f row w p).root i) = (dataP (numsOf f row pads) f.parts f.orders w p).Zi i := by
  have h := Z_read (turnF f i) row pads (turnW w i) (turnP p i) (sized_turn H hi)
  have e : (srcAt (turnF f i) row (turnW w i) (turnP p i)).rootsFrom (turnF f i).parts.length 0 =
      mulE oneE ((srcAt f row w p).root i) := rfl
  rw [e, readE_mul, readE_one, one_mul] at h
  exact h

/-- **CONDITIONAL ON `SizedP f p`: the product of the roots from part i on, read.** -/
theorem rest_read (H : SizedP f p) (i : Nat) :
    readE ((srcAt f row w p).rootsFrom f.parts.length i) =
      (dataP (numsOf f row pads) f.parts f.orders w p).rest i := by
  show readE (((List.range (f.parts.length - i)).map fun k =>
      (srcAt f row w p).root (i + k)).foldl mulE oneE) =
    restFrom (dataP (numsOf f row pads) f.parts f.orders w p).Zi (f.parts.length - i) i
  rw [foldl_mul_read, readE_one, one_mul, restFrom_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.1 hk
  exact root_read f row pads w p H (by omega)

theorem rest_ok (n i : Nat) : okE ((srcAt f row w p).rootsFrom n i) = true :=
  foldl_mul_ok _ _ ok_one

/-! ## 4 The parts' step -/

/-- The polynomial in Y of the specification's job at a parts' step, written out. -/
theorem splitJob_inY {P : Type} (A : Parts.DataP P) (i : Nat) (xs mk : List KE) :
    (splitJob A i).inY xs mk =
      [0 + A.Zi i * A.rest (i + 1), A.Zi i * mk.getD 1 0 + mk.getD 0 0 * A.rest (i + 1),
        mk.getD 0 0 * mk.getD 1 0] := by
  show [0 + OnBytes.HonestTrace.Look.ext 0 _ _ * OnBytes.HonestTrace.Look.ext 0 _ _,
    OnBytes.HonestTrace.Look.ext 0 _ _ * _ + _ * OnBytes.HonestTrace.Look.ext 0 _ _, _] = _
  simp [OnBytes.HonestTrace.Look.ext, TwV.eqN, TwV.byVar]

/-- **CONDITIONAL ON `SizedP f p`, at a part that there is: the parts' step: the end values.**
Member: Honest/K3/FastLaw/PartsGuards.lean [not in this library], by evaluation. -/
theorem split_endsP (H : SizedP f p) {i : Nat} (hi : i < f.parts.length) (rs : List E) :
    ((fastJobs f row).job (.split i)).ends w p rs =
      ((specJobsPAt f row pads).job (.split i)).ends w p rs := by
  show [(srcAt f row w p).root i, (srcAt f row w p).rootsFrom f.parts.length (i + 1)] =
    downs ((splitJob (dataP (numsOf f row pads) f.parts f.orders w p) i).ends (ups rs))
  refine eq_downs (fun x hx => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact keyLvl_ok f row w p i 0 0
    · exact rest_ok f row w p _ _
  · rw [split_ends]
    simp only [List.map_cons, List.map_nil]
    rw [root_read f row pads w p H hi, rest_read f row pads w p H]

/-- **CONDITIONAL ON the same: the parts' step: the polynomial in Y.** Member: as above. -/
theorem split_inYP (H : SizedP f p) {i : Nat} (hi : i < f.parts.length) (rs mk : List E) :
    ((fastJobs f row).job (.split i)).inY w p rs mk =
      ((specJobsPAt f row pads).job (.split i)).inY w p rs mk := by
  show Fast.mulY zeroE ((srcAt f row w p).root i)
      ((srcAt f row w p).rootsFrom f.parts.length (i + 1)) (mk.getD 0 zeroE) (mk.getD 1 zeroE) =
    downs ((splitJob (dataP (numsOf f row pads) f.parts f.orders w p) i).inY (ups rs) (ups mk))
  refine eq_downs (mulY_ok _ _ _ _ _) ?_
  rw [mulY_read, splitJob_inY, root_read f row pads w p H hi, rest_read f row pads w p H,
    readE_zero, getD_ups, getD_ups]

/-! ## 5 The tie's first step -/

theorem P1_read (H : SizedP f p) :
    readE (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes 1) =
      (dataAt (numsOf f row pads) w p).Pc 1 :=
  P_read (oneF f) row pads w p (sized_one H) (s := 1) H.two

theorem G0_read (H : SizedP f p) :
    readV ((srcAt f row w p).tabLvl 0) 0 = (dataAt (numsOf f row pads) w p).G 0 :=
  G_read (oneF f) row pads w p (sized_one H) (j := 0) (by show 0 < 2 ^ f.mu; positivity)

theorem aP_read (H : SizedP f p) (A : FactorFits f row pads p) :
    readE (f.factor p.theta p.alpha) = (dataAt (numsOf f row pads) w p).a :=
  a_read (oneF f) row pads w p (sized_one H) A

/-- **CONDITIONAL ON `SizedP f p`: the tie's first step: the end values.** Member:
Honest/K3/FastLaw/PartsGuards.lean [not in this library], by evaluation. -/
theorem tie0_endsP (H : SizedP f p) (rs : List E) :
    ((fastJobs f row).job (.tie 0)).ends w p rs =
      ((specJobsPAt f row pads).job (.tie 0)).ends w p rs := by
  refine eq_downs (tie_ends_ok f row w p 0 rs) ?_
  show [(srcAt f row w p).rootsFrom f.parts.length 0,
      Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes 1,
      ((srcAt f row w p).tabLvl 0).getD 0 zeroE].map readE =
    [(dataP (numsOf f row pads) f.parts f.orders w p).rest 0,
      (dataAt (numsOf f row pads) w p).Pc 1, (dataAt (numsOf f row pads) w p).G 0]
  simp only [List.map_cons, List.map_nil]
  rw [rest_read f row pads w p H, P1_read f row pads w p H, ← G0_read f row pads w p H]
  rfl

/-- **CONDITIONAL ON `SizedP f p` and `FactorFits f row pads p`: the tie's first step: the
polynomial in Y.** Member: as above. -/
theorem tie0_inYP (H : SizedP f p) (A : FactorFits f row pads p) (rs mk : List E) :
    ((fastJobs f row).job (.tie 0)).inY w p rs mk =
      ((specJobsPAt f row pads).job (.tie 0)).inY w p rs mk := by
  refine eq_downs (tie_inY_ok f row w p 0 rs mk) ?_
  show (addL [(srcAt f row w p).rootsFrom f.parts.length 0, mk.getD 0 zeroE]
      ((Fast.sqMulY (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes 1)
        (((srcAt f row w p).tabLvl 0).getD 0 zeroE) (mk.getD 1 zeroE) (mk.getD 2 zeroE)).map
        fun x => subE zeroE (mulE (f.factor p.theta p.alpha) x))).map readE =
    addP [(dataP (numsOf f row pads) f.parts f.orders w p).rest 0, (ups mk).getD 0 0]
      ((sqMul ((dataAt (numsOf f row pads) w p).Pc 1) ((dataAt (numsOf f row pads) w p).G 0)
        ((ups mk).getD 1 0) ((ups mk).getD 2 0)).map (-(dataAt (numsOf f row pads) w p).a * ·))
  rw [← rest_read f row pads w p H, ← P1_read f row pads w p H, ← G0_read f row pads w p H,
    ← aP_read f row pads w p H A, getD_ups, getD_ups, getD_ups]
  unfold Fast.sqMulY sqMul
  simp only [List.map_cons, List.map_nil, addL, addP, readE_add, readE_sub, readE_mul,
    readE_zero, OnBytes.Slice.readV]
  congr 1
  · ring
  congr 1
  · ring
  congr 1
  · ring
  congr 1
  ring

/-- **CONDITIONAL ON `SizedP f p`, at a later step of the tie: the polynomial in Y.** The public
factor is not read there. Member: Honest/K3/FastLaw/PartsGuards.lean [not in this library], by
evaluation. -/
theorem tieS_inYP (H : SizedP f p) {j : Nat} (hj : j + 1 + 2 ≤ f.planes) (rs mk : List E) :
    ((fastJobs f row).job (.tie (j + 1))).inY w p rs mk =
      ((specJobsPAt f row pads).job (.tie (j + 1))).inY w p rs mk := by
  refine eq_downs (tie_inY_ok f row w p (j + 1) rs mk) ?_
  show (Fast.sqMulY (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes (j + 2))
      (((srcAt f row w p).tabLvl 0).getD (j + 1) zeroE) (mk.getD 0 zeroE)
      (mk.getD 1 zeroE)).map readE =
    sqMul ((dataAt (numsOf f row pads) w p).Pc (j + 1 + 1))
      ((dataAt (numsOf f row pads) w p).G (j + 1)) ((ups mk).getD 0 0) ((ups mk).getD 1 0)
  have hP : readE (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes (j + 2)) =
      (dataAt (numsOf f row pads) w p).Pc (j + 2) :=
    P_read (oneF f) row pads w p (sized_one H) (s := j + 2) hj
  have hG : readV ((srcAt f row w p).tabLvl 0) (j + 1) =
      (dataAt (numsOf f row pads) w p).G (j + 1) :=
    G_read (oneF f) row pads w p (sized_one H) (j := j + 1)
      (lt_of_lt_of_le (by omega) H.fit)
  rw [sqMulY_read, hP, getD_ups, getD_ups]
  show sqMul _ (readV ((srcAt f row w p).tabLvl 0) (j + 1)) _ _ = _
  rw [hG]

end

/-! ## 6 The theorem -/

/-- **CONDITIONAL ON `SizedP f p`, `PtsSizedP f p`, every part's key orders being permutations, and,
AT THE TIE'S FIRST STEP ALONE, `FactorFits f row pads p`: at a stage of the row that is a masked
sumcheck, at any number of parts, the two fillings yield the same lists.** Members of the premises,
met together, and the equations by evaluation: Honest/K3/FastLaw/PartsGuards.lean
[not in this library]. -/
theorem stage_agreeP (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden)
    (p : Pts) (H : SizedP f p) (Z : PtsSizedP f p)
    (hO : ∀ y ∈ f.parts.zipIdx, ∀ m < y.1, (f.orders y.2 m).Perm (List.range m)) :
    ∀ s ∈ stages f, (s = .tie 0 → FactorFits f row pads p) → ∀ k, s.call f = some k →
      (∀ rs : List E, rs.length < k.vs.length →
        ((fastJobs f row).job s).round w p rs = ((specJobsPAt f row pads).job s).round w p rs) ∧
      (∀ rs mk : List E, rs.length = k.vs.length →
        ((fastJobs f row).job s).inY w p rs mk =
            ((specJobsPAt f row pads).job s).inY w p rs mk ∧
          ((fastJobs f row).job s).ends w p rs =
            ((specJobsPAt f row pads).job s).ends w p rs) := by
  intro s hs A k hk
  have H1 := sized_one H
  cases s with
  | shift => exact absurd hk (by simp [Stage.call])
  | alpha => exact absurd hk (by simp [Stage.call])
  | join => exact absurd hk (by simp [Stage.call])
  | keyLine i m => exact absurd hk (by simp [Stage.call])
  | tabLine l => exact absurd hk (by simp [Stage.call])
  | zero => exact absurd hk (by simp [Stage.call])
  | tie j =>
    cases j with
    | zero =>
      have hk' : k.vs.length = 0 := by
        have e := (Option.some.inj hk).symm
        rw [e]
        rfl
      rw [hk']
      exact ⟨fun rs h => absurd h (Nat.not_lt_zero _), fun rs mk _ =>
        ⟨tie0_inYP f row pads w p H (A rfl) rs mk, tie0_endsP f row pads w p H rs⟩⟩
    | succ j =>
      have hj : j + 1 + 2 ≤ (oneF f).planes := by
        have := tie_mem hs
        show j + 1 + 2 ≤ f.planes
        omega
      refine ⟨fun rs _ => ?_, fun rs mk _ => ⟨tieS_inYP f row pads w p H hj rs mk, ?_⟩⟩
      · rw [fast_free f row (.tie (j + 1)) trivial, spec_free f row pads (.tie (j + 1)) trivial]
        exact tie_round (oneF f) row pads w p (j + 1) rs
      · rw [fast_free f row (.tie (j + 1)) trivial, spec_free f row pads (.tie (j + 1)) trivial]
        exact tie_ends (oneF f) row pads w p H1 hj rs
  | split i =>
    have hi : i < f.parts.length := by
      have := split_mem hs
      omega
    have hk' : k.vs.length = 0 := by
      have e := (Option.some.inj hk).symm
      rw [e]
      rfl
    rw [hk']
    exact ⟨fun rs h => absurd h (Nat.not_lt_zero _), fun rs mk _ =>
      ⟨split_inYP f row pads w p H hi rs mk, split_endsP f row pads w p H hi rs⟩⟩
  | key i m =>
    obtain ⟨y, hy, hi, hm⟩ := mem_key hs
    subst hi
    obtain ⟨h1, h2⟩ := zip_facts hy
    have hm' : m < f.parts.getD y.2 0 := by rw [h2]; exact hm
    have hk' : k.vs.length = m := by
      have e : k = levelCall m := (Option.some.inj hk).symm
      rw [e]
      simp [levelCall, VerifiableInference.Desc.First.ProdV.levelVars]
    rw [hk']
    have HT := sized_turn H h1
    refine ⟨fun rs hl => ?_, fun rs mk hx => ⟨?_, ?_⟩⟩
    · rw [fast_key_round, spec_key_round]
      exact key_round (turnF f y.2) row pads (turnW w y.2) (turnP p y.2) HT hm' rs (hO y hy m hm)
        (Z.key y hy m hm) hl
    · rw [fast_key_inY, spec_key_inY]
      exact key_inY (turnF f y.2) row pads (turnW w y.2) (turnP p y.2) HT hm' (hO y hy m hm) rs mk
        hx
    · rw [fast_key_ends, spec_key_ends]
      exact key_ends (turnF f y.2) row pads (turnW w y.2) (turnP p y.2) HT hm' (hO y hy m hm) rs hx
  | tab l =>
    have hl : l < f.d := mem_tab hs
    have hk' : k.vs.length = f.mu + l := by
      have e : k = levelCall (f.mu + l) := (Option.some.inj hk).symm
      rw [e]
      simp [levelCall, VerifiableInference.Desc.First.ProdV.levelVars]
    rw [hk', fast_free f row (.tab l) trivial, spec_free f row pads (.tab l) trivial]
    exact ⟨fun rs h => tab_round (oneF f) row pads w p H1 hl rs (Z.tab l (Nat.le_of_lt hl)) h,
      fun rs mk hx => ⟨tab_inY (oneF f) row pads w p H1 hl rs mk hx,
        tab_ends (oneF f) row pads w p H1 hl rs hx⟩⟩
  | leaves =>
    have hk' : k.vs.length = f.mu + f.d := by
      have e := (Option.some.inj hk).symm
      rw [e]
      simp [VerifiableInference.Desc.K3.leafVars]
    rw [hk', fast_free f row .leaves trivial, spec_free f row pads .leaves trivial]
    exact ⟨fun rs h => leaves_round (oneF f) row pads w p H1 rs (Z.tab f.d (Nat.le_refl _)) h,
      fun rs mk _ => ⟨leaves_inY (oneF f) row pads w p rs mk, leaves_ends (oneF f) row pads w p rs⟩⟩
  | bits =>
    have hk' : k.vs.length = f.mu + f.d := by
      have e := (Option.some.inj hk).symm
      rw [e]
      simp [VerifiableInference.Desc.K3.bitsCall]
    rw [hk', fast_free f row .bits trivial, spec_free f row pads .bits trivial]
    exact ⟨fun rs h => bits_round (oneF f) row pads w p H1 rs Z.zero h,
      fun rs mk hx => ⟨bits_inY (oneF f) row pads w p H1 rs mk hx,
        bits_ends (oneF f) row pads w p H1 rs hx⟩⟩

/-- **CONDITIONAL ON `SizedP f p`, `FactorFits f row pads p`, `PtsSizedP f p` and every part's key
orders being permutations: at every stage of the row that is a masked sumcheck, at any number of
parts, the two fillings yield the same lists.** Members of the premises, met together, and the
equations by evaluation: Honest/K3/FastLaw/PartsGuards.lean [not in this library]. -/
theorem stages_agreeP (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden)
    (p : Pts) (H : SizedP f p) (A : FactorFits f row pads p) (Z : PtsSizedP f p)
    (hO : ∀ y ∈ f.parts.zipIdx, ∀ m < y.1, (f.orders y.2 m).Perm (List.range m)) :
    ∀ s ∈ stages f, ∀ k, s.call f = some k →
      (∀ rs : List E, rs.length < k.vs.length →
        ((fastJobs f row).job s).round w p rs = ((specJobsPAt f row pads).job s).round w p rs) ∧
      (∀ rs mk : List E, rs.length = k.vs.length →
        ((fastJobs f row).job s).inY w p rs mk =
            ((specJobsPAt f row pads).job s).inY w p rs mk ∧
          ((fastJobs f row).job s).ends w p rs =
            ((specJobsPAt f row pads).job s).ends w p rs) :=
  fun s hs k hk => stage_agreeP f row pads w p H Z hO s hs (fun _ => A) k hk

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.zip_facts
#print axioms ProofFile.Honest.K3.FastLaw.sized_one
#print axioms ProofFile.Honest.K3.FastLaw.sized_turn
#print axioms ProofFile.Honest.K3.FastLaw.foldl_mul_read
#print axioms ProofFile.Honest.K3.FastLaw.foldl_mul_ok
#print axioms ProofFile.Honest.K3.FastLaw.restFrom_prod
#print axioms ProofFile.Honest.K3.FastLaw.root_read
#print axioms ProofFile.Honest.K3.FastLaw.rest_read
#print axioms ProofFile.Honest.K3.FastLaw.rest_ok
#print axioms ProofFile.Honest.K3.FastLaw.splitJob_inY
#print axioms ProofFile.Honest.K3.FastLaw.split_endsP
#print axioms ProofFile.Honest.K3.FastLaw.split_inYP
#print axioms ProofFile.Honest.K3.FastLaw.P1_read
#print axioms ProofFile.Honest.K3.FastLaw.G0_read
#print axioms ProofFile.Honest.K3.FastLaw.aP_read
#print axioms ProofFile.Honest.K3.FastLaw.tie0_endsP
#print axioms ProofFile.Honest.K3.FastLaw.tie0_inYP
#print axioms ProofFile.Honest.K3.FastLaw.tieS_inYP
#print axioms ProofFile.Honest.K3.FastLaw.stage_agreeP
#print axioms ProofFile.Honest.K3.FastLaw.stages_agreeP
