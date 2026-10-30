-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Proof.lean: the honest side of the kind "lookup" (K3): THE
PROOF of `LawfulSpecP` (Honest/K3/Parts/Lawful.lean): CONDITIONAL ON `Fit R`, `NumberedP R` AND
`SpecAtP R N w`, the specification's summands AT SEVERAL PARTS OF KEYS meet `Lawful`, the premise of
every statement on values of Honest/K3/Law/Statements.lean. Theorems with proofs; no definition.

  `top_eq`, `sized_top`, `endTerm_top`, `bits_sum_of`, `planes_sum`   what the one-part files take
     from the relation at one key vector, from the relation at parts
  `len_noVar`, `key_claimed`, `tab_claimed`   lengths; what is claimed in front of a level
  `sums_tie0`, `sums_tie`, `sums_split`, `sums_key`, `sums_tab`, `sums_bits`, `sums_leaves`
                              stage by stage
  `bits_end`, `count_ok`, `key_end`   the three clauses that sum nothing
  `lawfulSpecP`   the statement

The texts on the table's side, the leaves and the bits follow Honest/K3/Law/SpecProof.lean
line for line.

Limits. THE PREMISES ARE NOT SHOWN OF ANY COURSE HERE (Honest/K3/Parts/Member.lean has one, by
evaluation; `NumberedP R` follows from `Fit R`: Honest/K3/Parts/Numbered.lean).
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Course
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE oneE addE subE mulE)
open OnBytes.Model (orderDefault ofNat)
open OnBytes.Slice (readE readE_zero readE_sub readE_mul)
open OnBytes.HonestTrace.Look (Job Data pj ext tieJob keyJob tabJob leavesJob bitsJob)
open VerifiableInference.Desc.First.ProdV (levelVars levelEnds)
open VerifiableInference.Desc.K3 (leafVars bitsCall noVar eqPairs)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Spec (CarriedAt T_read shapeAt_eq levelCall_len sums_stage_ends
  sums_stage_open
  varsFit_nil varsFit_tie claimed_tie0 claimed_tie1 claimed_tie2 endTerm_tie endTerm_level
    endTerm_bits
  size_keyPt size_tabPt size_zeroPt withPoints_tab withPoints_leaves withPoints_bits mem_leaves
    mem_bits
  tab_lt byBit_toArray leaves_fin planes_eq byVar_down key_top planesOf cornerW_count sum_split
    up_getD)

variable {P : Type} {N : KE → TwV.Nums P KE} {w : Hidden} {R : Course Ask}

-- `Sums` is never unfolded below. At a sumcheck without a variable its list of variables is a
-- literal, so that Lean, left to itself, goes on to unfold the run's list of challenges: dear, and
-- to no end.
attribute [local irreducible] Sums

/-! ## What comes out of the relation at parts -/

/-- CONDITIONAL ON the relation at parts: the product of all parts' roots is the public factor times
the chain's first step. -/
theorem top_eq (A : DataP P) (hM : A.Mid) : A.rest 0 = A.D.a * (A.D.Pc 1 ^ 2 * A.D.G 0) := by
  rw [← OnBytes.HonestTrace.Look.Pc_step A.D (Nat.zero_le _)]
  have h := hM.2.2
  unfold Data.Pc
  rw [Alg.Lookup.chainFrom_eq_prod]
  simpa using h

/-- The tie's first step over letters: no variable; four coefficients in Y. -/
theorem sized_top (Z a P1 G0 : KE) : JobSized (tieTop Z a P1 G0) := by
  refine ⟨rfl, fun rs h => absurd h (Nat.not_lt_zero _), fun dY hY xs m => ?_⟩
  have e : dY = 3 := (Option.some.inj hY).symm
  subst e
  simp [tieTop, OnBytes.HonestTrace.Look.sqMul, OnBytes.HonestTrace.Look.addP]

/-- The verifier's end term at the tie's first step, read, is the job's summand. -/
theorem endTerm_top (Z aK P1 G0 : KE) (a : E) (ha : up a = aK) (v : List E) :
    rd (endTerm a (.tie 0) v) = (tieTop Z aK P1 G0).S0 (ups v) := by
  show readE (subE (v.getD 0 zeroE)
    (mulE a (mulE (mulE (v.getD 1 zeroE) (v.getD 1 zeroE)) (v.getD 2 zeroE)))) =
    (ups v).getD 0 0 - aK * ((ups v).getD 1 0 ^ 2 * (ups v).getD 2 0)
  rw [readE_sub, readE_mul, readE_mul, readE_mul, ← ha, ← up_getD, ← up_getD, ← up_getD]
  ring

/-- CONDITIONAL ON bits that are bits: the true sum of the bits' job is 0. -/
theorem bits_sum_of (D : Data P KE) (hB : Cb.Lkp.Bits D.N.d D.N.w D.bits) (z : List KE) :
    (bitsJob D z).sum = 0 := by
  show ∑ X ∈ Finset.range (2 ^ (D.N.w + D.N.d)),
    TwV.eqN z X * (0 + D.bitAt X * (D.bitAt X - 1)) = 0
  refine Finset.sum_eq_zero fun X hX => ?_
  have hu : X / 2 ^ D.N.w < 2 ^ D.N.d := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add]
    exact Finset.mem_range.1 hX
  have hb' : D.bitAt X * (D.bitAt X - 1) = 0 :=
    hB _ hu (X % 2 ^ D.N.w) (Nat.mod_lt _ (by positivity))
  rw [hb']
  ring

/-- At the pairs of the count the planes come to the sum of the counts, where the bits are 0 at
planes that do not count. -/
theorem planes_sum (f : LFace) (D : Data P KE) (hw : D.N.w = f.mu) (hroom : D.N.n + 2 ≤ 2 ^ D.N.w)
    (hz : ∀ u j, D.N.n + 2 ≤ j → D.bits u j = 0) :
    planesOf D (countPairs f) = ∑ u ∈ Finset.range (2 ^ D.N.d),
      ∑ j ∈ Finset.range (D.N.n + 2), (2 : KE) ^ j * D.bits u j := by
  unfold planesOf
  rw [Finset.sum_congr rfl fun X _ => show Spec.cornerW (countPairs f) X * D.bitAt X =
    (fun u j => (2 : KE) ^ j * D.bits u j) (X / 2 ^ D.N.w) (X % 2 ^ D.N.w) by
      rw [cornerW_count, ← hw]; rfl,
    Nat.add_comm, pow_add,
    sum_split (2 ^ D.N.w) (by positivity) (fun u j => (2 : KE) ^ j * D.bits u j) (2 ^ D.N.d)]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine (Finset.sum_subset (Finset.range_subset_range.2 hroom) fun j _ hj => ?_).symm
  rw [hz u j (by simpa using hj), mul_zero]

/-- CONDITIONAL ON `NumberedP R`: a sumcheck without a variable has one challenge: Y's. -/
theorem len_noVar (hW : NumberedP R) (s : Stage) (dY n : Nat) (hs : s ∈ stages R.f)
    (hc : s.call R.f = some (noVar dY n)) : (R.r s).length = (noVar dY n).vs.length + 1 := by
  rw [hW.len _ hs, shapeAt_eq R _ _ hc]
  rfl

/-! ## Stage by stage -/

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the tie's first step sums as `Lawful` asks. -/
theorem sums_tie0 (hW : NumberedP R) (hS : SpecAtP R N w) :
    Sums R (.tie 0) (rd (R.claimed (.tie 0))) (rd (endTerm R.factor (.tie 0) (R.shown (.tie 0)))) :=
      by
  have hs := mem_tie0 hS
  have hc : (Stage.tie 0).call R.f = some (noVar 3 3) := rfl
  have hm : (R.masks (.tie 0)).length = 3 := hW.masks _ hs
  have key := sums_stage_ends R (.tie 0) (noVar 3 3) ⟨3, 3⟩ _ hc rfl (carried_tie0 hW hS hs)
    (tieTop_lawful _ _ _ _ (top_eq _ hS.mid)) (sized_top _ _ _ _) rfl
    (show VarsFit [] _ from varsFit_nil _ rfl) (fun _ => rfl) (len_noVar hW _ 3 3 hs hc) hm
  have e1 : rd (R.claimed (.tie 0)) = 0 := by
    rw [claimed_tie0]
    exact readE_zero
  rw [e1, endTerm_top ((dataP N R.f.parts R.f.orders w R.pts).rest 0) _ ((dataAt N w R.pts).Pc 1)
    ((dataAt N w R.pts).G 0) R.factor hS.factor]
  exact key

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: a later step of the tie. -/
theorem sums_tie (hW : NumberedP R) (hS : SpecAtP R N w) (j : Nat)
    (hs : Stage.tie (j + 1) ∈ stages R.f) :
    Sums R (.tie (j + 1)) (rd (R.claimed (.tie (j + 1))))
      (rd (endTerm R.factor (.tie (j + 1)) (R.shown (.tie (j + 1))))) := by
  have hj := tie_lt hs
  have hpl := hS.nums.planes
  have hn0 : j + 1 ≤ (dataAt N w R.pts).N.n := by
    show j + 1 ≤ (N (up R.pts.theta)).n
    omega
  have hc : (Stage.tie (j + 1)).call R.f = some (noVar 3 2) := rfl
  have hm : (R.masks (.tie (j + 1))).length = 2 := hW.masks _ hs
  have hn : ∀ xs, ((tieJob (dataAt N w R.pts) (j + 1)).ends xs).length = 2 := fun xs => by
    rw [OnBytes.HonestTrace.Look.tie_ends_succ]
    rfl
  have key := sums_stage_ends R (.tie (j + 1)) (noVar 3 2) ⟨3, 2⟩ (tieJob (dataAt N w R.pts)
    (j + 1))
    hc rfl (carried_tie hW hS j hs) (tie_lawful_succ _ j hn0) (sized_tie _ _) rfl
    (varsFit_tie _ _ 3 2 _) hn (len_noVar hW _ 3 2 hs hc) hm
  have e1 : rd (R.claimed (.tie (j + 1))) = (tieJob (dataAt N w R.pts) (j + 1)).sum := by
    rw [OnBytes.HonestTrace.Look.tie_sum_succ]
    cases j with
    | zero =>
      rw [claimed_tie1, tie0_ends hW hS 1]
      rfl
    | succ i =>
      rw [claimed_tie2, T_read R (.tie (i + 1)) (noVar 3 2) _ rfl
        (carried_tie hW hS i (mem_tie (by omega))),
        OnBytes.HonestTrace.Look.tie_ends_succ]
      rfl
  rw [e1, endTerm_tie (dataAt N w R.pts) R.factor j]
  exact key

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: A PARTS' STEP. -/
theorem sums_split (hW : NumberedP R) (hS : SpecAtP R N w) (i : Nat)
    (hs : Stage.split i ∈ stages R.f) :
    Sums R (.split i) (rd (R.claimed (.split i)))
      (rd (endTerm R.factor (.split i) (R.shown (.split i)))) := by
  obtain ⟨h1, h2⟩ := split_same hW i hs
  have hi := split_lt hs
  have hc : (Stage.split i).call R.f = some (noVar 2 2) := rfl
  have hm : (R.masks (.split i)).length = 2 := hW.masks _ hs
  have key := sums_stage_ends R (.split i) (noVar 2 2) ⟨2, 2⟩
    (splitJob (dataP N R.f.parts R.f.orders w R.pts) i) hc rfl (carried_split hS i hs h1 h2)
    (split_lawful _ i) (sized_pj 0 0 _ _ [] [] rfl) rfl (show VarsFit [] _ from varsFit_nil _ rfl)
    (fun _ => rfl) (len_noVar hW _ 2 2 hs hc) hm
  rw [split_claimed hW hS i hs,
    ← split_sum (dataP N R.f.parts R.f.orders w R.pts) (i := i) (by
      show i < R.f.parts.length
      omega),
    show rd (endTerm R.factor (.split i) (R.shown (.split i))) = _ from
      endTerm_level 0 (fun _ => (dataP N R.f.parts R.f.orders w R.pts).Zi i)
        (fun _ => (dataP N R.f.parts R.f.orders w R.pts).rest (i + 1)) [] [] _]
  exact key

/-- CONDITIONAL ON `NumberedP R`, `SpecAtP R N w` AND the verifier's tests on the face: what is
claimed in front of part i's level with m variables; at m := the part's number of levels:
behind its tree. -/
theorem key_claimed (hW : NumberedP R) (hS : SpecAtP R N w) (hok : R.f.ok = true) {y : Nat × Nat}
    (hy : y ∈ R.f.parts.zipIdx) (m : Nat) (hm : m ≤ y.1) :
    rd (R.claimed (.key y.2 m)) =
      ext m (((dataP N R.f.parts R.f.orders w R.pts).part y.2).kLvl m)
        (byBit (R.pts.keyPt y.2 m)) := by
  cases m with
  | zero => exact key_zero hW hS y.2 (getD_of_mem hy).1
  | succ m => exact key_succ hW hS hok hy m hm

/-- CONDITIONAL ON `NumberedP R`, `SpecAtP R N w` AND the verifier's tests on the face: a level of
part i's tree. -/
theorem sums_key (hW : NumberedP R) (hS : SpecAtP R N w) (hok : R.f.ok = true) {y : Nat × Nat}
    (hy : y ∈ R.f.parts.zipIdx) (m : Nat) (hm : m < y.1) :
    Sums R (.key y.2 m) (rd (R.claimed (.key y.2 m)))
      (rd (endTerm R.factor (.key y.2 m) (R.shown (.key y.2 m)))) := by
  have hs : Stage.key y.2 m ∈ stages R.f := mem_keyOf hy hm
  obtain ⟨_, _, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  have hp : (R.f.orders y.2 m).Perm (List.range m) := perm_of_okP hok hy hm
  have hz : (R.pts.keyPt y.2 m).size = m := size_keyPt _ _ _ y.2 m
  have hv : (((dataP N R.f.parts R.f.orders w R.pts).part y.2)).v = y.1 :=
    part_v (dataP N R.f.parts R.f.orders w R.pts) hy ((facts_of_ok hok).1 y.1 (by
      have := (getD_of_mem hy)
      rw [← this.2, List.getD_eq_getElem _ _ this.1]
      exact List.getElem_mem _))
  have hvf : VarsFit (withPoints (levelCall m).vs (pointsAt R.f (.key y.2 m)
    (R.ptsAt (.key y.2 m))))
      (keyJob ((dataP N R.f.parts R.f.orders w R.pts).part y.2) m (byBit (R.pts.keyPt y.2 m))) := by
    rw [withPoints_key R.f y.2 m _ (by rw [hp.length_eq, List.length_range]), h3]
    exact varsFit_level m 0 _ _ _ _ hz hp
  have key := sums_stage_ends R (.key y.2 m) (levelCall m) levelEnds
    (keyJob ((dataP N R.f.parts R.f.orders w R.pts).part y.2) m (byBit (R.pts.keyPt y.2 m))) rfl rfl
    (carried_key hW hS y.2 m hs)
    (OnBytes.HonestTrace.Look.pj_lawful m 0 _ _ _ _ hp (by rw [byBit_length, hz]))
    (sized_pj m 0 _ _ (R.f.orders y.2 m) _ (by rw [hp.length_eq, List.length_range])) rfl hvf
    (fun _ => rfl) (by rw [len_level hW _ m hs rfl, levelCall_len]) (hW.masks _ hs)
  rw [key_claimed hW hS hok hy m (Nat.le_of_lt hm),
    ← OnBytes.HonestTrace.Look.keyJob_sum _ (by rw [hv]; exact hm),
    show rd (endTerm R.factor (.key y.2 m) (R.shown (.key y.2 m))) = _ from
      endTerm_level m _ _ (R.f.orders y.2 m) (byBit (R.pts.keyPt y.2 m)) _]
  exact key

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: what is claimed in front of the table side's
level number l; at l := d: in front of the leaves. -/
theorem tab_claimed (hW : NumberedP R) (hS : SpecAtP R N w) (l : Nat) (hl : l ≤ R.f.d) :
    rd (R.tabV l) = ext ((dataAt N w R.pts).N.w + l) ((dataAt N w R.pts).tLvl l)
      (byBit (R.pts.tabPt l)) := by
  cases l with
  | zero => exact tab_zero hW hS
  | succ l => exact tab_succ hW hS l hl

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: a level of the table side. -/
theorem sums_tab (hW : NumberedP R) (hS : SpecAtP R N w) (l : Nat) (hl : l < R.f.d) :
    Sums R (.tab l) (rd (R.claimed (.tab l)))
      (rd (endTerm R.factor (.tab l) (R.shown (.tab l)))) := by
  have hs : Stage.tab l ∈ stages R.f := mem_tabOf hl
  obtain ⟨_, _, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hd : (dataAt N w R.pts).N.d = R.f.d := hS.nums.d
  have hT : (dataAt N w R.pts).N.oT l = orderDefault (R.f.mu + l) := hS.nums.oT l
  have hp : ((dataAt N w R.pts).N.oT l).Perm (List.range ((dataAt N w R.pts).N.w + l)) := by
    rw [hT, hw]
    exact perm_orderDefault _
  have hz : (R.pts.tabPt l).size = (dataAt N w R.pts).N.w + l := by
    rw [hw]
    exact size_tabPt _ _ _ l
  have hv : VarsFit
      (withPoints (levelCall (R.f.mu + l)).vs (pointsAt R.f (.tab l) (R.ptsAt (.tab l))))
      (tabJob (dataAt N w R.pts) l (byBit (R.pts.tabPt l))) := by
    rw [withPoints_tab, h3, ← hT, ← hw]
    exact varsFit_level _ 0 _ _ _ _ hz hp
  have key := sums_stage_ends R (.tab l) (levelCall (R.f.mu + l)) levelEnds
    (tabJob (dataAt N w R.pts) l (byBit (R.pts.tabPt l))) rfl rfl (carried_tab hW hS l hs)
    (OnBytes.HonestTrace.Look.pj_lawful _ 0 _ _ _ _ hp (by rw [byBit_length, hz]))
    (sized_pj _ 0 _ _ _ _ (by rw [hp.length_eq, List.length_range])) rfl hv (fun _ => rfl)
    (by rw [len_level hW _ _ hs rfl, levelCall_len]) (hW.masks _ hs)
  rw [show R.claimed (.tab l) = R.tabV l from rfl, tab_claimed hW hS l (Nat.le_of_lt hl),
    ← OnBytes.HonestTrace.Look.tabJob_sum _ (by rw [hd]; exact hl),
    show rd (endTerm R.factor (.tab l) (R.shown (.tab l))) = _ from
      endTerm_level ((dataAt N w R.pts).N.w + l) _ _ ((dataAt N w R.pts).N.oT l)
        (byBit (R.pts.tabPt l)) _]
  exact key

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the bits. -/
theorem sums_bits (hW : NumberedP R) (hS : SpecAtP R N w) :
    Sums R .bits (rd (R.claimed .bits)) (rd (endTerm R.factor .bits (R.shown .bits))) := by
  have hs : Stage.bits ∈ stages R.f := mem_bits R.f
  obtain ⟨_, _, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hd : (dataAt N w R.pts).N.d = R.f.d := hS.nums.d
  have hB : (dataAt N w R.pts).N.oB =
      orderDefault ((dataAt N w R.pts).N.w + (dataAt N w R.pts).N.d) := by
    rw [hw, hd]
    exact hS.nums.oB
  have hz : R.pts.zeroPt.size = (dataAt N w R.pts).N.w + (dataAt N w R.pts).N.d := by
    rw [hw, hd]
    exact size_zeroPt _ _ _
  have hv : VarsFit (withPoints (bitsCall (List.replicate (R.f.mu + R.f.d) zeroE)).vs
      (pointsAt R.f .bits (R.ptsAt .bits))) (bitsJob (dataAt N w R.pts) (byBit R.pts.zeroPt)) := by
    rw [withPoints_bits R.f _ (size_zeroPt _ _ _), h3]
    exact varsFit_bits _ _ hB hz
  have key := sums_stage_ends R .bits (bitsCall (List.replicate (R.f.mu + R.f.d) zeroE)) ⟨2, 1⟩
    (bitsJob (dataAt N w R.pts) (byBit R.pts.zeroPt)) rfl rfl (carried_bits hW hS hs)
    (OnBytes.HonestTrace.Look.bitsJob_lawful _ _ (by rw [byBit_length, hz])
      (by rw [hB]; exact perm_orderDefault _))
    (sized_bits _ _ (by rw [hB, (perm_orderDefault _).length_eq, List.length_range])) rfl hv
    (fun _ => rfl)
    (by
      rw [hW.len _ hs, shapeAt_eq R _ _ rfl]
      show (_ ++ [_]).length = _
      rw [List.length_append]
      rfl) (hW.masks _ hs)
  rw [endTerm_bits (dataAt N w R.pts) R.factor (byBit R.pts.zeroPt),
    show rd (R.claimed .bits) = (bitsJob (dataAt N w R.pts) (byBit R.pts.zeroPt)).sum by
      rw [bits_sum_of (dataAt N w R.pts) hS.mid.1]
      exact readE_zero]
  exact key

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the leaves. -/
theorem sums_leaves (hW : NumberedP R) (hS : SpecAtP R N w) :
    Sums R .leaves (rd (R.claimed .leaves))
      (1 + rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) *
        planesOf (dataAt N w R.pts) (eqPairs (R.f.mu + R.f.d) R.zb0)) := by
  have hs : Stage.leaves ∈ stages R.f := mem_leaves R.f
  obtain ⟨_, _, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hd : (dataAt N w R.pts).N.d = R.f.d := hS.nums.d
  have hE : (dataAt N w R.pts).N.oE = orderDefault (R.f.mu + R.f.d) := hS.nums.oE
  have hz : (R.pts.tabPt R.f.d).size = R.f.mu + R.f.d := size_tabPt _ _ _ _
  have hlen : (R.r .leaves).length = R.f.mu + R.f.d := by
    rw [hW.len _ hs, shapeAt_eq R _ _ rfl]
    show (leafVars R.f #[]).length = _
    simp [leafVars]
  have hv : VarsFit (withPoints (leafVars R.f #[]) (pointsAt R.f .leaves (R.ptsAt .leaves)))
      (leavesJob (dataAt N w R.pts) (byBit (R.pts.tabPt R.f.d))) := by
    rw [withPoints_leaves, h3]
    exact varsFit_leaves R.f _ _ hw hE hz
  have key := sums_stage_open R .leaves ⟨0, leafVars R.f #[], none⟩
    (leavesJob (dataAt N w R.pts) (byBit (R.pts.tabPt R.f.d))) rfl rfl (carried_leaves hW hS hs)
    (OnBytes.HonestTrace.Look.leavesJob_lawful _ _ (by rw [byBit_length, hz, hw, hd])
      (by rw [hE, hw, hd]; exact perm_orderDefault _))
    (sized_leaves _ _) hv (by rw [hlen]; simp [leafVars])
  have hz0 : R.zb0.size = R.f.mu + R.f.d := by rw [hW.zb0]; simpa using hlen
  have hb : byBit R.zb0 = (ups (R.r .leaves)).reverse := by rw [hW.zb0, byBit_toArray]
  rw [show R.claimed .leaves = R.tabV R.f.d from rfl, tab_claimed hW hS _ (Nat.le_refl _), ← hd,
    ← OnBytes.HonestTrace.Look.leavesJob_sum]
  rw [hd]
  have e : (1 : KE) + rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) *
      planesOf (dataAt N w R.pts) (eqPairs (R.f.mu + R.f.d) R.zb0) =
      (leavesJob (dataAt N w R.pts) (byBit (R.pts.tabPt R.f.d))).fin (ups (R.r .leaves)) := by
    rw [leaves_fin _ _ _ (by simp [ups, hlen, hw, hd]) (by rw [hE, hw, hd]), ← hb,
      show rd (R.f.leaf R.pts.theta R.pts.alpha R.zb0) = _ from hS.leaf, hw, hd,
      ← hw, ← hd, planes_eq _ _ (by rw [hz0, hw, hd]), mul_comm]
    rfl
  rw [e]
  exact key

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the bits' sumcheck's true end value is the
planes' value at its point. -/
theorem bits_end (hW : NumberedP R) (hS : SpecAtP R N w) :
    rd (R.T .bits 0) = planesOf (dataAt N w R.pts) (eqPairs (R.f.mu + R.f.d) R.zb1) := by
  have hs : Stage.bits ∈ stages R.f := mem_bits R.f
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hd : (dataAt N w R.pts).N.d = R.f.d := hS.nums.d
  have hvl : (bitsCall (List.replicate (R.f.mu + R.f.d) zeroE)).vs.length = R.f.mu + R.f.d := by
    simp [bitsCall]
  have hlen : (R.r .bits).length = R.f.mu + R.f.d + 1 := by
    rw [hW.len _ hs, shapeAt_eq R _ _ rfl]
    show (_ ++ [_]).length = _
    rw [List.length_append, hvl]
    rfl
  have hl : ((R.r .bits).take (R.f.mu + R.f.d)).length = R.f.mu + R.f.d := by
    rw [List.length_take, hlen]
    omega
  have hx : (ups ((R.r .bits).take (R.f.mu + R.f.d))).length = R.f.mu + R.f.d := by
    unfold ups
    rw [List.length_map, hl]
  have hbv := byVar_down (ups ((R.r .bits).take (R.f.mu + R.f.d)))
  rw [hx] at hbv
  have e := planes_eq (dataAt N w R.pts) R.zb1 (by rw [hW.zb1, hw, hd]; simpa using hl)
  rw [hw, hd] at e
  rw [e, T_read R .bits _ _ rfl (carried_bits hW hS hs), hvl, hW.zb1,
    byBit_toArray ((R.r .bits).take (R.f.mu + R.f.d)), ← hbv,
    ← show (dataAt N w R.pts).N.oB = orderDefault (R.f.mu + R.f.d) from hS.nums.oB, ← hw, ← hd]
  rfl

/-- CONDITIONAL ON `SpecAtP R N w` AND the verifier's tests on the face: the counts add up to the
number of all parts' keys that are no padding. -/
theorem count_ok (hS : SpecAtP R N w) (hok : R.f.ok = true) :
    planesOf (dataAt N w R.pts) (countPairs R.f) = rd (ofNat R.f.count) := by
  have hroom : (dataAt N w R.pts).N.n + 2 ≤ 2 ^ (dataAt N w R.pts).N.w := by
    show (N (up R.pts.theta)).n + 2 ≤ 2 ^ (N (up R.pts.theta)).w
    rw [← hS.nums.planes, hS.nums.w]
    exact (facts_of_ok hok).2.2
  refine (planes_sum R.f _ hS.nums.w hroom (fun u j hj => if_neg (Nat.not_lt.2 hj))).trans
    (hS.mid.2.1.trans ?_)
  rw [show rd (ofNat R.f.count) = ((R.f.count : Nat) : KE) from OnBytes.Ends.A.readE_ofNat _]
  congr 1
  unfold VerifiableInference.Desc.K3.Face.count VerifiableInference.Desc.K3.Face.allKeys
  rw [← hS.padding]
  rfl

/-- CONDITIONAL ON `NumberedP R`, `SpecAtP R N w` AND the verifier's tests on the face: behind part
i's tree: alpha less that part's keys' value at the tree's last point. -/
theorem key_end (hW : NumberedP R) (hS : SpecAtP R N w) (hok : R.f.ok = true) {y : Nat × Nat}
    (hy : y ∈ R.f.parts.zipIdx) :
    rd (R.claimed (.key y.2 y.1)) =
      rd R.pts.alpha - keysOfP (dataP N R.f.parts R.f.orders w R.pts) y.2 (R.pts.keyPt y.2 y.1) :=
        by
  have hv : (((dataP N R.f.parts R.f.orders w R.pts).part y.2)).v = y.1 :=
    part_v (dataP N R.f.parts R.f.orders w R.pts) hy ((facts_of_ok hok).1 y.1 (by
      have := (getD_of_mem hy)
      rw [← this.2, List.getD_eq_getElem _ _ this.1]
      exact List.getElem_mem _))
  rw [key_claimed hW hS hok hy _ (Nat.le_refl _)]
  have e := key_top ((dataP N R.f.parts R.f.orders w R.pts).part y.2) (byBit (R.pts.keyPt y.2 y.1))
    (by rw [byBit_length, hv]; exact size_keyPt _ _ _ y.2 _)
  rw [hv] at e
  rw [e]
  unfold keysOfP
  rw [hv]
  rfl

/-- **CONDITIONAL ON `Fit R`, `NumberedP R` AND `SpecAtP R N w`: the specification's summands at
several parts of keys are lawful.** A member, by evaluation: Honest/K3/Parts/Member.lean. -/
theorem lawfulSpecP : LawfulSpecP := by
  intro P N w R hF hW hS
  refine ⟨fun s hs ht => ?_, sums_leaves hW hS, bits_end hW hS, count_ok hS hF.ok,
    fun y hy => key_end hW hS hF.ok hy⟩
  match s, hs, ht with
  | .tie 0, _, _ => exact sums_tie0 hW hS
  | .tie (j + 1), hs, _ => exact sums_tie hW hS j hs
  | .split i, hs, _ => exact sums_split hW hS i hs
  | .key i m, hs, _ =>
    obtain ⟨x, hx, hi, hm⟩ := ProofFile.Honest.K3.mem_key hs
    subst hi
    exact sums_key hW hS hF.ok hx m hm
  | .tab l, hs, _ => exact sums_tab hW hS l (tab_lt hs)
  | .bits, _, _ => exact sums_bits hW hS
  | .shift, _, ht => exact absurd ht (Nat.lt_irrefl 0)
  | .alpha, _, ht => exact absurd ht (Nat.lt_irrefl 0)
  | .join, _, ht => exact absurd ht (Nat.lt_irrefl 0)
  | .keyLine _ _, _, ht => exact absurd ht (Nat.lt_irrefl 0)
  | .tabLine _, _, ht => exact absurd ht (Nat.lt_irrefl 0)
  | .leaves, _, ht => exact absurd ht (Nat.lt_irrefl 0)
  | .zero, _, ht => exact absurd ht (Nat.lt_irrefl 0)

#print axioms ProofFile.Honest.K3.Parts.top_eq
#print axioms ProofFile.Honest.K3.Parts.sized_top
#print axioms ProofFile.Honest.K3.Parts.endTerm_top
#print axioms ProofFile.Honest.K3.Parts.bits_sum_of
#print axioms ProofFile.Honest.K3.Parts.planes_sum
#print axioms ProofFile.Honest.K3.Parts.len_noVar
#print axioms ProofFile.Honest.K3.Parts.sums_tie0
#print axioms ProofFile.Honest.K3.Parts.sums_tie
#print axioms ProofFile.Honest.K3.Parts.sums_split
#print axioms ProofFile.Honest.K3.Parts.key_claimed
#print axioms ProofFile.Honest.K3.Parts.sums_key
#print axioms ProofFile.Honest.K3.Parts.tab_claimed
#print axioms ProofFile.Honest.K3.Parts.sums_tab
#print axioms ProofFile.Honest.K3.Parts.sums_bits
#print axioms ProofFile.Honest.K3.Parts.sums_leaves
#print axioms ProofFile.Honest.K3.Parts.bits_end
#print axioms ProofFile.Honest.K3.Parts.count_ok
#print axioms ProofFile.Honest.K3.Parts.key_end
#print axioms ProofFile.Honest.K3.Parts.lawfulSpecP

end ProofFile.Honest.K3.Parts
