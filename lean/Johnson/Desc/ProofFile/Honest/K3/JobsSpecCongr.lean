-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsSpecCongr.lean: the honest side of the kind "lookup" (K3). The
proof of the statement `JobsCongr` (Honest/K3/JobsSpecOwed.lean): at public numbers whose counting
planes lie inside the cube and whose orders list their levels' variables, the specification's five
jobs read keys and bits inside the sizes alone, at the tie's own steps and the trees' own levels.
Theorems.

Terms. Honest/K3/GLOSSARY.md ("specification", "job"). The five jobs are `tieJob`, `keyJob`,
`tabJob`, `leavesJob` and `bitsJob` (Johnson/HonestTrace/LookDefs.lean). JobsSpecOwed.lean defines
`SameInside` (two data are the same inside the sizes), `Inside` (the condition on the public
numbers) and `SameJob` (two jobs give the same lists and the same true sum).

What is shown, by the file's sections.
  1. `setBit_lt`, `foldN_same`, `ext_same`, `pjRound_same`, `pj_same`: the job of a product of two
     tables reads them on the cube alone.
  2. `lvl_same`: a level of a product tree reads the leaves inside the tree alone.
  3. `chain_same`: the tie's chain reads the planes' roots from its step to the last plane.
  4. `jobsCongr`: the statement `JobsCongr`: under `SameInside D D'` and `Inside D.N`, each of the
     five jobs at D is the same job, in the sense of `SameJob`, as at D': the tie's at its own steps
     (s ≤ n), the trees' at their own levels (below v on the key side, below d on the table's).
     Helper: `sameJob_of_eq`.

Hypotheses that remain. Of `jobsCongr`: those inside the statement.
  `hf`, `hA`, `hB`: (in sections 1 and 2) the two functions agree on the cube, or inside the tree.
  `O`, `ho`: (in `pjRound_same`, `pj_same`) o is an order of the m bits. `hl`: (in `pjRound_same`)
    there are fewer challenges than variables. `h`: (in `sameJob_of_eq`) the two jobs are equal.
  Without a name, in front of arrows: ranges, in `setBit_lt`, `foldN_same` and `lvl_same`; in
    `chain_same`: the two lists of roots agree from the step to the last plane.

Users. Honest/K3/Law/Thread/ExchangeKeys.lean imports this file and calls `ext_same`.

Limits. Facts on the specification's terms. Nothing is said of a filling that folds tables.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecOwed
import Johnson.HonestTrace.LookCube

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Congr
open OnBytes.HonestTrace.Look (Job Data pj pjRound ext setBit fixAt foldN Ord ord_of_perm tieJob
  keyJob
  tabJob leavesJob bitsJob)

/-! ## 1 The job of a product of two tables -/

/-- Laying a bit below m keeps a number below 2 ^ m. -/
theorem setBit_lt : ∀ (m c : Nat), c < m → ∀ (b : Bool) (X : Nat), X < 2 ^ m → setBit c b X < 2 ^ m
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, 0, _, b, X, hX => by
    show 2 * (X / 2) + b.toNat < 2 ^ (m + 1)
    have hb : b.toNat < 2 := by cases b <;> decide
    rw [pow_succ] at hX ⊢
    omega
  | m + 1, c + 1, h, b, X, hX => by
    show 2 * setBit c b (X / 2) + X % 2 < 2 ^ (m + 1)
    have ih := setBit_lt m c (by omega) b (X / 2) (by rw [pow_succ] at hX; omega)
    rw [pow_succ]
    omega

/-- Tables that agree on the cube agree there behind any rounds that bind bits of the cube. -/
theorem foldN_same (m : Nat) (o : List Nat) (rs : List KE) (f f' : Nat → KE)
    (hf : ∀ X, X < 2 ^ m → f X = f' X) : ∀ l, (∀ i, i < l → o.getD i 0 < m) →
    ∀ X, X < 2 ^ m → foldN o rs f l X = foldN o rs f' l X
  | 0, _, X, hX => hf X hX
  | l + 1, ho, X, hX => by
    have hc := ho l (Nat.lt_succ_self l)
    have ih := foldN_same m o rs f f' hf l fun i hi => ho i (Nat.lt_succ_of_lt hi)
    show (1 - rs.getD l 0) * foldN o rs f l (setBit (o.getD l 0) false X) +
        rs.getD l 0 * foldN o rs f l (setBit (o.getD l 0) true X) =
      (1 - rs.getD l 0) * foldN o rs f' l (setBit (o.getD l 0) false X) +
        rs.getD l 0 * foldN o rs f' l (setBit (o.getD l 0) true X)
    rw [ih _ (setBit_lt m _ hc false X hX), ih _ (setBit_lt m _ hc true X hX)]

/-- Tables that agree on the cube have one extension. -/
theorem ext_same (m : Nat) (f f' : Nat → KE) (hf : ∀ X, X < 2 ^ m → f X = f' X) (pt : List KE) :
    ext m f pt = ext m f' pt :=
  Finset.sum_congr rfl fun X hX => by rw [hf X (Finset.mem_range.1 hX)]

/-- The round polynomial, behind fewer challenges than there are variables. -/
theorem pjRound_same (m : Nat) (k : KE) (A A' B B' : Nat → KE) (o : List Nat) (z rs : List KE)
    (O : Ord o m) (hA : ∀ X, X < 2 ^ m → A X = A' X) (hB : ∀ X, X < 2 ^ m → B X = B' X)
    (hl : rs.length < m) : pjRound m k A B o z rs = pjRound m k A' B' o z rs := by
  have hc : o.getD rs.length 0 < m := O.lt _ hl
  have ho : ∀ i, i < rs.length → o.getD i 0 < m := fun i hi => O.lt i (by omega)
  have eA : ∀ (b : Bool) X, X < 2 ^ m → foldN o rs A rs.length (setBit (o.getD rs.length 0) b X) =
      foldN o rs A' rs.length (setBit (o.getD rs.length 0) b X) := fun b X hX =>
    foldN_same m o rs A A' hA _ ho _ (setBit_lt m _ hc b X hX)
  have eB : ∀ (b : Bool) X, X < 2 ^ m → foldN o rs B rs.length (setBit (o.getD rs.length 0) b X) =
      foldN o rs B' rs.length (setBit (o.getD rs.length 0) b X) := fun b X hX =>
    foldN_same m o rs B B' hB _ ho _ (setBit_lt m _ hc b X hX)
  unfold pjRound
  dsimp only
  refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl)) <;>
    refine Finset.sum_congr rfl fun X hX => ?_ <;>
    simp only [eA _ X (Finset.mem_range.1 hX), eB _ X (Finset.mem_range.1 hX)]

/-- **The job of a product of two tables reads them on the cube alone.** -/
theorem pj_same (m : Nat) (k : KE) (A A' B B' : Nat → KE) (o : List Nat) (z : List KE)
    (ho : o.Perm (List.range m)) (hA : ∀ X, X < 2 ^ m → A X = A' X)
    (hB : ∀ X, X < 2 ^ m → B X = B' X) : SameJob (pj m k A B o z) (pj m k A' B' o z) := by
  have O := ord_of_perm ho
  have hz : (pj m k A B o z).zs.length = m := by
    show (TwV.inRounds o z).length = m
    unfold TwV.inRounds
    rw [List.length_map, O.len]
  refine ⟨rfl, rfl, rfl, ?_, fun rs hl => ?_, fun xs => ?_, fun xs mk => ?_, fun xs => ?_⟩
  · show ∑ X ∈ Finset.range (2 ^ m), TwV.eqN z X * (k + A X * B X) =
      ∑ X ∈ Finset.range (2 ^ m), TwV.eqN z X * (k + A' X * B' X)
    exact Finset.sum_congr rfl fun X hX => by
      rw [hA X (Finset.mem_range.1 hX), hB X (Finset.mem_range.1 hX)]
  · exact pjRound_same m k A A' B B' o z rs O hA hB (by rw [← hz]; exact hl)
  · show [ext m A _, ext m B _] = [ext m A' _, ext m B' _]
    rw [ext_same m A A' hA, ext_same m B B' hB]
  · show [k + ext m A _ * ext m B _, ext m A _ * _ + _ * ext m B _, _] =
      [k + ext m A' _ * ext m B' _, ext m A' _ * _ + _ * ext m B' _, _]
    rw [ext_same m A A' hA, ext_same m B B' hB]
  · show k + ext m A _ * ext m B _ = k + ext m A' _ * ext m B' _
    rw [ext_same m A A' hA, ext_same m B B' hB]

/-! ## 2 A level of a product tree -/

/-- Leaves that agree inside the tree give levels that agree inside the tree. -/
theorem lvl_same (w T : Nat) (f f' : Nat → KE) (hf : ∀ X, X < 2 ^ (w + T) → f X = f' X) :
    ∀ (k m : Nat), m + k = T → ∀ X, X < 2 ^ (w + m) → Blocks.lvl w T f m X = Blocks.lvl w T f' m X
  | 0, m, h, X, hX => by
    have e : m = T := by omega
    subst e
    rw [Blocks.lvl_top, Blocks.lvl_top]
    exact hf X hX
  | k + 1, m, h, X, hX => by
    have hm : m < T := by omega
    have ih := lvl_same w T f f' hf k (m + 1) (by omega)
    have hp : 2 ^ (w + (m + 1)) = 2 ^ (w + m) + 2 ^ (w + m) := by
      rw [← Nat.add_assoc, pow_succ]
      omega
    rw [Blocks.lvl_step w T f hm X, Blocks.lvl_step w T f' hm X, ih X (by omega),
      ih _ (by rw [Nat.add_comm m w]; omega)]

/-! ## 3 The tie's chain -/

/-- Roots that agree from step s to step s + k give one chain. -/
theorem chain_same (g g' : Nat → KE) : ∀ (k s : Nat), (∀ j, s ≤ j → j ≤ s + k → g j = g' j) →
    Alg.Lookup.chainFrom g k s = Alg.Lookup.chainFrom g' k s
  | 0, s, h => h s (Nat.le_refl _) (by omega)
  | k + 1, s, h => by
    show Alg.Lookup.chainFrom g k (s + 1) ^ 2 * g s = Alg.Lookup.chainFrom g' k (s + 1) ^ 2 * g' s
    rw [chain_same g g' k (s + 1) fun j h1 h2 => h j (by omega) (by omega),
      h s (Nat.le_refl _) (by omega)]

/-! ## 4 The five jobs -/

/-- One job is the same as itself. -/
theorem sameJob_of_eq {J J' : Job KE} (h : J = J') : SameJob J J' := by
  subst h
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- **At public numbers whose counting planes lie inside the cube and whose orders list their
levels' variables, the five jobs read keys and bits inside the sizes alone**, at the tie's own steps
and the trees' own levels. -/
theorem jobsCongr : JobsCongr := by
  intro P D D' h hI
  obtain ⟨N, key, bits, al⟩ := D
  obtain ⟨N', key', bits', al'⟩ := D'
  obtain ⟨hN, hal, hkey, hbits⟩ := h
  simp only at hN hal hkey hbits hI
  subst hN
  subst hal
  have hG : ∀ j, j < 2 ^ N.w → (⟨N, key, bits, al⟩ : Data P KE).G j =
      (⟨N, key', bits', al⟩ : Data P KE).G j := fun j hj => by
    show ∏ u ∈ Finset.range (2 ^ N.d), (1 + bits u j * (al - 1 - N.tab u)) =
      ∏ u ∈ Finset.range (2 ^ N.d), (1 + bits' u j * (al - 1 - N.tab u))
    exact Finset.prod_congr rfl fun u hu => by rw [hbits u j (Finset.mem_range.1 hu) hj]
  have hZ : (⟨N, key, bits, al⟩ : Data P KE).Z = (⟨N, key', bits', al⟩ : Data P KE).Z := by
    show ∏ b ∈ Finset.range (2 ^ (N.v' + 1)), (al - key b) =
      ∏ b ∈ Finset.range (2 ^ (N.v' + 1)), (al - key' b)
    exact Finset.prod_congr rfl fun b hb => by rw [hkey b (Finset.mem_range.1 hb)]
  have hPc : ∀ s, s ≤ N.n + 1 → (⟨N, key, bits, al⟩ : Data P KE).Pc s =
      (⟨N, key', bits', al⟩ : Data P KE).Pc s := fun s hs => by
    show Alg.Lookup.chainFrom _ (N.n + 1 - s) s = Alg.Lookup.chainFrom _ (N.n + 1 - s) s
    exact chain_same _ _ _ _ fun j _ h2 => hG j (by
      have := hI.planes
      omega)
  have hbit : ∀ X, X < 2 ^ (N.w + N.d) → (⟨N, key, bits, al⟩ : Data P KE).bitAt X =
      (⟨N, key', bits', al⟩ : Data P KE).bitAt X := fun X hX =>
    hbits _ _ (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hX)) (Nat.mod_lt _ (by positivity))
  have hk : ∀ (m : Nat), m ≤ N.v' + 1 → ∀ X, X < 2 ^ m →
      (⟨N, key, bits, al⟩ : Data P KE).kLvl m X = (⟨N, key', bits', al⟩ : Data P KE).kLvl m X :=
    fun m hm X hX => lvl_same 0 (N.v' + 1) _ _
      (fun Y hY => by
        show al - key Y = al - key' Y
        rw [hkey Y (by rw [Nat.zero_add] at hY; exact hY)])
      (N.v' + 1 - m) m (by omega) X (by rw [Nat.zero_add]; exact hX)
  have ht : ∀ (l : Nat), l ≤ N.d → ∀ X, X < 2 ^ (N.w + l) →
      (⟨N, key, bits, al⟩ : Data P KE).tLvl l X = (⟨N, key', bits', al⟩ : Data P KE).tLvl l X :=
    fun l hl X hX => lvl_same N.w N.d _ _
      (fun Y hY => by
        show 1 + bits (Y / 2 ^ N.w) (Y % 2 ^ N.w) * (al - 1 - N.tab (Y / 2 ^ N.w)) =
          1 + bits' (Y / 2 ^ N.w) (Y % 2 ^ N.w) * (al - 1 - N.tab (Y / 2 ^ N.w))
        rw [show bits (Y / 2 ^ N.w) (Y % 2 ^ N.w) = bits' (Y / 2 ^ N.w)
          (Y % 2 ^ N.w) from hbit Y hY])
      (N.d - l) l (by omega) X hX
  refine ⟨fun s hs => ?_, fun l z hl => ?_, fun l z hl => ?_, fun z => ?_, fun z => ?_⟩
  · have hp := hI.planes
    have hs' : s ≤ N.n := hs
    refine sameJob_of_eq ?_
    have ha : (⟨N, key, bits, al⟩ : Data P KE).a = (⟨N, key', bits', al⟩ : Data P KE).a := rfl
    unfold tieJob
    simp only [hZ, ha, hPc 1 (by omega), hPc s (by omega), hPc (s + 1) (by omega), hG 0 (by omega),
      hG s (by omega)]
  · have hl' : l < N.v' + 1 := hl
    have hp : 2 ^ (l + 1) = 2 ^ l + 2 ^ l := by rw [pow_succ]; omega
    exact pj_same l 0 _ _ _ _ _ z (hI.oK l hl') (fun X hX => hk (l + 1) (by omega) X (by omega))
      (fun X hX => hk (l + 1) (by omega) _ (by omega))
  · have hl' : l < N.d := hl
    have hp : 2 ^ (N.w + (l + 1)) = 2 ^ (N.w + l) + 2 ^ (N.w + l) := by
      rw [← Nat.add_assoc, pow_succ]
      omega
    exact pj_same (N.w + l) 0 _ _ _ _ _ z (hI.oT l hl')
      (fun X hX => ht (l + 1) (by omega) X (by omega))
      (fun X hX => ht (l + 1) (by omega) (X + 2 ^ (N.w + l)) (by omega))
  · have Q := pj_same (N.w + N.d) 1 _ _ (⟨N, key, bits, al⟩ : Data P KE).rowAt
      (⟨N, key', bits', al⟩ : Data P KE).rowAt N.oE z hI.oE hbit (fun _ _ => rfl)
    refine ⟨Q.1, rfl, rfl, Q.2.2.2.1, fun rs hr => ?_, fun _ => rfl, fun _ _ => rfl,
      Q.2.2.2.2.2.2.2⟩
    show (pjRound _ _ _ _ _ _ rs).take _ = (pjRound _ _ _ _ _ _ rs).take _
    rw [show pjRound (N.w + N.d) 1 (⟨N, key, bits, al⟩ : Data P KE).bitAt
      (⟨N, key, bits, al⟩ : Data P KE).rowAt N.oE z rs = _ from Q.2.2.2.2.1 rs hr]
    rfl
  · have Q := pj_same (N.w + N.d) 0 _ _ (fun X => (⟨N, key, bits, al⟩ : Data P KE).bitAt X - 1)
      (fun X => (⟨N, key', bits', al⟩ : Data P KE).bitAt X - 1) N.oB z hI.oB hbit
      (fun X hX => congrArg (· - 1) (hbit X hX))
    have e := fun pt => ext_same (N.w + N.d) _ _ hbit pt
    refine ⟨Q.1, rfl, rfl, Q.2.2.2.1, Q.2.2.2.2.1, fun xs => ?_, fun xs m => ?_, Q.2.2.2.2.2.2.2⟩
    · show [ext _ _ _] = [ext _ _ _]
      rw [e]
    · show [ext _ _ _ * (ext _ _ _ - 1), _ * (2 * ext _ _ _ - 1), _] =
        [ext _ _ _ * (ext _ _ _ - 1), _ * (2 * ext _ _ _ - 1), _]
      rw [e]

#print axioms ProofFile.Honest.K3.Congr.sameJob_of_eq
#print axioms ProofFile.Honest.K3.Congr.jobsCongr
#print axioms ProofFile.Honest.K3.Congr.setBit_lt
#print axioms ProofFile.Honest.K3.Congr.foldN_same
#print axioms ProofFile.Honest.K3.Congr.ext_same
#print axioms ProofFile.Honest.K3.Congr.pjRound_same
#print axioms ProofFile.Honest.K3.Congr.pj_same
#print axioms ProofFile.Honest.K3.Congr.lvl_same
#print axioms ProofFile.Honest.K3.Congr.chain_same

end ProofFile.Honest.K3.Congr
