-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/FormPortZF.lean: the sample row that the verifier program makes for an oracle message
(`Send.form`, OnBytes/Iop/Send.lean), read in the field, is the row of the library's sample map for
that message's shape (`portZ`, Johnson/Pack/PortZ.lean), coefficient by coefficient, for a shape
with no mask row and main rows over the base field (`CaseF`, Johnson/Pack/PortF.lean).

Statements and proofs. In this case the pad is the last three places of the last main row. The
program gives place number t the coefficient beta times `thetaE t`; the library gives it beta times
`Cb.Gl.padW t`. Both are 1, x, x², in this order. Off the pad both sides have the weight of the
seed's point at the entry's corner of the message's cube. Johnson/Pack/PortTie.lean ties the numbers
of `portZ` to the program's functions; OnBytes/Slice/BlkSend.lean gives the program's coefficient as
the entry's weight plus a sum over the pad's places (`coefAt_form`). This file joins the two.
Main names:
  `form_portZ_F_theta`: the program's basis element number t, read, is the library's weight of that
    number.
  `form_portZ_F_hit`, `form_portZ_F_miss`: a sum over places with different indices, at an index
    that one place has, and at an index that none has.
  `form_portZ_F_padSum`: the sum of `coefAt_form` for a list of places of the main table.
  `form_portZ_F_cubeIdx`: the entry's vertex on the cube, by the program's formula, is `idxZ`.
  `form_portZ_F`: for every entry j of the message: the program's coefficient at (o, j's table, j's
    index in the table), read, is `(portZ cs s).mat (the seed's point read, β) () j`.
What is not claimed: anything for more than one answer, or for a shape with a mask row or with main
rows over the extension field. The seed's point is asked to have as many coordinates as the cube
has bits, and β to be a unit whose value is the seed's factor, read. Nothing on the row's target,
on other oracle messages (`coefAt_form_other` has these: 0), on indices of the table that are no
entry of the message, or on a run of the program's block. Nothing on the honest prover or on
hiding. That the hypotheses hold together at some size is not shown in this file.
-/
import Johnson.Pack.PortTie
import Johnson.Pack.PortF
import OnBytes.Slice.RecordOK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open OnBytes OnBytes.Slice Cb Cb.Ood

/-- The program's basis element number t, read, is the library's weight number t. -/
theorem form_portZ_F_theta (t : Fin 3) : readE (thetaE t.val) = Cb.Gl.padW t := by
  rw [readE_theta]
  fin_cases t <;> rfl

/-- A sum over places none of which has the index i is 0. -/
theorem form_portZ_F_miss (g : ℕ → ℕ) (v : ℕ → GE) (n i : ℕ) (hi : ∀ t, t < n → g t ≠ i) :
    ((List.range n).map fun t => if g t = i then v t else 0).sum = 0 := by
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
  exact if_neg (hi t (List.mem_range.1 ht))

/-- A sum over places with different indices, at the index of place number u. -/
theorem form_portZ_F_hit (g : ℕ → ℕ) (hg : Function.Injective g) (v : ℕ → GE) (u : ℕ) :
    ∀ n : ℕ, u < n → ((List.range n).map fun t => if g t = g u then v t else 0).sum = v u
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
      rw [List.sum_range_succ]
      by_cases e : u = n
      · subst e
        rw [form_portZ_F_miss g v u (g u) fun t ht q => Nat.ne_of_lt ht (hg q), if_pos rfl,
          zero_add]
      · rw [form_portZ_F_hit g hg v u n (by omega), if_neg fun q => e (hg q).symm, add_zero]

section
variable (cs : Codes) (s : OracleShape)

/-- What places of the main table, all of answer 0 and with the basis elements in their order,
change at the index i of the main table. -/
theorem form_portZ_F_padSum (seed : SampleSeed) (g : ℕ → ℕ) (n i : ℕ) :
    padSum cs s seed 0 ((List.range n).map fun t => ⟨.main, g t, 0, thetaE t⟩) .main i =
      ((List.range n).map fun t => if g t = i then
        readE seed.beta * readE (thetaE t) - tableW cs s seed.z .main (g t) else 0).sum := by
  unfold padSum
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show (if ((Part.main == Part.main) && (g t == i)) = true then
    padW seed 0 ⟨.main, g t, 0, thetaE t⟩ - tableW cs s seed.z .main (g t) else 0) = _
  have hw : padW seed 0 ⟨.main, g t, 0, thetaE t⟩ = readE seed.beta * readE (thetaE t) := rfl
  by_cases e : g t = i
  · rw [if_pos e, if_pos (by rw [e, beq_self_eq_true, beq_self_eq_true]; rfl), hw]
  · rw [if_neg e, if_neg]
    rw [beq_eq_false_iff_ne.2 e, Bool.and_false]
    exact Bool.false_ne_true

/-- An entry's table has a row. -/
theorem form_portZ_F_hasPart (j : (portCode cs s).J) :
    hasPart (Send.cube cs s) (partZ cs s j) = true := by
  rcases j with x | x
  · exact (cube_main cs s (lt_of_le_of_lt (Nat.zero_le _) x.1.isLt)).2.2
  · exact (cube_mask cs s (lt_of_le_of_lt (Nat.zero_le _) x.1.isLt)).2.2

/-- An entry's index lies inside its table. -/
theorem form_portZ_F_locZ_lt (j : (portCode cs s).J) :
    locZ cs s j < 2 ^ partBits (Send.cube cs s) (partZ cs s j) := by
  rcases j with x | x
  · show x.1.val + 2 ^ k1 s * x.2.val < 2 ^ (Send.cube cs s).mainBits
    rw [(cube_main cs s (lt_of_le_of_lt (Nat.zero_le _) x.1.isLt)).2.1]
    exact main_lt cs s x
  · show x.1.val + 2 ^ k2 s * x.2.val < 2 ^ (Send.cube cs s).maskBits
    rw [(cube_mask cs s (lt_of_le_of_lt (Nat.zero_le _) x.1.isLt)).2.1]
    exact mask_lt cs s x

/-- The entry's vertex on the cube, by the program's formula, is the library's corner. -/
theorem form_portZ_F_cubeIdx (j : (portCode cs s).J) :
    cubeIdx (Send.cube cs s) (partZ cs s j) (locZ cs s j) = idxZ cs s j := by
  rw [idxZ_loc, Nat.add_comm]
  unfold cubeIdx
  rw [cube_bits, cube_hasMain_eq, cube_hasMask_eq]
  rcases j with x | x
  · simp [partZ]
  · have h0 : 0 < s.maskRows := lt_of_le_of_lt (Nat.zero_le _) x.1.isLt
    by_cases h1 : 0 < s.mainRows <;> simp [partZ, h0, h1]

end

/-- **The program's sample row, read, is the library's**, with the pad on three places. -/
theorem form_portZ_F (cs : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (row : Row)
    (h : Send.form cs s o seed 0 = some row) (h1 : s.answers = 1) (hF : CaseF s)
    (hz : seed.z.length = bitsZ cs s) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (j : (portCode cs s).J) :
    coefAt row o (partZ cs s j) (locZ cs s j) =
      (portZ cs s).mat (readP (bitsZ cs s) seed.z, β) () j := by
  obtain ⟨places, hpl, hc⟩ := coefAt_form cs s o seed 0 row h (partZ cs s j) (locZ cs s j)
  rw [hc, if_pos (form_portZ_F_hasPart cs s j)]
  have hmem := pad_mem cs s h1 places hpl j
  have h3 := each_three s hF
  rcases j with x | x
  swap
  · exfalso
    have hx : x.1.val < s.maskRows := x.1.isLt
    have hm := hF.1
    omega
  have h0 : 0 < s.mainRows := lt_of_le_of_lt (Nat.zero_le _) x.1.isLt
  rw [pad_main cs s hF.1 h0 h1] at hpl
  by_cases hl : (pMain cs s).ell < eachZ s
  · rw [if_pos hl] at hpl
    cases hpl
  rw [if_neg hl] at hpl
  have hpl' := (Option.some.inj hpl).symm
  have hg : Function.Injective fun t : ℕ =>
      (s.mainRows - 1) + ((pMain cs s).ell - eachZ s + t) * 2 ^ k1 s := fun a b e => by
    have e' := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos (k1 s)) (Nat.add_left_cancel e)
    omega
  have hsum := form_portZ_F_padSum cs s seed
    (fun t : ℕ => (s.mainRows - 1) + ((pMain cs s).ell - eachZ s + t) * 2 ^ k1 s) (eachZ s)
    (locZ cs s (.inl x))
  show tableW cs s seed.z .main (locZ cs s (.inl x)) +
    padSum cs s seed 0 places .main (locZ cs s (.inl x)) = _
  rw [hpl', hsum]
  by_cases hp : padP cs s (.inl x)
  · have a := hp.2.1
    have b := hp.2.2
    have hc' : x.2.val < (pMain cs s).ell := x.2.isLt
    have hu : padNo cs s (.inl x) = x.2.val + eachZ s - (pMain cs s).ell := rfl
    have hlt : padNo cs s (.inl x) < eachZ s := by omega
    have hloc : locZ cs s (.inl x) =
        (s.mainRows - 1) + ((pMain cs s).ell - eachZ s + padNo cs s (.inl x)) * 2 ^ k1 s := by
      show x.1.val + 2 ^ k1 s * x.2.val = _
      rw [show s.mainRows - 1 = x.1.val by omega,
        show (pMain cs s).ell - eachZ s + padNo cs s (.inl x) = x.2.val by omega, Nat.mul_comm]
    rw [hloc, form_portZ_F_hit _ hg _ (padNo cs s (.inl x)) (eachZ s) hlt]
    have e : sigmaZ cs s (.inl x) = Sum.inr ⟨.inl x, hp⟩ := by
      simp [sigmaZ, Equiv.sumCompl, hp]
    show _ = Sum.elim _ _ (sigmaZ cs s (.inl x))
    rw [e]
    show _ = (β : GE) * wZ cs s ⟨.inl x, hp⟩
    have hw : wZ cs s ⟨.inl x, hp⟩ = readE (thetaE (padNo cs s (.inl x))) := by
      unfold wZ
      rw [← form_portZ_F_theta]
      show readE (thetaE (padNo cs s (.inl x) % 3)) = _
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hw, hβ]
    ring
  · have hno : ∀ t, t < eachZ s →
        (s.mainRows - 1) + ((pMain cs s).ell - eachZ s + t) * 2 ^ k1 s ≠ locZ cs s (.inl x) :=
      fun t ht q => hp (hmem.2 ⟨_, by
        rw [hpl']
        exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩, rfl, q⟩)
    rw [form_portZ_F_miss
        (fun t : ℕ => (s.mainRows - 1) + ((pMain cs s).ell - eachZ s + t) * 2 ^ k1 s) _ _ _ hno,
      add_zero, tableW_eq_eqW cs s seed.z .main _ (by rw [cube_bits]; exact hz)
        (form_portZ_F_hasPart cs s (.inl x)) (form_portZ_F_locZ_lt cs s (.inl x))]
    have hi : cubeIdx (Send.cube cs s) .main (locZ cs s (.inl x)) = idxZ cs s (.inl x) :=
      form_portZ_F_cubeIdx cs s (.inl x)
    rw [hi, cube_bits]
    have e : sigmaZ cs s (.inl x) = Sum.inl ⟨.inl x, hp⟩ := by
      simp [sigmaZ, Equiv.sumCompl, hp]
    show _ = Sum.elim _ _ (sigmaZ cs s (.inl x))
    rw [e]
    rfl

end Johnson.Pack
