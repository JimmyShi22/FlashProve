-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Digits/PortKeys.lean: the keys, the planes and the tables of the lookup on the
digits of a smallness test, as terms in what is committed, at the verifier's own record.

The lookup of a sub-proof takes from its caller each call's key vector, as a function of the
committed entries, a form that reads that vector's extension at the call's point, and the places of
the bits of the counts. Here these are given for the two calls of the smallness test.

Main names:
  `digInCall`, `inCall_fwd`, `inCall_bwd`: `keyNo` and its inverse inside one call.
  `Kp tl mu q`: call q's own key vector: at key number kn the digit that lies there, read in ZZ's
    entries; 0 at a padding place of the call. `Tp`: the range table.
  `dgP_key_port`: (portQ tl).key mu X = Port.key tl.f9 Tp (Kp tl mu) X, for every X.
  `dgP_KF`: ext n_q (Kp tl mu q) pt is the sum over the digits of call q of eqN n_q 0 pt (keyNo tl q
    c u) * mu (ZZ, u, q mz + c), for every point.
  `AffK`, `KFl`, `dgP_KFok`: the same as a sparse affine value, at a point given as a list.
  `bcP`, `dgP_bc`, `dgP_plane_split`, `bitP`: the planes' places in BZ.
Limits: all under `TailOK tl` (PortLaws.lean). `dgP_key_port` asks that call 0's padding row is row
0. The entries have the infinite type `Ent3`; PortJ.lean carries all terms to a caller's type.

-/
import OnBytes.Tie.Pv.Lookup.Digits.PortLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.DgP
open OnBytes OnBytes.Model CbQ Cb.LdLkp Cb.Lkp Blocks

variable {tl : HTailF2}

/-- The digit at key number kn of call q. none: a padding place of the call. -/
def digInCall (tl : HTailF2) (q kn : ℕ) : Option (ℕ × ℕ × ℕ) := (pieceK tl q kn).bind fun p => cut p
    q kn

theorem digAtN_eq (tl : HTailF2) (X : ℕ) : digAtN tl X =
    if treeOf tl.f9 X < tl.f9.NT then digInCall tl (Port.co tl.f9 (treeOf tl.f9 X)) (knOf tl.f9 X)
        else none := rfl

/-- Inside a call, forwards. -/
theorem inCall_fwd (hT : TailOK tl) {q c u : ℕ} (hq : q < 2) (hc : c < tl.mz) (hu : u < tl.tau) :
    keyNo tl q c u < 2 ^ Port.nOf tl.f9 q ∧ digInCall tl q (keyNo tl q c u) = some (q, c, u) := by
  have hqN : q < tl.f9.NC := by rw [hT.nc]; exact hq
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (hT.rows q hqN u hu)
  have hmem : p ∈ piecesL tl q := List.mem_of_find?_eq_some hp
  have hpred := List.find?_some hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  obtain ⟨hCp, hCP, hRC, hoff, _⟩ := hT.pc q hqN p hmem
  have hcCp : c < p.Cp := by rw [hCp]; exact hc
  have hcCP : c < p.CP := lt_of_lt_of_le hcCp hCP
  have hr : u - p.r0 < p.Rp := by omega
  obtain ⟨inner, hinner⟩ : ∃ inner, inner = c + p.CP * (u - p.r0) := ⟨_, rfl⟩
  have hin : inner < 2 ^ p.b := by
    rw [← hRC, hinner]
    calc c + p.CP * (u - p.r0) < p.CP + p.CP * (u - p.r0) := by omega
      _ = p.CP * (u - p.r0 + 1) := by ring
      _ ≤ p.CP * p.Rp := Nat.mul_le_mul_left _ hr
  obtain ⟨kn, hknd⟩ : ∃ kn, kn = p.off + inner := ⟨_, rfl⟩
  have hkn : keyNo tl q c u = kn := by
    unfold keyNo
    rw [hp, hknd, hinner]
    rfl
  rw [hkn]
  refine ⟨by omega, ?_⟩
  have hex : (pieceK tl q kn).isSome = true := by
    unfold pieceK
    rw [List.find?_isSome]
    refine ⟨p, hmem, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.1 hex
  have hmem' : p' ∈ piecesL tl q := List.mem_of_find?_eq_some hp'
  have hpred' := List.find?_some hp'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred'
  obtain ⟨o1, o2, o3, o4, o5, _⟩ := hT.one q hqN p hmem p' hmem' (Or.inr ⟨by omega, by omega⟩)
  unfold digInCall
  rw [hp']
  show cut p' q kn = _
  have hsub : kn - p'.off = c + p.CP * (u - p.r0) := by rw [← o1, ← hinner]; omega
  have hCPpos : 0 < p.CP := by omega
  unfold cut
  rw [hsub, ← o4, ← o3, ← o5, ← o2, Nat.add_mul_div_left _ _ hCPpos, Nat.div_eq_of_lt hcCP,
      Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcCP, if_pos ⟨hr, hcCp⟩]
  have e : p.r0 + (u - p.r0) = u := by omega
  rw [e]

/-- Inside a call, backwards. -/
theorem inCall_bwd (hT : TailOK tl) {q kn q' c u : ℕ} (hq : q < 2) (hd : digInCall tl q kn = some
    (q', c, u)) :
    q' = q ∧ c < tl.mz ∧ u < tl.tau ∧ keyNo tl q c u = kn := by
  have hqN : q < tl.f9.NC := by rw [hT.nc]; exact hq
  unfold digInCall at hd
  obtain ⟨p, hp, hcut⟩ := Option.bind_eq_some_iff.1 hd
  have hmem : p ∈ piecesL tl q := List.mem_of_find?_eq_some hp
  have hpred := List.find?_some hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  obtain ⟨hCp, _, _, _, hrow⟩ := hT.pc q hqN p hmem
  unfold cut at hcut
  obtain ⟨r, hrd⟩ : ∃ r, r = (kn - p.off) / p.CP := ⟨_, rfl⟩
  obtain ⟨c', hcd⟩ : ∃ c', c' = (kn - p.off) % p.CP := ⟨_, rfl⟩
  rw [← hrd, ← hcd] at hcut
  by_cases hcond : r < p.Rp ∧ c' < p.Cp
  · rw [if_pos hcond] at hcut
    simp only [Option.some.injEq, Prod.mk.injEq] at hcut
    obtain ⟨rfl, rfl, rfl⟩ := hcut
    refine ⟨rfl, by rw [← hCp]; exact hcond.2, by omega, ?_⟩
    have hex : (pieceAt tl q (p.r0 + r)).isSome = true := by
      unfold pieceAt
      rw [List.find?_isSome]
      refine ⟨p, hmem, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.1 hex
    have hmem' : p' ∈ piecesL tl q := List.mem_of_find?_eq_some hp'
    have hpred' := List.find?_some hp'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred'
    obtain ⟨o1, o2, _, o4, _, _⟩ := hT.one q hqN p hmem p' hmem' (Or.inl ⟨by omega, by omega⟩)
    unfold keyNo
    rw [hp']
    show inP p' _ _ = kn
    unfold inP
    rw [← o1, ← o2, ← o4, Nat.add_sub_cancel_left, hcd, hrd, Nat.mod_add_div]
    omega
  · rw [if_neg hcond] at hcut
    exact absurd hcut (by simp)

section
variable {E : Type} [Field E]

/-- Call q's own key vector, as a term in the entries of ZZ. -/
def Kp (tl : HTailF2) (μ : Ent3 → E) (q kn : ℕ) : E :=
  match digInCall tl q kn with
  | some t => μ (tl.ix.ZZ, t.2.2, q * tl.mz + t.2.1)
  | none => 0

/-- Call c's table: the range table. -/
def Tp (_c t : ℕ) : E := ((t : ℕ) : E)

/-- The planes as a function of (joint row, plane), in BZ's entries. -/
def bitP (tl : HTailF2) (μ : Ent3 → E) (Y j : ℕ) : E := μ ((portQ tl).bAt Y j)

/-- The linear form on the entries of ZZ that reads call q's key vector at a point. -/
def KFp (tl : HTailF2) (q : ℕ) (pt : ℕ → E) : Ent3 → E :=
  Cb.RngPk.placed (fun i : Pl tl => ((tl.ix.ZZ, i.2.val, q * tl.mz + i.1.val) : Ent3))
    fun i => eqN (Port.nOf tl.f9 q) 0 pt (keyNo tl q i.1.val i.2.val)

theorem Kp_key (hT : TailOK tl) (μ : Ent3 → E) {q c u : ℕ} (hq : q < 2) (hc : c < tl.mz) (hu : u <
    tl.tau) :
    Kp tl μ q (keyNo tl q c u) = μ (tl.ix.ZZ, u, q * tl.mz + c) := by
  unfold Kp
  rw [(inCall_fwd hT hq hc hu).2]

/-- The extension of call q's key vector at a point is a sum over the digits, for every point. -/
theorem dgP_KF (hT : TailOK tl) (μ : Ent3 → E) {q : ℕ} (hq : q < 2) (pt : ℕ → E) :
    ext (Port.nOf tl.f9 q) (Kp tl μ q) pt =
      ∑ i : Pl tl, eqN (Port.nOf tl.f9 q) 0 pt (keyNo tl q i.1.val i.2.val) * μ (tl.ix.ZZ, i.2.val,
          q * tl.mz + i.1.val) := by
  classical
  unfold Blocks.ext
  have hinj : Function.Injective fun i : Pl tl => keyNo tl q i.1.val i.2.val := by
    intro i i' e
    have h1 := (inCall_fwd hT hq i.1.isLt i.2.isLt).2
    have h2 := (inCall_fwd hT hq i'.1.isLt i'.2.isLt).2
    have e' : keyNo tl q i.1.val i.2.val = keyNo tl q i'.1.val i'.2.val := e
    rw [e', h2] at h1
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h1
    exact Prod.ext (Fin.ext h1.1.symm) (Fin.ext h1.2.symm)
  have hsub : (Finset.univ : Finset (Pl tl)).image (fun i => keyNo tl q i.1.val i.2.val) ⊆
      Finset.range (2 ^ Port.nOf tl.f9 q) := fun X hX => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hX
    exact Finset.mem_range.2 (inCall_fwd hT hq i.1.isLt i.2.isLt).1
  rw [← Finset.sum_subset hsub fun X _ hn => by
    cases hd : digInCall tl q X with
    | none => unfold Kp; rw [hd, mul_zero]
    | some t =>
      obtain ⟨q', c, u⟩ := t
      obtain ⟨_, g2, g3, g4⟩ := inCall_bwd hT hq hd
      exact absurd (Finset.mem_image.2 ⟨(⟨c, g2⟩, ⟨u, g3⟩), Finset.mem_univ _, g4⟩) hn]
  rw [Finset.sum_image fun i _ i' _ e => hinj e]
  exact Finset.sum_congr rfl fun i _ => by rw [Kp_key hT μ hq i.1.isLt i.2.isLt]

theorem key_some {I J : Type} (Q : DatQ I J) (μ : J → E) {X : ℕ} {p : Bool × I} (h : Q.digAt X =
    some p) :
    Q.key μ X = μ (Q.plc p) := by
  unfold DatQ.key
  rw [h]

/-- The digits' joint keys are `Port.key` at K := Kp, T := Tp. -/
theorem dgP_key_port (hT : TailOK tl) (ht0 : Port.t0Of tl.f9 0 = 0) (μ : Ent3 → E) (X : ℕ) :
    (portQ tl).key μ X = Port.key tl.f9 (Tp (E := E)) (Kp tl μ) X := by
  rw [Cb.port_prover E tl.f9 Tp (Kp tl μ) hT.port X]
  obtain ⟨_, _, _, h4, _, _⟩ := hT.port
  unfold Port.keyP
  by_cases hy : X % 2 ^ tl.f9.rK < tl.f9.NT
  · have hy' : treeOf tl.f9 X < tl.f9.NT := hy
    rw [if_pos hy]
    have hq2 : Port.co tl.f9 (X % 2 ^ tl.f9.rK) < 2 := lt_of_lt_of_eq (h4 _ hy).1 hT.nc
    have hk : (X % 2 ^ tl.f9.rK - Port.fst tl.f9 (Port.co tl.f9 (X % 2 ^ tl.f9.rK))) * 2 ^ tl.f9.dT
        + X / 2 ^ tl.f9.rK =
        knOf tl.f9 X := by
      unfold knOf treeOf
      rw [Nat.add_comm, Nat.mul_comm]
    rw [hk]
    have hN : digAtN tl X = digInCall tl (Port.co tl.f9 (X % 2 ^ tl.f9.rK)) (knOf tl.f9 X) := by
      rw [digAtN_eq, if_pos hy']
      rfl
    unfold Kp
    cases hd : digInCall tl (Port.co tl.f9 (X % 2 ^ tl.f9.rK)) (knOf tl.f9 X) with
    | none =>
      have hP : (portQ tl).digAt X = none := by
        show digAtP tl X = none
        unfold digAtP
        rw [hN, hd]
      exact (portQ tl).key_none μ hP
    | some t =>
      obtain ⟨q', c, u⟩ := t
      obtain ⟨g1, g2, g3, _⟩ := inCall_bwd hT hq2 hd
      have hP : (portQ tl).digAt X = some (q' == 1, (⟨c, g2⟩ : Fin tl.mz), (⟨u, g3⟩ : Fin tl.tau))
          := by
        show digAtP tl X = _
        unfold digAtP
        rw [hN, hd]
        simp only [dif_pos g2, dif_pos g3]
      rw [key_some (portQ tl) μ hP]
      subst g1
      obtain ⟨q0, hq0⟩ : ∃ q0, q0 = Port.co tl.f9 (X % 2 ^ tl.f9.rK) := ⟨_, rfl⟩
      rw [← hq0] at hq2 ⊢
      interval_cases q0
      · show μ (tl.ix.ZZ, u, c) = μ (tl.ix.ZZ, u, 0 * tl.mz + c)
        rw [Nat.zero_mul, Nat.zero_add]
      · show μ (tl.ix.ZZ, u, tl.mz + c) = μ (tl.ix.ZZ, u, 1 * tl.mz + c)
        rw [Nat.one_mul]
  · have hy' : ¬ treeOf tl.f9 X < tl.f9.NT := hy
    rw [if_neg hy, ht0]
    have hP : (portQ tl).digAt X = none := by
      show digAtP tl X = none
      unfold digAtP
      rw [digAtN_eq, if_neg hy']
    rw [(portQ tl).key_none μ hP]
    show (0 : E) = ((0 : ℕ) : E)
    simp

/-- The joint table, the tags and the sizes are those of `Port`, by rfl. -/
theorem dgP_tab_port (Y : ℕ) : (portQ tl).tab (E := E) Y = Port.tab tl.f9 (Tp (E := E)) Y := rfl
theorem dgP_tag_port (c : ℕ) : (portQ tl).tagE (E := E) c = ((c : ℕ) : E) := rfl
theorem dgP_sizes_port : (portQ tl).v = tl.f9.v ∧ (portQ tl).d = tl.f9.d ∧ (portQ tl).fK = Port.fK
    tl.f9 ∧ (portQ tl).fT = Port.fT tl.f9 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## As sparse affine values, at points given as lists -/

/-- An affine value: (a sparse list of coefficients, a constant). -/
abbrev AffK (J E : Type) : Type := List (J × E) × E
def AffK.val {J : Type} (f : AffK J E) (μ : J → E) : E := (f.1.map fun x => x.2 * μ x.1).sum + f.2

/-- The digits' places of one kind, as a list: column by column. -/
def plL (tl : HTailF2) : List (ℕ × ℕ) := (List.range tl.mz).flatMap fun c => (List.range tl.tau).map
    fun u => (c, u)

/-- The form of call q as an affine value, at a point given as a list, top bit first (the verifier's
order). -/
def KFl (tl : HTailF2) (q : ℕ) (z : List E) : AffK Ent3 E :=
  ((plL tl).map fun x => ((tl.ix.ZZ, x.2, q * tl.mz + x.1), eqN z.length 0 (ofList z) (keyNo tl q
      x.1 x.2)), 0)

theorem sum_list_range {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_list_range f n,
        Finset.sum_range_succ]
    simp

theorem sum_flatMap {α β M : Type} [AddCommMonoid M] (l : List α) (g : α → List β) (h : β → M) :
    ((l.flatMap g).map h).sum = (l.map fun a => ((g a).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- The affine value reads the extension of call q's key vector, top bit first (`Blocks.ext` at
`ofList z`), for every tuple of entries and every list of the call's length. -/
theorem dgP_KFok (hT : TailOK tl) (μ : Ent3 → E) {q : ℕ} (hq : q < 2) (z : List E) (hz : z.length =
    Port.nOf tl.f9 q) :
    (KFl tl q z).val μ = ext z.length (Kp tl μ q) (ofList z) := by
  rw [hz, dgP_KF hT μ hq, Fintype.sum_prod_type]
  unfold AffK.val KFl plL
  rw [add_zero, List.map_map, sum_flatMap, sum_list_range, ← Fin.sum_univ_eq_sum_range
    (fun c => (((List.range tl.tau).map fun u => (c, u)).map
      ((fun x : Ent3 × E => x.2 * μ x.1) ∘ fun x : ℕ × ℕ =>
        ((tl.ix.ZZ, x.2, q * tl.mz + x.1), eqN z.length 0 (ofList z) (keyNo tl q x.1 x.2)))).sum)
            tl.mz]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [List.map_map, sum_list_range, ← Fin.sum_univ_eq_sum_range
    (fun u => (((fun x : Ent3 × E => x.2 * μ x.1) ∘ fun x : ℕ × ℕ =>
        ((tl.ix.ZZ, x.2, q * tl.mz + x.1), eqN z.length 0 (ofList z) (keyNo tl q x.1 x.2))) ∘ fun u
            => ((c : ℕ), u)) u) tl.tau]
  refine Finset.sum_congr rfl fun u _ => ?_
  show eqN z.length 0 (ofList z) (keyNo tl q c u) * μ (tl.ix.ZZ, u, q * tl.mz + c) = _
  rw [hz]

/-- The entry of bit j of the count of row t of call c, in BZ. -/
def bcP (tl : HTailF2) (t c j : ℕ) : Ent3 := (portQ tl).bAt (t * 2 ^ tl.f9.cK + c) j

/-- By (row of the call, call) it is the place of the record of the digits. -/
theorem dgP_bc (u j : ℕ) : bcP tl (u / 2 ^ tl.f9.cK) (u % 2 ^ tl.f9.cK) j = (portQ tl).bAt u j := by
  unfold bcP
  rw [Nat.div_add_mod']

/-- The planes' split at BZ: eq(zb, (t | c | j)) = eq(the first five coordinates, BZ's row) times
eq(the others, BZ's column): the weights of `linBits9` and `coefficientsF`
(OnBytes/Model/Tail.lean). -/
theorem dgP_plane_split (pt : ℕ → E) (Y j : ℕ) :
    rowBAt (portQ tl) wP pt Y j =
      eqN 5 0 pt (bitNo wP Y j / tl.bzColumns) *
        eqN (tl.f9.kT + tl.f9.cK) 5 pt (bitNo wP Y j % tl.bzColumns) := by
  unfold rowBAt
  show eqN (tl.f9.kT + tl.f9.cK + 5) 0 pt (bitNo wP Y j) = _
  have hpos : 0 < tl.bzColumns := by
    unfold HTailF2.bzColumns
    positivity
  have hlt : bitNo wP Y j % tl.bzColumns < 2 ^ (tl.f9.kT + tl.f9.cK) := Nat.mod_lt _ hpos
  have e := eqN_append' 5 (tl.f9.kT + tl.f9.cK) 0 pt (bitNo wP Y j / tl.bzColumns) hlt
  rw [Nat.zero_add] at e
  rw [← e, Nat.add_comm 5]
  congr 1
  exact (Nat.div_add_mod' _ _).symm

end

#print axioms dgP_KFok
#print axioms dgP_plane_split
#print axioms inCall_fwd
#print axioms inCall_bwd
#print axioms dgP_KF
#print axioms dgP_key_port
#print axioms dgP_tab_port

end OnBytes.DgP
