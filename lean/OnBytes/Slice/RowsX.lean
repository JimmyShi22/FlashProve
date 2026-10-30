-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RowsX.lean: the rows of the link as a function of what the verifier holds.

The link is the format's protocol between two stored tables (OnBytes/Slice/README.md has the
vocabulary). After its first five rounds the verifier forms linear claims, rows, on the two folded
rows that were sent, and combines them into one (OnBytes/Slice/BatSem.lean). A statement about a
whole transcript needs these rows fixed before the round in which they are combined. So this file
gives them as one function, `rowsX`, of the statement x that the library's verifier holds after the
fifth round: the point of comparison, the two seeds with their answers, the drawn locations with the
folds of the columns read. Everything is in the field `GE`. No array and no word occurs in the
definition.

Each folded row is stored as a member of one group: a table of R rows of the code C, in a block of
2 ^ aR rows of the group's main table. The vectors are given at every entry of that table, also on
the rows of a member's block that the member does not have. There a sample row has the weight of
the entry's vertex. The equality row and the draws' rows are 0 there if a row of C has 2 ^ aP
places: this is a remark, no theorem of this file.

Main definitions: `Sz.eqC`, `Sz.colC`, `Sz.smpC` (a coefficient by the number of an entry),
`tgX`, `cfX`, `vsX`, `rowsX`.
Main theorems.
 `layF_closed`, `colF_closed`, `mat_closed`: the library's forms of the layout, of a column and of a
   sample, by the number of an entry.
 `isRows_rowsX`: for every x the rows are the library's on each member's entries (`IsRows`).




Not claimed. Nothing on a protocol. `isRows_rowsX` asks that a row of the code C has 2 ^ aP places.
That the rows that the format's verifier writes (Fmt/M3Link.lean), laid on the group's tables, are
these rows at the statement after the five written rounds is not shown here.
-/
import OnBytes.Slice.BlockBat

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## The coefficients, by the number of an entry -/

namespace Sz
variable (S : Sz)

/-- The equality row's coefficient at entry e of a folded row: the weight of e's vertex at the
point φ if e is before the cut, else 0. -/
def eqC (φ : Fin S.P.aPhi → GE) (e : ℕ) : GE :=
  if e < S.P.cut then Alg.eqk φ (fun u => e.testBit u.val) else 0

/-- The coefficient of the row of a draw at the location x, at entry e of a folded row: a power of
x's point on the message's entries and, from entry t0 on, on the tail's; else 0. -/
def colC (x : S.Pos) (e : ℕ) : GE :=
  if e < S.P.T.l then algebraMap GF GE (ptOf S.P.T.a x ^ (S.P.T.r + e))
  else if S.P.t0 ≤ e then
    (if e - S.P.t0 < S.P.T.r then algebraMap GF GE (ptOf S.P.T.a x ^ (e - S.P.t0)) else 0)
  else 0

/-- The index of the sample's pad in a member's table. -/
def padIdx : ℕ := (S.P.R - 1) + 2 ^ S.P.aR * (S.P.C.l - 1)

/-- A sample row's coefficient at the index i of a member's table: the seed's factor at the pad,
else the weight of i's vertex at the seed's point. -/
def smpC (ρ : (Fin (S.P.aR + S.P.aP) → GE) × GEˣ) (i : ℕ) : GE :=
  if i = S.padIdx then ρ.2.val else Alg.eqk ρ.1 (fun u => i.testBit u.val)

end Sz

/-! ## The rows -/

/-- The target of row number b: 0 for the equality row, the answers for the two sample rows, the
folds of the columns read for the draws' rows. -/
def tgX (S : Sz) (x : S.lk.X4) (b : ℕ) : GE :=
  if b = 0 then 0
  else if b = 1 then (x.1.1.2 false).2 ()
  else if b = 2 then (x.1.1.2 true).2 ()
  else if h : b - 3 < S.P.nu0 then x.1.2.1.2 ⟨b - 3, h⟩
  else if h : b - 3 - S.P.nu0 < S.P.nuj then x.1.2.2.2 ⟨b - 3 - S.P.nu0, h⟩
  else 0

/-- The coefficient of row number b at row r, place p of member a's block. -/
def cfX (S : Sz) (x : S.lk.X4) (b : ℕ) (a : Bool) (r p : ℕ) : GE :=
  if b = 0 then (if a then -S.eqC x.2 (r * 2 ^ S.P.aP + p) else S.eqC x.2 (r * 2 ^ S.P.aP + p))
  else if b = 1 then (if a then 0 else S.smpC (x.1.1.2 false).1 (r + 2 ^ S.P.aR * p))
  else if b = 2 then (if a then S.smpC (x.1.1.2 true).1 (r + 2 ^ S.P.aR * p) else 0)
  else if h : b - 3 < S.P.nu0 then
    (if a then 0 else S.colC (x.1.2.1.1 ⟨b - 3, h⟩) (r * 2 ^ S.P.aP + p))
  else if h : b - 3 - S.P.nu0 < S.P.nuj then
    (if a then S.colC (x.1.2.2.1 ⟨b - 3 - S.P.nu0, h⟩) (r * 2 ^ S.P.aP + p) else 0)
  else 0

/-- The vector of row number b on the group's tables. The row with the number n of the group's main
table is row n % 2 ^ aR of the first member's block if n < 2 ^ aR, else of the second's. On the
mask table the vector is 0. -/
def vsX (S : Sz) (t : ℕ) (x : S.lk.X4) (b : ℕ) : (S.sg t).cIn.J → GE
  | .inl y => cfX S x b (decide (2 ^ S.P.aR ≤ Sz.rowNo y.1)) (Sz.rowNo y.1 % 2 ^ S.P.aR) y.2.val
  | .inr _ => 0

/-- The rows of the link, targets and vectors, as a function of the statement that the library's
verifier holds after the link's first five rounds. -/
def rowsX (S : Sz) (t : ℕ) (x : S.lk.X4) : (ℕ → GE) × (ℕ → (S.sg t).cIn.J → GE) :=
  (tgX S x, vsX S t x)

/-! ## They are the library's rows on each member's entries -/

/-- The vector of a row at an entry of a member. -/
theorem vsX_atJ (S : Sz) (t : ℕ) (x : S.lk.X4) (b : ℕ) (a : Bool) (r : Fin S.P.R)
    (p : Fin S.P.C.l) :
    vsX S t x b (atJ S t a (.inl (r, p))) = cfX S x b a r.val p.val := by
  have hr : r.val < 2 ^ S.P.aR := lt_of_lt_of_le r.isLt (le_two_pow_clog S.P.R)
  show cfX S x b (decide (2 ^ S.P.aR ≤ Sz.rowNo (memRow S t a r.val)))
    (Sz.rowNo (memRow S t a r.val) % 2 ^ S.P.aR) p.val = _
  rw [rowNo_memRow S t a r.val hr]
  cases a
  · have h1 : S.blk false + r.val = r.val := Nat.zero_add _
    rw [h1, Nat.mod_eq_of_lt hr, decide_eq_false (by omega)]
  · have h1 : S.blk true + r.val = 2 ^ S.P.aR + r.val := rfl
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt hr, decide_eq_true (by omega)]

/-- The library's form of the layout, by the number of an entry. -/
theorem layF_closed (S : Sz) (i : Bool) (φ : Fin S.P.aPhi → GE) (r : Fin S.P.R)
    (p : Fin S.P.C.l) :
    S.lk.layF i S.putAt φ (.inl (r, p)) = S.eqC φ (r.val * S.P.C.l + p.val) := by
  have key : ∀ k : S.Co, S.putAt k = Sum.inl (r, p) ↔ S.entryOf k = r.val * S.P.C.l + p.val :=
    fun k => putAt_eq_iff S k r p
  have hent : ∀ a : S.Lay, S.entryOf (S.lk.D.X.pl (S.lk.D.lay a)) = a.val := fun a => by
    show (if S.P.T.r + a.val < S.P.T.r then _ else S.P.T.r + a.val - S.P.T.r) = a.val
    rw [if_neg (by omega)]
    omega
  unfold Cb.LdLkP.layF Cb.Slf.push Sz.eqC
  generalize r.val * S.P.C.l + p.val = e at key ⊢
  by_cases h1 : e < S.P.cut
  · rw [if_pos h1, Finset.sum_eq_single (⟨e, h1⟩ : S.Lay)]
    · rw [if_pos ((key _).2 (hent _))]
    · intro a _ ha
      refine if_neg fun h => ha (Fin.ext ?_)
      have h2 := (key _).1 h
      rw [hent] at h2
      exact h2
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg h1]
    refine Finset.sum_eq_zero fun a _ => if_neg fun h => h1 ?_
    have h2 := (key _).1 h
    rw [hent] at h2
    exact h2 ▸ a.isLt

/-- The library's form of a column, by the number of an entry. -/
theorem colF_closed (S : Sz) (i : Bool) (x : S.Pos) (r : Fin S.P.R) (p : Fin S.P.C.l) :
    S.lk.colF i S.putAt x (.inl (r, p)) = S.colC x (r.val * S.P.C.l + p.val) := by
  have ht0 := le_t0 S.P
  have key : ∀ k : S.Co, S.putAt k = Sum.inl (r, p) ↔ S.entryOf k = r.val * S.P.C.l + p.val :=
    fun k => putAt_eq_iff S k r p
  have hent : ∀ k : S.Co,
      S.entryOf k = if k.val < S.P.T.r then S.P.t0 + k.val else k.val - S.P.T.r := fun _ => rfl
  unfold Cb.LdLkP.colF Cb.Slf.push Sz.colC
  generalize r.val * S.P.C.l + p.val = e at key ⊢
  by_cases h1 : e < S.P.T.l
  · rw [if_pos h1, Finset.sum_eq_single (Fin.natAdd S.P.T.r ⟨e, h1⟩)]
    · rw [if_pos ((key _).2 (by
        rw [hent]
        show (if S.P.T.r + e < S.P.T.r then _ else S.P.T.r + e - S.P.T.r) = e
        rw [if_neg (by omega)]
        omega))]
      rfl
    · intro k _ hk
      refine if_neg fun h => hk (Fin.ext ?_)
      have h2 := (key k).1 h
      rw [hent] at h2
      show k.val = S.P.T.r + e
      split at h2 <;> omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg h1]
    by_cases h2 : S.P.t0 ≤ e ∧ e - S.P.t0 < S.P.T.r
    · rw [if_pos h2.1, if_pos h2.2, Finset.sum_eq_single (Fin.castAdd S.P.T.l ⟨e - S.P.t0, h2.2⟩)]
      · rw [if_pos ((key _).2 (by
          rw [hent]
          show (if e - S.P.t0 < S.P.T.r then S.P.t0 + (e - S.P.t0) else _) = e
          rw [if_pos h2.2]
          omega))]
        rfl
      · intro k _ hk
        refine if_neg fun h => hk (Fin.ext ?_)
        have h3 := (key k).1 h
        have h4 := k.isLt
        rw [hent] at h3
        show k.val = e - S.P.t0
        split at h3 <;> omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hz : (if S.P.t0 ≤ e then (if e - S.P.t0 < S.P.T.r
          then algebraMap GF GE (ptOf S.P.T.a x ^ (e - S.P.t0)) else 0) else 0) = 0 := by
        by_cases h3 : S.P.t0 ≤ e
        · rw [if_pos h3, if_neg fun h4 => h2 ⟨h3, h4⟩]
        · rw [if_neg h3]
      rw [hz]
      refine Finset.sum_eq_zero fun k _ => if_neg fun h => ?_
      have h3 := (key k).1 h
      have h4 := k.isLt
      rw [hent] at h3
      split at h3 <;> omega

/-- The library's sample row of a member, by the index of an entry. -/
theorem mat_closed (S : Sz) (hl2 : S.P.C.l = 2 ^ S.P.aP) (a : Bool)
    (ρ : (Fin (S.P.aR + S.P.aP) → GE) × GEˣ) (r : Fin S.P.R) (p : Fin S.P.C.l) :
    (S.fam.om a).Z.mat ρ () (.inl (r, p)) = S.smpC ρ (r.val + 2 ^ S.P.aR * p.val) := by
  show Sum.elim (fun j : {j : S.MJ // j ≠ S.padJ} => Alg.eqk ρ.1 (S.memb.plc j))
    (fun _ => ρ.2.val * 1) (splitAt S.padJ (.inl (r, p))) = _
  unfold Sz.smpC
  by_cases hj : (Sum.inl (r, p) : S.MJ) = S.padJ
  · rw [hj, splitAt_self]
    have hj' : (r, p) = ((⟨S.P.R - 1, Nat.sub_lt S.hR Nat.one_pos⟩ : Fin S.P.R),
        (⟨S.P.C.l - 1, Nat.sub_lt S.hl Nat.one_pos⟩ : Fin S.P.C.l)) := Sum.inl.inj hj
    have h1 : r.val = S.P.R - 1 := congrArg (fun z => z.1.val) hj'
    have h2 : p.val = S.P.C.l - 1 := congrArg (fun z => z.2.val) hj'
    rw [if_pos (by rw [h1, h2]; rfl)]
    exact mul_one _
  · rw [show splitAt S.padJ (Sum.inl (r, p) : S.MJ) = Sum.inl ⟨_, hj⟩ from dif_neg hj, if_neg]
    · rfl
    · intro h
      obtain ⟨h1, h2⟩ := idx_inj S.P.aR (idx_facts S hl2 r p).1
        (idx_facts S hl2 ⟨S.P.R - 1, Nat.sub_lt S.hR Nat.one_pos⟩
          ⟨S.P.C.l - 1, Nat.sub_lt S.hl Nat.one_pos⟩).1 h
      exact hj (congrArg Sum.inl (Prod.ext (Fin.ext h1) (Fin.ext h2)))

/-- The target of the row of the first table's draw number i. -/
theorem tgX_first (S : Sz) (x : S.lk.X4) (i : Fin S.P.nu0) :
    tgX S x (3 + i.val) = x.1.2.1.2 i := by
  have h : 3 + i.val - 3 < S.P.nu0 := by
    have := i.isLt
    omega
  unfold tgX
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos h]
  exact congrArg _ (Fin.ext (by show 3 + i.val - 3 = i.val; omega))

/-- The target of the row of the copy's draw number i. -/
theorem tgX_further (S : Sz) (x : S.lk.X4) (i : Fin S.P.nuj) :
    tgX S x (3 + S.P.nu0 + i.val) = x.1.2.2.2 i := by
  have h : 3 + S.P.nu0 + i.val - 3 - S.P.nu0 < S.P.nuj := by
    have := i.isLt
    omega
  unfold tgX
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega), dif_pos h]
  exact congrArg _ (Fin.ext (by show 3 + S.P.nu0 + i.val - 3 - S.P.nu0 = i.val; omega))

/-- The coefficients of the row of the first table's draw number i. -/
theorem cfX_first (S : Sz) (x : S.lk.X4) (i : Fin S.P.nu0) (a : Bool) (r p : ℕ) :
    cfX S x (3 + i.val) a r p =
      if a then 0 else S.colC (x.1.2.1.1 i) (r * 2 ^ S.P.aP + p) := by
  have h : 3 + i.val - 3 < S.P.nu0 := by
    have := i.isLt
    omega
  have hi : (⟨3 + i.val - 3, h⟩ : Fin S.P.nu0) = i := Fin.ext (by show 3 + i.val - 3 = i.val; omega)
  unfold cfX
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos h, hi]

/-- The coefficients of the row of the copy's draw number i. -/
theorem cfX_further (S : Sz) (x : S.lk.X4) (i : Fin S.P.nuj) (a : Bool) (r p : ℕ) :
    cfX S x (3 + S.P.nu0 + i.val) a r p =
      if a then S.colC (x.1.2.2.1 i) (r * 2 ^ S.P.aP + p) else 0 := by
  have h : 3 + S.P.nu0 + i.val - 3 - S.P.nu0 < S.P.nuj := by
    have := i.isLt
    omega
  have hi : (⟨3 + S.P.nu0 + i.val - 3 - S.P.nu0, h⟩ : Fin S.P.nuj) = i :=
    Fin.ext (by show 3 + S.P.nu0 + i.val - 3 - S.P.nu0 = i.val; omega)
  unfold cfX
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega), dif_pos h, hi]

/-- The rows are the library's on each member's entries, whatever the statement. Asked: a row of the
code C has 2 ^ aP places. -/
theorem isRows_rowsX (S : Sz) (t : ℕ) (hl2 : S.P.C.l = 2 ^ S.P.aP) (x : S.lk.X4) :
    IsRows S t x (rowsX S t x).1 (rowsX S t x).2 := by
  have he : ∀ (r : Fin S.P.R) (p : Fin S.P.C.l),
      r.val * S.P.C.l + p.val = r.val * 2 ^ S.P.aP + p.val :=
    fun r p => congrArg (fun n => r.val * n + p.val) hl2
  refine ⟨fun _ _ => rfl, rfl, ?_, ?_, ?_, ?_, ?_, tgX_first S x, ?_, ?_, tgX_further S x,
    ?_, ?_⟩
  · rintro (⟨r, p⟩ | y)
    · show vsX S t x 0 (atJ S t false (.inl (r, p))) = _
      rw [vsX_atJ, layF_closed, he]
      rfl
    · exact y.1.elim
  · rintro (⟨r, p⟩ | y)
    · show vsX S t x 0 (atJ S t true (.inl (r, p))) = _
      rw [vsX_atJ, layF_closed, he]
      rfl
    · exact y.1.elim
  · intro a
    cases a <;> rfl
  · rintro a (⟨r, p⟩ | y)
    · show vsX S t x (1 + a.toNat) (atJ S t a (.inl (r, p))) = _
      rw [vsX_atJ, mat_closed S hl2]
      cases a <;> rfl
    · exact y.1.elim
  · rintro a (⟨r, p⟩ | y)
    · show vsX S t x (1 + a.toNat) (atJ S t (!a) (.inl (r, p))) = 0
      rw [vsX_atJ]
      cases a <;> rfl
    · exact y.1.elim
  · rintro i (⟨r, p⟩ | y)
    · show vsX S t x (3 + i.val) (atJ S t false (.inl (r, p))) = _
      rw [vsX_atJ, cfX_first, colF_closed, he]
      rfl
    · exact y.1.elim
  · rintro i (⟨r, p⟩ | y)
    · show vsX S t x (3 + i.val) (atJ S t true (.inl (r, p))) = 0
      rw [vsX_atJ, cfX_first]
      rfl
    · exact y.1.elim
  · rintro i (⟨r, p⟩ | y)
    · show vsX S t x (3 + S.P.nu0 + i.val) (atJ S t true (.inl (r, p))) = _
      rw [vsX_atJ, cfX_further, colF_closed, he]
      rfl
    · exact y.1.elim
  · rintro i (⟨r, p⟩ | y)
    · show vsX S t x (3 + S.P.nu0 + i.val) (atJ S t false (.inl (r, p))) = 0
      rw [vsX_atJ, cfX_further]
      rfl
    · exact y.1.elim

/-! ## The written rows are these rows -/

/-- A laid row's coefficient at any entry of the group's main table: the coefficient of one
member's form at the entry's index in that member's own table. -/
theorem vecIn_inl (S : Sz) (t : ℕ) (R : Fmt.M2.MRow)
    (β : Fin ((S.sg t).h + (S.sg t).g) → Bool) (p : Fin S.P.C.l) :
    vecIn (S.sg t) (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l R).toG (.inl (β, p)) =
      vec (R.main.getD (if 2 ^ S.P.aR ≤ Sz.rowNo β then 1 else 0) #[])
        (Sz.rowNo β % 2 ^ S.P.aR + 2 ^ S.P.aR * p.val) := by
  have hn : Sz.rowNo β < 2 ^ (S.P.aR + 1) :=
    lt_of_lt_of_eq (rowNo_lt β) (congrArg (fun n => 2 ^ n) (Nat.zero_add (S.P.aR + 1)))
  have hn2 : Sz.rowNo β < 2 ^ S.P.aR + 2 ^ S.P.aR := by
    rw [Nat.pow_succ] at hn
    omega
  show vec (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l R).c
    (Sz.rowNo β + 2 ^ (0 + (S.P.aR + 1)) * p.val) = _
  generalize Sz.rowNo β = n at hn hn2 ⊢
  rw [Nat.zero_add, vec_toK_c S.P S.hR, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hn, Nat.zero_add, if_pos]
  · by_cases h1 : n < 2 ^ S.P.aR
    · rw [if_pos h1, if_neg (by omega), Nat.mod_eq_of_lt h1]
    · rw [if_neg h1, if_pos (by omega), Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)]
  · calc n + 2 ^ (S.P.aR + 1) * p.val
        < 2 ^ (S.P.aR + 1) + 2 ^ (S.P.aR + 1) * p.val := Nat.add_lt_add_right hn _
      _ = 2 ^ (S.P.aR + 1) * (p.val + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ 2 ^ (S.P.aR + 1) * S.P.C.l := Nat.mul_le_mul_left _ p.isLt

/-- Row r, place p of a block lies within a member's table, also if the member has no row r. -/
theorem blk_facts (S : Sz) (hl2 : S.P.C.l = 2 ^ S.P.aP) (r : ℕ) (hr : r < 2 ^ S.P.aR)
    (p : Fin S.P.C.l) :
    r + 2 ^ S.P.aR * p.val < 2 ^ (S.P.aR + S.P.aP) ∧ r * 2 ^ S.P.aP + p.val < S.P.nTab := by
  have hp : p.val < 2 ^ S.P.aP := hl2 ▸ p.isLt
  refine ⟨?_, ?_⟩
  · calc r + 2 ^ S.P.aR * p.val < 2 ^ S.P.aR + 2 ^ S.P.aR * p.val := Nat.add_lt_add_right hr _
      _ = 2 ^ S.P.aR * (p.val + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ 2 ^ S.P.aR * 2 ^ S.P.aP := Nat.mul_le_mul_left _ hp
      _ = 2 ^ (S.P.aR + S.P.aP) := (Nat.pow_add 2 _ _).symm
  · show r * 2 ^ S.P.aP + p.val < 2 ^ (S.P.aR + S.P.aP)
    calc r * 2 ^ S.P.aP + p.val < r * 2 ^ S.P.aP + 2 ^ S.P.aP := Nat.add_lt_add_left hp _
      _ = (r + 1) * 2 ^ S.P.aP := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 2 ^ S.P.aR * 2 ^ S.P.aP := Nat.mul_le_mul_right _ hr
      _ = 2 ^ (S.P.aR + S.P.aP) := (Nat.pow_add 2 _ _).symm

/-- The written equality row's form on a member's table. -/
theorem vec_lay_eq (S : Sz) (hh : S.P.high = true) (hl2 : S.P.C.l = 2 ^ S.P.aP)
    (phi : List Fmt.M1.E) (hphi : phi.length = S.P.aPhi) (r : ℕ) (hr : r < 2 ^ S.P.aR)
    (p : Fin S.P.C.l) :
    vec (Fmt.M3.layHi S.P (Fmt.M3.eqVecG (Fmt.M1.opsOf .two) S.P.cut S.P.nTab phi))
        (r + 2 ^ S.P.aR * p.val) =
      S.eqC (fun u => lst phi u.val) (r * 2 ^ S.P.aP + p.val) := by
  obtain ⟨h1, h2⟩ := blk_facts S hl2 r hr p
  have hcut : S.P.cut ≤ 2 ^ S.P.aPhi :=
    le_trans (Nat.sub_le _ _) (le_two_pow_clog S.P.T.l)
  rw [vec_layHi, if_pos h1, hh, loAt_idx _ _ _ _ hr, vec_eqVec, if_pos h2, hphi]
  unfold Sz.eqC
  by_cases h3 : r * 2 ^ S.P.aP + p.val < S.P.cut
  · rw [if_pos h3, if_pos h3, if_pos (lt_of_lt_of_le h3 hcut)]
    rfl
  · rw [if_neg h3, if_neg h3]

/-- The form of a written draw's row on a member's table. -/
theorem vec_lay_col (S : Sz) (hh : S.P.high = true) (hl2 : S.P.C.l = 2 ^ S.P.aP) (x : S.Pos)
    (r : ℕ) (hr : r < 2 ^ S.P.aR) (p : Fin S.P.C.l) :
    vec (Fmt.M3.layHi S.P (Fmt.M3.colVecG (Fmt.M1.opsOf S.P.fld) S.P.t0 S.P.nTab
        ((Fmt.M1.genM S.P.T x.val).map Fmt.Fld.ofF) ((Fmt.M1.genT S.P.T x.val).map Fmt.Fld.ofF)))
        (r + 2 ^ S.P.aR * p.val) =
      S.colC x (r * 2 ^ S.P.aP + p.val) := by
  obtain ⟨h1, h2⟩ := blk_facts S hl2 r hr p
  rw [vec_layHi, if_pos h1, hh, loAt_idx _ _ _ _ hr, vec_colVec_gen, if_pos h2]
  rfl

/-- The form of a written sample row on its member's table. -/
theorem vec_smp (S : Sz) (hl2 : S.P.C.l = 2 ^ S.P.aP) (z : List Fmt.M1.E) (beta y : Fmt.M1.E)
    (β : GEˣ) (hz : S.P.aR + S.P.aP ≤ z.length) (hβ : toE beta = β.val) (i : ℕ)
    (hi : i < 2 ^ (S.P.aR + S.P.aP)) :
    vec (Fmt.M2.sampleOf .two S.P.C.l S.P.Z.l S.P.mem z beta y).1 i =
      S.smpC (fun u => lst z u.val, β) i := by
  have hp : Fmt.M2.padAt S.P.mem (S.P.C.l - 1) < 2 ^ mainBits S.P.C.l S.P.mem :=
    (idx_facts S hl2 ⟨S.P.R - 1, Nat.sub_lt S.hR Nat.one_pos⟩
      ⟨S.P.C.l - 1, Nat.sub_lt S.hl Nat.one_pos⟩).2.1
  have hpe : Fmt.M2.padAt S.P.mem (S.P.C.l - 1) = S.padIdx := rfl
  have hmb : mainBits S.P.C.l S.P.mem = S.P.aR + S.P.aP := rfl
  rw [vec_sampleOf_overE S.P.C.l S.P.Z.l S.P.mem z beta y i rfl rfl hz hp, hpe, hmb]
  unfold Sz.smpC
  by_cases h1 : i = S.padIdx
  · rw [if_pos h1, if_pos h1, hβ]
  · rw [if_neg h1, if_neg h1, if_pos hi]
    rfl

/-- A list of triples, read entry by entry. -/
private theorem getD_map_toE (l : List Fmt.M1.E) (i : ℕ) : (l.map toE).getD i 0 = lst l i := by
  unfold lst
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact toE_zeroE.symm
  | some a => rfl

section Lit
variable (S : Sz) (t e d : ℕ) (d1 d2 d3 d4 d5 dA : PQ.RD)

/-- The seed that the library's verifier holds is the seed that the decision reads. -/
theorem gSeed_rv (m2 : (wRound d2).Msg) (c2 : (wRound d2).Chal) (n : ℕ) :
    gSeed n _ (valsOf d2 c2) =
      (fun u : Fin n => lst ((rvOf d2 m2 c2).els.take n) u.val,
        unitOf (lst (rvOf d2 m2 c2).els n)) := by
  unfold gSeed
  rw [gVec_rv d2 m2 c2 n, ← rvOf_els d2 m2 c2, getD_map_toE]
  exact congrArg (fun f => (f, unitOf (lst (rvOf d2 m2 c2).els n)))
    (funext fun u => (lst_take n _ u.val u.isLt).symm)

end Lit

end OnBytes.Slice

#print axioms OnBytes.Slice.vsX_atJ
#print axioms OnBytes.Slice.layF_closed
#print axioms OnBytes.Slice.colF_closed
#print axioms OnBytes.Slice.mat_closed
#print axioms OnBytes.Slice.tgX_first
#print axioms OnBytes.Slice.tgX_further
#print axioms OnBytes.Slice.cfX_first
#print axioms OnBytes.Slice.cfX_further
#print axioms OnBytes.Slice.isRows_rowsX
#print axioms OnBytes.Slice.vecIn_inl
#print axioms OnBytes.Slice.blk_facts
#print axioms OnBytes.Slice.vec_lay_eq
#print axioms OnBytes.Slice.vec_lay_col
#print axioms OnBytes.Slice.vec_smp
#print axioms OnBytes.Slice.gSeed_rv
