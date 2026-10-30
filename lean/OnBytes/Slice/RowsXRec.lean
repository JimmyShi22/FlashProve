-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RowsXRec.lean: the rows behind the written link for stored tables WITH A RECORD,
written out, as a function of the statement that the library's verifier holds after the link's five
rounds; they are the rows that OnBytes/Slice/BatSemRec.lean asks (`IsRowsR`).

OnBytes/Slice/RowsX.lean writes the link's rows out before the records' rows are added (`rowsX`) and
shows that they are the library's on each member's entries (`isRows_rowsX`). For each answer of a
row's sample there are two rows more: the record's row of the first table's fold and that of
the copy's. This file writes them out. The coefficient of such a row at entry e of the folded row is
the sample's matrix at the record's seed, the answer and e, if e is an entry of a row's message, and
0 from entry l on (`Sz.recC`); on the other member's block it is 0; the target is the fold of the
record's answers (the library's `LdIx.tgt`). The other rows are those of `rowsX`, moved by twice the
number s of answers. The numbers are those of `RowNo.port`. The answers are numbered by a bijection
num with the numbers below s. On the rows of a member's block that the member does not have, a
record's row is 0 if a row of C has 2 ^ aP places (an entry there has a number of at least R l_C,
which is at least l): a remark, no theorem.

Main definitions: `Sz.recC`, `Sz.forget`, `tgXR`, `cfXR`, `vsXR`, `rowsXR`.
Main theorems: `recF_closed` (the library's form of a record's row, by the number of an entry),
`isRowsR_rowsXR`.

What it is for. A guard: where a row of the code C has 2 ^ aP places, `IsRowsR` can be met at the
numbers of `RowNo.port`, at every sample map and every statement. And a form against which a
program's rows can be held entry by entry.

Not claimed. That any program's rows are these, in coefficients or in order: not here
(OnBytes/Slice/BlkRecRow.lean, BlkLinkRec.lean and BlkLinkJoinRec.lean show it of the program's
link). Nothing on soundness, on a decision, a file or a hash function.

-/
import OnBytes.Slice.RowsX
import OnBytes.Slice.BatSemRec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

namespace Sz
variable (S : Sz) (Z : Sample GE S.En)

/-- The coefficient of a record's row at entry e of a folded row: the sample's matrix at the seed ρ,
the answer σ and e, if e is an entry of a row's message; else 0. -/
def recC (ρ : Z.D) (σ : Z.S) (e : ℕ) : GE := if h : e < S.P.T.l then Z.mat ρ σ ⟨e, h⟩ else 0

/-- The statement after the link's five rounds without its two records. -/
def forget (x : (S.lkR Z).X4) : S.lk.X4 :=
  (((((S.rec0, S.rec0), x.1.1.1.2), x.1.1.2), x.1.2), x.2)

end Sz

/-- The library's form of a record's row, by the number of an entry. -/
theorem recF_closed (S : Sz) (Z : Sample GE S.En) (i : Bool) (σ : Z.S) (ρ : Z.D) (r : Fin S.P.R)
    (p : Fin S.P.C.l) :
    (S.lkR Z).recF i S.putAt σ ρ (.inl (r, p)) = S.recC Z ρ σ (r.val * S.P.C.l + p.val) := by
  have key : ∀ k : S.Co, S.putAt k = Sum.inl (r, p) ↔ S.entryOf k = r.val * S.P.C.l + p.val :=
    fun k => putAt_eq_iff S k r p
  have hent : ∀ j : S.En, S.entryOf ((S.lkR Z).D.X.pl j) = j.val := fun j => by
    show (if S.P.T.r + j.val < S.P.T.r then _ else S.P.T.r + j.val - S.P.T.r) = j.val
    rw [if_neg (by omega)]
    omega
  unfold Cb.LdLkP.recF Cb.Slf.push Sz.recC
  generalize r.val * S.P.C.l + p.val = e at key ⊢
  by_cases h1 : e < S.P.T.l
  · rw [dif_pos h1, Finset.sum_eq_single (⟨e, h1⟩ : S.En)]
    · rw [if_pos ((key _).2 (hent _))]
    · intro a _ ha
      refine if_neg fun h => ha (Fin.ext ?_)
      have h2 := (key _).1 h
      rw [hent] at h2
      exact h2
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dif_neg h1]
    refine Finset.sum_eq_zero fun a _ => if_neg fun h => h1 ?_
    have h2 := (key _).1 h
    rw [hent] at h2
    exact h2 ▸ a.isLt

section
variable (S : Sz) (Z : Sample GE S.En) (s : ℕ) (num : Z.S ≃ Fin s)

/-- The target of row number b: the fold of the first record's answer number b for b < s; of the
copy's record's answer number b - s for s ≤ b < 2 s; from 2 s on the target of `rowsX`'s row number
b - 2 s. -/
noncomputable def tgXR (x : (S.lkR Z).X4) (b : ℕ) : GE :=
  if h : b < s then (S.ixR Z).tgt x.1.1.1.1.1 x.1.1.1.2 (num.symm ⟨b, h⟩)
  else if h : b - s < s then (S.ixR Z).tgt x.1.1.1.1.2 x.1.1.1.2 (num.symm ⟨b - s, h⟩)
  else tgX S (S.forget Z x) (b - 2 * s)

/-- The coefficient of row number b at row r, place p of member a's block. -/
def cfXR (x : (S.lkR Z).X4) (b : ℕ) (a : Bool) (r p : ℕ) : GE :=
  if h : b < s then
    (if a then 0 else S.recC Z x.1.1.1.1.1.1 (num.symm ⟨b, h⟩) (r * 2 ^ S.P.aP + p))
  else if h : b - s < s then
    (if a then S.recC Z x.1.1.1.1.2.1 (num.symm ⟨b - s, h⟩) (r * 2 ^ S.P.aP + p) else 0)
  else cfX S (S.forget Z x) (b - 2 * s) a r p

/-- The vector of row number b on the group's tables, laid as `vsX` lays it. -/
def vsXR (t : ℕ) (x : (S.lkR Z).X4) (b : ℕ) : (S.sg t).cIn.J → GE
  | .inl y =>
    cfXR S Z s num x b (decide (2 ^ S.P.aR ≤ Sz.rowNo y.1)) (Sz.rowNo y.1 % 2 ^ S.P.aR) y.2.val
  | .inr _ => 0

/-- **The rows of the link with a record**, targets and vectors, as a function of the statement that
the library's verifier holds after the link's first five rounds. -/
noncomputable def rowsXR (t : ℕ) (x : (S.lkR Z).X4) :
    (ℕ → GE) × (ℕ → (S.sg t).cIn.J → GE) :=
  (tgXR S Z s num x, vsXR S Z s num t x)

/-- The vector of a row at an entry of a member. -/
theorem vsXR_atJ (t : ℕ) (x : (S.lkR Z).X4) (b : ℕ) (a : Bool) (r : Fin S.P.R)
    (p : Fin S.P.C.l) :
    vsXR S Z s num t x b (atJ S t a (.inl (r, p))) = cfXR S Z s num x b a r.val p.val := by
  have hr : r.val < 2 ^ S.P.aR := lt_of_lt_of_le r.isLt (le_two_pow_clog S.P.R)
  show cfXR S Z s num x b (decide (2 ^ S.P.aR ≤ Sz.rowNo (memRow S t a r.val)))
    (Sz.rowNo (memRow S t a r.val) % 2 ^ S.P.aR) p.val = _
  rw [rowNo_memRow S t a r.val hr]
  cases a
  · have h1 : S.blk false + r.val = r.val := Nat.zero_add _
    rw [h1, Nat.mod_eq_of_lt hr, decide_eq_false (by omega)]
  · have h1 : S.blk true + r.val = 2 ^ S.P.aR + r.val := rfl
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt hr, decide_eq_true (by omega)]

/-- From 2 s on the targets are those of `rowsX`. -/
theorem tgXR_old (x : (S.lkR Z).X4) (b k : ℕ) (hb : b = 2 * s + k) :
    tgXR S Z s num x b = tgX S (S.forget Z x) k := by
  subst hb
  unfold tgXR
  rw [dif_neg (by omega), dif_neg (by omega), show 2 * s + k - 2 * s = k from by omega]

/-- From 2 s on the vectors are those of `rowsX`. -/
theorem vsXR_old (t : ℕ) (x : (S.lkR Z).X4) (b k : ℕ) (hb : b = 2 * s + k) :
    vsXR S Z s num t x b = vsX S t (S.forget Z x) k := by
  subst hb
  funext j
  rcases j with y | y
  · show cfXR S Z s num x (2 * s + k) _ _ _ = cfX S (S.forget Z x) k _ _ _
    unfold cfXR
    rw [dif_neg (by omega), dif_neg (by omega), show 2 * s + k - 2 * s = k from by omega]
  · rfl

/-- The target of the first table's record's row of the answer σ. -/
theorem tgXR_lo (x : (S.lkR Z).X4) (σ : Z.S) (b : ℕ) (hb : b = (num σ).val) :
    tgXR S Z s num x b = (S.ixR Z).tgt x.1.1.1.1.1 x.1.1.1.2 σ := by
  subst hb
  unfold tgXR
  rw [dif_pos (num σ).isLt, Fin.eta, Equiv.symm_apply_apply]

/-- The target of the copy's record's row of the answer σ. -/
theorem tgXR_hi (x : (S.lkR Z).X4) (σ : Z.S) (b : ℕ) (hb : b = s + (num σ).val) :
    tgXR S Z s num x b = (S.ixR Z).tgt x.1.1.1.1.2 x.1.1.1.2 σ := by
  subst hb
  have hlt := (num σ).isLt
  have h : s + (num σ).val - s < s := by omega
  have hi : (⟨s + (num σ).val - s, h⟩ : Fin s) = num σ :=
    Fin.ext (by show s + (num σ).val - s = (num σ).val; omega)
  unfold tgXR
  rw [dif_neg (by omega), dif_pos h, hi, Equiv.symm_apply_apply]

/-- The coefficients of the first table's record's row of the answer σ. -/
theorem cfXR_lo (x : (S.lkR Z).X4) (σ : Z.S) (b : ℕ) (hb : b = (num σ).val) (a : Bool)
    (r p : ℕ) :
    cfXR S Z s num x b a r p =
      if a then 0 else S.recC Z x.1.1.1.1.1.1 σ (r * 2 ^ S.P.aP + p) := by
  subst hb
  unfold cfXR
  rw [dif_pos (num σ).isLt, Fin.eta, Equiv.symm_apply_apply]

/-- The coefficients of the copy's record's row of the answer σ. -/
theorem cfXR_hi (x : (S.lkR Z).X4) (σ : Z.S) (b : ℕ) (hb : b = s + (num σ).val) (a : Bool)
    (r p : ℕ) :
    cfXR S Z s num x b a r p =
      if a then S.recC Z x.1.1.1.1.2.1 σ (r * 2 ^ S.P.aP + p) else 0 := by
  subst hb
  have hlt := (num σ).isLt
  have h : s + (num σ).val - s < s := by omega
  have hi : (⟨s + (num σ).val - s, h⟩ : Fin s) = num σ :=
    Fin.ext (by show s + (num σ).val - s = (num σ).val; omega)
  unfold cfXR
  rw [dif_neg (by omega), dif_pos h, hi, Equiv.symm_apply_apply]

/-- **The rows are the library's on each member's entries, the record's rows among them**, whatever
the statement, at the numbers of `RowNo.port`. Asked: a row of the code C has 2 ^ aP places. -/
theorem isRowsR_rowsXR (t : ℕ) (hl2 : S.P.C.l = 2 ^ S.P.aP) (x : (S.lkR Z).X4) :
    IsRowsR S Z t (RowNo.port S Z s fun σ => num σ) x (rowsXR S Z s num t x).1
      (rowsXR S Z s num t x).2 := by
  have H := isRows_rowsX S t hl2 (S.forget Z x)
  have he : ∀ (r : Fin S.P.R) (p : Fin S.P.C.l),
      r.val * S.P.C.l + p.val = r.val * 2 ^ S.P.aP + p.val :=
    fun r p => congrArg (fun n => r.val * n + p.val) hl2
  have hsm : ∀ a : Bool, 2 * s + 1 + a.toNat = 2 * s + (1 + a.toNat) := fun a => by omega
  have hc0 : ∀ i : Fin S.P.nu0, 2 * s + 3 + i.val = 2 * s + (3 + i.val) := fun i => by omega
  have hc1 : ∀ i : Fin S.P.nuj, 2 * s + 3 + S.P.nu0 + i.val = 2 * s + (3 + S.P.nu0 + i.val) :=
    fun i => by omega
  have hlo : ∀ σ : Z.S, (if false = true then s else 0) + (num σ).val = (num σ).val :=
    fun σ => by simp
  have hhi : ∀ σ : Z.S, (if true = true then s else 0) + (num σ).val = s + (num σ).val :=
    fun σ => by simp
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (tgXR_old S Z s num x _ 0 rfl).trans H.eqT
  · exact fun j => (congrFun (vsXR_old S Z s num t x _ 0 rfl) _).trans (H.eq0 j)
  · exact fun j => (congrFun (vsXR_old S Z s num t x _ 0 rfl) _).trans (H.eq1 j)
  · exact fun a => (tgXR_old S Z s num x _ _ (hsm a)).trans (H.smT a)
  · exact fun a j => (congrFun (vsXR_old S Z s num t x _ _ (hsm a)) _).trans (H.smS a j)
  · exact fun a j => (congrFun (vsXR_old S Z s num t x _ _ (hsm a)) _).trans (H.smO a j)
  · exact fun i => (tgXR_old S Z s num x _ _ (hc0 i)).trans (H.c0T i)
  · exact fun i j => (congrFun (vsXR_old S Z s num t x _ _ (hc0 i)) _).trans (H.c0S i j)
  · exact fun i j => (congrFun (vsXR_old S Z s num t x _ _ (hc0 i)) _).trans (H.c0O i j)
  · exact fun i => (tgXR_old S Z s num x _ _ (hc1 i)).trans (H.c1T i)
  · exact fun i j => (congrFun (vsXR_old S Z s num t x _ _ (hc1 i)) _).trans (H.c1S i j)
  · exact fun i j => (congrFun (vsXR_old S Z s num t x _ _ (hc1 i)) _).trans (H.c1O i j)
  · exact fun σ => tgXR_lo S Z s num x σ _ (hlo σ)
  · rintro σ (⟨r, p⟩ | y)
    · show vsXR S Z s num t x _ (atJ S t false (.inl (r, p))) = _
      rw [vsXR_atJ, cfXR_lo S Z s num x σ ((RowNo.port S Z s fun σ => num σ).rc false σ)
        (hlo σ), recF_closed, he]
      rfl
    · exact y.1.elim
  · rintro σ (⟨r, p⟩ | y)
    · show vsXR S Z s num t x _ (atJ S t true (.inl (r, p))) = 0
      rw [vsXR_atJ, cfXR_lo S Z s num x σ ((RowNo.port S Z s fun σ => num σ).rc false σ) (hlo σ)]
      rfl
    · exact y.1.elim
  · exact fun σ => tgXR_hi S Z s num x σ _ (hhi σ)
  · rintro σ (⟨r, p⟩ | y)
    · show vsXR S Z s num t x _ (atJ S t true (.inl (r, p))) = _
      rw [vsXR_atJ, cfXR_hi S Z s num x σ ((RowNo.port S Z s fun σ => num σ).rc true σ)
        (hhi σ), recF_closed, he]
      rfl
    · exact y.1.elim
  · rintro σ (⟨r, p⟩ | y)
    · show vsXR S Z s num t x _ (atJ S t false (.inl (r, p))) = 0
      rw [vsXR_atJ, cfXR_hi S Z s num x σ ((RowNo.port S Z s fun σ => num σ).rc true σ) (hhi σ)]
      rfl
    · exact y.1.elim

end

end OnBytes.Slice
