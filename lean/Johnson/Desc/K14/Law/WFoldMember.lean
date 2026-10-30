--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/WFoldMember.lean: all the premises of w_is_the_committed_fold
(Johnson/Desc/K14/Law/WFold.lean) can be met together: they follow from five tests with code and
facts of a run, at a stored table that is a function of rows before encoding.

  wfold_member          applies w_is_the_committed_fold at tab := tabOfRows of the rows. The five:
                        foldRowsB (so NearAt), recAllB (so RecAll), dotUB (so DotUAt), recRowsB (so
                        the table decodes and no point is bad), visB (so the point is not lost for
                        the vector). Beside them: the eight blocks, the first block's yes with the
                        point that it drew, that the key fits, and sizes.
  wfold_member_tables   the same with the claim's weights and the vector as tables made once (gTabA,
                        vTabA): the terms that a sheet evaluates.

Why. A theorem whose premises nobody can meet says nothing. With this one, five evaluations at one
run's files and words show that the premises hold there.

What is not claimed. That the five tests say yes anywhere: that is an evaluation's word, outside
this file. That tabOfRows of the rows is the table beneath the key's root. Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.RowsB
import Johnson.Desc.K14.Law.DotUB
import Johnson.Desc.K14.Law.WFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K13.Law (EvalAt WIs matBy)

/-- A key that fits: each seed's point has the cube's bits. -/
theorem fits_z (key : TableKey) (s : IndexShape) (h : key.fits s = true) :
    ∀ a < s.answers, (key.seeds.getD a default).z.length = s.cubeBits := by
  intro a ha
  unfold TableKey.fits at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨_, hl⟩, hall⟩ := h
  have ha' : a < key.seeds.length := by omega
  have e : key.seeds.getD a default = key.seeds[a] := by
    simp [List.getD, ha']
  rw [e]
  exact hall _ (List.getElem_mem ha')

/-- **ALL THE PREMISES OF w_is_the_committed_fold, MET TOGETHER, FROM FIVE TESTS WITH CODE.** The
stored table is the function tabOfRows of rows RwF before encoding. m0, m1: the first and the shared
chain's words, as the program's elements. -/
theorem wfold_member (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (ha : P.par.S.fold.index.code.logN ≤ 32)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hk : P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell ≤
      2 ^ P.par.S.fold.index.code.logN)
    (hp : P.par.S.fold.index.plain + 3 * P.par.S.fold.index.answers =
      P.par.S.fold.index.code.ell)
    (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (he : eM + eM < 2 ^ P.par.S.fold.index.code.logN -
      (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) + 1)
    (RwF : Nat → Nat → UInt64)
    (s s' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (psi : Fin P.par.S.kCol → GE)
    (hyes : b1.decide s rs gs = .ok s')
    (hpsi : s'.loc.psiSh.map OnBytes.Model.Reading.gl.val = List.ofFn psi)
    (hfit : s.loc.key.fits P.par.S.fold.index = true)
    (D : EvalAt) (m0 m1 : Words E) (gE VE : Nat → E)
    (hV : ∀ c < 2 ^ P.par.S.kCol, VE c = m0 D.w .main (D.lay.index c))
    (hg : ∀ y < P.par.S.matrixRows, OnBytes.Model.Reading.gl.val (gE y) =
      (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hw : (weights P.par.S (withNext P.par s').loc).size = 2 ^ P.par.S.fold.index.v)
    (B1 : foldRowsB P.par (withNext P.par s') m1 (fun r k => OnBytes.ofF (RwF r k)) = true)
    (B2 : recAllB P.par (withNext P.par s') m1 = true)
    (B3 : dotUB P.par.S gE (withNext P.par s').loc m1 VE = true)
    (B4 : recRowsB P.par s.loc.key RwF = true)
    (B5 : visB P.par.S gE RwF VE = true) :
    WFold P.par err eM rank (tabOfRows P.par.S.fold RwF) s.loc.key D
      (wordsOf OnBytes.Model.Reading.gl m0) := by
  have hon := honest_tab P.par err eM eM rank (tabOfRows P.par.S.fold RwF) s.loc.key
    (rowsOf P.par.S.fold fun n k => OnBytes.Model.Reading.gl.val (OnBytes.ofF (RwF n k))) ha hk he
    (htab_of_cols P.par _ _ ha fun x _ n hn => tabOfRows_col P.par.S.fold RwF x n hn)
    (hrec_of_rows P.par err eM rank s.loc.key _ hp (fits_z _ _ hfit)
      (recRows_of_B P.par s.loc.key RwF B4))
  have hv : P.par.S.kCol = P.par.S.kLo + P.par.S.fold.index.v := rfl
  refine w_is_the_committed_fold P b1 b2 b3 b4 b5 b6 b7 b8 hbl ha err eM rank
    (tabOfRows P.par.S.fold RwF) s s' rs gs psi hyes hpsi hfit D
    (wordsOf OnBytes.Model.Reading.gl m0) (wordsOf OnBytes.Model.Reading.gl m1)
    (fun y => OnBytes.Model.Reading.gl.val (gE y))
    (fun c => OnBytes.Model.Reading.gl.val (VE c)) hg
    (fun c hc => (congrArg OnBytes.Model.Reading.gl.val (hV c hc)).symm)
    (hon.2.2 _) ?_ ?_ (recAll_of_B _ _ _ _ B2) (dotUAt_of_B _ _ _ _ _ B3)
  · intro hb
    refine hb.1 (vIs_of_B P.par.S gE RwF _ _ ?_ B5)
    intro c hc y hy
    have h2 : 0 < 2 ^ P.par.S.kLo := Nat.two_pow_pos _
    have hr : c / 2 ^ P.par.S.kLo < 2 ^ P.par.S.fold.index.v := by
      rw [hv, Nat.pow_add] at hc
      exact Nat.div_lt_of_lt_mul hc
    have hm : c % 2 ^ P.par.S.kLo < 2 ^ P.par.S.kLo := Nat.mod_lt _ h2
    have hkk : c % 2 ^ P.par.S.kLo + 2 ^ P.par.S.kLo * y < P.par.S.fold.index.code.ell := by
      have h3 : 2 ^ P.par.S.kLo * (y + 1) ≤ 2 ^ P.par.S.kLo * P.par.S.matrixRows :=
        Nat.mul_le_mul_left _ hy
      rw [Nat.mul_add, Nat.mul_one] at h3
      rw [Nat.mul_comm] at hroom
      omega
    rw [honest_TabX2 P.par err eM rank _ s.loc.key _ hon.1 _ _ hkk]
    unfold rowsOf full2
    rw [Fin.addCases_right, numOf_bitsOf _ _ hr]
  · refine nearAt_of_foldRowsB _ P.par (withNext P.par s') m1 _
      (fun r k => OnBytes.ofF (RwF r k)) ?_ B1 eM
    intro x _ r hr
    rw [hw] at hr
    exact tabOfRows_col P.par.S.fold RwF x r hr

/-- A table made once holds the function's values. -/
theorem tab_getD (f : Nat → E) (n k : Nat) (h : k < n) :
    ((Array.range n).map f).getD k zeroE = f k := by
  simp [Array.getD, h]

theorem val_foldl_add {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) : ∀ (l : List E) (a : E),
    ρ.val (l.foldl addE a) = ρ.val a + (l.map ρ.val).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, val_foldl_add ρ l, ρ.add, List.map_cons, List.sum_cons, add_assoc]

/-- The claim's weights on the matrix's rows, as a table. -/
def gTabA (S : LinShape) (D : EvalAt) : Array E :=
  (Array.range S.matrixRows).map fun y => (D.row.g.map fun t => t.entry y).foldl addE zeroE

/-- W's vector, as a table. -/
def vTabA (S : LinShape) (D : EvalAt) (m0 : Words E) : Array E :=
  (Array.range (2 ^ S.kCol)).map fun c => m0 D.w .main (D.lay.index c)

/-- **The same AT THE VERY TERMS THAT THE SHEET EVALUATES**: the claim's weights and W's vector as
tables made once. -/
theorem wfold_member_tables (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (ha : P.par.S.fold.index.code.logN ≤ 32)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hk : P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell ≤
      2 ^ P.par.S.fold.index.code.logN)
    (hp : P.par.S.fold.index.plain + 3 * P.par.S.fold.index.answers =
      P.par.S.fold.index.code.ell)
    (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (he : eM + eM < 2 ^ P.par.S.fold.index.code.logN -
      (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) + 1)
    (RwF : Nat → Nat → UInt64)
    (s s' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (psi : Fin P.par.S.kCol → GE)
    (hyes : b1.decide s rs gs = .ok s')
    (hpsi : s'.loc.psiSh.map OnBytes.Model.Reading.gl.val = List.ofFn psi)
    (hfit : s.loc.key.fits P.par.S.fold.index = true)
    (D : EvalAt) (m0 m1 : Words E)
    (hw : (weights P.par.S (withNext P.par s').loc).size = 2 ^ P.par.S.fold.index.v)
    (B1 : foldRowsB P.par (withNext P.par s') m1 (fun r k => OnBytes.ofF (RwF r k)) = true)
    (B2 : recAllB P.par (withNext P.par s') m1 = true)
    (B3 : dotUB P.par.S (fun y => (gTabA P.par.S D).getD y zeroE) (withNext P.par s').loc m1
      (fun c => (vTabA P.par.S D m0).getD c zeroE) = true)
    (B4 : recRowsB P.par s.loc.key RwF = true)
    (B5 : visB P.par.S (fun y => (gTabA P.par.S D).getD y zeroE) RwF
      (fun c => (vTabA P.par.S D m0).getD c zeroE) = true) :
    WFold P.par err eM rank (tabOfRows P.par.S.fold RwF) s.loc.key D
      (wordsOf OnBytes.Model.Reading.gl m0) := by
  refine wfold_member P b1 b2 b3 b4 b5 b6 b7 b8 hbl ha hroom hk hp err eM rank he RwF s s' rs gs
    psi hyes hpsi hfit D m0 m1 (fun y => (gTabA P.par.S D).getD y zeroE)
    (fun c => (vTabA P.par.S D m0).getD c zeroE) (fun c hc => tab_getD _ _ _ hc) ?_ hw B1 B2 B3 B4
    B5
  intro y hy
  show OnBytes.Model.Reading.gl.val ((gTabA P.par.S D).getD y zeroE) = _
  unfold gTabA
  rw [tab_getD _ _ _ hy, val_foldl_add, OnBytes.Model.Reading.gl.zero, zero_add, List.map_map]
  rfl

end Desc.K14.Law
