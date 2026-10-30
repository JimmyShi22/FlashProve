-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkRec.lean: the rows of the program's link, the records' rows among them, in
the field.

OnBytes/Slice/BlkLink.lean shows that the equality, sample and column rows of the program's link
are the rows rowsX of OnBytes/Slice/RowsX.lean. Beside these the program puts aside, for each of
the two tables and each seed of its record, one row more (OnBytes/Slice/BlkRecRow.lean). This file
shows that the list of all rows in ONE ORDER (the first table's record's rows, the copy's, the
equality row, the two sample rows, the rows of the first table's draws, the copy's: the order of
RowNo.port, OnBytes/Slice/BatSemRec.lean) has the targets tgXR and the coefficients cfXR of
OnBytes/Slice/RowsXRec.lean, at the sample map recZ of one row (OnBytes/Slice/RecordRead.lean) and
with the answers numbered as they are. The order is part of the statement, not a result. What a run
yields enters as hypotheses, gathered in two bundles of hypotheses, XTieR and LinkRowsR, over XTie
and LinkRows of OnBytes/Slice/BlkLink.lean. It is general in the number s of answers.

The text of stmG_rowsXR is that of stmG_rowsX (OnBytes/Slice/BlkLink.lean), cut by a program: the
link over the format with a sample map, the records' rows, their number.

Main definitions.
 Sz.nRowsR   the number of rows: twice s more than `Sz.nRows`.
 XTieR       what ties the library's statement to what the program has drawn, received and holds in
             its two keys: XTie, the point of the fold, and that each key holds its record.
 LinkRowsR   what the program's rows are: LinkRows, and the calls that made the records' rows.
Main theorems.
 recRows_read  one table's record's rows: targets, coefficients, and 0 elsewhere.
 rows_cfXR     the list of the program's rows has the targets tgXR and the coefficients cfXR.
 stmG_rowsXR   a row on the group that is the sum of these rows under the powers of an element, read
               as a statement of the link's stage, is the combination sumStmR of the rows rowsXR at
               the numbers of RowNo.port.

Not claimed. That a run of the program's link meets XTieR and LinkRowsR, or that its test takes the
rows in in this order. Nothing on a folded row that is arranged row by row in the low digits.
Nothing on soundness.

-/
import OnBytes.Slice.BlkRecRow

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

/-- The number of the link's rows where a table's record has s answers: the number n of
RowNo.port. -/
def Sz.nRowsR (S : Sz) (s : ℕ) : ℕ := 2 * s + 3 + (S.P.nu0 + S.P.nuj)

/-- It is twice s more than `Sz.nRows`. -/
theorem Sz.nRowsR_eq (S : Sz) (s : ℕ) : S.nRowsR s = 2 * s + S.nRows := Nat.add_assoc _ _ _

/-- From 2 s on the coefficients are those of rowsX. -/
theorem cfXR_old (S : Sz) (Z : Sample GE S.En) (s : ℕ) (num : Z.S ≃ Fin s) (x : (S.lkR Z).X4)
    (b k : ℕ) (hb : b = 2 * s + k) (a : Bool) (r p : ℕ) :
    cfXR S Z s num x b a r p = cfX S (S.forget Z x) k a r p := by
  subst hb
  unfold cfXR
  rw [dif_neg (by omega), dif_neg (by omega), show 2 * s + k - 2 * s = k from by omega]

/-- What ties the statement that the library's verifier holds after the five rounds to what the
program has drawn and received and to its two keys. k0, k1: the keys of the first table and of the
copy. gamma: the point of the fold. The other letters are those of XTie. -/
structure XTieR (S : Sz) (lg s : ℕ) (x : (S.lkR (recZ S.P.T.l lg s)).X4)
    (Sf0 Sf1 : Params.FoldeqShape) (k0 k1 : TableKey) (gamma phi z : List E) (beta y0 y1 : E)
    (d0 d1 : List ℕ) (f0 f1 : ℕ → E) : Prop where
  old : XTie S (S.forget (recZ S.P.T.l lg s) x) phi z beta y0 y1 d0 d1 f0 f1
  len : gamma.length = S.P.v
  gamma : x.1.1.1.2 = readP S.P.v gamma
  key0 : KeyHasR S.P.v lg s Sf0.index k0 x.1.1.1.1.1
  key1 : KeyHasR S.P.v lg s Sf1.index k1 x.1.1.1.1.2

/-- What the rows of the program's link are. rc0, rc1: the rows of the two tables' records, made
seed by seed by the program's call. The other letters are those of LinkRows. -/
structure LinkRowsR (S : Sz) (Λ : Params.LinkShape) (Sf0 Sf1 : Params.FoldeqShape) (o0 o1 : ℕ)
    (k0 k1 : TableKey) (gamma phi z : List E) (beta y0 y1 : E) (d0 d1 : List ℕ) (f0 f1 : ℕ → E)
    (rc0 rc1 : List Row) (rE s0 s1 : Row) (rs0 rs1 : List Row) : Prop where
  old : LinkRows S Λ Sf0 Sf1 o0 o1 phi z beta y0 y1 d0 d1 f0 f1 rE s0 s1 rs0 rs1
  rec0 : (k0.seeds.zipIdx.mapM fun x =>
    foldeqRecordRow Sf0 x.1 k0.record x.2 (foldeqWeights gamma) ⟨o0, S.layU⟩) = some rc0
  rec1 : (k1.seeds.zipIdx.mapM fun x =>
    foldeqRecordRow Sf1 x.1 k1.record x.2 (foldeqWeights gamma) ⟨o1, S.layU⟩) = some rc1

/-- One table's record's rows: row number i has the library's fold of the record's answers as its
target, the coefficients Sz.recC on the table's folded row, and 0 on the main table of every other
oracle message. -/
theorem recRows_read (S : Sz) (Sf : Params.FoldeqShape) (lg s : ℕ) (key : TableKey)
    (gamma : List E) (o : ℕ) (rc : List Row) (rec : (S.ixR (recZ S.P.T.l lg s)).Rec)
    (hK : KeyHasR S.P.v lg s Sf.index key rec) (hg : gamma.length = S.P.v)
    (hc : codeOf Sf.index.code = S.P.T) (h3 : 3 * s ≤ S.P.T.l) (hl2 : S.P.C.l = 2 ^ S.P.aP)
    (h : (key.seeds.zipIdx.mapM fun x =>
      foldeqRecordRow Sf x.1 key.record x.2 (foldeqWeights gamma) ⟨o, S.layU⟩) = some rc) :
    rc.length = s ∧ ∀ i : Fin s,
      readE (rc.getD i.val default).target =
          (S.ixR (recZ S.P.T.l lg s)).tgt rec (readP S.P.v gamma) i ∧
        (∀ r p : ℕ, r < 2 ^ S.P.aR → p < 2 ^ S.P.aP →
          coefAt (rc.getD i.val default) o .main (r + 2 ^ S.P.aR * p) =
            S.recC (recZ S.P.T.l lg s) rec.1 i (r * 2 ^ S.P.aP + p)) ∧
        ∀ o' j, o' ≠ o → coefAt (rc.getD i.val default) o' .main j = 0 := by
  obtain ⟨h1, h2⟩ := recRows_getD Sf key _ _ rc h
  refine ⟨h1.trans hK.seeds_length, fun i => ?_⟩
  obtain ⟨hl, hz, hβ⟩ := hK.seed_at i
  have hrow := h2 i.val (by rw [hl]; exact i.isLt)
  refine ⟨recRow_target S Sf lg s key _ i gamma _ _ rec hK hg hrow, fun r p hr hp => ?_,
    fun o' j ho => coefAt_recRow_else _ _ _ _ _ _ _ hrow o' .main j fun hh => ho hh.1⟩
  exact coefAt_recRow S Sf lg s _ key.record i _ ⟨o, S.layU⟩ _ (congrArg (·.l) hc) hK.answers h3
    hl2 rfl rec.1 hz hβ hrow r p hr hp

/-- **The rows of the program's link are the rows of rowsXR.** Row number b of the list that begins
with the first table's record's rows, goes on with the copy's, the equality row and the two sample
rows, and ends with the rows of the first and of the second table's draws has the target tgXR and,
at row r, place p of member a's table, the coefficient cfXR. -/
theorem rows_cfXR (S : Sz) (lg s : ℕ) (Λ : Params.LinkShape) (Sf0 Sf1 : Params.FoldeqShape)
    (o0 o1 : ℕ) (hne : o0 ≠ o1) (x : (S.lkR (recZ S.P.T.l lg s)).X4) (k0 k1 : TableKey)
    (gamma phi z : List E) (beta y0 y1 : E) (d0 d1 : List ℕ) (f0 f1 : ℕ → E)
    (rc0 rc1 : List Row) (rE s0 s1 : Row) (rs0 rs1 : List Row) (hF : LinkFit S Λ Sf0 Sf1)
    (h3 : 3 * s ≤ S.P.T.l)
    (hx : XTieR S lg s x Sf0 Sf1 k0 k1 gamma phi z beta y0 y1 d0 d1 f0 f1)
    (hR : LinkRowsR S Λ Sf0 Sf1 o0 o1 k0 k1 gamma phi z beta y0 y1 d0 d1 f0 f1 rc0 rc1 rE s0 s1
      rs0 rs1) (b : ℕ) (hb : b < S.nRowsR s) :
    readE ((rc0 ++ (rc1 ++ rE :: s0 :: s1 :: (rs0 ++ rs1))).getD b default).target =
        tgXR S (recZ S.P.T.l lg s) s (Equiv.refl (Fin s)) x b ∧
      ∀ (a : Bool) (r p : ℕ), r < 2 ^ S.P.aR → p < 2 ^ S.P.aP →
        coefAt ((rc0 ++ (rc1 ++ rE :: s0 :: s1 :: (rs0 ++ rs1))).getD b default)
          (if a then o1 else o0) .main (r + 2 ^ S.P.aR * p) =
          cfXR S (recZ S.P.T.l lg s) s (Equiv.refl (Fin s)) x b a r p := by
  obtain ⟨l0, r0⟩ := recRows_read S Sf0 lg s k0 gamma o0 rc0 x.1.1.1.1.1 hx.key0 hx.len hF.code0
    h3 hF.pow hR.rec0
  obtain ⟨l1, r1⟩ := recRows_read S Sf1 lg s k1 gamma o1 rc1 x.1.1.1.1.2 hx.key1 hx.len hF.code1
    h3 hF.pow hR.rec1
  by_cases hb0 : b < s
  · -- a row of the first table's record
    have hg : (rc0 ++ (rc1 ++ rE :: s0 :: s1 :: (rs0 ++ rs1))).getD b default =
        rc0.getD b default := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [l0]; exact hb0)]
    obtain ⟨t0, c0, z0⟩ := r0 ⟨b, hb0⟩
    rw [hg]
    refine ⟨?_, fun a r p hr hp => ?_⟩
    · rw [tgXR_lo S _ s (Equiv.refl (Fin s)) x ⟨b, hb0⟩ b rfl, hx.gamma]
      exact t0
    · rw [cfXR_lo S _ s (Equiv.refl (Fin s)) x ⟨b, hb0⟩ b rfl]
      cases a
      · exact c0 r p hr hp
      · exact z0 o1 _ (Ne.symm hne)
  · by_cases hb1 : b - s < s
    · -- a row of the copy's record
      have hg : (rc0 ++ (rc1 ++ rE :: s0 :: s1 :: (rs0 ++ rs1))).getD b default =
          rc1.getD (b - s) default := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [l0]; omega), l0,
          List.getElem?_append_left (by rw [l1]; exact hb1)]
      obtain ⟨t1, c1, z1⟩ := r1 ⟨b - s, hb1⟩
      have eb : b = s + (b - s) := by omega
      rw [hg]
      refine ⟨?_, fun a r p hr hp => ?_⟩
      · rw [tgXR_hi S _ s (Equiv.refl (Fin s)) x ⟨b - s, hb1⟩ b eb, hx.gamma]
        exact t1
      · rw [cfXR_hi S _ s (Equiv.refl (Fin s)) x ⟨b - s, hb1⟩ b eb]
        cases a
        · exact z1 o0 _ hne
        · exact c1 r p hr hp
    · -- a row of `rowsX`
      have hg : (rc0 ++ (rc1 ++ rE :: s0 :: s1 :: (rs0 ++ rs1))).getD b default =
          (rE :: s0 :: s1 :: (rs0 ++ rs1)).getD (b - 2 * s) default := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [l0]; omega), l0,
          List.getElem?_append_right (by rw [l1]; omega), l1,
          show b - s - s = b - 2 * s from by omega]
      have eb : b = 2 * s + (b - 2 * s) := by omega
      have hk : b - 2 * s < S.nRows := by
        rw [Sz.nRowsR_eq] at hb
        omega
      obtain ⟨t2, c2⟩ := rows_cfX S Λ Sf0 Sf1 o0 o1 hne _ phi z beta y0 y1 d0 d1 f0 f1 rE s0 s1 rs0
        rs1 hF hx.old hR.old (b - 2 * s) hk
      rw [hg]
      refine ⟨?_, fun a r p hr hp => ?_⟩
      · rw [tgXR_old S _ s (Equiv.refl (Fin s)) x b _ eb]
        exact t2
      · rw [cfXR_old S _ s (Equiv.refl (Fin s)) x b _ eb]
        exact c2 a r p hr hp

/-- The combined row, as a statement. G: a row on the group. If its target and its
coefficients are the sums of the rows' under the powers of θ, each member's table being in its
block of the group's main table, and if it is 0 on the one row of the group's mask table, then G,
read as a statement of the link's stage, is the combination sumStmR of the rows of rowsXR, at the
numbers of RowNo.port. General in the sample map Z and in the numbering num of its answers. -/
theorem stmG_rowsXR (S : Sz) (Z : Sample GE S.En) (s : ℕ) (num : Z.S ≃ Fin s) (t : ℕ)
    (hl2 : S.P.C.l = 2 ^ S.P.aP) (x : (S.lkR Z).X4) (rows : List Row) (o0 o1 : ℕ) (θ : GE)
    (G : GroupRow)
    (hrows : ∀ b, b < S.nRowsR s →
      readE (rows.getD b default).target = tgXR S Z s num x b ∧
      ∀ (a : Bool) (r p : ℕ), r < 2 ^ S.P.aR → p < 2 ^ S.P.aP →
        coefAt (rows.getD b default) (if a then o1 else o0) .main (r + 2 ^ S.P.aR * p) =
          cfXR S Z s num x b a r p)
    (hT : readE G.target =
      ∑ b ∈ Finset.range (S.nRowsR s), θ ^ b * readE (rows.getD b default).target)
    (hc : ∀ (a : Bool) (r p : ℕ), r < 2 ^ S.P.aR → p < 2 ^ S.P.aP →
      formAt G.c (S.blk a + r + 2 ^ (S.P.aR + 1) * p) = ∑ b ∈ Finset.range (S.nRowsR s),
        θ ^ b * coefAt (rows.getD b default) (if a then o1 else o0) .main (r + 2 ^ S.P.aR * p))
    (hd : ∀ i, i < S.P.Z.l → readV G.d i = 0) :
    stmG (S.sg t) G = sumStmR (RowNo.port S Z s fun σ => num σ) t (rowsXR S Z s num t x).1
      (rowsXR S Z s num t x).2 θ := by
  unfold stmG sumStmR
  refine Prod.ext ?_ (funext fun j => ?_)
  · show readE G.target = ∑ b : Fin (S.nRowsR s), θ ^ b.val * tgXR S Z s num x b.val
    rw [hT, Finset.sum_range]
    exact Finset.sum_congr rfl fun b _ => by rw [(hrows b.val b.isLt).1]
  · rcases j with ⟨β, p⟩ | j'
    · have hn : Sz.rowNo β < 2 ^ (S.P.aR + 1) :=
        lt_of_lt_of_eq (rowNo_lt β) (congrArg (fun n => 2 ^ n) (Nat.zero_add (S.P.aR + 1)))
      have hp : p.val < 2 ^ S.P.aP := hl2 ▸ p.isLt
      have hr : Sz.rowNo β % 2 ^ S.P.aR < 2 ^ S.P.aR := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hsplit : S.blk (decide (2 ^ S.P.aR ≤ Sz.rowNo β)) + Sz.rowNo β % 2 ^ S.P.aR =
          Sz.rowNo β := by
        rw [Nat.pow_succ] at hn
        by_cases h1 : 2 ^ S.P.aR ≤ Sz.rowNo β
        · rw [decide_eq_true h1, Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
          show 2 ^ S.P.aR + _ = _
          omega
        · rw [decide_eq_false h1, Nat.mod_eq_of_lt (by omega)]
          exact Nat.zero_add _
      show formAt G.c (Sz.rowNo β + 2 ^ (0 + (S.P.aR + 1)) * p.val) =
        ∑ b : Fin (S.nRowsR s), cfXR S Z s num x b.val (decide (2 ^ S.P.aR ≤ Sz.rowNo β))
          (Sz.rowNo β % 2 ^ S.P.aR) p.val * θ ^ b.val
      have h2 := hc (decide (2 ^ S.P.aR ≤ Sz.rowNo β)) (Sz.rowNo β % 2 ^ S.P.aR) p.val hr hp
      rw [hsplit] at h2
      have e0 : (0 + (S.P.aR + 1)) = S.P.aR + 1 := Nat.zero_add _
      generalize Sz.rowNo β = n at h2 hr ⊢
      rw [e0, h2, Finset.sum_range]
      exact Finset.sum_congr rfl fun b _ => by
        rw [(hrows b.val b.isLt).2 _ _ _ hr hp, mul_comm]
    · have h0 : Sz.rowNo j'.1 = 0 := Nat.lt_one_iff.1 (rowNo_lt j'.1)
      show readV G.d (Sz.rowNo j'.1 + 2 ^ 0 * j'.2.val) =
        ∑ b : Fin (S.nRowsR s), (0 : GE) * θ ^ b.val
      rw [h0, Nat.zero_add, pow_zero, Nat.one_mul, hd _ j'.2.isLt]
      simp

end OnBytes.Slice
