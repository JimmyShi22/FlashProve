-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontCols.lean: THE LINK's FIRST TREE, WRITTEN, AND READ BACK. The tree that
goes out in the link's second round holds three oracle messages: the first table's fold (R rows),
the copy's (R rows), and one further row under the mask code. Definitions, statements and proofs.

  firstSyms, firstColW   the written column at a position x: the R symbols of the first member's
                         rows, the R of the second's, the further row's at x modulo its code's
                         length; each symbol written (ofE of symG, Johnson/Prover/Link/Base.lean)
  length_firstColW       3 (2 R + 1) words
  rho0                   the tails on the group's rows: a member's rows' tails on its block's real
                         rows; 0 on the rows that no member has; 0 on the carried mask row
  wordIn_first           where every column of the written oracle is firstColW: the word that the
                         library reads off the first tree (wordIn s (col1 S d orc),
                         OnBytes/Slice/SemLib.lean) IS the group's code word of (μ, ρ), for μ and ρ
                         that hold the members' rows and tails on their blocks and 0 elsewhere
  wordFr_first           and wordFr s (col1 S d orc) is the further row's code word
  membN, wordIn_front    the same at this folder's own terms: μ := mu0 S t m (FrontMsg.lean),
                         ρ := rho0 S t tN, the rows' messages read off m
  lt_firstColW           every word of the column is below the prime, in viewWordsBelowPrime's form

By: the library's groupCol_inv | groupCol_zero | groupCol_isSome (OnBytes/Slice/BlkColumns.lean,
GroupColSome.lean) and enc_ldOf | enc_ldRep (Johnson/Prover/Link/SymTie.lean).
Three premises on the format's layout of two equal members (hst, hf, hk) are left as letters, as in
the library's own lemmas; at the full size: fr_groupFacts (OnBytes/Slice/FullRecBlkFacts.lean).

Not shown here. That a strategy's oracle has these columns. Nothing on a decision; nothing on
soundness; nothing on what any row is for, or on what any entry discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FrontMsg
import Johnson.Prover.Link.SymTie
import OnBytes.Slice.SemLib
import OnBytes.Slice.GroupColSome

set_option autoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb _root_.Run
open VerifiableInference.Desc (fieldPrimeWord)

variable (S : Sz) (mN tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE)

/-- The symbols of the first tree's column at x. -/
def firstSyms (x : ℕ) : List Fmt.M1.E :=
  wr S.P.R (fun i => symG S.P.C x (mN false i) (tN false i)) ++
    (wr S.P.R (fun i => symG S.P.C x (mN true i) (tN true i)) ++
      [ofE (symG S.P.Z (x % 2 ^ S.P.Z.a) φN ψN)])

/-- **The written column.** -/
def firstColW (x : ℕ) : List UInt64 := wordsOf (firstSyms S mN tN φN ψN x)

theorem length_firstSyms (x : ℕ) : (firstSyms S mN tN φN ψN x).length = S.P.R + (S.P.R + 1) := by
  unfold firstSyms
  rw [List.length_append, List.length_append, length_wr, length_wr]
  rfl

theorem length_firstColW (x : ℕ) :
    (firstColW S mN tN φN ψN x).length = 3 * (S.P.R + (S.P.R + 1)) := by
  unfold firstColW
  rw [length_wordsOf, length_firstSyms]

theorem sym_first0 (x i : ℕ) (hi : i < S.P.R) :
    toE (sym3 (firstColW S mN tN φN ψN x) (3 * i)) = symG S.P.C x (mN false i) (tN false i) := by
  unfold firstColW
  rw [sym3_wordsOf _ i (by rw [length_firstSyms]; omega)]
  unfold firstSyms
  rw [List.getD_append _ _ _ _ (by rw [length_wr]; exact hi)]
  exact lst_wr S.P.R _ i hi

theorem sym_first1 (x i : ℕ) (hi : i < S.P.R) :
    toE (sym3 (firstColW S mN tN φN ψN x) (3 * (S.P.R + i))) =
      symG S.P.C x (mN true i) (tN true i) := by
  unfold firstColW
  rw [sym3_wordsOf _ (S.P.R + i) (by rw [length_firstSyms]; omega)]
  unfold firstSyms
  rw [List.getD_append_right _ _ _ _ (by rw [length_wr]; omega), length_wr,
    Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by rw [length_wr]; exact hi)]
  exact lst_wr S.P.R _ i hi

theorem sym_firstF (x : ℕ) :
    toE (sym3 (firstColW S mN tN φN ψN x) (3 * (S.P.R + S.P.R))) =
      symG S.P.Z (x % 2 ^ S.P.Z.a) φN ψN := by
  unfold firstColW
  rw [sym3_wordsOf _ (S.P.R + S.P.R) (by rw [length_firstSyms]; omega)]
  unfold firstSyms
  rw [List.getD_append_right _ _ _ _ (by rw [length_wr]; omega), length_wr,
    Nat.add_sub_cancel_left, List.getD_append_right _ _ _ _ (by rw [length_wr]), length_wr,
    Nat.sub_self]
  exact toE_ofE _

theorem lt_firstColW (x : ℕ) : ∀ w ∈ firstColW S mN tN φN ψN x, w < fieldPrimeWord := by
  refine lt_wordsOf_wr _ fun e he => ?_
  unfold firstSyms at he
  rcases List.mem_append.1 he with h | h
  · exact mem_wr _ _ e h
  rcases List.mem_append.1 h with h | h
  · exact mem_wr _ _ e h
  · exact ⟨_, List.mem_singleton.1 h⟩

/-- **The tails on the group's rows.** A member's rows' tails on its block's real rows; THE WRITTEN
0 on the rows that no member has and on the carried mask row. -/
def rho0 (t : ℕ) (tl : Bool → ℕ → ℕ → GE) : (S.sg t).cIn.Q → GE
  | .inl x =>
    if Sz.rowNo x.1 % 2 ^ S.P.aR < S.P.R then
      tl (decide (2 ^ S.P.aR ≤ Sz.rowNo x.1)) (Sz.rowNo x.1 % 2 ^ S.P.aR) x.2.val
    else 0
  | .inr _ => 0

variable {S mN tN φN ψN}

/-- The column is cut, and col1 is the cut. -/
theorem col1_first (d : PQ.RD) (orc : (wRound d).Orc) (x : ℕ)
    (hcol : colW d orc x = firstColW S mN tN φN ψN x) :
    ∃ kc, Fmt.M2.groupCol [S.P.mem, S.P.mem] 1 (firstColW S mN tN φN ψN x) = some kc ∧
      col1 S d orc x = kc.col := by
  have hw : (firstColW S mN tN φN ψN x).length = Fmt.M2.widthOf [S.P.mem, S.P.mem] 1 := by
    have hdeg : Fmt.M2.degsOf [S.P.mem, S.P.mem] = List.replicate (S.P.R + S.P.R) true := by
      show List.replicate S.P.R true ++ (List.replicate S.P.R true ++ []) = _
      rw [List.append_nil, List.replicate_append_replicate]
    have hsum : ([S.P.mem, S.P.mem].map (·.masks)).sum = 0 := rfl
    rw [length_firstColW]
    unfold Fmt.M2.widthOf
    rw [hdeg, hsum, List.map_replicate, List.sum_replicate]
    simp only [if_true, smul_eq_mul]
    omega
  obtain ⟨kc, hkc⟩ := Option.isSome_iff_exists.1 (groupCol_isSome _ 1 _ hw)
  refine ⟨kc, hkc, ?_⟩
  unfold col1
  rw [hcol]
  show ((Fmt.M2.groupCol [S.P.mem, S.P.mem] 1 _).map (·.col)).getD default = _
  rw [hkc]
  rfl

/-- Every vertex of the group's rows is a row of a member's block. -/
theorem vertex_memRow (t : ℕ) (b : Fin ((S.sg t).h + (S.sg t).g) → Bool) :
    b = memRow S t (decide (2 ^ S.P.aR ≤ Sz.rowNo b)) (Sz.rowNo b % 2 ^ S.P.aR) := by
  have hp : 0 < 2 ^ S.P.aR := Nat.pos_of_ne_zero (by positivity)
  have hlt : Sz.rowNo b < 2 ^ S.P.aR * 2 :=
    lt_of_lt_of_eq (rowNo_lt b) (by
      show 2 ^ (0 + (S.P.aR + 1)) = _
      rw [Nat.zero_add, Nat.pow_succ])
  refine rowNo_inj ?_
  rw [rowNo_memRow S t _ _ (Nat.mod_lt _ hp)]
  by_cases c : 2 ^ S.P.aR ≤ Sz.rowNo b
  · rw [decide_eq_true c]
    show _ = 2 ^ S.P.aR + _
    have : Sz.rowNo b % 2 ^ S.P.aR = Sz.rowNo b - 2 ^ S.P.aR := by
      rw [Nat.mod_eq_sub_mod c, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [decide_eq_false c]
    show _ = 0 + _
    have : Sz.rowNo b % 2 ^ S.P.aR = Sz.rowNo b := Nat.mod_eq_of_lt (by omega)
    omega

theorem symG_zero (C : Fmt.M1.Code) (x : ℕ) : symG C x (fun _ => 0) (fun _ => 0) = 0 := by
  simp [symG]

/-- **The word that the library reads off the first tree is the group's code word.** -/
theorem wordIn_first (t : ℕ) (d : PQ.RD) (orc : (wRound d).Orc) (μ : (S.sg t).cIn.J → GE)
    (ρ : (S.sg t).cIn.Q → GE)
    (hst : (Fmt.M2.starts [S.P.mem, S.P.mem]).1 = [some 0, some (2 ^ S.P.aR)])
    (hk : 2 ^ S.P.aR + S.P.R ≤ 2 ^ Fmt.M2.kOf [S.P.mem, S.P.mem])
    (hμ : ∀ a i, i < S.P.R → ∀ j, μ (.inl (memRow S t a i, j)) = mN a i j.val)
    (hμz : FreeZero S t μ) (hμm : ∀ j, μ (.inr j) = 0)
    (hρ : ∀ a i, i < S.P.R → ∀ q, ρ (.inl (memRow S t a i, q)) = tN a i q.val)
    (hρz : ∀ a i q, S.P.R ≤ i → i < 2 ^ S.P.aR → ρ (.inl (memRow S t a i, q)) = 0)
    (hρm : ∀ q, ρ (.inr q) = 0)
    (hcol : ∀ x, x < 2 ^ S.P.C.a → colW d orc x = firstColW S mN tN φN ψN x) :
    wordIn (S.sg t) (col1 S d orc) = (S.sg t).cIn.enc μ ρ := by
  have hR : S.P.R ≤ 2 ^ S.P.aR := le_two_pow_clog S.P.R
  have hp : 0 < 2 ^ S.P.aR := Nat.pos_of_ne_zero (by positivity)
  funext p
  rcases p with x | x
  · funext a
    obtain ⟨b, ⟨⟩⟩ := a
    obtain ⟨kc, hkc, hc⟩ := col1_first d orc x.val (hcol x.val x.isLt)
    obtain ⟨g1, g2, -, -⟩ := groupCol_inv S.P.mem rfl rfl (2 ^ S.P.aR) hst hR hk _ kc hkc
    show vec (col1 S d orc x.val).main (Sz.rowNo b) =
      (ldOf S.P.C S.P.C.a).enc (fun j => μ (.inl (b, j))) (fun q => ρ (.inl (b, q))) x ()
    rw [hc]
    have hb := vertex_memRow t b
    have hi : Sz.rowNo b % 2 ^ S.P.aR < 2 ^ S.P.aR := Nat.mod_lt _ hp
    have hn : Sz.rowNo b = S.blk (decide (2 ^ S.P.aR ≤ Sz.rowNo b)) + Sz.rowNo b % 2 ^ S.P.aR := by
      conv_lhs => rw [hb]
      exact rowNo_memRow S t _ _ hi
    by_cases c : Sz.rowNo b % 2 ^ S.P.aR < S.P.R
    · have e1 : (fun j => μ (.inl (b, j))) =
          fun j : Fin S.P.C.l => mN (decide (2 ^ S.P.aR ≤ Sz.rowNo b))
            (Sz.rowNo b % 2 ^ S.P.aR) j.val := funext fun j => by
        conv_lhs => rw [hb]
        exact hμ _ _ c j
      have e2 : (fun q => ρ (.inl (b, q))) =
          fun q : Fin S.P.C.r => tN (decide (2 ^ S.P.aR ≤ Sz.rowNo b))
            (Sz.rowNo b % 2 ^ S.P.aR) q.val := funext fun q => by
        conv_lhs => rw [hb]
        exact hρ _ _ c q
      rw [e1, e2, enc_ldOf S.P.C S.P.C.a x]
      by_cases c2 : 2 ^ S.P.aR ≤ Sz.rowNo b
      · rw [decide_eq_true c2] at hn ⊢
        have hn2 : Sz.rowNo b = 2 ^ S.P.aR + Sz.rowNo b % 2 ^ S.P.aR := hn
        conv_lhs => rw [hn2]
        exact (g2 _ c).trans (sym_first1 S mN tN φN ψN x.val _ c)
      · rw [decide_eq_false c2] at hn ⊢
        have hn2 : Sz.rowNo b = Sz.rowNo b % 2 ^ S.P.aR := hn.trans (Nat.zero_add _)
        conv_lhs => rw [hn2]
        exact (g1 _ c).trans (sym_first0 S mN tN φN ψN x.val _ c)
    · have e1 : (fun j => μ (.inl (b, j))) = fun j : Fin S.P.C.l => (fun _ : ℕ => (0 : GE)) j.val :=
        funext fun j => by
          conv_lhs => rw [hb]
          exact hμz _ _ j (Nat.le_of_not_lt c) hi
      have e2 : (fun q => ρ (.inl (b, q))) = fun q : Fin S.P.C.r => (fun _ : ℕ => (0 : GE)) q.val :=
        funext fun q => by
          conv_lhs => rw [hb]
          exact hρz _ _ q (Nat.le_of_not_lt c) hi
      rw [e1, e2]
      refine Eq.trans ?_ ((enc_ldOf S.P.C S.P.C.a x (fun _ => 0) (fun _ => 0)).trans
        (symG_zero _ _)).symm
      refine groupCol_zero S.P.mem rfl rfl (2 ^ S.P.aR) hst _ kc hkc _ ?_ ?_
      · show S.P.R ≤ Sz.rowNo b
        rw [hn]; omega
      · by_cases c2 : 2 ^ S.P.aR ≤ Sz.rowNo b
        · refine Or.inr ?_
          show 2 ^ S.P.aR + S.P.R ≤ Sz.rowNo b
          rw [hn, decide_eq_true c2]
          show _ ≤ 2 ^ S.P.aR + _
          omega
        · exact Or.inl (Nat.lt_of_not_le c2)
  · funext a
    obtain ⟨b, ⟨⟩⟩ := a
    obtain ⟨kc, hkc, hc⟩ := col1_first d orc x.val (hcol x.val x.isLt)
    obtain ⟨-, -, g3, -⟩ := groupCol_inv S.P.mem rfl rfl (2 ^ S.P.aR) hst hR hk _ kc hkc
    show vec (col1 S d orc x.val).mask (Sz.rowNo b) =
      (ldRep S.P.Z S.P.C.a).enc (fun j => μ (.inr (b, j))) (fun q => ρ (.inr (b, q))) x ()
    have e1 : (fun j => μ (.inr (b, j))) = fun j : Fin S.P.Z.l => (fun _ : ℕ => (0 : GE)) j.val :=
      funext fun j => hμm _
    have e2 : (fun q => ρ (.inr (b, q))) = fun q : Fin S.P.Z.r => (fun _ : ℕ => (0 : GE)) q.val :=
      funext fun q => hρm _
    rw [hc, e1, e2]
    exact (g3 _).trans ((enc_ldRep S.P.Z S.P.C.a x (fun _ => 0) (fun _ => 0)).trans
      (symG_zero _ _)).symm

/-- **And the further row's code word.** -/
theorem wordFr_first (t : ℕ) (d : PQ.RD) (orc : (wRound d).Orc) (φ : (S.sg t).cFr.J → GE)
    (ψ : (S.sg t).cFr.Q → GE)
    (hst : (Fmt.M2.starts [S.P.mem, S.P.mem]).1 = [some 0, some (2 ^ S.P.aR)])
    (hk : 2 ^ S.P.aR + S.P.R ≤ 2 ^ Fmt.M2.kOf [S.P.mem, S.P.mem])
    (hφ : ∀ b j, φ (b, j) = φN j.val) (hψ : ∀ b q, ψ (b, q) = ψN q.val)
    (hcol : ∀ x, x < 2 ^ S.P.C.a → colW d orc x = firstColW S mN tN φN ψN x) :
    wordFr (S.sg t) (col1 S d orc) = (S.sg t).cFr.enc φ ψ := by
  have hR : S.P.R ≤ 2 ^ S.P.aR := le_two_pow_clog S.P.R
  funext x a
  obtain ⟨b, ⟨⟩⟩ := a
  obtain ⟨kc, hkc, hc⟩ := col1_first d orc x.val (hcol x.val x.isLt)
  obtain ⟨-, -, -, g4⟩ := groupCol_inv S.P.mem rfl rfl (2 ^ S.P.aR) hst hR hk _ kc hkc
  show vec (col1 S d orc x.val).fresh (Sz.rowNo b) =
    (ldRep S.P.Z S.P.C.a).enc (fun j => φ (b, j)) (fun q => ψ (b, q)) x ()
  have hb0 : Sz.rowNo b = 0 := by
    have := rowNo_lt b
    simpa using this
  rw [hc, hb0, funext (hφ b), funext (hψ b), enc_ldRep S.P.Z S.P.C.a x]
  exact g4.trans (sym_firstF S mN tN φN ψN x.val)

/-- The members' rows' messages, by numbers; 0 out of range. -/
def membN (S : Sz) (m : Bool → S.MJ → GE) : Bool → ℕ → ℕ → GE := fun a i j =>
  if h : i < S.P.R ∧ j < S.P.C.l then m a (.inl (⟨i, h.1⟩, ⟨j, h.2⟩)) else 0

/-- **At this folder's own terms.** -/
theorem wordIn_front (t : ℕ) (d : PQ.RD) (orc : (wRound d).Orc) (m : Bool → S.MJ → GE)
    (hst : (Fmt.M2.starts [S.P.mem, S.P.mem]).1 = [some 0, some (2 ^ S.P.aR)])
    (hk : 2 ^ S.P.aR + S.P.R ≤ 2 ^ Fmt.M2.kOf [S.P.mem, S.P.mem])
    (hcol : ∀ x, x < 2 ^ S.P.C.a → colW d orc x = firstColW S (membN S m) tN φN ψN x) :
    wordIn (S.sg t) (col1 S d orc) = (S.sg t).cIn.enc (mu0 S t m) (rho0 S t tN) := by
  have hR : S.P.R ≤ 2 ^ S.P.aR := le_two_pow_clog S.P.R
  refine wordIn_first t d orc _ _ hst hk (fun a i hi j => ?_) (free_mu0 S t m) (fun _ => rfl)
    (fun a i hi q => ?_) (fun a i q h1 h2 => ?_) (fun _ => rfl) hcol
  · refine (mu0_atJ S t m a (.inl (⟨i, hi⟩, j))).trans ?_
    unfold membN
    rw [dif_pos ⟨hi, j.isLt⟩]
  · obtain ⟨e1, e2⟩ := rowNo_split S t a i (lt_of_lt_of_le hi hR)
    show (if Sz.rowNo (memRow S t a i) % 2 ^ S.P.aR < S.P.R then _ else _) = _
    rw [e1, e2, if_pos hi]
  · show (if Sz.rowNo (memRow S t a i) % 2 ^ S.P.aR < S.P.R then _ else _) = _
    rw [(rowNo_split S t a i h2).1, if_neg (Nat.not_lt.2 h1)]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.membN
#print axioms Johnson.Prover.Link.wordIn_front
#print axioms Johnson.Prover.Link.firstColW
#print axioms Johnson.Prover.Link.length_firstColW
#print axioms Johnson.Prover.Link.sym_first0
#print axioms Johnson.Prover.Link.sym_first1
#print axioms Johnson.Prover.Link.sym_firstF
#print axioms Johnson.Prover.Link.lt_firstColW
#print axioms Johnson.Prover.Link.rho0
#print axioms Johnson.Prover.Link.col1_first
#print axioms Johnson.Prover.Link.vertex_memRow
#print axioms Johnson.Prover.Link.symG_zero
#print axioms Johnson.Prover.Link.wordIn_first
#print axioms Johnson.Prover.Link.wordFr_first
