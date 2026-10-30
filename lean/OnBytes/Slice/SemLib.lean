-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SemLib.lean: the entry file's decision, block by block, in the field.

OnBytes/Slice/ChainSem.lean has a predicate in the field on the written rounds, `SemAccept`, and a
chain that holds for every verdict whose yes implies it. This file has the blocks of that
implication for the format's own decision on an entry file (Fmt/M3Dec.lean: `dec`), in the written
protocol. The words (entry file, written protocol, link) are in OnBytes/Slice/README.md.

The course. The written protocol's yes gives a yes of the decision at the view that shows every
column (OnBytes/Slice/Unfold.lean). The decision is a tower of tests on the rounds' sizes and of
functions on claims. The rounds have the right sizes, so no test of a size refuses
(OnBytes/Slice/RoundsOf.lean), and the equations of OnBytes/Slice/Parse.lean take the tower apart:
the batching gives a row, each code switch gives a row, the base test says yes. Block by block the
row that the format's function computes, read in the field, is the closed form of the chain.

Main definitions.
 `col1`, `colSt`   a column of the first tree and of a later tree, cut as the format cuts it.
 `stdReads`   the standard readings: the record that `SemAccept` takes.
 `foldRow`    what the format's fold hands on, from a row and the written rounds.
 `LibOK`, `TreesOK`   what is asked of sizes and rounds, and which rounds send a tree.
Main theorems.
 `stdReads_rows`, `stdReads_word`   the standard readings have the two properties that the chain
              asks.
 `fold_parse`, `fold_simW`, `fold_wordW`, `cs_simW`, `base_simW`   one block each: the decision
              reads its rounds without refusing, and what its function computes is the chain's
              closed form.






Not claimed. That a yes of the decision gives `SemAccept`: the blocks are not joined here. The
converse. Nothing on the program's decision: the decision here is the library's. Nothing on a
protocol with another number of stages than three. Nothing on the sizes of the error counts.
-/
import OnBytes.Slice.ChainCloses
import OnBytes.Slice.RowsX
import OnBytes.Slice.BatCol
import OnBytes.Slice.LastJoint
import OnBytes.Slice.GroupCut
import OnBytes.Slice.SemSizes
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

/-! ## The standard readings -/

/-- The column at x of the first tree, laid on the group's rows; a default where it cannot be
cut. -/
def col1 (S : Sz) (d2 : PQ.RD) (o : (wRound d2).Orc) (x : ℕ) : Fmt.M1.Col :=
  ((Fmt.M2.groupCol S.P.mems 1 (colW d2 o x)).map (·.col)).getD default

/-- The column at x of a later stage's tree, laid on the stage's rows; a default where it cannot be
cut. -/
def colSt (s : Sg) (d : PQ.RD) (o : (wRound d).Orc) (x : ℕ) : Fmt.M1.Col :=
  (Fmt.M1.stageCol s.st 0 (2 ^ s.st.k) (colW d o x)).getD default

/-- The standard readings: columns are cut as the format cuts them. -/
def stdReads (S : Sz) (t₀ : ℕ) (s2 s3 : Sg) (d2 dS2 dS3 dL dB : PQ.RD) :
    Reads S t₀ s2 s3 d2 dS2 dS3 dL dB where
  rows := rowsX S t₀
  n1 := S.P.Z.l
  n2 := s2.Z.l
  w1 := fun o => wordIn (S.sg t₀) (col1 S d2 o)
  z1 := fun o => wordFr (S.sg t₀) (col1 S d2 o)
  w2 := fun m => wordIn s2 (colSt s2 dS2 m.1)
  z2 := fun m => wordFr s2 (colSt s2 dS2 m.1)
  w3 := fun m => wordIn s3 (lastColW dS3 m.1)
  g3 := fun m => wordMk s3 (lastMk dS3 m.1)
  fu := fun m => lst (sentW dL m) 0
  fs := fun m => shownW s3 (sentW dB m)

/-- The standard rows are the link's rows. -/
theorem stdReads_rows (S : Sz) (t₀ : ℕ) (s2 s3 : Sg) (d2 dS2 dS3 dL dB : PQ.RD)
    (hl : S.P.C.l = 2 ^ S.P.aP) (x : S.lk.X4) :
    IsRows S t₀ x ((stdReads S t₀ s2 s3 d2 dS2 dS3 dL dB).rows x).1
      ((stdReads S t₀ s2 s3 d2 dS2 dS3 dL dB).rows x).2 := isRows_rowsX S t₀ hl x

/-- The standard word of the first tree holds the written symbols, if the tree has the group's width
and the group's positions. -/
theorem stdReads_word (S : Sz) (t₀ : ℕ) (s2 s3 : Sg) (d2 dS2 dS3 dL dB : PQ.RD)
    (hW : PQ.colW d2.tree = Fmt.M2.widthOf S.P.mems 1) (hN : PQ.posN d2.tree = 2 ^ S.P.C.a)
    (o : (wRound d2).Orc) :
    WordTie S t₀ d2 o ((stdReads S t₀ s2 s3 d2 dS2 dS3 dL dB).w1 o) := by
  refine wordTie_of_col S t₀ d2 o (col1 S d2 o) (colTie_of_groupCol S d2 o _ fun x => ?_)
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (groupCol_isSome S.P.mems 1 (colW d2 o x.val)
    ((colW_length d2 o x.val (by rw [hN]; exact x.isLt)).trans hW))
  unfold col1
  rw [hk]
  rfl

/-! ## A fold, as the format's decision reads it -/

section
variable (s : Sg) (dE dT : PQ.RD)

/-- What the format's fold hands on, from the row G and the written rounds. -/
def foldRow (G : Fmt.M1.GRow) (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) : Fmt.M1.SRow :=
  Fmt.M1.foldStep .two (s.h + s.g) s.h G ((rvOf dE τ.1 τ.2.1).sent.getD 0 Fmt.Fld.zeroE)
    ((rvOf dE τ.1 τ.2.1).els.getD 0 Fmt.Fld.zeroE) (qsOf dT _ τ.2.2) (gsOf dT _ τ.2.2)

/-- The decision reads the rounds of a fold without refusing. -/
theorem fold_parse (hR : FoldRounds dE dT) (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) :
    Fmt.M1.nextN 1 1 0 (rsOf (foldRds s dE dT) τ) =
      some (⟨[(rvOf dE τ.1 τ.2.1).sent.getD 0 Fmt.Fld.zeroE],
        [(rvOf dE τ.1 τ.2.1).els.getD 0 Fmt.Fld.zeroE], (rvOf dE τ.1 τ.2.1).poss⟩,
        rsOf _ τ.2.2) ∧
    Fmt.M1.takeRounds (s.h + s.g) (rsOf _ τ.2.2) =
      some (qsOf dT _ τ.2.2, gsOf dT _ τ.2.2, []) := by
  obtain ⟨m, c, τ⟩ := τ
  exact ⟨(hR.eps.next m c (rsOf _ τ)).trans (by rw [← rvOf_one hR.eps m c]),
    takeRounds_rsOf hR.two _ τ⟩

/-- The claim after a fold is what the format's fold hands on, read in the field. Asked: n0 is
`maskLen s G`. -/
theorem fold_simW (G : Fmt.M1.GRow) (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) (n0 : ℕ)
    (hn : maskLen s G = n0) :
    foldNext s n0 dE dT (stmIn s G) τ = stmMid s (foldRow s dE dT G τ) := by
  subst hn
  obtain ⟨m, c, τ⟩ := τ
  have hsig := toE_sent dE m c 0
  have heps := toE_els dE m c
  have hfirst : sentAt dE m 0 + toE G.t * gOne _ (valsOf dE c) =
      toE (Fmt.Fld.two.addE ((rvOf dE m c).sent.getD 0 Fmt.Fld.zeroE)
        (Fmt.Fld.two.mulE ((rvOf dE m c).els.getD 0 Fmt.Fld.zeroE) G.t)) := by
    rw [toE_addE, toE_mulE, hsig, heps, mul_comm]
  show (claimF dT _ (sentAt dE m 0 + toE G.t * gOne _ (valsOf dE c)) τ,
    midVec s (maskLen s G) (vecIn s G) (gOne _ (valsOf dE c)) (ptF dT _ τ)) = _
  rw [hfirst, claimF_eq, ptF_eq, ← heps, ← slOut_mid,
    slOut_eq s G ((rvOf dE m c).sent.getD 0 Fmt.Fld.zeroE) _ (qsOf dT _ τ)]
  rfl

/-- The three folded words are those at the point that the format's fold hands on. -/
theorem fold_wordW (G : Fmt.M1.GRow) (col : ℕ → Fmt.M1.Col)
    (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) :
    foldWords s (wordIn s col) (wordFr s col) (foldPt s dE dT τ) =
      wordMid s col (ptL _ (foldRow s dE dT G τ).g) := by
  unfold foldRow foldPt
  rw [ptL_foldStep_g _ _ _ _ _ _ _ _ _ (le_refl _), ptF_eq]
  rfl

/-- The point that the format's fold hands on has as many coordinates as the stage has row
variables. -/
theorem foldRow_g_length (G : Fmt.M1.GRow) (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) :
    (foldRow s dE dT G τ).g.length = s.h + s.g := length_foldStep_g _ _ _ _ _ _ _ _

end

/-! ## A code switch, as the format's decision reads it -/

/-- The decision reads the two rounds of a switch without refusing, and the row that its switch
computes is the claim after the switch, read in the field. -/
theorem cs_simW {s s' : Sg} (hf : CsFit s s') (dS dC : PQ.RD) (hr : CsRounds s s' dS dC)
    (τ : Tr (PQ.uL (ckP .two) [dS, dC])) :
    ∃ z beta rs3 alpha theta xs,
      Fmt.M1.seedOf s'.st.na (rsOf [dS, dC] τ) = some (z, beta, rs3) ∧
      Fmt.M1.nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, []) ∧
      ∀ (R : Fmt.M1.SRow), R.g.length = s.h + s.g →
        ∀ (col : ℕ → Fmt.M1.Col) (cols : ℕ → Option Fmt.M1.Col),
        (∀ x c, cols x = some c → c = col x) → ∀ G' : Fmt.M1.GRow,
        Fmt.M1.csStep .two s.st s'.st R (Fmt.M1.sampleRow .two s'.st.Am s'.st.Az z beta alpha) xs
          theta cols = some G' →
        csNextW hf dS dC (stmMid s R) (wordMid s col (ptL _ R.g)) τ = stmIn s' G' := by
  obtain ⟨m1, c1, m2, c2, _⟩ := τ
  obtain ⟨β, hseed, hβ⟩ := seed_read hr.nz m1 c1
  obtain ⟨alpha, theta, xs, hrv, hxs, hans, hth, hQ⟩ := cs_read hr.cs m2 c2
  have hS : Fmt.M1.seedOf s'.st.na (rsOf [dS, dC] (m1, c1, m2, c2, ())) =
      some ((rvOf dS m1 c1).els.take s'.st.na,
        (rvOf dS m1 c1).els.getD s'.st.na Fmt.Fld.zeroE, [rvOf dC m2 c2]) := by
    show Fmt.M1.seedOf s'.st.na (rvOf dS m1 c1 :: [rvOf dC m2 c2]) = _
    unfold Fmt.M1.seedOf
    rw [hr.seed.next m1 c1]
  have hC : Fmt.M1.nextN 1 1 s.t [rvOf dC m2 c2] = some (⟨[alpha], [theta], xs⟩, []) := by
    rw [hr.cs.next m2 c2, hrv]
  have hzl : ((rvOf dS m1 c1).els.take s'.st.na).length = s'.st.na := by
    rw [List.length_take, hr.seed.els_length m1 c1]
    omega
  refine ⟨_, _, _, alpha, theta, xs, hS, hC, fun R hg col cols hcols G' hcs => ?_⟩
  have hnext := cs_sim hf R hg col cols hcols _ _ alpha theta xs hzl hxs β hβ
    (gCs s.C.a s.t _ (valsOf dC c2)).1 hQ G' hcs
  rw [← hth, ← hans, ← hseed] at hnext
  exact hnext

/-! ## The base case, as the format's decision reads it -/

/-- The decision reads the two rounds of the base case without refusing, and a yes of its test
gives the library's test, at the values read in the field. -/
theorem base_simW (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (dL dB : PQ.RD)
    (hL : SendsDraws dL 1 1 0 0) (hB : SendsDraws dB (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t s.C.a)
    (τ : Tr (PQ.uL (ckP .two) [dL, dB])) :
    ∃ tauS lam ps rs1 v,
      Fmt.M1.nextN 1 1 0 (rsOf [dL, dB] τ) = some (⟨[tauS], [lam], ps⟩, rs1) ∧
      Fmt.M1.nextN (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t rs1 = some (v, []) ∧
      ∀ (G : Fmt.M1.GRow) (col : ℕ → Fmt.M1.Col) (mk : ℕ → Fmt.M1.E × Fmt.M1.E)
        (last : ℕ → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E)),
        (∀ x q, last x = some q → Fmt.M1.ent (col x).main 0 = q.1 ∧ (mk x).1 = q.2.1 ∧
          Fmt.M1.ent (col x).mask 0 = q.2.2.1 ∧ (mk x).2 = q.2.2.2) →
        Fmt.M1.baseOK .two s.C s.Z G.c G.d G.t tauS lam (v.sent.take s.C.l)
          ((v.sent.drop s.C.l).take s.Z.l) ((v.sent.drop (s.C.l + s.Z.l)).take s.C.r)
          (v.sent.drop (s.C.l + s.Z.l + s.C.r)) v.poss last = true →
        LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) (stmIn s G))
          (stmIn s G).1 (s.cIn.T (wordIn s col)) (s.cIn.T (wordMk s mk)) (lst (sentW dL τ.1) 0)
          (gOne _ (valsOf dL τ.2.1)) (shownW s (sentW dB τ.2.2.1))
          (gPos s.C.a s.t _ (valsOf dB τ.2.2.2.1)) := by
  obtain ⟨m1, c1, m2, c2, _⟩ := τ
  obtain ⟨tauS, hts⟩ := List.length_eq_one_iff.1 (hL.sent_length m1 c1)
  obtain ⟨lam, hlm⟩ := List.length_eq_one_iff.1 (hL.els_length m1 c1)
  have hn1 : Fmt.M1.nextN 1 1 0 (rsOf [dL, dB] (m1, c1, m2, c2, ())) =
      some (⟨[tauS], [lam], (rvOf dL m1 c1).poss⟩, [rvOf dB m2 c2]) := by
    rw [← hts, ← hlm]
    exact hL.next m1 c1 [rvOf dB m2 c2]
  refine ⟨tauS, lam, _, _, _, hn1, hB.next m2 c2 [], fun G col mk last hlast hok => ?_⟩
  have hQ : ∀ i, (gPos s.C.a s.t _ (valsOf dB c2) i).val ∈ (rvOf dB m2 c2).poss := by
    intro i
    have hlt : i.val < (rvOf dB m2 c2).poss.length := by
      rw [hB.poss_length]
      exact i.isLt
    rw [hB.gPos_val m2 c2 i, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]
    exact List.getElem_mem hlt
  have hu : lst (sentW dL m1) 0 = toE tauS := by
    show lst (rvOf dL m1 c1).sent 0 = _
    rw [hts]
    rfl
  have hμ : gOne _ (valsOf dL c1) = toE lam := gOne_of_els dL m1 c1 hlm
  have hacc := accept_of_baseOK s h0 g0 G col mk _ hlast tauS lam _ _ _ _ _ _ hQ hok
  rw [← hu, ← hμ] at hacc
  exact hacc

/-! ## The columns that a view shows -/

/-- What is cut from a shown column of the first tree is the standard reading. -/
theorem cols_col1 (S : Sz) (d2 : PQ.RD) (m2 : (wRound d2).Msg) (V : Fmt.M1.View) (tree : ℕ)
    (h : ∀ x, Fmt.M1.colAt V tree x = treeCol d2 m2 x) (x : ℕ) (c : Fmt.M1.Col)
    (hc : ((Fmt.M1.colAt V tree x).bind (Fmt.M2.groupCol S.P.mems 1)).map (·.col) = some c) :
    c = col1 S d2 m2.1 x := by
  rw [h x] at hc
  cases hw : treeCol d2 m2 x with
  | none =>
    rw [hw] at hc
    cases hc
  | some w =>
    rw [hw, treeCol_some d2 m2 x w hw] at hc
    unfold col1
    rw [show (Fmt.M2.groupCol S.P.mems 1 (colW d2 m2.1 x)).map (·.col) = some c from hc]
    rfl

/-- What is cut from a shown column of a later tree is the standard reading. -/
theorem cols_colSt (s : Sg) (d : PQ.RD) (m : (wRound d).Msg) (V : Fmt.M1.View) (tree : ℕ)
    (h : ∀ x, Fmt.M1.colAt V tree x = treeCol d m x) (x : ℕ) (c : Fmt.M1.Col)
    (hc : (Fmt.M1.colAt V tree x).bind (Fmt.M1.stageCol s.st 0 (2 ^ s.st.k)) = some c) :
    c = colSt s d m.1 x := by
  rw [h x] at hc
  cases hw : treeCol d m x with
  | none =>
    rw [hw] at hc
    cases hc
  | some w =>
    rw [hw, treeCol_some d m x w hw] at hc
    unfold colSt
    rw [show Fmt.M1.stageCol s.st 0 (2 ^ s.st.k) (colW d m.1 x) = some c from hc]
    rfl

/-! ## What is asked of sizes and rounds -/

section
variable (S : Sz) (t₀ : ℕ) (s2 s3 : Sg) (hf1 : CsFit (S.sg t₀) s2) (hf2 : CsFit s2 s3)
  (d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB : PQ.RD)

/-- What is asked of the sizes and of the rounds. The sizes of the batching are in order; the
record of sizes has these three stages; every round sends and draws what its block reads; the last
stage has one main row and one mask row. -/
structure LibOK (e d : ℕ) : Prop where
  bat : BatOK S e d
  draws : BatDraws S d1 d2 d3 d4 d5 dA
  stages : S.P.stages = [(S.sg t₀).st, s2.st, s3.st]
  f1 : FoldRounds dE1 dT1
  c1 : CsRounds (S.sg t₀) s2 dS2 dC1
  f2 : FoldRounds dE2 dT2
  c2 : CsRounds s2 s3 dS3 dC2
  rL : SendsDraws dL 1 1 0 0
  rB : SendsDraws dB (s3.C.l + s3.Z.l + s3.C.r + s3.Z.r) 0 s3.t s3.C.a
  h3 : s3.h = 0
  g3 : s3.g = 0

/-! ## Which rounds send a tree -/

/-- Which rounds send a tree: the second, and the first round of each code switch. -/
structure TreesOK : Prop where
  t1 : d1.tree.isSome = false
  t2 : d2.tree.isSome = true
  t3 : d3.tree.isSome = false
  t4 : d4.tree.isSome = false
  t5 : d5.tree.isSome = false
  tA : dA.tree.isSome = false
  tE1 : dE1.tree.isSome = false
  tT1 : dT1.tree.isSome = false
  tS2 : dS2.tree.isSome = true
  tC1 : dC1.tree.isSome = false
  tE2 : dE2.tree.isSome = false
  tT2 : dT2.tree.isSome = false
  tS3 : dS3.tree.isSome = true

end

/-- Rounds without a tree, repeated, send no tree. -/
theorem nTrees_replicate (d : PQ.RD) (h : d.tree.isSome = false) : ∀ k : ℕ,
    nTrees (List.replicate k d) = 0
  | 0 => rfl
  | k + 1 => by
    show (if d.tree.isSome then 1 else 0) + nTrees (List.replicate k d) = 0
    rw [h, nTrees_replicate d h k]
    rfl

/-- The rounds of a fold send no tree. -/
theorem nTrees_fold (s : Sg) (dE dT : PQ.RD) (hE : dE.tree.isSome = false)
    (hT : dT.tree.isSome = false) : nTrees (foldRds s dE dT) = 0 := by
  show (if dE.tree.isSome then 1 else 0) + nTrees (List.replicate (s.h + s.g) dT) = 0
  rw [hE, nTrees_replicate dT hT]
  rfl

/-- After rounds that send no tree the trees keep their numbers. -/
theorem colAtS_join_none (ds₁ ds₂ : List PQ.RD) (h : nTrees ds₁ = 0)
    (τ : Tr (PQ.uL (ckP .two) ds₁)) (b : Tr (PQ.uL (ckP .two) ds₂)) (n x : ℕ) :
    PQ.colAtS (ckP .two) (ds₁ ++ ds₂) (joinT ds₁ ds₂ τ b) n x = PQ.colAtS (ckP .two) ds₂ b n x := by
  have h0 := colAtS_join_ge ds₁ ds₂ τ b n x
  rw [h, Nat.zero_add] at h0
  exact h0

/-- The whole view of the empty transcript shows the two stored tables' columns. -/
theorem viewTie_whole (S : Sz) (y : S.lk.E0.Str) : ViewTie S (whole [] S.P.T.a y ()) y := by
  intro x c
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [whole_stored] at h
    unfold storedOf at h
    rw [dif_pos x.isLt, if_pos rfl] at h
    exact (Option.some.inj h).symm
  · rw [whole_stored] at h
    unfold storedOf at h
    rw [dif_pos x.isLt, if_neg Nat.one_ne_zero, if_pos rfl] at h
    exact (Option.some.inj h).symm

section
variable (S : Sz) (t₀ : ℕ) (s2 s3 : Sg) (hf1 : CsFit (S.sg t₀) s2) (hf2 : CsFit s2 s3)
  (d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB : PQ.RD)

end

end OnBytes.Slice

#print axioms OnBytes.Slice.stdReads_rows
#print axioms OnBytes.Slice.stdReads_word
