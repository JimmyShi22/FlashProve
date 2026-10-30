-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ChainOf.lean: the blocks after the link's fifth round, joined.

OnBytes/Slice/LinkSound.lean states one hypothesis on the written link (the format's protocol
between two stored tables), `Closes`: after the link's five rounds, if the statement that
the library's verifier holds has no witness, the prover has lost (the library's `Doomed`,
Iop/Rbr.lean) in the rounds that follow. These rounds are the batching, two stages of the proximity
test (a fold and a code switch each) and the base case. OnBytes/Slice/BlockHolds.lean states, for
each kind of block, that the block is taken off. This file derives `Closes` for the entry file's
decision (Fmt/M3Dec.lean: `dec`) from these statements.

How the blocks meet. Each block asks that the prover has lost after it if the claim that the
format's own function computes there has no witness: that is the next block's conclusion. It also
asks that the written protocol refuses where a test of work fails or the format's function refuses.
For this the decision is evaluated along the rounds before that point (OnBytes/Slice/Parse.lean)
at the view that shows every column (OnBytes/Slice/Unfold.lean, ChainTop.lean). The columns that a
block reads are those of a tree that was sent before the block, so they do not depend on what
follows.

The stages are those of the small test configuration (OnBytes/Slice/ToySg.lean), so that the lists
of rounds are written out and their shapes are joined by evaluation. The sizes of the link and all
rounds are variables.

Main definitions.
 `Tail`          the rounds after the fifth, with the lists of rounds of each block.
 `ThreeTrees`    which of all rounds send a tree.
 `grpCols`, `stgCols`, `orEmpty`   the columns of a tree, split by rows as a block takes them.
Main theorem.
 `closes_of_blocks`   `Closes`, with the blocks' error counts in a row.
Not claimed here. That the four statements hold: they are hypotheses in this file. Nothing on the
sizes of the error counts. No theorem of this library takes `Closes` as a hypothesis; the link's
soundness theorems ask `ClosesR`.
-/
import OnBytes.Slice.BlockHolds
import OnBytes.Slice.GroupCut
import OnBytes.Slice.LastJoint
import OnBytes.Slice.LinkSound
import OnBytes.Slice.SimFold
import OnBytes.Slice.ToySg

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## Tests of work -/

section
variable (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁)) (b : Tr (PQ.uL (ckP .two) ds₂))
  (τ' : Tr (PQ.uL (ckP .two) (ds₁ ++ ds₂))) (h : HEq τ' (Tr.app τ b))
include h

/-- A test of work that fails in the first part fails in the joined transcript. -/
theorem pass_left (hp : PQ.passSL (ckP .two) ds₁ (PQ.rhoSL (ckP .two) ds₁ τ) = false) :
    PQ.passSL (ckP .two) (ds₁ ++ ds₂) (PQ.rhoSL (ckP .two) (ds₁ ++ ds₂) τ') = false := by
  rw [pass_app ds₁ ds₂ τ b τ' h, hp, Bool.false_and]

/-- A test of work that fails in the second part fails in the joined transcript. -/
theorem pass_right (hp : PQ.passSL (ckP .two) ds₂ (PQ.rhoSL (ckP .two) ds₂ b) = false) :
    PQ.passSL (ckP .two) (ds₁ ++ ds₂) (PQ.rhoSL (ckP .two) (ds₁ ++ ds₂) τ') = false := by
  rw [pass_app ds₁ ds₂ τ b τ' h, hp, Bool.and_false]

end

/-- A test of work that fails after a round fails with that round in front. -/
theorem pass_behind (d : PQ.RD) (r : List PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal)
    (b : Tr (PQ.uL (ckP .two) r))
    (h : PQ.passSL (ckP .two) r (PQ.rhoSL (ckP .two) r b) = false) :
    PQ.passSL (ckP .two) (d :: r) (PQ.rhoSL (ckP .two) (d :: r) (m, c, b)) = false := by
  simp only [PQ.passSL, PQ.rhoSL, h, Bool.and_false]

/-- A round's own test of work. -/
theorem pass_here (d : PQ.RD) (r : List PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal)
    (b : Tr (PQ.uL (ckP .two) r)) (h : GChal.pass (b := d.entry.work) c = false) :
    PQ.passSL (ckP .two) (d :: r) (PQ.rhoSL (ckP .two) (d :: r) (m, c, b)) = false := by
  simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and]

/-! ## The rounds after the fifth -/

/-- The rounds after the link's fifth: the batching; for each of two stages the round that
joins a hiding sum to the claim, the round of a fold (which is repeated), the sending of the next
tree and the code switch; the two rounds of the base case. -/
structure Tail where
  dA : PQ.RD
  dE1 : PQ.RD
  dT1 : PQ.RD
  dS2 : PQ.RD
  dC1 : PQ.RD
  dE2 : PQ.RD
  dT2 : PQ.RD
  dS3 : PQ.RD
  dC2 : PQ.RD
  dL : PQ.RD
  dB : PQ.RD

namespace Tail
variable (T : Tail)

/-- the rounds of the first fold -/
abbrev f1 : List PQ.RD := T.dE1 :: List.replicate (toySg1.h + toySg1.g) T.dT1
/-- the rounds of the first code switch -/
abbrev c1 : List PQ.RD := [T.dS2, T.dC1]
/-- the rounds of the second fold -/
abbrev f2 : List PQ.RD := T.dE2 :: List.replicate (toySg2.h + toySg2.g) T.dT2
/-- the rounds of the second code switch -/
abbrev c2 : List PQ.RD := [T.dS3, T.dC2]
/-- the rounds of the base case -/
abbrev bs : List PQ.RD := [T.dL, T.dB]
/-- the rounds from the second code switch on -/
abbrev r4 : List PQ.RD := T.c2 ++ T.bs
/-- the rounds from the second fold on -/
abbrev r3 : List PQ.RD := T.f2 ++ T.r4
/-- the rounds from the first code switch on -/
abbrev r2 : List PQ.RD := T.c1 ++ T.r3
/-- the rounds from the first fold on -/
abbrev r1 : List PQ.RD := T.f1 ++ T.r2
/-- all rounds after the fifth -/
abbrev all : List PQ.RD := T.dA :: T.r1

end Tail

/-- Which rounds send a tree: the link's second round and the two sendings of the proximity
test, and no other round before the last of these. -/
structure ThreeTrees (d1 d2 d3 d4 d5 : PQ.RD) (T : Tail) : Prop where
  none0 : nTrees [d1] = 0
  tree0 : d2.tree.isSome = true
  one : nTrees (d1 :: d2 :: d3 :: d4 :: d5 :: T.dA :: T.f1) = 1
  tree1 : T.dS2.tree.isSome = true
  two : nTrees (d1 :: d2 :: d3 :: d4 :: d5 :: T.dA :: (T.f1 ++ (T.c1 ++ T.f2))) = 2
  tree2 : T.dS3.tree.isSome = true

/-! ## Columns, as the blocks take them -/

/-- The columns of a group's tree, each split by rows. -/
def grpCols (ms : List Fmt.M2.Mem) (d : PQ.RD) (m : (wRound d).Msg) (x : ℕ) : Option Fmt.M1.Col :=
  ((treeCol d m x).bind (Fmt.M2.groupCol ms 1)).map (·.col)

/-- The columns of a later stage's tree, each split by rows. -/
def stgCols (s : Fmt.M1.Stage) (d : PQ.RD) (m : (wRound d).Msg) (x : ℕ) : Option Fmt.M1.Col :=
  (treeCol d m x).bind (Fmt.M1.stageCol s 0 (2 ^ s.k))

/-- A column at every position: the empty one where none is given. -/
def orEmpty (f : ℕ → Option Fmt.M1.Col) (x : ℕ) : Fmt.M1.Col := (f x).getD default

/-- Where a column is given, `orEmpty` is that column. -/
theorem orEmpty_of_some (f : ℕ → Option Fmt.M1.Col) (x : ℕ) (c : Fmt.M1.Col) (h : f x = some c) :
    c = orEmpty f x := by
  unfold orEmpty
  rw [h]
  rfl

/-- What the whole view shows of the two stored tables is what the strings hold. -/
theorem whole_shows (a : ℕ) (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) (x : Fin (2 ^ a)) (c : List UInt64) :
    (Fmt.M3.storedAt (whole [] a y ()) 0 x.val = some c → c = (y.1 x).2) ∧
      (Fmt.M3.storedAt (whole [] a y ()) 1 x.val = some c → c = (y.2 x).2) := by
  have s0 : storedOf a y 0 x.val = some (y.1 x).2 := by
    unfold storedOf
    rw [dif_pos x.isLt]
    rfl
  have s1 : storedOf a y 1 x.val = some (y.2 x).2 := by
    unfold storedOf
    rw [dif_pos x.isLt]
    rfl
  constructor
  · intro h
    rw [whole_stored, s0] at h
    exact (Option.some.inj h).symm
  · intro h
    rw [whole_stored, s1] at h
    exact (Option.some.inj h).symm

/-! ## The joining -/

section
variable (S : Sz) (eU e2 e3 : ℕ) (d1 d2 d3 d4 d5 : PQ.RD) (T : Tail) (xs : List PQ.XO)

/-- `Closes` holds of the rounds after the fifth, for the entry file's decision, if each block is
taken off. eU, e2, e3: the radii at the three stages. The error counts are the blocks', in a row.
Asked besides: the sizes name the field `.two` and the three stages of the small test configuration;
`ThreeTrees`; the first tree has the group's number of positions and width of a column. -/
theorem closes_of_blocks
    (hfld : S.P.fld = .two) (hst : S.P.stages = [toySg1.st, toySg2.st, toySg3.st])
    (ht : ThreeTrees d1 d2 d3 d4 d5 T) (hpos : PQ.posN d2.tree = 2 ^ S.P.C.a)
    (hW : PQ.colW d2.tree = Fmt.M2.widthOf S.P.mems 1)
    (εa : ℕ) (εf1 : Err (PQ.uL (ckP .two) T.f1)) (εc1 : Err (PQ.uL (ckP .two) T.c1))
    (εf2 : Err (PQ.uL (ckP .two) T.f2)) (εc2 : Err (PQ.uL (ckP .two) T.c2))
    (εb : Err (PQ.uL (ckP .two) T.bs))
    (hBat : BatHolds S toySg1 eU d1 d2 d3 d4 d5 T.dA εa)
    (hF1 : FoldHolds toySg1 eU T.dE1 T.dT1 εf1)
    (hC1 : CsHolds toySg1 toySg2 eU e2 T.dS2 T.dC1 εc1)
    (hF2 : FoldHolds toySg2 e2 T.dE2 T.dT2 εf2)
    (hC2 : CsHolds toySg2 toySg3 e2 e3 T.dS3 T.dC2 εc2)
    (hB : BaseHolds toySg3 e3 T.dL T.dB εb) :
    Closes S d1 d2 d3 d4 d5 T.all xs (Fmt.M3.dec S.P)
      (εa, Err.app εf1 (Err.app εc1 (Err.app εf2 (Err.app εc2 εb)))) := by
  intro y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 hno
  -- emb: a transcript of the rounds after the fifth, put after the five rounds fixed above.
  -- V: the whole view there. Yes: the decision says yes there.
  let emb : Tr (PQ.uL (ckP .two) T.all) →
      Tr (PQ.uL (ckP .two) (d1 :: d2 :: d3 :: d4 :: d5 :: T.all)) :=
    fun b => (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, b)
  let V : Tr (PQ.uL (ckP .two) T.all) → Fmt.M3.View := fun b => whole _ S.P.T.a y (emb b)
  let Yes : Tr (PQ.uL (ckP .two) T.all) → Prop := fun b =>
    Fmt.M3.decBy Fmt.M1.blocks S.P (V b) (Fmt.M3.batchLit S.P (whole [] S.P.T.a y ())) = true
  refine doomed_accept S.P _ S.P.T.a y xs m0 c0 _ _ emb ?_
  -- the two ways to a refusal
  have noP : ∀ b, PQ.passSL (ckP .two) T.all (PQ.rhoSL (ckP .two) T.all b) = false →
      NoAt S.P _ S.P.T.a y (emb b) := fun b h =>
    noAt_of_pass _ _ _ _ _ (pass_behind d1 _ m1 c1 _ (pass_behind d2 _ m2 c2 _
      (pass_behind d3 _ m3 c3 _ (pass_behind d4 _ m4 c4 _ (pass_behind d5 _ m5 c5 b h)))))
  have noD : ∀ b, ¬ Yes b → NoAt S.P _ S.P.T.a y (emb b) := fun b h =>
    noAt_of_dec _ _ _ _ _ (Bool.eq_false_iff.2 h)
  -- the first tree's columns
  have own0 : ∀ b x, Fmt.M1.colAt (V b).own 0 x = treeCol d2 m2 x := fun b x =>
    whole_tree [d1] (d3 :: d4 :: d5 :: T.all) d2 ht.tree0 0 ht.none0 S.P.T.a y (m1, c1, ()) m2 c2
      (m3, c3, m4, c4, m5, c5, b) _ HEq.rfl x
  have cols0 : ∀ b, (fun x => ((Fmt.M1.colAt (V b).own 0 x).bind
      (Fmt.M2.groupCol S.P.mems 1)).map (·.col)) = grpCols S.P.mems d2 m2 := fun b =>
    funext fun x => by rw [own0]; rfl
  -- the batching
  refine hBat _ _ y (whole [] S.P.T.a y ()) (whole_shows S.P.T.a y) m1 c1 m2 c2 m3 c3 m4 c4 m5 c5
    (orEmpty (grpCols S.P.mems d2 m2))
    (fun x => groupCol_col S.P.mems 1 d2 m2 hW x.val (by rw [hpos]; exact x.isLt)) hno _
    (fun mA cA τ h => noP _ (pass_here T.dA _ mA cA τ h)) ?_ ?_
  swap
  · intro mA cA thetaA hels hbat b
    exact noAt_of_dec _ _ _ _ _ (decBy_none Fmt.M1.blocks S.P _ _ (rvOf d1 m1 c1) (rvOf d2 m2 c2)
      (rvOf d3 m3 c3) (rvOf d4 m4 c4) (rvOf d5 m5 c5) (rvOf T.dA mA cA) (rsOf T.r1 b) thetaA rfl
      hels (by rw [seedLen_mems]; exact hbat))
  intro mA cA thetaA R hels hbat hnoR
  have noP1 : ∀ b, PQ.passSL (ckP .two) T.r1 (PQ.rhoSL (ckP .two) T.r1 b) = false →
      NoAt S.P _ S.P.T.a y (emb (mA, cA, b)) := fun b h => noP _ (pass_behind T.dA _ mA cA b h)
  -- a yes of the decision, after the batching
  have yes1 : ∀ b : Tr (PQ.uL (ckP .two) T.r1), Yes (mA, cA, b) →
      Fmt.M2.lastAt Fmt.M1.blocks .two [toySg1.st, toySg2.st, toySg3.st] S.P.mems 1 0
        (V (mA, cA, b)).own R.toG (rsOf T.r1 b) = true := by
    intro b h
    have h1 := decBy_some Fmt.M1.blocks S.P _ _ (rvOf d1 m1 c1) (rvOf d2 m2 c2) (rvOf d3 m3 c3)
      (rvOf d4 m4 c4) (rvOf d5 m5 c5) (rvOf T.dA mA cA) (rsOf T.r1 b) thetaA R rfl hels
      (by rw [seedLen_mems]; exact hbat) h
    rwa [hfld, hst] at h1
  -- the first fold
  refine hF1 _ _ R.toG _ hnoR _ (fun τ b h => noP1 _ (pass_left T.f1 T.r2 τ b _ HEq.rfl h)) ?_
  intro τF1 sigma1 eps1 ps1 rs1 qs1 g1 hF11 hF12 hnoM1
  have noP2 : ∀ b, PQ.passSL (ckP .two) T.r2 (PQ.rhoSL (ckP .two) T.r2 b) = false →
      NoAt S.P _ S.P.T.a y (emb (mA, cA, Tr.app τF1 b)) := fun b h =>
    noP1 _ (pass_right T.f1 T.r2 τF1 b _ HEq.rfl h)
  have rs1_eq : ∀ (τC : Tr (PQ.uL (ckP .two) T.c1)) (b : Tr (PQ.uL (ckP .two) T.r3)),
      rsOf T.r1 (Tr.app τF1 (Tr.app τC b)) = rsOf T.f1 τF1 ++ (rsOf T.c1 τC ++ rsOf T.r3 b) :=
    fun τC b => (rsOf_app T.f1 T.r2 τF1 (Tr.app τC b) _ HEq.rfl).trans
      (congrArg (rsOf T.f1 τF1 ++ ·) (rsOf_app T.c1 T.r3 τC b _ HEq.rfl))
  -- the first code switch
  refine hC1 _ _ (Fmt.M1.foldStep .two (toySg1.h + toySg1.g) toySg1.h R.toG sigma1 eps1 qs1 g1)
    (length_foldStep_g _ _ _ _ _ _ _ _) (orEmpty (grpCols S.P.mems d2 m2))
    (grpCols S.P.mems d2 m2) (orEmpty_of_some _)
    (fun m => wordIn toySg2 (orEmpty (stgCols toySg2.st T.dS2 m)))
    (by rw [ptL_foldStep_g _ _ _ _ _ _ _ _ _ (Nat.le_refl _)]; exact hnoM1) _
    (fun τ b h => noP2 _ (pass_left T.c1 T.r3 τ b _ HEq.rfl h)) ?_ ?_
  swap
  · intro τC1 z1 beta1 rs31 alpha1 theta1 xs1 hC11 hC12 hcs1 b
    refine noD _ fun hd => ?_
    have h1 := yes1 _ hd
    rw [rs1_eq, lastAt_none Fmt.M1.blocks .two toySg1.st toySg2.st [toySg3.st] S.P.mems 1 0 _ R.toG
      _ _ _ sigma1 eps1 ps1 rs1 qs1 g1 z1 beta1 rs31 alpha1 theta1 xs1 hF11 hF12 hC11 hC12
      (by rw [cols0]; exact hcs1)] at h1
    cases h1
  intro τC1 z1 beta1 rs31 alpha1 theta1 xs1 G1 hC11 hC12 hcs1 hnoG1
  have noP3 : ∀ b, PQ.passSL (ckP .two) T.r3 (PQ.rhoSL (ckP .two) T.r3 b) = false →
      NoAt S.P _ S.P.T.a y (emb (mA, cA, Tr.app τF1 (Tr.app τC1 b))) := fun b h =>
    noP2 _ (pass_right T.c1 T.r3 τC1 b _ HEq.rfl h)
  -- a yes of the decision, after the first code switch
  have yes2 : ∀ b : Tr (PQ.uL (ckP .two) T.r3), Yes (mA, cA, Tr.app τF1 (Tr.app τC1 b)) →
      Fmt.M1.iopp Fmt.M1.blocks .two (V (mA, cA, Tr.app τF1 (Tr.app τC1 b))).own
        [toySg2.st, toySg3.st] 1 0 (2 ^ toySg2.st.k) G1 (rsOf T.r3 b) = true := by
    intro b hd
    have h1 := yes1 _ hd
    rwa [rs1_eq, lastAt_some Fmt.M1.blocks .two toySg1.st toySg2.st [toySg3.st] S.P.mems 1 0 _
      R.toG _ _ _ sigma1 eps1 ps1 rs1 qs1 g1 z1 beta1 rs31 alpha1 theta1 xs1 G1 hF11 hF12 hC11 hC12
      (by rw [cols0]; exact hcs1)] at h1
  -- the second tree's columns
  have own1 : ∀ b x, Fmt.M1.colAt (V (mA, cA, Tr.app τF1 (Tr.app τC1 b))).own 1 x =
      treeCol T.dS2 τC1.1 x := fun b x =>
    whole_tree (d1 :: d2 :: d3 :: d4 :: d5 :: T.dA :: T.f1) (T.dC1 :: T.r3) T.dS2 ht.tree1 1 ht.one
      S.P.T.a y (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, τF1) τC1.1 τC1.2.1
      (τC1.2.2.1, τC1.2.2.2.1, b) _ HEq.rfl x
  have cols1 : ∀ b, (fun x => (Fmt.M1.colAt (V (mA, cA, Tr.app τF1 (Tr.app τC1 b))).own 1 x).bind
      (Fmt.M1.stageCol toySg2.st 0 (2 ^ toySg2.st.k))) = stgCols toySg2.st T.dS2 τC1.1 := fun b =>
    funext fun x => by rw [own1]; rfl
  -- the second fold
  refine hF2 _ _ G1 (orEmpty (stgCols toySg2.st T.dS2 τC1.1)) hnoG1 _
    (fun τ b h => noP3 _ (pass_left T.f2 T.r4 τ b _ HEq.rfl h)) ?_
  intro τF2 sigma2 eps2 ps2 rs2 qs2 g2 hF21 hF22 hnoM2
  have noP4 : ∀ b, PQ.passSL (ckP .two) T.r4 (PQ.rhoSL (ckP .two) T.r4 b) = false →
      NoAt S.P _ S.P.T.a y (emb (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 b)))) := fun b h =>
    noP3 _ (pass_right T.f2 T.r4 τF2 b _ HEq.rfl h)
  have rs2_eq : ∀ (τC : Tr (PQ.uL (ckP .two) T.c2)) (b : Tr (PQ.uL (ckP .two) T.bs)),
      rsOf T.r3 (Tr.app τF2 (Tr.app τC b)) = rsOf T.f2 τF2 ++ (rsOf T.c2 τC ++ rsOf T.bs b) :=
    fun τC b => (rsOf_app T.f2 T.r4 τF2 (Tr.app τC b) _ HEq.rfl).trans
      (congrArg (rsOf T.f2 τF2 ++ ·) (rsOf_app T.c2 T.bs τC b _ HEq.rfl))
  -- the second code switch
  refine hC2 _ _ (Fmt.M1.foldStep .two (toySg2.h + toySg2.g) toySg2.h G1 sigma2 eps2 qs2 g2)
    (length_foldStep_g _ _ _ _ _ _ _ _) (orEmpty (stgCols toySg2.st T.dS2 τC1.1))
    (stgCols toySg2.st T.dS2 τC1.1) (orEmpty_of_some _)
    (fun m => wordIn toySg3 (lastColW T.dS3 m.1))
    (by rw [ptL_foldStep_g _ _ _ _ _ _ _ _ _ (Nat.le_refl _)]; exact hnoM2) _
    (fun τ b h => noP4 _ (pass_left T.c2 T.bs τ b _ HEq.rfl h)) ?_ ?_
  swap
  · intro τC2 z2 beta2 rs32 alpha2 theta2 xs2 hC21 hC22 hcs2 b
    refine noD _ fun hd => ?_
    have h1 := yes2 _ hd
    rw [rs2_eq, iopp_step_none Fmt.M1.blocks .two _ toySg2.st toySg3.st [] 1 0 (2 ^ toySg2.st.k) G1
      _ _ _ sigma2 eps2 ps2 rs2 qs2 g2 z2 beta2 rs32 alpha2 theta2 xs2 hF21 hF22 hC21 hC22
      (by rw [cols1]; exact hcs2)] at h1
    cases h1
  intro τC2 z2 beta2 rs32 alpha2 theta2 xs2 G2 hC21 hC22 hcs2 hnoG2
  -- a yes of the decision, after the second code switch
  have yes3 : ∀ b : Tr (PQ.uL (ckP .two) T.bs),
      Yes (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 (Tr.app τC2 b)))) →
      Fmt.M1.iopp Fmt.M1.blocks .two
        (V (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 (Tr.app τC2 b))))).own
        [toySg3.st] 2 0 (2 ^ toySg3.st.k) G2 (rsOf T.bs b) = true := by
    intro b hd
    have h1 := yes2 _ hd
    rwa [rs2_eq, iopp_step_some Fmt.M1.blocks .two _ toySg2.st toySg3.st [] 1 0 (2 ^ toySg2.st.k) G1
      _ _ _ sigma2 eps2 ps2 rs2 qs2 g2 z2 beta2 rs32 alpha2 theta2 xs2 G2 hF21 hF22 hC21 hC22
      (by rw [cols1]; exact hcs2)] at h1
  -- the third tree's columns
  have own2 : ∀ b x,
      Fmt.M1.colAt (V (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 (Tr.app τC2 b))))).own 2 x =
        treeCol T.dS3 τC2.1 x := fun b x =>
    whole_tree (d1 :: d2 :: d3 :: d4 :: d5 :: T.dA :: (T.f1 ++ (T.c1 ++ T.f2))) (T.dC2 :: T.bs)
      T.dS3 ht.tree2 2 ht.two S.P.T.a y
      (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, Tr.app τF1 (Tr.app τC1 τF2)) τC2.1 τC2.2.1
      (τC2.2.2.1, τC2.2.2.2.1, b) _ HEq.rfl x
  -- the base case
  refine hB G2 (lastColW T.dS3 τC2.1.1) (lastMk T.dS3 τC2.1.1) (fun b => Fmt.M1.lastCol
    (V (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 (Tr.app τC2 b))))).own 2)
    (fun b x q h => lastCol_tie _ 2 T.dS3 τC2.1.1
      (fun x' w hw => treeCol_some _ _ _ _ ((own2 b x').symm.trans hw)) x q h) hnoG2 _
    (fun b h => noP4 _ (pass_right T.c2 T.bs τC2 b _ HEq.rfl h)) ?_
  intro b tauS lam ps3 rs3 v hB1 hB2 hbase
  refine noD _ fun hd => ?_
  have h1 := yes3 _ hd
  rw [iopp_base_eq Fmt.M1.blocks .two _ toySg3.st 2 0 (2 ^ toySg3.st.k) G2 _ tauS lam ps3 rs3 v hB1
    hB2] at h1
  exact Bool.noConfusion (hbase.symm.trans h1)

end

end OnBytes.Slice

#print axioms OnBytes.Slice.pass_left
#print axioms OnBytes.Slice.pass_right
#print axioms OnBytes.Slice.pass_behind
#print axioms OnBytes.Slice.pass_here
#print axioms OnBytes.Slice.orEmpty_of_some
#print axioms OnBytes.Slice.whole_shows
#print axioms OnBytes.Slice.closes_of_blocks
