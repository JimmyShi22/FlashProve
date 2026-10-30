-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Own.lean: the own rounds of a layers' sub-proof as one chain (Cb/Pv/Att/Chain.lean), at
letters: the order and kinds of the stages are fixed; everything else is a parameter: maps, forms,
claims and linear claims, and also the numbers of scalars and coordinates, the degrees, the picks
of the coefficients that are left out, and the bounds on the bad draws.

The stages, in the order of the plan of rounds: the draw of the token point (in the first
sub-proof two more points); a round with the limbs' scalars and a draw of one element; the draw of
the norms' join; the sumcheck of the sums of squares and a last draw (in the programs nothing
reads it); a round with the products' scalars and a draw of one element; the sumcheck of the
products of the rows; the sumcheck of the terms; a draw of one element that combines the open
claims; the batched sumcheck of the inner products; the sumcheck of the gated products and its
last draw; the draw of the join of the layers with routed experts; the sumcheck of the routed
gated products and its last draw; the weight claims' round (no scalar, or one, and a draw of one
element); the merge of the weight claims.

Main names:
  `Stg E M X`: the letters of one sumcheck at statements X: the parameters L of Cb/Pv/Lay/Sum.lean
    with their conditions (kept maps allowed; `L.Rd` is not used here), the number n of further
    scalars in the first message, the pick F, the claim cl, the reading msg of the messages, the
    linear claims Lc. `S.Nx`: the statements behind it. `S.stage`, `S.stage_ok`, `S.stage_nums`:
    it as a stage of a chain.
  `LayTail E M X`: the letters of all stages from the limbs' scalars on. `T.ch`: their chain.
    `T.Laws`: a bound on the bad draws at each of the nine rounds outside the sumchecks that draw,
    and at each of the first six sumchecks: what is owed at the chain's end, with the claim that
    follows, gives its output claims. So an end value that a later stage's claim gives is not owed
    at the end. Of the seventh sumcheck all output claims are owed.
  `LayOwn`, `LayOwnFirst`: the token point (and the first sub-proof's two further points) before a
    tail. `ch`, `Laws`, `ok`.
  `LayOwn.knowAt`, `LayOwnFirst.knowAt`: `KnowAt` (Cb/G6/Cut.lean) for the whole chain, from "Dn,
    and what is claimed before the token point" to `ch.Last Dn`, under `Laws`.
  `LayOwn.errs`, `LayOwnFirst.errs`: the list of the errors, written out in the letters
    (`LayTail.nums`).
  `law_idle`, `law_powers`, `law_split`: three forms of claims from which a law on a drawing round
    follows: a draw that nothing reads; a batch by the powers of one element; sent scalars that
    split identities.

Limits: those of Cb/Pv/Att/Chain.lean. The theorem is worth what a value of the letters is worth,
and no value is built here. `Laws` speaks of all messages m: its clauses are laws on the letters,
to be proved at a value; each `Stg.L` carries its conditions `ok`, which a user pays too. The
bounds on the bad draws are letters: a bound as large as the set of draws makes its clause true of
any claims. With every claim "True" the laws hold and the theorem says nothing; with an owed claim
"False" the last claim has no member. The errors are numbers of bad draws; at the draw of a point
of g coordinates a count among |E|^g points. At a pick that is not lawful a sumcheck's verifier
may refuse everything.
This file does not stand on the other reductions of this folder: at each sumcheck the chain's
verifier is `rideNR` (Cb/Pv/Att/Ride.lean). What the other files give a value is their algebra,
towards `Laws` (Cb/Pv/Lay/OwnParts.lean, OwnEnds.lean, OwnMid.lean; put together in OwnAll.lean).
The sub-proof is taken with terms, with routed experts and with both joins: where the plan leaves
one of these out the chain is another. The three laws at the end do not fit the limbs' round
(groups of scalars under one draw), the first sub-proof's weight round, nor a draw of a point.
The programs refuse a proof in which the coefficient drawn in the sumcheck of the terms is 0
(Cb/Pv/Lay/Over.lean); this chain does not, and a chain has no condition on its later statements:
the laws are asked at a coefficient 0 too. With the programs' form of that sumcheck's first row,
divided by the coefficient, the law on that sumcheck is had with "the coefficient is not 0" among
what is owed at the end (`o3_over`, Cb/Pv/Lay/OwnMid.lean): it then stands in
`ch.Last`, a claim on the statement alone that whoever follows must test (`knowAt_test`).
That the letters at a value are the programs' maps, forms and claims is not said here. Nothing is
said on the honest prover, on completeness or on zero knowledge.

-/
import Cb.Pv.Att.Chain
import Cb.Pv.Lay.Sum
import Cb.G6.Johnson.Layers.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR TWhole Johnson.L5.Layers Cb.Pv.Att

variable {E : Type} [Field E] [Fintype E] {M : Type}

/-! ### The letters of one sumcheck -/

/-- The letters of one sumcheck at statements X. -/
structure Stg (E : Type) [Field E] [Fintype E] (M X : Type) where
  /-- the sumcheck's parameters, with their conditions -/
  L : SumL E
  /-- the number of further scalars in the first message -/
  n : ℕ
  /-- which coefficients are left out -/
  F : ∀ st, HFixs (L.T.par.vars st)
  /-- the claimed sum and the sumcheck's state, from the statement and the further scalars -/
  cl : X → (Fin n → E) → E × L.St
  /-- the entries, read off the messages -/
  msg : M → L.J → E
  /-- what is claimed of the further scalars -/
  Lc : X → (Fin n → E) → M → Prop

namespace Stg
variable {X : Type} (S : Stg E M X)

/-- The statements behind it. -/
abbrev Nx : Type := (X × (Fin S.n → E)) × S.L.T.par.Out

/-- All its output claims. -/
def Out (b : S.Nx) (m : M) : Prop := S.L.T.par.OutHolds b.2 (S.msg m)

/-- The stage, with what is owed at the chain's end as a parameter. -/
noncomputable def stage (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx) : Ch E M X :=
  .ride S.L.T.par S.n S.F S.cl S.msg S.Lc Ow next

/-- The list of its errors. -/
def nums : List ℕ := 1 :: (List.ofFn S.L.M.n ++ [S.L.M.DY] ++ [0])

theorem stage_nums (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx) :
    (S.stage Ow next).nums = S.nums ++ next.nums := by
  show (1 :: (S.L.T.par.fmt.map PFmt.n ++ [0])) ++ next.nums = _
  rw [S.L.degs]
  rfl

theorem stage_ok (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx)
    (hO : ∀ b m, Ow b m → next.Todo b m → S.Out b m) (h : next.OK) : (S.stage Ow next).OK :=
  ⟨⟨(psc_our_ok E S.L.T).1 S.L.conds.1,
      psc_our_deg E S.L.T S.L.conds.2.2.1 S.L.conds.2.2.2,
      (psc_our_ok E S.L.T).2 S.L.conds.2.1⟩, hO, h⟩

end Stg

/-- One element of E. -/
abbrev dE (E : Type) [Field E] [Fintype E] : Dr := ⟨E⟩
/-- A point of g coordinates. -/
abbrev dPt (E : Type) [Field E] [Fintype E] (g : ℕ) : Dr := ⟨Fin g → E⟩

/-! ### The stages behind the first points -/

/-- The letters of the stages from the limbs' scalars on, at statements X. -/
structure LayTail (E : Type) [Field E] [Fintype E] (M X : Type) where
  /-- the limbs' scalars: their number; the bound on the bad draws; what is claimed before them and
  of them -/
  nL : ℕ
  eL : ℕ
  pL : X → M → Prop
  lL : X → (Fin nL → E) → M → Prop
  /-- the join of the norms: its coordinates; the bound; what is claimed before it -/
  gN : ℕ
  eN : ℕ
  pN : (X × (Fin nL → E)) × E → M → Prop
  /-- the sums of squares; what of its output claims is owed at the end; what is claimed before its
  last draw -/
  s1 : Stg E M (((X × (Fin nL → E)) × E) × (Fin gN → E))
  ow1 : s1.Nx → M → Prop
  p1 : s1.Nx → M → Prop
  /-- the products' scalars -/
  nP : ℕ
  eP : ℕ
  pP : s1.Nx × E → M → Prop
  lP : s1.Nx × E → (Fin nP → E) → M → Prop
  /-- the products of the rows -/
  s2 : Stg E M (((s1.Nx × E) × (Fin nP → E)) × E)
  ow2 : s2.Nx → M → Prop
  /-- the terms -/
  s3 : Stg E M s2.Nx
  ow3 : s3.Nx → M → Prop
  /-- what is claimed before the draw that combines; the number of claims combined -/
  n4 : ℕ
  p4 : s3.Nx → M → Prop
  /-- the batched inner products -/
  s4 : Stg E M (s3.Nx × E)
  ow4 : s4.Nx → M → Prop
  /-- the gated products -/
  s5 : Stg E M s4.Nx
  ow5 : s5.Nx → M → Prop
  p5 : s5.Nx → M → Prop
  /-- the join of the layers with routed experts -/
  gR : ℕ
  eR : ℕ
  pR : s5.Nx × E → M → Prop
  /-- the routed gated products -/
  s6 : Stg E M ((s5.Nx × E) × (Fin gR → E))
  ow6 : s6.Nx → M → Prop
  p6 : s6.Nx → M → Prop
  /-- the weight claims' round: scalars sent (none, or one); the bound -/
  nW : ℕ
  eW : ℕ
  pW : s6.Nx × E → M → Prop
  lW : s6.Nx × E → (Fin nW → E) → M → Prop
  /-- the merge of the weight claims -/
  s7 : Stg E M (((s6.Nx × E) × (Fin nW → E)) × E)

namespace LayTail
variable {X : Type} (T : LayTail E M X)

/-- From the weight claims' round on. -/
noncomputable def chW : Ch E M (T.s6.Nx × E) :=
  .send T.nW (dE E) T.eW T.pW T.lW (T.s7.stage T.s7.Out (.done _))
/-- From the routed gated products on. -/
noncomputable def ch6 : Ch E M ((T.s5.Nx × E) × (Fin T.gR → E)) :=
  T.s6.stage T.ow6 (.draw (dE E) 1 T.p6 T.chW)
/-- From the gated products on. -/
noncomputable def ch5 : Ch E M T.s4.Nx :=
  T.s5.stage T.ow5 (.draw (dE E) 1 T.p5 (.draw (dPt E T.gR) T.eR T.pR T.ch6))
/-- From the draw that combines on. -/
noncomputable def ch4 : Ch E M T.s3.Nx := .draw (dE E) (T.n4 - 1) T.p4 (T.s4.stage T.ow4 T.ch5)
/-- From the products' scalars on. -/
noncomputable def chP : Ch E M (T.s1.Nx × E) :=
  .send T.nP (dE E) T.eP T.pP T.lP (T.s2.stage T.ow2 (T.s3.stage T.ow3 T.ch4))
/-- From the sums of squares on. -/
noncomputable def ch1 : Ch E M (((X × (Fin T.nL → E)) × E) × (Fin T.gN → E)) :=
  T.s1.stage T.ow1 (.draw (dE E) 1 T.p1 T.chP)
/-- All stages from the limbs' scalars on. -/
noncomputable def ch : Ch E M X :=
  .send T.nL (dE E) T.eL T.pL T.lL (.draw (dPt E T.gN) T.eN T.pN T.ch1)

/-- The laws on the letters: a bound on the bad draws at each round that draws; and at each
sumcheck: what is owed at the end, with the claim that follows, gives its output claims. -/
structure Laws : Prop where
  cL : ∀ x m, ¬ T.pL x m → ∀ s, T.lL x s m → cnt (fun β : E => T.pN ((x, s), β) m) ≤ T.eL
  cN : ∀ x m, ¬ T.pN x m → cnt (fun p : Fin T.gN → E => T.ch1.Todo (x, p) m) ≤ T.eN
  o1 : ∀ b m, T.ow1 b m → T.p1 b m → T.s1.Out b m
  c1 : ∀ x m, ¬ T.p1 x m → cnt (fun β : E => T.pP (x, β) m) ≤ 1
  cP : ∀ x m, ¬ T.pP x m → ∀ s, T.lP x s m →
    cnt (fun β : E => (T.s2.stage T.ow2 (T.s3.stage T.ow3 T.ch4)).Todo ((x, s), β) m) ≤ T.eP
  o2 : ∀ b m, T.ow2 b m → (T.s3.stage T.ow3 T.ch4).Todo b m → T.s2.Out b m
  o3 : ∀ b m, T.ow3 b m → T.p4 b m → T.s3.Out b m
  c4 : ∀ x m, ¬ T.p4 x m → cnt (fun β : E => (T.s4.stage T.ow4 T.ch5).Todo (x, β) m) ≤ T.n4 - 1
  o4 : ∀ b m, T.ow4 b m → T.ch5.Todo b m → T.s4.Out b m
  o5 : ∀ b m, T.ow5 b m → T.p5 b m → T.s5.Out b m
  c5 : ∀ x m, ¬ T.p5 x m → cnt (fun β : E => T.pR (x, β) m) ≤ 1
  cR : ∀ x m, ¬ T.pR x m → cnt (fun p : Fin T.gR → E => T.ch6.Todo (x, p) m) ≤ T.eR
  o6 : ∀ b m, T.ow6 b m → T.p6 b m → T.s6.Out b m
  c6 : ∀ x m, ¬ T.p6 x m → cnt (fun β : E => T.pW (x, β) m) ≤ 1
  cW : ∀ x m, ¬ T.pW x m → ∀ s, T.lW x s m →
    cnt (fun β : E => (T.s7.stage T.s7.Out (.done _)).Todo ((x, s), β) m) ≤ T.eW

theorem ch_ok (h : T.Laws) : T.ch.OK :=
  ⟨h.cL, h.cN, T.s1.stage_ok _ _ h.o1
    ⟨h.c1, h.cP, T.s2.stage_ok _ _ h.o2 (T.s3.stage_ok _ _ h.o3
      ⟨h.c4, T.s4.stage_ok _ _ h.o4 (T.s5.stage_ok _ _ h.o5
        ⟨h.c5, h.cR, T.s6.stage_ok _ _ h.o6
          ⟨h.c6, h.cW, T.s7.stage_ok _ _ (fun _ _ h1 _ => h1) trivial⟩⟩)⟩)⟩⟩

/-- The list of the errors. -/
def nums : List ℕ :=
  [T.eL] ++ ([T.eN] ++ (T.s1.nums ++ ([1] ++ ([T.eP] ++ (T.s2.nums ++ (T.s3.nums ++
    ([T.n4 - 1] ++ (T.s4.nums ++ (T.s5.nums ++ ([1] ++ ([T.eR] ++ (T.s6.nums ++ ([1] ++
      ([T.eW] ++ (T.s7.nums ++ [])))))))))))))))

theorem ch_nums : T.ch.nums = T.nums :=
  congrArg ([T.eL] ++ ·) <| congrArg ([T.eN] ++ ·) <|
  (T.s1.stage_nums _ _).trans <| congrArg (T.s1.nums ++ ·) <| congrArg ([1] ++ ·) <|
  congrArg ([T.eP] ++ ·) <| (T.s2.stage_nums _ _).trans <| congrArg (T.s2.nums ++ ·) <|
  (T.s3.stage_nums _ _).trans <| congrArg (T.s3.nums ++ ·) <| congrArg ([T.n4 - 1] ++ ·) <|
  (T.s4.stage_nums _ _).trans <| congrArg (T.s4.nums ++ ·) <|
  (T.s5.stage_nums _ _).trans <| congrArg (T.s5.nums ++ ·) <| congrArg ([1] ++ ·) <|
  congrArg ([T.eR] ++ ·) <| (T.s6.stage_nums _ _).trans <| congrArg (T.s6.nums ++ ·) <|
  congrArg ([1] ++ ·) <| congrArg ([T.eW] ++ ·) <| T.s7.stage_nums _ _

end LayTail

/-! ### The whole -/

/-- The letters of the own rounds of a layers' sub-proof that is not the first: the token point,
then the stages. -/
structure LayOwn (E : Type) [Field E] [Fintype E] (M X : Type) where
  /-- the token point: its coordinates; the bound on its bad draws; what is claimed before it -/
  gT : ℕ
  eT : ℕ
  pT : X → M → Prop
  tail : LayTail E M (X × (Fin gT → E))

/-- The same for the first sub-proof: two more points are drawn. -/
structure LayOwnFirst (E : Type) [Field E] [Fintype E] (M X : Type) where
  gT : ℕ
  eT : ℕ
  pT : X → M → Prop
  gA : ℕ
  eA : ℕ
  pA : X × (Fin gT → E) → M → Prop
  gB : ℕ
  eB : ℕ
  pB : (X × (Fin gT → E)) × (Fin gA → E) → M → Prop
  tail : LayTail E M (((X × (Fin gT → E)) × (Fin gA → E)) × (Fin gB → E))

namespace LayOwn
variable {X : Type} (A : LayOwn E M X)

/-- The chain. -/
noncomputable def ch : Ch E M X := .draw (dPt E A.gT) A.eT A.pT A.tail.ch

/-- The laws. -/
structure Laws : Prop where
  cT : ∀ x m, ¬ A.pT x m → cnt (fun p : Fin A.gT → E => A.tail.pL (x, p) m) ≤ A.eT
  tail : A.tail.Laws

theorem ok (h : A.Laws) : A.ch.OK := ⟨h.cT, A.tail.ch_ok h.tail⟩

/-- Knowledge soundness of the own rounds. This is said under the hypotheses that stand in the
statement itself, which this comment does not list; it is no claim that they hold. -/
theorem knowAt {Kc X0 Wp : Type} (h : A.Laws) (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp))
    (pr : X → X0) (Dn : X → M → Prop) :
    KnowAt (A.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ A.pT x m)
      (jt A0 (fun e => pr (A.ch.back e)) (A.ch.Last Dn)) (fun _ _ _ wp => wp) (A.ch.eps Ex) :=
  Ch.knowAt Ex A0 A.ch pr Dn (A.ok h)

/-- The list of its errors. -/
theorem errs (Ex : ExtSpec) : TWhole.errList (A.ch.eps Ex) = A.eT :: A.tail.nums := by
  rw [Ch.errList_eps]
  exact congrArg ([A.eT] ++ ·) A.tail.ch_nums

end LayOwn

namespace LayOwnFirst
variable {X : Type} (A : LayOwnFirst E M X)

/-- The chain. -/
noncomputable def ch : Ch E M X :=
  .draw (dPt E A.gT) A.eT A.pT
    (.draw (dPt E A.gA) A.eA A.pA (.draw (dPt E A.gB) A.eB A.pB A.tail.ch))

/-- The laws. -/
structure Laws : Prop where
  cT : ∀ x m, ¬ A.pT x m → cnt (fun p : Fin A.gT → E => A.pA (x, p) m) ≤ A.eT
  cA : ∀ x m, ¬ A.pA x m → cnt (fun p : Fin A.gA → E => A.pB (x, p) m) ≤ A.eA
  cB : ∀ x m, ¬ A.pB x m → cnt (fun p : Fin A.gB → E => A.tail.pL (x, p) m) ≤ A.eB
  tail : A.tail.Laws

theorem ok (h : A.Laws) : A.ch.OK := ⟨h.cT, h.cA, h.cB, A.tail.ch_ok h.tail⟩

/-- Knowledge soundness of the own rounds. This is said under the hypotheses that stand in the
statement itself, which this comment does not list; it is no claim that they hold. -/
theorem knowAt {Kc X0 Wp : Type} (h : A.Laws) (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp))
    (pr : X → X0) (Dn : X → M → Prop) :
    KnowAt (A.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ A.pT x m)
      (jt A0 (fun e => pr (A.ch.back e)) (A.ch.Last Dn)) (fun _ _ _ wp => wp) (A.ch.eps Ex) :=
  Ch.knowAt Ex A0 A.ch pr Dn (A.ok h)

/-- The list of its errors. -/
theorem errs (Ex : ExtSpec) :
    TWhole.errList (A.ch.eps Ex) = A.eT :: A.eA :: A.eB :: A.tail.nums := by
  rw [Ch.errList_eps]
  exact congrArg ([A.eT] ++ ·) (congrArg ([A.eA] ++ ·) (congrArg ([A.eB] ++ ·) A.tail.ch_nums))

end LayOwnFirst

/-! ### Laws from the form of the claims -/

/-- A draw that nothing reads: if the claim behind it gives the claim before it, no draw is bad. -/
theorem law_idle {X D : Type} [Fintype D] (P : X → M → Prop) (T : X × D → M → Prop)
    (hT : ∀ x β m, T (x, β) m → P x m) (e : ℕ) (x : X) (m : M) (h : ¬ P x m) :
    cnt (fun β : D => T (x, β) m) ≤ e :=
  le_trans (le_of_eq (cnt_false fun β hβ => h (hT x β m hβ))) (Nat.zero_le _)

/-- A batch by the powers of one element: if the claim before the draw says that n gaps are 0 and
Q, and the claim behind it gives that the gaps' batch is 0 and Q, at most n - 1 draws are bad. -/
theorem law_powers {X : Type} (n : ℕ) (g : X → M → Fin n → E) (Q P : X → M → Prop)
    (T : X × E → M → Prop) (hP : ∀ x m, (∀ b, g x m b = 0) → Q x m → P x m)
    (hT : ∀ x β m, T (x, β) m → ∑ b : Fin n, β ^ (b : ℕ) * g x m b = 0 ∧ Q x m) (x : X) (m : M)
    (h : ¬ P x m) : cnt (fun β : E => T (x, β) m) ≤ n - 1 := by
  refine le_trans (cnt_mono fun β hβ => ?_) (cnt_badPow (g x m))
  obtain ⟨h1, h2⟩ := hT x β m hβ
  exact ⟨fun h0 => h (hP x m (fun b => congrFun h0 b) h2), h1⟩

/-- Sent scalars that split identities. Identity b says a b = c b. Of the sent scalars it is claimed
that s b - k b = c b (k: a mask). If the claim behind the draw gives that the batch of the gaps
a b + k b - s b is 0, and Q, then at most n - 1 draws are bad. -/
theorem law_split {X : Type} (n : ℕ) (a c k : X → M → Fin n → E) (Q P : X → M → Prop)
    (L : X → (Fin n → E) → M → Prop) (T : (X × (Fin n → E)) × E → M → Prop)
    (hP : ∀ x m, (∀ b, a x m b = c x m b) → Q x m → P x m)
    (hL : ∀ x s m, L x s m → ∀ b, s b - k x m b = c x m b)
    (hT : ∀ x s β m, T ((x, s), β) m →
      ∑ b : Fin n, β ^ (b : ℕ) * (a x m b + k x m b - s b) = 0 ∧ Q x m)
    (x : X) (m : M) (h : ¬ P x m) (s : Fin n → E) (hs : L x s m) :
    cnt (fun β : E => T ((x, s), β) m) ≤ n - 1 := by
  refine le_trans (cnt_mono fun β hβ => ?_) (cnt_badPow fun b => a x m b + k x m b - s b)
  obtain ⟨h1, h2⟩ := hT x s β m hβ
  refine ⟨fun h0 => h (hP x m (fun b => ?_) h2), h1⟩
  have e1 : a x m b + k x m b - s b = 0 := congrFun h0 b
  have e2 := hL x s m hs b
  linear_combination e1 + e2

end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.law_idle
#print axioms Cb.Pv.Lay.law_powers
#print axioms Cb.Pv.Lay.law_split
#print axioms Cb.Pv.Lay.LayOwn.knowAt
#print axioms Cb.Pv.Lay.LayOwn.errs
#print axioms Cb.Pv.Lay.LayOwnFirst.knowAt
#print axioms Cb.Pv.Lay.LayOwnFirst.errs
