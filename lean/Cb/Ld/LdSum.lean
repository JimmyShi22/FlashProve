-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSum.lean: a sumcheck protocol that folds: it reduces one linear claim on tables of codewords
with rows on a cube to one linear claim on single codewords.

In this library's terms: the zero-knowledge sumcheck that folds. The term, the honest side, the
numbers, and the statements on the honest side (each a `Prop` in `Cb.Spec`); their proofs are in
Cb/Ld/LdSumHon.lean, Cb/Ld/LdSumAcc.lean and Cb/Ld/LdSumZk.lean.
The file follows the paper that this protocol builds on (lean/CREDITS.md).

The protocol. Statement: one linear claim (Cb/Ld/LdRel.lean: the main relation) on a main table with
rows on the cube of k = h + g variables under a code C, and on a carried mask table with rows on the
cube of the first h variables under a code Z.
  Round 0: the prover sends a fresh mask oracle: a table with rows on the cube of the first h
  variables under Z's encoder, whose message holds the coefficients of one hiding polynomial U
  (Cb/Ld/LdHide.lean); with it, in the clear, the sum μ of U over the cube. The verifier sends a
  coefficient ε.
  Round j (j = 1 .. k): plain sumcheck on H = U + ε (claim polynomial): the prover sends the n + 1
  coefficients of a round polynomial, the verifier a challenge γ_j.
  The claim polynomial at X is <form of the main table folded at X, main messages folded at X> +
  <form of the mask folded at the first h variables, mask messages folded there> X_(h+1) .. X_k.
  Checks, all in the clear: the first round polynomial sums to μ + ε (target), each later one to the
  value of the one before at its challenge. The verifier reads no oracle.
  Output. New oracles: the three tables folded at the challenges (the masks at the first h of them);
  a symbol at a long position is computed from the one symbol of the input at that position and from
  the native symbols of the fresh mask behind that position (under the three `Laws`:
  `Spec.ld_sum_local`). New claim: target = the last round polynomial at the last challenge; forms:
  ε (main form fixed at γ), ε γ_(h+1) .. γ_k (mask form fixed at the first h challenges), and the
  weights of the hiding polynomial at γ.
  k + 1 rounds; nothing is merged. The coefficient ε multiplies the claim, not the mask; μ goes out
  with the mask oracle, before ε.

Main names:
  `SumPar`: the parameters.
  `SumPar.ior`: the reduction told above under "The protocol".
  `SumPar.hon`: its honest prover, in closed form.

The parameters:
  The degree: n is the largest degree of a round polynomial (n + 1 coefficients). The claim
  polynomial has degree up to 2 in each variable, so `Spec.ld_sum_rounds`, `Spec.ld_sum_acc` and
  `Spec.ld_sum_exact` assume 2 ≤ n.
  How the coefficients lie in the table is a parameter: `pk` lays the k n + 1 coefficients into a
  table with 2^h rows, `Qw` gives the public weights at a point, and `SumPar.PackOK` is the law that
  ties them: U(γ) = <weights at γ, table folded at the first h challenges>. With h = 0 the table has
  one row, which holds the coefficients (`pk0` in Cb/Ld/LdSumPack.lean, with the packing into 2^h
  rows that saves h places).

Limits:
Declared differences to the paper that this protocol builds on.
 (1) One finite field stands for its ring, its module and the centre from which challenges come; the
     module's one generator is 1.
 (2) The transformation of the fresh mask is asked to be linear also when h = 0
     (there: only if h > 0).
 (3) Honest-verifier zero knowledge is in this library's exact form (Ior/Honest.lean): error 0,
     every set of further positions within the budget, where the text has an error and uniform
     positions.
     `H.ExactWith Ri bud S`: for every (x, y, w) in Ri, every ρ outside `H.Hid w x` and every T with
       `bud ρ T`, the distribution `H.output w x ρ T` equals `S x ρ T a`, where a gives the symbols
       of y at the positions `R.given ρ T` and `none` at the others. `Exact` says that some S does.
       Here `H` is `Y.hon`, `R` is `Y.ior`, `Ri` is `Con Y.Cin.N Y.slIn.Holds` and `bud` is
       `Y.bud t`: `H.Exact Ri bud` is the conclusion of `Spec.ld_sum_exact`.
     The view holds the prover's own oracle only, so the simulator is given nothing of the input
     oracles.
     In the text a reader of the output oracle is simulated with one query to the input for each of
     its queries; here that share of a query is booked by srcE, and it is the composition rule of a
     chain that charges the reads of the input.
 (4) The packing is a parameter with one law; the size condition on the mask's message and the
     padding with zeros belong to the instances.
 (5) k = 0 is allowed (there: k ≥ 1).
 (6) Message lengths need not be powers of two.
Not here: round-by-round knowledge soundness, its extractor and the record `IOR.GoodT`:
Cb/Ld/LdSumMain.lean, over Cb/Ld/LdSumStep*.lean. This file says nothing on running times.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdHide
import Cb.Ld.LdRel
import Ior.KnowCollGood

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop
open scoped ENNReal

noncomputable section

/-! ## The rounds -/

/-- the variables: k plain ones -/
abbrev sVars (E : Type) [Field E] (n k : ℕ) : List (HVar E) := List.replicate k (HVar.plain E n)

/-- a round of the sumcheck: n + 1 coefficients in the clear, a challenge -/
@[reducible] def sRound (E Ch : Type) [Field E] [Fintype Ch] [Nonempty Ch] (n : ℕ) : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim,
    Plain := Fin (n + 1) → E, Chal := Ch, dOrc := (), dPlain := 0 }

section Rounds
variable {E Ch : Type} [Field E] [Fintype Ch] [Nonempty Ch] (val : Ch → E) (n : ℕ)

/-- the round polynomials and the challenges of the k rounds, in the terms of Cb/Ld/LdHide.lean -/
def sQ : (k : ℕ) → Plains (List.replicate k (sRound E Ch n)) → RIdx (sVars E n k) → E
  | 0, _, i => i.elim
  | _ + 1, pl, .inl t => pl.1 t
  | k + 1, pl, .inr i => sQ k pl.2 i
def sG : (k : ℕ) → Rho (List.replicate k (sRound E Ch n)) → HPt (sVars E n k)
  | 0, _ => ()
  | k + 1, ρ => (val ρ.1, sG k ρ.2)

/-- a point as a function of the variable -/
def sPt : (k : ℕ) → HPt (sVars E n k) → Fin k → E
  | 0, _ => Fin.elim0
  | k + 1, γ => Fin.cons γ.1 (sPt k γ.2)

/-- the point 0 -/
def sZero : (k : ℕ) → HPt (sVars E n k)
  | 0 => ()
  | k + 1 => (0, sZero k)

/-- A prover from its messages in closed form: q γ holds all round polynomials at the challenges γ;
in each round the prover sends its part of q at the challenges so far (the later ones set to 0; the
runs' lemmas ask that the part do not depend on them: `SCausal`, Cb/Ld/LdSumRun.lean). -/
def sStrat {β : Type} :
    (k : ℕ) → (HPt (sVars E n k) → RIdx (sVars E n k) → E) → (HPt (sVars E n k) → β) →
    Strat (List.replicate k (sRound E Ch n)) β
  | 0, _, res => res ()
  | k + 1, q, res =>
    (((), fun t => q (0, sZero n k) (.inl t)),
      fun c => sStrat k (fun γ i => q (val c, γ) (.inr i)) fun γ => res (val c, γ))

/-- errors of the k rounds from a function of the round's number -/
def sErr : (k : ℕ) → (ℕ → ℕ) → Err (List.replicate k (sRound E Ch n))
  | 0, _ => ()
  | k + 1, f => (f 0, sErr k fun j => f (j + 1))

variable {J : Type} [Fintype J]

/-- the pairing of two tables with rows on a cube -/
def sBl {k : ℕ} (L m : (Fin k → Bool) → J → E) : E := ∑ b, ∑ c, L b c * m b c

/-- the two halves of a table, and its fold in the first variable -/
def sHalf {k : ℕ} (β : Bool) (L : (Fin (k + 1) → Bool) → J → E) : (Fin k → Bool) → J → E := fun b =>
  L (Fin.cons β b)
def sFold1 {k : ℕ} (x : E) (L : (Fin (k + 1) → Bool) → J → E) : (Fin k → Bool) → J → E := fun b c =>
  (1 - x) * sHalf false L b c + x * sHalf true L b c

/-- The round polynomials of the claim polynomial <L folded at X, m folded at X>: degree 2 in each
round. -/
def sTr :
    (k : ℕ) → ((Fin k → Bool) → J → E) → ((Fin k → Bool) → J → E) →
    HPt (sVars E n k) → RIdx (sVars E n k) → E
  | 0, _, _, _, i => i.elim
  | _ + 1, L, m, _, .inl t =>
      if (t : ℕ) = 0 then sBl (sHalf false L) (sHalf false m)
      else if (t : ℕ) = 1 then
        sBl (sHalf false L) (sHalf true m - sHalf false m) +
          sBl (sHalf true L - sHalf false L) (sHalf false m)
      else if (t : ℕ) = 2 then sBl (sHalf true L - sHalf false L) (sHalf true m - sHalf false m)
      else 0
  | k + 1, L, m, γ, .inr i => sTr k (sFold1 γ.1 L) (sFold1 γ.1 m) γ.2 i

end Rounds

/-! ## The parameters -/

/-- The parameters of the block. -/
structure SumPar (E P : Type) [Field E] where
  /-- the mask tables have rows on the cube of the first h variables; g further variables -/
  h : ℕ
  g : ℕ
  /-- the largest degree of a round polynomial -/
  n : ℕ
  /-- the challenge set -/
  Ch : Type
  [finCh : Fintype Ch]
  [neCh : Nonempty Ch]
  val : Ch → E
  /-- the code of the main table; the code of the masks, under the transformation of the carried
  mask -/
  C : LdCode E P
  Z : LdCode E P
  /-- the transformation under which the fresh mask is read -/
  AaW : Type
  TW : Z.Word → P → AaW → E
  srcW : P → Finset Z.NP
  /-- the forms -/
  St : Type
  StS : Type
  sl : Slf E St ((Fin (h + g) → Bool) × C.J)
  slS : Slf E StS ((Fin h → Bool) × Z.J)
  /-- how the coefficients of the hiding polynomial are laid into a table, and the public weights at
  a point -/
  pk : (HIdx (sVars E n (h + g)) → E) → (Fin h → Bool) × Z.J → E
  Qw : Slf E (Fin (h + g) → E) Z.J

attribute [instance] SumPar.finCh SumPar.neCh

namespace SumPar
variable {E P : Type} [Field E] (Y : SumPar E P)

abbrev k : ℕ := Y.h + Y.g
abbrev vars : List (HVar E) := sVars E Y.n Y.k

/-- the code of the masks, under the transformation of the fresh mask: the same encoder -/
@[reducible] def Zw : LdCode E P := { Y.Z with Aa := Y.AaW, T := Y.TW, src := Y.srcW }

/-- The codes of the input and of the output statement. -/
abbrev Cin : LdCode E P := (Y.C.il (Fin Y.k → Bool)).pair (Y.Z.il (Fin Y.h → Bool))
abbrev Cout : LdCode E P := Y.C.pair (Y.Z.pair Y.Zw)
/-- the code of the oracle that the prover sends -/
abbrev Cw : LdCode E P := Y.Zw.il (Fin Y.h → Bool)

/-- The forms of the input and of the output statement. -/
abbrev slIn : Slf E (Y.St × Y.StS) Y.Cin.J := Y.sl.pair Y.slS
abbrev slOut :
    Slf E (((Y.St × (Fin Y.k → E)) × E) × (((Y.StS × (Fin Y.h → E)) × E) × (Fin Y.k → E)))
      Y.Cout.J :=
  Y.sl.fix.smul.pair (Y.slS.fix.smul.pair Y.Qw)

abbrev Xi : Type := E × (Y.St × Y.StS)
abbrev Xo : Type :=
  E × (((Y.St × (Fin Y.k → E)) × E) × (((Y.StS × (Fin Y.h → E)) × E) × (Fin Y.k → E)))

/-- the first h coordinates of a point; the product of the later ones -/
def pre (γ : Fin Y.k → E) : Fin Y.h → E := fun i => γ (Fin.castAdd Y.g i)
def late (γ : Fin Y.k → E) : E := ∏ t : Fin Y.g, γ (Fin.natAdd Y.h t)

/-- The law of the packing: the hiding polynomial at a point is the value of the public weights at
the folded table. -/
def PackOK : Prop :=
  ∀ (W : HIdx Y.vars → E) (γ : HPt Y.vars),
    hU Y.vars W γ = ∑ j, Y.Qw (sPt Y.n Y.k γ) j * foldV (Y.pre (sPt Y.n Y.k γ)) (Y.pk W) j

/-- round 0: the fresh mask oracle, read natively, symbol by symbol; the sum in the clear; the
coefficient -/
@[reducible] def round0 : Round :=
  { Orc := Y.Cw.Word, Pos := Y.Cw.NP, Sym := fun p => Y.Cw.NS p → E, rd := fun f p => f p,
    Plain := E, Chal := Y.Ch, dOrc := fun _ _ => 0, dPlain := 0 }

abbrev rounds : Shape := List.replicate Y.k (sRound E Y.Ch Y.n)
abbrev shape : Shape := Y.round0 :: Y.rounds

/-- the fold of a native word with interleaved rows -/
def foldW {ι : Type} [Fintype ι] [DecidableEq ι] (C : LdCode E P)
    (γ : ι → E) (f : (C.il (ι → Bool)).Word) : C.Word :=
  fun p => foldV γ (f p)

/-- what the verifier reads off a transcript: coefficient, challenges, sum, round polynomials -/
def eps (ρ : Rho Y.shape) : E := Y.val ρ.1
def gam (ρ : Rho Y.shape) : HPt Y.vars := sG Y.val Y.n Y.k ρ.2
def pt (ρ : Rho Y.shape) : Fin Y.k → E := sPt Y.n Y.k (Y.gam ρ)
def mu (pl : Plains Y.shape) : E := pl.1
def qs (pl : Plains Y.shape) : RIdx Y.vars → E := sQ Y.n Y.k pl.2

/-- the new explicit part, given the new target -/
def newX (x : Y.Xi) (ρ : Rho Y.shape) (τ' : E) : Y.Xo :=
  (τ', (((x.2.1, Y.pt ρ), Y.eps ρ), (((x.2.2, Y.pre (Y.pt ρ)), Y.eps ρ * Y.late (Y.pt ρ)), Y.pt ρ)))

open Classical in
/-- The verifier: the checks of the sumcheck for the claimed sum μ + ε (target); the new target is
the last round polynomial at the last challenge. -/
def out (x : Y.Xi) (τ : Tr Y.shape) : Option Y.Xo :=
  if HCons Y.vars (Y.mu τ.plains + x.1 * Y.eps τ.rho) (Y.qs τ.plains) (Y.gam τ.rho) then
    some (Y.newX x τ.rho
      (hFin Y.vars (Y.mu τ.plains + x.1 * Y.eps τ.rho) (Y.qs τ.plains) (Y.gam τ.rho)))
  else none

/-- The new implicit instance: the three tables, folded. -/
def imp (y : Y.Cin.Word) (τ : Tr Y.shape) : Y.Cout.Word :=
  LdCode.mkW (foldW Y.C (Y.pt τ.rho) (LdCode.fstW y))
    (LdCode.mkW (C₁ := Y.Z) (C₂ := Y.Zw) (foldW Y.Z (Y.pre (Y.pt τ.rho)) (LdCode.sndW y))
      (foldW Y.Zw (Y.pre (Y.pt τ.rho)) τ.1.1))

/-- The block. -/
def ior : IOR Y.Xi Y.Cin.ext Y.Xo Y.Cout.ext where
  shape := Y.shape
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun x _ τ => Y.out x τ
  imp := Y.imp
  srcE := fun _ x => {x}
  srcO := fun _ x => (Y.srcW x).map ⟨Sum.inl, Sum.inl_injective⟩
  tie := fun _ _ => ∅

end SumPar

/-! ## The honest side -/

namespace SumPar
variable {E P : Type} [Field E] [Fintype E] (Y : SumPar E P)

/-- the two tables of the claim polynomial, with rows on the whole cube and the coordinates of main
table and mask side by side: the mask's form carries the weight "all later variables are 1", the
mask's messages do not depend on the later variables -/
def tabL (x : Y.Xi) : (Fin Y.k → Bool) → Y.C.J ⊕ Y.Z.J → E := fun b =>
  Sum.elim (fun c => Y.sl x.2.1 (b, c)) fun c =>
    Y.slS x.2.2 (fun i => b (Fin.castAdd Y.g i), c) *
      ∏ t : Fin Y.g, if b (Fin.natAdd Y.h t) then 1 else 0
def tabM (m : Y.Cin.J → E) : (Fin Y.k → Bool) → Y.C.J ⊕ Y.Z.J → E := fun b =>
  Sum.elim (fun c => m (.inl (b, c))) fun c => m (.inr (fun i => b (Fin.castAdd Y.g i), c))

/-- the prover's coins: the coefficients of the hiding polynomial, the encoding randomness of the
fresh mask -/
abbrev Coin : Type := (HIdx Y.vars → E) × (Y.Cw.Q → E)

/-- The honest round polynomials, in closed form. -/
def honQ (w : Y.Cin.N.Wit) (x : Y.Xi) (W : HIdx Y.vars → E) (ε : E) (γ : HPt Y.vars) :
    RIdx Y.vars → E :=
  fun i => hTr Y.vars 0 W γ i + ε * sTr Y.n Y.k (Y.tabL x) (Y.tabM w.1) γ i

/-- The honest prover's new witness: messages and randomness, folded. -/
def honW (w : Y.Cin.N.Wit) (c : Y.Coin) (γ : Fin Y.k → E) : Y.Cout.N.Wit :=
  (Sum.elim (foldV γ fun a => w.1 (.inl a))
      (Sum.elim (foldV (Y.pre γ) fun a => w.1 (.inr a)) (foldV (Y.pre γ) (Y.pk c.1))),
    Sum.elim (foldV γ fun a => w.2 (.inl a))
      (Sum.elim (foldV (Y.pre γ) fun a => w.2 (.inr a)) (foldV (Y.pre γ) c.2)))

/-- with what the honest prover ends, at the coefficient ε and the challenges γ -/
def honEnd (w : Y.Cin.N.Wit) (x : Y.Xi) (c : Y.Coin) (ε : E) (γ : HPt Y.vars) :
    Y.Xo × Y.Cout.N.Wit :=
  ((hFin Y.vars (hMu Y.vars c.1 + x.1 * ε) (Y.honQ w x c.1 ε γ) γ,
      (((x.2.1, sPt Y.n Y.k γ), ε),
        (((x.2.2, Y.pre (sPt Y.n Y.k γ)), ε * Y.late (sPt Y.n Y.k γ)), sPt Y.n Y.k γ))),
    Y.honW w c (sPt Y.n Y.k γ))

/-- The honest side. Nothing is withheld. -/
def hon : Y.ior.Honest Y.Cin.N.Wit Y.Cout.N.Wit where
  Coin := Y.Coin
  strat := fun w x c =>
    ((Y.Cw.enc (Y.pk c.1) c.2, hMu Y.vars c.1),
      fun e => sStrat Y.val Y.n Y.k (Y.honQ w x c.1 (Y.val e)) (Y.honEnd w x c (Y.val e)))
  Bad := ∅
  Hid := fun _ _ => ∅

/-- the summand of the sumcheck, as a function of a point -/
def summand (w : Y.Cin.N.Wit) (x : Y.Xi) (W : HIdx Y.vars → E) (ε : E) (γ : HPt Y.vars) : E :=
  hU Y.vars W γ +
    ε * (∑ c, Y.sl.fix (x.2.1, sPt Y.n Y.k γ) c * foldV (sPt Y.n Y.k γ) (fun a => w.1 (.inl a)) c +
        (∑ c, Y.slS.fix (x.2.2, Y.pre (sPt Y.n Y.k γ)) c *
            foldV (Y.pre (sPt Y.n Y.k γ)) (fun a => w.1 (.inr a)) c) *
          Y.late (sPt Y.n Y.k γ))

/-- The budget of further reads: native positions of the fresh mask that lie behind at most t long
positions. -/
def bud (t : ℕ) : Rho Y.ior.shape → Finset (OPos Y.ior.shape) → Prop := fun _ T =>
  ∃ X : Finset P, X.card ≤ t ∧ ∀ p ∈ T, ∃ q ∈ X.biUnion Y.srcW, p = Sum.inl q

/-- The errors, as counts of challenges. Lst j: the list size of the complex after j rounds; mC j,
mS j, mW j: the counts of mutual correlated agreement of the three tables after j rounds. -/
def err (Lst mC mS mW : ℕ → ℕ) : Err Y.ior.shape :=
  (Lst 0, sErr Y.n Y.k fun i =>
      mC (i + 1) + (if i + 1 ≤ Y.h then mS (i + 1) + mW (i + 1) else 0) + Lst i * Y.n)

/-- the complex after j rounds: rows on the cubes of the variables that are left -/
abbrev stage (j : ℕ) : LdCode E P :=
  (Y.C.il (Fin (Y.k - j) → Bool)).pair
    ((Y.Z.il (Fin (Y.h - j) → Bool)).pair (Y.Zw.il (Fin (Y.h - j) → Bool)))

/-- What the errors require of the codes, at the radius e. -/
structure ErrOK [Fintype P] (e : ℕ) (Lst mC mS mW : ℕ → ℕ) : Prop where
  list : ∀ j, j ≤ Y.k → (Y.stage j).ListAt e (Lst j)
  mcaC : ∀ j, 1 ≤ j → j ≤ Y.k → (Y.C.il (Fin (Y.k - j) → Bool)).MCAat e (mC j)
  mcaS : ∀ j, 1 ≤ j → j ≤ Y.h → (Y.Z.il (Fin (Y.h - j) → Bool)).MCAat e (mS j)
  mcaW : ∀ j, 1 ≤ j → j ≤ Y.h → (Y.Zw.il (Fin (Y.h - j) → Bool)).MCAat e (mW j)

/-- The numbers. -/
def nums (t : ℕ) (Lst mC mS mW : ℕ → ℕ) : IOR.Nums Unit Y.ior :=
  ⟨Y.err Lst mC mS mW, 0, 0, Y.bud t, fun _ => ∅⟩

end SumPar

namespace Spec
section
variable (E P : Type) [Field E] [Fintype E] [Fintype P]

/-- The block's oracles are strings; and, under `Y.C.Laws`, `Y.Z.Laws` and `Y.Zw.Laws`, verifier and
new oracles read what the term declares. -/
def ld_sum_point : Prop := ∀ Y : SumPar E P, Nonempty Y.ior.shape.IsPoint
def ld_sum_local : Prop := ∀ Y : SumPar E P, Y.C.Laws → Y.Z.Laws → Y.Zw.Laws → Y.ior.IsLocal

/-- Under `2 ≤ Y.n`: the honest prover is the sumcheck prover: its first scalar is the sum of U over
the cube, and its round polynomials are those of the summand U + ε (claim polynomial). -/
def ld_sum_rounds : Prop :=
  ∀ Y : SumPar E P, 2 ≤ Y.n →
    ∀ (w : Y.Cin.N.Wit) (x : Y.Xi) (W : HIdx Y.vars → E) (ε : E) (γ : HPt Y.vars),
      hSumAll Y.vars (hU Y.vars W) = hMu Y.vars W ∧
      HRounds Y.vars (Y.summand w x W ε) (Y.honQ w x W ε γ) γ

/-- what the honest prover sends in a run is its closed form at the run's challenges -/
def ld_sum_run : Prop :=
  ∀ (Y : SumPar E P) (w : Y.Cin.N.Wit) (x : Y.Xi) (c : Y.Coin) (ρ : Rho Y.ior.shape),
    Y.qs ((Y.hon.strat w x c).run ρ).1.plains = Y.honQ w x c.1 (Y.eps ρ) (Y.gam ρ) ∧
    Y.mu ((Y.hon.strat w x c).run ρ).1.plains = hMu Y.vars c.1 ∧
    ((Y.hon.strat w x c).run ρ).1.rho = ρ ∧
    ((Y.hon.strat w x c).run ρ).2 = Y.honEnd w x c (Y.eps ρ) (Y.gam ρ)

/-- Perfect completeness, from the main relation to the main relation (under `2 ≤ Y.n`, `Y.PackOK`,
`Y.C.Laws`, `Y.Z.Laws`, `Y.Zw.Laws`). -/
def ld_sum_acc : Prop :=
  ∀ Y : SumPar E P, 2 ≤ Y.n → Y.PackOK → Y.C.Laws → Y.Z.Laws → Y.Zw.Laws →
    Y.hon.Acc (Con Y.Cin.N Y.slIn.Holds) (Con Y.Cout.N Y.slOut.Holds)

/-- Under `2 ≤ Y.n`: honest-verifier zero knowledge, exact: if the encoding of the fresh mask table
hides t long positions under its transformation. -/
def ld_sum_exact : Prop :=
  ∀ (Y : SumPar E P) (t : ℕ), 2 ≤ Y.n → Y.Cw.Zk t → Y.hon.Exact (Con Y.Cin.N Y.slIn.Holds) (Y.bud t)

end
end Spec
end
end Cb
