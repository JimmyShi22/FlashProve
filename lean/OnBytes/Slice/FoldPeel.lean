-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FoldPeel.lean: the rounds of a fold are taken off a written proximity test by the
library's theorem on its sumcheck that folds.

A fold of the written test has one round that sends the sum of a hiding polynomial and draws a
coefficient, and then one round for each row variable, which sends the constant and the quadratic
coefficient of a round polynomial and draws an element. The library's block (Cb/Ld/LdSum.lean) has
the same rounds in its own types. It differs in two things. Its prover sends the fresh mask rows in
the first round; the written prover has sent them before, in the stage's tree. Its prover sends all
three coefficients of a round polynomial; the written verifier computes the linear one from the
running claim. The maps of this file put both in (OnBytes/Slice/Carry.lean).

`fold_block_sem`. Let a claim (a target, a vector of coefficients, a word) before the fold have no
witness in the relaxed relation of the stage. Then the prover has lost in the fold's rounds and what
follows, if it has lost wherever a test of work fails, and has lost in what follows whenever the
claim after the fold has no witness. The claim after the fold is given in the field: the target
`claimF`, the vector `midVec`, the word `foldWords`, at the drawn point `ptF`.
`fold_block`. The same, where the claim before the fold is a row of the format's verifier and the
claim after the fold is what the format's own function `foldStep` (Fmt/M1Fold.lean) computes.

What is asked: the laws and a distance of the stage's two codes, bounds on lists and on exceptional
points in the library's own words, and what the rounds send and draw.

The format's function cuts the vector of hiding weights to the length of the folded mask row, which
depends on the length of the row that it is given. So the library's block is taken with the weights
cut at a length n0. Its knowledge soundness asks only the degrees of the weights.

Main definitions: `Sg.par`, `hideW`, `carT`, `carF`, `foldErr`, `ptF`, `claimF`, `midVec`,
`foldWords`. Main theorems: `fold_block_sem`, `fold_block`.
Not claimed. No bound on a list or on a count of exceptional points. Nothing on an honest prover.
-/
import OnBytes.Slice.Peel
import OnBytes.Slice.Stage
import OnBytes.Slice.RoundsMaps
import OnBytes.Slice.SimFold
import Cb.Ld.LdSumKnowProofs
import Cb.Ld.LdSumPackProofs
import Cb.Ld.LdHideShort
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## The library's fold at a stage -/

/-- The public weights on the folded fresh mask row, as functions of the point: entry j of the
format's vector of weights; 0 from the entry n0 on. -/
def hideW (h g n0 : ℕ) (z : Fin (h + g) → GE) (j : ℕ) : GE :=
  if j < n0 then QwAt (hidePlace h g) (QwC h g 1) z j else 0

/-- The library's fold at the codes of a stage. Round polynomials have degree 2. A challenge is
an element of the field. A form is its vector of coefficients. The fresh mask rows are read as the
carried ones are. The packing of an honest prover is not read by knowledge soundness. -/
@[reducible] def Sg.par (s : Sg) (n0 : ℕ) : SumPar GE s.Ps where
  h := s.h
  g := s.g
  n := 2
  Ch := GE
  val := id
  C := s.cM
  Z := s.cZ
  AaW := Unit
  TW := s.cZ.T
  srcW := s.cZ.src
  St := (Fin (s.h + s.g) → Bool) × s.cM.J → GE
  StS := (Fin s.h → Bool) × s.cZ.J → GE
  sl := Slf.idf
  slS := Slf.idf
  pk := fun _ _ => 0
  Qw := fun z j => hideW s.h s.g n0 z j.val

/-- Every weight is a polynomial in the point, of degree at most 1 in each of the first h variables
and at most 2 in each of the others. -/
theorem hideW_deg (h g n0 j : ℕ) :
    Alg.DegLE (fun i : Fin (h + g) => if i.val < h then 2 - 1 else 2)
      fun z => hideW h g n0 z j := by
  by_cases hj : j < n0
  · have h1 : (fun z : Fin (h + g) → GE => hideW h g n0 z j) =
        fun z => QwAt (hidePlace h g) (QwC h g 1) z j := by
      funext z
      unfold hideW
      rw [if_pos hj]
    rw [h1]
    exact Cb.ld_pack_deg_place GE (Fin (h + g)) (PCol h g 1) ℕ (hidePlace h g) (QwC h g 1) _
      (Cb.ld_pack_deg GE h g 1) j
  · have h1 : (fun z : Fin (h + g) → GE => hideW h g n0 z j) = fun _ => 0 := by
      funext z
      unfold hideW
      rw [if_neg hj]
    rw [h1]
    exact Alg.DegLE.const _ 0

/-- The library's fold at a stage is round-by-round knowledge sound. -/
theorem par_know (s : Sg) (n0 d e : ℕ) (Lst mC mS mW : ℕ → ℕ)
    (hC : Spec.CodesOK GE s.Ps s.cM s.cZ s.cZ d e) (hE : (s.par 0).ErrOK e Lst mC mS mW) :
    (s.par n0).ior.red.Know (fun _ => True) (ConL (s.par n0).Cin.N e (s.par n0).slIn.Holds)
      (ConL (s.par n0).Cout.N e (s.par n0).slOut.Holds) ((s.par n0).ext d)
      ((s.par 0).err Lst mC mS mW) := by
  have hE' : (s.par n0).ErrOK e Lst mC mS mW := ⟨hE.list, hE.mcaC, hE.mcaS, hE.mcaW⟩
  have hQ : (s.par n0).QwDeg := fun j => hideW_deg s.h s.g n0 j.val
  exact ld_sum_know GE s.Ps (s.par n0) d e Lst mC mS mW hC hE' Function.injective_id le_rfl hQ

/-- On consistent round polynomials the library's verifier does not refuse. -/
theorem sum_out {P : Type} (Y : SumPar GE P) (x : Y.Xi) (y : Y.Cin.Word) (τ : Tr Y.shape)
    (h : HCons Y.vars (Y.mu τ.plains + x.1 * Y.eps τ.rho) (Y.qs τ.plains) (Y.gam τ.rho)) :
    Y.ior.red.out (x, y) τ = some (Y.newX x τ.rho
      (hFin Y.vars (Y.mu τ.plains + x.1 * Y.eps τ.rho) (Y.qs τ.plains) (Y.gam τ.rho)),
      Y.imp y τ) := by
  show Option.map _ (Y.out x τ) = _
  unfold SumPar.out
  rw [if_pos h]
  rfl

/-! ## The maps of the rounds -/

/-- Element number i that a written prover message sends, in the field; 0 beyond the end. -/
def sentAt (d : PQ.RD) (m : (wRound d).Msg) (i : ℕ) : GE := (ansOf d m).getD i 0

/-- The round polynomial that a written message describes at the running claim σ. The message has
the constant and the quadratic coefficient. The linear coefficient is the one with which the values
at 0 and 1 add up to σ. -/
def fillT (σ : GE) (d : PQ.RD) (m : (wRound d).Msg) : Fin (2 + 1) → GE :=
  hFill (HVar.plain GE 2) ((1 : Fin 3), (1 : GE)) σ
    (fun t : Fin 2 => if t.val = 0 then sentAt d m 0 else sentAt d m 1)

/-- The maps of k rounds of the sumcheck, from the running claim σ on. -/
def carT (dT : PQ.RD) : (k : ℕ) → GE →
    Carry (PQ.uL (ckP .two) (List.replicate k dT)) (List.replicate k (sRound GE GE 2))
  | 0, _ => ()
  | k + 1, σ =>
      (fun m => ((), fillT σ dT m), fun _ => chalTo dT (gOne _),
        fun m c => carT dT k (hev (fillT σ dT m) (gOne _ (valsOf dT c))))

/-- The maps of all rounds of a fold. t0: the target before the fold. z: the fresh mask rows, which
were sent before the fold. -/
def carF (s : Sg) (n0 : ℕ) (dE dT : PQ.RD) (t0 : GE) (z : s.cFr.Word) :
    Carry (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT)) (s.par n0).ior.red.shape :=
  (fun m => (z, sentAt dE m 0), fun _ => chalTo dE (gOne _),
    fun m c => carT dT (s.h + s.g) (sentAt dE m 0 + t0 * gOne _ (valsOf dE c)))

/-! ## What is asked of the rounds, and the error counts -/

/-- What the rounds of a fold send and draw: the first one element and one element, each of the
others two elements and one element. -/
structure FoldRounds (dE dT : PQ.RD) : Prop where
  eps : SendsDraws dE 1 1 0 0
  two : SendsDraws dT 2 1 0 0

/-- The numbers in the law of the format's sampler, for k equal rounds. -/
def wsT (dT : PQ.RD) : (k : ℕ) → Err (PQ.uL (ckP .two) (List.replicate k dT))
  | 0 => ()
  | k + 1 => ((bsRound .two dT.entry dT.kind).w, wsT dT k)

/-- The same for all rounds of a fold. -/
def wsF (dE dT : PQ.RD) (k : ℕ) : Err (PQ.uL (ckP .two) (dE :: List.replicate k dT)) :=
  ((bsRound .two dE.entry dE.kind).w, wsT dT k)

/-- The error counts of the written rounds of a fold: the library's, each times the number in
the law of the format's sampler. -/
def foldErr (s : Sg) (dE dT : PQ.RD) (Lst mC mS mW : ℕ → ℕ) :
    Err (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT)) :=
  mulErr _ (s.par 0).ior.red.shape (wsF dE dT (s.h + s.g)) ((s.par 0).err Lst mC mS mW)

/-- In each of k rounds at most as many written verifier messages go to one element as the law of
the format's sampler says. -/
theorem carT_fib {dT : PQ.RD} (h : SendsDraws dT 2 1 0 0) :
    ∀ (k : ℕ) (σ : GE), (carT dT k σ).Fib (wsT dT k) := by
  intro k
  induction k with
  | zero =>
    intro σ
    exact trivial
  | succ k ih =>
    intro σ
    exact And.intro (fun _ c' => chalTo_fib dT _ h.gOne_inj h.logN c') fun _ _ => ih _

/-- The same for all rounds of a fold. -/
theorem carF_fib (s : Sg) (n0 : ℕ) {dE dT : PQ.RD} (h : FoldRounds dE dT) (t0 : GE)
    (z : s.cFr.Word) : (carF s n0 dE dT t0 z).Fib (wsF dE dT (s.h + s.g)) :=
  And.intro (fun _ c' => chalTo_fib dE _ h.eps.gOne_inj h.eps.logN c')
    fun _ _ => carT_fib h.two _ _

/-! ## The image of a written transcript -/

/-- Among k rounds, a transcript without an image has failed a test of work. -/
theorem carT_none (dT : PQ.RD) : ∀ (k : ℕ) (σ : GE)
    (τ : Tr (PQ.uL (ckP .two) (List.replicate k dT))),
    (carT dT k σ).tr τ = none → PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false := by
  intro k
  induction k with
  | zero =>
    intro σ τ h
    exact absurd h (Option.some_ne_none _)
  | succ k ih =>
    rintro σ ⟨m, c, τ⟩ h
    have h1 : (chalTo dT (gOne _) c).bind (fun c' =>
        ((carT dT k (hev (fillT σ dT m) (gOne _ (valsOf dT c)))).tr τ).map
          fun τ' => (((), fillT σ dT m), c', τ')) = none := h
    show (GChal.pass (b := dT.entry.work) c &&
      PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ)) = false
    cases hc : chalTo dT (gOne _) c with
    | none => rw [chalTo_none dT _ c hc, Bool.false_and]
    | some c' =>
      cases ht : (carT dT k (hev (fillT σ dT m) (gOne _ (valsOf dT c)))).tr τ with
      | none => rw [ih _ τ ht, Bool.and_false]
      | some τ' =>
        rw [hc, ht] at h1
        exact absurd h1 (Option.some_ne_none _)

/-- A transcript without an image has failed a test of work. -/
theorem carF_none (s : Sg) (n0 : ℕ) (dE dT : PQ.RD) (t0 : GE) (z : s.cFr.Word)
    (τ : Tr (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT)))
    (h : (carF s n0 dE dT t0 z).tr τ = none) :
    PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false := by
  obtain ⟨m, c, τ⟩ := τ
  have h1 : (chalTo dE (gOne _) c).bind (fun c' =>
      ((carT dT (s.h + s.g) (sentAt dE m 0 + t0 * gOne _ (valsOf dE c))).tr τ).map
        fun τ' => ((z, sentAt dE m 0), c', τ')) = none := h
  show (GChal.pass (b := dE.entry.work) c &&
    PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ)) = false
  cases hc : chalTo dE (gOne _) c with
  | none => rw [chalTo_none dE _ c hc, Bool.false_and]
  | some c' =>
    cases ht : (carT dT (s.h + s.g) (sentAt dE m 0 + t0 * gOne _ (valsOf dE c))).tr τ with
    | none => rw [carT_none dT _ _ τ ht, Bool.and_false]
    | some τ' =>
      rw [hc, ht] at h1
      exact absurd h1 (Option.some_ne_none _)

/-- The image of a transcript of a fold: the fresh mask rows and the sent sum, the drawn
coefficient, the image of the other rounds. -/
theorem carF_some (s : Sg) (n0 : ℕ) (dE dT : PQ.RD) (t0 : GE) (z : s.cFr.Word)
    (m : (wRound dE).Msg) (c : (wRound dE).Chal)
    (τ : Tr (PQ.uL (ckP .two) (List.replicate (s.h + s.g) dT))) (τ' : Tr (s.par n0).ior.red.shape)
    (h : (carF s n0 dE dT t0 z).tr (m, c, τ) = some τ') :
    ∃ τ₂, (carT dT (s.h + s.g) (sentAt dE m 0 + t0 * gOne _ (valsOf dE c))).tr τ = some τ₂ ∧
      τ' = ((z, sentAt dE m 0), gOne _ (valsOf dE c), τ₂) := by
  have h1 : (chalTo dE (gOne _) c).bind (fun c' =>
      ((carT dT (s.h + s.g) (sentAt dE m 0 + t0 * gOne _ (valsOf dE c))).tr τ).map
        fun τ₂ => ((z, sentAt dE m 0), c', τ₂)) = some τ' := h
  cases hc : chalTo dE (gOne _) c with
  | none =>
    rw [hc] at h1
    exact absurd h1.symm (Option.some_ne_none _)
  | some c' =>
    cases ht : (carT dT (s.h + s.g) (sentAt dE m 0 + t0 * gOne _ (valsOf dE c))).tr τ with
    | none =>
      rw [hc, ht] at h1
      exact absurd h1.symm (Option.some_ne_none _)
    | some τ₂ =>
      rw [hc, ht] at h1
      have hc' : c' = gOne _ (valsOf dE c) := chalTo_some dE _ c c' hc
      refine ⟨τ₂, rfl, ?_⟩
      rw [← hc']
      exact (Option.some.inj h1).symm

/-- The point that k written rounds draw. -/
def ptF (dT : PQ.RD) : (k : ℕ) → Tr (PQ.uL (ckP .two) (List.replicate k dT)) → Fin k → GE
  | 0, _ => Fin.elim0
  | k + 1, (_, c, τ) => Fin.cons (α := fun _ => GE) (gOne _ (valsOf dT c)) (ptF dT k τ)

/-- The running claim after k written rounds, from the running claim σ: in each round, the value
of the round polynomial at the drawn element. -/
def claimF (dT : PQ.RD) : (k : ℕ) → GE →
    Tr (PQ.uL (ckP .two) (List.replicate k dT)) → GE
  | 0, σ, _ => σ
  | k + 1, σ, (m, c, τ) => claimF dT k (hev (fillT σ dT m) (gOne _ (valsOf dT c))) τ

/-- The values at 0 and 1 of the round polynomial that a message describes add up to the running
claim. -/
theorem phi_fillT (σ : GE) (d : PQ.RD) (m : (wRound d).Msg) :
    (HVar.plain GE 2).phi (fillT σ d m) = σ :=
  phi_fill (HVar.plain GE 2) ((1 : Fin 3), (1 : GE)) ((one_mul _).trans mon_one) σ _

/-- The image of k written rounds: its round polynomials are consistent, its last value is the
running claim, its point is the drawn point. -/
theorem carT_some (dT : PQ.RD) : ∀ (k : ℕ) (σ : GE)
    (τ : Tr (PQ.uL (ckP .two) (List.replicate k dT))) (τ' : Tr (List.replicate k (sRound GE GE 2))),
    (carT dT k σ).tr τ = some τ' →
      HCons (sVars GE 2 k) σ (sQ 2 k τ'.plains) (sG id 2 k τ'.rho) ∧
      hFin (sVars GE 2 k) σ (sQ 2 k τ'.plains) (sG id 2 k τ'.rho) = claimF dT k σ τ ∧
      sPt 2 k (sG id 2 k τ'.rho) = ptF dT k τ
  | 0, _, _, _, _ => ⟨trivial, rfl, rfl⟩
  | k + 1, σ, (m, c, τ), τ', h => by
      have h1 : (chalTo dT (gOne _) c).bind (fun c' =>
          ((carT dT k (hev (fillT σ dT m) (gOne _ (valsOf dT c)))).tr τ).map fun τ₂ =>
            ((((), fillT σ dT m), c', τ₂) : Tr (List.replicate (k + 1) (sRound GE GE 2)))) =
          some τ' := h
      cases hc : chalTo dT (gOne _) c with
      | none =>
        rw [hc] at h1
        cases h1
      | some c' =>
        obtain rfl := chalTo_some dT _ c c' hc
        cases ht : (carT dT k (hev (fillT σ dT m) (gOne _ (valsOf dT c)))).tr τ with
        | none =>
          rw [hc, ht] at h1
          cases h1
        | some τ₂ =>
          rw [hc, ht] at h1
          obtain rfl := Option.some.inj h1
          obtain ⟨ic, ifn, ipt⟩ := carT_some dT k _ τ τ₂ ht
          exact ⟨⟨phi_fillT σ dT m, ic⟩, ifn,
            congrArg (Fin.cons (α := fun _ => GE) _) ipt⟩

/-! ## The claim after a fold, in the field -/

/-- The coefficients after a fold, from the coefficients v before it, the drawn coefficient ε
and the drawn point γ: on the folded main row, ε times the main rows' coefficients folded at γ; on
the folded carried mask row, ε times the later coordinates of γ times the mask rows' coefficients
folded at the first h coordinates; on the folded fresh mask row, the hiding weights at γ. -/
def midVec (s : Sg) (n0 : ℕ) (v : s.cIn.J → GE) (ε : GE)
    (γ : Fin (s.h + s.g) → GE) : s.cMid.J → GE
  | .inl j => (∑ b, v (.inl (b, j)) * Alg.eqk γ b) * ε
  | .inr (.inl j) => (∑ b, v (.inr (b, j)) * Alg.eqk (preP s γ) b) *
      (ε * ∏ t : Fin s.g, γ (Fin.natAdd s.h t))
  | .inr (.inr j) => hideW s.h s.g n0 γ j.val

/-- The three folded words, from the word y of main rows and carried mask rows and the word z of
fresh mask rows. -/
def foldWords (s : Sg) (y : s.cIn.Word) (z : s.cFr.Word) (γ : Fin (s.h + s.g) → GE) :
    s.cMid.Word :=
  LdCode.mkW (SumPar.foldW s.cM γ (LdCode.fstW y))
    (LdCode.mkW (C₁ := s.cZ) (C₂ := s.cZ) (SumPar.foldW s.cZ (preP s γ) (LdCode.sndW y))
      (SumPar.foldW s.cZ (preP s γ) z))

/-- The library's form after the fold, as a vector. -/
theorem slOut_mid (s : Sg) (n0 : ℕ) (v : s.cIn.J → GE) (ε : GE) (γ : Fin (s.h + s.g) → GE) :
    (s.par n0).slOut (((fun x => v (.inl x), γ), ε),
      (((fun x => v (.inr x), (s.par n0).pre γ), ε * (s.par n0).late γ), γ)) =
      midVec s n0 v ε γ :=
  funext fun j => by rcases j with j | j | j <;> rfl

/-- The rounds of a fold are taken off, with the claims in the field. If the claim (t0, v, y)
has no witness, the prover has lost in the fold's rounds and t, given that it has lost wherever a
test of work fails and, in t, whenever the claim after the fold (`claimF`, `midVec`, `foldWords` at
the point `ptF`) has no witness. z: the fresh mask rows. n0: the length at which the hiding weights
are cut. -/
theorem fold_block_sem (s : Sg) (n0 d e : ℕ) (Lst mC mS mW : ℕ → ℕ)
    (hC : Spec.CodesOK GE s.Ps s.cM s.cZ s.cZ d e) (hE : (s.par 0).ErrOK e Lst mC mS mW)
    (dE dT : PQ.RD) (hR : FoldRounds dE dT) (t : Shape) (εt : Err t)
    (t0 : GE) (v : s.cIn.J → GE) (y : s.cIn.Word) (z : s.cFr.Word)
    (hno : ∀ w, ¬ s.RIn e ((t0, v), y) w)
    (bad : Tr (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT) ++ t) → Prop)
    (hp : ∀ τ b, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad (Tr.app τ b))
    (H : ∀ (m : (wRound dE).Msg) (c : (wRound dE).Chal)
        (τ : Tr (PQ.uL (ckP .two) (List.replicate (s.h + s.g) dT))),
      (∀ w, ¬ s.RMid e ((claimF dT _ (sentAt dE m 0 + t0 * gOne _ (valsOf dE c)) τ,
        midVec s n0 v (gOne _ (valsOf dE c)) (ptF dT _ τ)), foldWords s y z (ptF dT _ τ)) w) →
      Doomed t εt fun b =>
        bad (Tr.app (s := PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT)) (m, c, τ) b)) :
    Doomed _ (Err.app (foldErr s dE dT Lst mC mS mW) εt) bad := by
  have hno' : ∀ w, ¬ ConL (s.par n0).Cin.N e (s.par n0).slIn.Holds
      ((t0, (fun x => v (.inl x), fun x => v (.inr x))), y) w := by
    intro w hw
    refine hno w ⟨hw.1, ?_⟩
    have h2 : (s.par n0).slIn (fun x => v (.inl x), fun x => v (.inr x)) = v :=
      funext fun j => by cases j <;> rfl
    have h3 := hw.2
    unfold Slf.Holds at h3
    rw [h2] at h3
    exact h3
  refine peel (s.par n0).ior.red (par_know s n0 d e Lst mC mS mW hC hE) _
    trivial hno' (carF s n0 dE dT t0 z) (wsF dE dT (s.h + s.g))
    (carF_fib s _ hR _ z) εt bad ?_ ?_
  · intro τ hτ
    exact doomed_of_all _ _ _ fun b => hp τ b (carF_none s _ dE dT _ z τ hτ)
  · rintro ⟨m, c, τ⟩ τ' hτ hout
    obtain ⟨τ₂, hτ₂, rfl⟩ := carF_some s n0 dE dT t0 z m c τ τ' hτ
    obtain ⟨hcons, hfin, hpt⟩ := carT_some dT _ _ τ τ₂ hτ₂
    have hpt' : (s.par n0).pt (Tr.rho (s := (s.par n0).shape)
        ((z, sentAt dE m 0), gOne _ (valsOf dE c), τ₂)) = ptF dT _ τ := hpt
    refine H m c τ fun w hw => ?_
    refine hout _ w (sum_out (s.par n0) (t0, (fun x => v (.inl x), fun x => v (.inr x))) y
      ((z, sentAt dE m 0), gOne _ (valsOf dE c), τ₂) hcons) ⟨?_, ?_⟩
    · have e3 : (s.par n0).imp y ((z, sentAt dE m 0), gOne _ (valsOf dE c), τ₂) =
          foldWords s y z (ptF dT _ τ) := by
        unfold SumPar.imp
        rw [hpt']
        rfl
      rw [← e3] at hw
      exact hw.1
    · unfold SumPar.newX Slf.Holds
      rw [hpt']
      show ∑ j, (s.par n0).slOut (((fun x => v (.inl x), ptF dT _ τ), gOne _ (valsOf dE c)),
        (((fun x => v (.inr x), (s.par n0).pre (ptF dT _ τ)),
          gOne _ (valsOf dE c) * (s.par n0).late (ptF dT _ τ)), ptF dT _ τ)) j * w.1 j = _
      rw [slOut_mid]
      exact hw.2.trans hfin.symm

/-! ## What the format's decision reads of the rounds -/

/-- The pairs that k written rounds send. -/
def qsOf (dT : PQ.RD) : (k : ℕ) → Tr (PQ.uL (ckP .two) (List.replicate k dT)) →
    List (Fmt.M1.E × Fmt.M1.E)
  | 0, _ => []
  | k + 1, (m, c, τ) =>
      ((rvOf dT m c).sent.getD 0 Fmt.Fld.zeroE, (rvOf dT m c).sent.getD 1 Fmt.Fld.zeroE) ::
        qsOf dT k τ

/-- The elements that are drawn in k written rounds. -/
def gsOf (dT : PQ.RD) : (k : ℕ) → Tr (PQ.uL (ckP .two) (List.replicate k dT)) → List Fmt.M1.E
  | 0, _ => []
  | k + 1, (m, c, τ) => (rvOf dT m c).els.getD 0 Fmt.Fld.zeroE :: gsOf dT k τ

/-- A list of length 1 is the list of its first member. -/
private theorem list_one {α : Type} (d : α) (l : List α) (h : l.length = 1) : l = [l.getD 0 d] := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · exact absurd h (by simp only [List.length_nil]; omega)
  · rfl
  · exact absurd h (by simp only [List.length_cons]; omega)

/-- A list of length 2 is the list of its first two members. -/
private theorem list_two {α : Type} (d : α) (l : List α) (h : l.length = 2) :
    l = [l.getD 0 d, l.getD 1 d] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact absurd h (by simp only [List.length_nil]; omega)
  · exact absurd h (by simp only [List.length_cons, List.length_nil]; omega)
  · rfl
  · exact absurd h (by simp only [List.length_cons]; omega)

/-- One step of takeRounds on a round that sends two elements and draws one. -/
private theorem takeRounds_cons (n : ℕ) (v : Fmt.M1.RV) (rs : Fmt.M1.Rs)
    (hs : v.sent.length = 2) (he : v.els.length = 1) (hp : v.poss.length = 0) :
    Fmt.M1.takeRounds (n + 1) (v :: rs) = (Fmt.M1.takeRounds n rs).map fun x =>
      ((v.sent.getD 0 Fmt.Fld.zeroE, v.sent.getD 1 Fmt.Fld.zeroE) :: x.1,
        v.els.getD 0 Fmt.Fld.zeroE :: x.2.1, x.2.2) := by
  obtain ⟨sent, els, poss⟩ := v
  have e2 : sent = [sent.getD 0 Fmt.Fld.zeroE, sent.getD 1 Fmt.Fld.zeroE] := list_two _ sent hs
  have e1 : els = [els.getD 0 Fmt.Fld.zeroE] := list_one _ els he
  have e0 : poss = [] := List.eq_nil_of_length_eq_zero hp
  generalize sent.getD 0 Fmt.Fld.zeroE = a at e2 ⊢
  generalize sent.getD 1 Fmt.Fld.zeroE = b at e2 ⊢
  generalize els.getD 0 Fmt.Fld.zeroE = g at e1 ⊢
  subst e2 e1 e0
  rfl

/-- The decision takes the k rounds off its list and reads these pairs and elements. -/
theorem takeRounds_rsOf {dT : PQ.RD} (h : SendsDraws dT 2 1 0 0) :
    ∀ (k : ℕ) (τ : Tr (PQ.uL (ckP .two) (List.replicate k dT))),
      Fmt.M1.takeRounds k (rsOf _ τ) = some (qsOf dT k τ, gsOf dT k τ, []) := by
  intro k
  induction k with
  | zero =>
    intro τ
    rfl
  | succ k ih =>
    rintro ⟨m, c, τ⟩
    have step := takeRounds_cons k (rvOf dT m c) (rsOf (List.replicate k dT) τ)
      (h.sent_length m c) (h.els_length m c) (h.poss_length m c)
    rw [ih τ] at step
    exact step

/-- The format's running claim, one round unfolded. -/
theorem claimOf_cons (f : Fmt.Fld) (k : ℕ) (first : Fmt.M1.E) (q : Fmt.M1.E × Fmt.M1.E)
    (qs : List (Fmt.M1.E × Fmt.M1.E)) (g : Fmt.M1.E) (gs : List Fmt.M1.E) :
    Fmt.M1.claimOf f (k + 1) first (q :: qs) (g :: gs) =
      Fmt.M1.claimOf f k (Fmt.M1.nextClaim f first q g) qs gs := by
  unfold Fmt.M1.claimOf
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  rfl

/-- An element that the decision reads as sent, in the field. -/
theorem toE_sent (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) (i : ℕ) :
    toE ((rvOf d m c).sent.getD i Fmt.Fld.zeroE) = sentAt d m i := by
  unfold sentAt
  rw [← rvOf_sent d m c, ← toE_zeroE, List.getD_map]

/-- The first element that the decision reads as drawn, in the field. -/
theorem toE_els (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) :
    toE ((rvOf d m c).els.getD 0 Fmt.Fld.zeroE) = gOne _ (valsOf d c) :=
  (gOne_rvOf d m c).symm

/-- What the decision reads of a round that sends one element and draws one. -/
theorem rvOf_one {d : PQ.RD} {a : ℕ} (h : SendsDraws d 1 1 0 a) (m : (wRound d).Msg)
    (c : (wRound d).Chal) :
    rvOf d m c = ⟨[(rvOf d m c).sent.getD 0 Fmt.Fld.zeroE],
      [(rvOf d m c).els.getD 0 Fmt.Fld.zeroE], (rvOf d m c).poss⟩ := by
  have e1 := list_one Fmt.Fld.zeroE _ (h.sent_length m c)
  have e2 := list_one Fmt.Fld.zeroE _ (h.els_length m c)
  rw [← e1, ← e2]

/-- The running claim in the field is the format's. -/
theorem claimF_eq (dT : PQ.RD) : ∀ (k : ℕ) (first : Fmt.M1.E)
    (τ : Tr (PQ.uL (ckP .two) (List.replicate k dT))),
    claimF dT k (toE first) τ =
      toE (Fmt.M1.claimOf .two k first (qsOf dT k τ) (gsOf dT k τ))
  | 0, _, _ => rfl
  | k + 1, first, (m, c, τ) => by
      show claimF dT k (hev (fillT (toE first) dT m) (gOne _ (valsOf dT c))) τ =
        toE (Fmt.M1.claimOf .two (k + 1) first (_ :: qsOf dT k τ) (_ :: gsOf dT k τ))
      rw [claimOf_cons, ← claimF_eq dT k, toE_nextClaim_hev, toE_sent, toE_sent, toE_els]
      rfl

/-- The drawn point is the format's list of drawn elements. -/
theorem ptF_eq (dT : PQ.RD) : ∀ (k : ℕ) (τ : Tr (PQ.uL (ckP .two) (List.replicate k dT))),
    ptF dT k τ = ptL k (gsOf dT k τ)
  | 0, _ => funext fun i => i.elim0
  | k + 1, (m, c, τ) => funext fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (toE_els dT m c).symm
      · exact congrFun (ptF_eq dT k τ) j

/-! ## The library's output is the format's -/

/-- The length of the two folded mask rows' vectors of coefficients. It does not depend on what is
sent or drawn. -/
def maskLen (s : Sg) (G : Fmt.M1.GRow) : ℕ :=
  (Fmt.M1.foldStep .two (s.h + s.g) s.h G Fmt.Fld.zeroE Fmt.Fld.zeroE [] []).d0.size

/-- The library's form after the fold is the vector that the format's function computes. -/
theorem slOut_eq (s : Sg) (G : Fmt.M1.GRow) (sigma eps : Fmt.M1.E)
    (qs : List (Fmt.M1.E × Fmt.M1.E)) (g : List Fmt.M1.E) :
    (s.par (maskLen s G)).slOut
      (((fun x => vecIn s G (.inl x), ptL (s.h + s.g) g), toE eps),
        (((fun x => vecIn s G (.inr x), (s.par (maskLen s G)).pre (ptL (s.h + s.g) g)),
          toE eps * (s.par (maskLen s G)).late (ptL (s.h + s.g) g)), ptL (s.h + s.g) g)) =
      vecMid s (Fmt.M1.foldStep .two (s.h + s.g) s.h G sigma eps qs g) := by
  funext j
  rcases j with j | j | j
  · show (∑ b : Fin (s.h + s.g) → Bool, vec G.c (Sz.rowNo b + 2 ^ (s.h + s.g) * j.val) *
        Alg.eqk (ptL (s.h + s.g) g) b) * toE eps =
      vec (Fmt.M1.foldStep .two (s.h + s.g) s.h G sigma eps qs g).c j.val
    rw [vec_foldStep_c]
    rfl
  · show (∑ b : Fin s.h → Bool, vec G.d (Sz.rowNo b + 2 ^ s.h * j.val) *
        Alg.eqk ((s.par (maskLen s G)).pre (ptL (s.h + s.g) g)) b) *
        (toE eps * (s.par (maskLen s G)).late (ptL (s.h + s.g) g)) =
      vec (Fmt.M1.foldStep .two (s.h + s.g) s.h G sigma eps qs g).d0 j.val
    rw [vec_foldStep_d0]
    rfl
  · show hideW s.h s.g (maskLen s G) (ptL (s.h + s.g) g) j.val =
      vec (Fmt.M1.foldStep .two (s.h + s.g) s.h G sigma eps qs g).d1 j.val
    have hsz : (Fmt.M1.foldStep .two (s.h + s.g) s.h G sigma eps qs g).d0.size = maskLen s G :=
      size_foldStep_d0 _ _ _ _ _ _ _ _ _ _ _ _
    unfold hideW
    split
    · next hj =>
      rw [vec_foldStep_d1 s.h s.g G sigma eps qs g j.val (by rw [hsz]; exact hj)]
      rfl
    · next hj =>
      rw [vec_of_le _ _ (by rw [size_foldStep_d1, hsz]; omega)]

/-! ## The block -/

/-- The rounds of a fold are taken off, with the claims as the format's verifier holds them. If
the row G on the columns col (`stmIn`, `wordIn`) has no witness, the prover has lost in the fold's
rounds and t, given that it has lost wherever a test of work fails and, in t, whenever what
`foldStep` (Fmt/M1Fold.lean) computes from the rounds' values (`stmMid`), on the folded columns
(`wordMid`), has no witness. -/
theorem fold_block (s : Sg) (d e : ℕ) (Lst mC mS mW : ℕ → ℕ)
    (hC : Spec.CodesOK GE s.Ps s.cM s.cZ s.cZ d e) (hE : (s.par 0).ErrOK e Lst mC mS mW)
    (dE dT : PQ.RD) (hR : FoldRounds dE dT) (t : Shape) (εt : Err t)
    (G : Fmt.M1.GRow) (col : ℕ → Fmt.M1.Col)
    (hno : ∀ w, ¬ s.RIn e (stmIn s G, wordIn s col) w)
    (bad : Tr (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT) ++ t) → Prop)
    (hp : ∀ τ b, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad (Tr.app τ b))
    (H : ∀ (τ : Tr (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT))) sigma eps ps rs1 qs g,
      Fmt.M1.nextN 1 1 0 (rsOf _ τ) = some (⟨[sigma], [eps], ps⟩, rs1) →
      Fmt.M1.takeRounds (s.h + s.g) rs1 = some (qs, g, []) →
      (∀ w, ¬ s.RMid e (stmMid s (Fmt.M1.foldStep .two (s.h + s.g) s.h G sigma eps qs g),
        wordMid s col (ptL _ g)) w) →
      Doomed t εt fun b => bad (Tr.app τ b)) :
    Doomed _ (Err.app (foldErr s dE dT Lst mC mS mW) εt) bad := by
  refine fold_block_sem s (maskLen s G) d e Lst mC mS mW hC hE dE dT hR t εt (toE G.t)
    (vecIn s G) (wordIn s col) (wordFr s col) hno bad hp fun m c τ hw => ?_
  have hrv := rvOf_one hR.eps m c
  have hsig := toE_sent dE m c 0
  have heps := toE_els dE m c
  refine H (m, c, τ) ((rvOf dE m c).sent.getD 0 Fmt.Fld.zeroE)
    ((rvOf dE m c).els.getD 0 Fmt.Fld.zeroE) (rvOf dE m c).poss (rsOf _ τ) (qsOf dT _ τ)
    (gsOf dT _ τ) ?_ (takeRounds_rsOf hR.two _ τ) fun w h => hw w ?_
  · exact (hR.eps.next m c (rsOf _ τ)).trans (by rw [← hrv])
  · have hfirst : sentAt dE m 0 + toE G.t * gOne _ (valsOf dE c) =
        toE (Fmt.Fld.two.addE ((rvOf dE m c).sent.getD 0 Fmt.Fld.zeroE)
          (Fmt.Fld.two.mulE ((rvOf dE m c).els.getD 0 Fmt.Fld.zeroE) G.t)) := by
      rw [toE_addE, toE_mulE, hsig, heps, mul_comm]
    rw [hfirst, claimF_eq, ptF_eq, ← heps, ← slOut_mid,
      slOut_eq s G ((rvOf dE m c).sent.getD 0 Fmt.Fld.zeroE) _ (qsOf dT _ τ)]
    exact h

end OnBytes.Slice

#print axioms OnBytes.Slice.hideW_deg
#print axioms OnBytes.Slice.par_know
#print axioms OnBytes.Slice.sum_out
#print axioms OnBytes.Slice.carT_fib
#print axioms OnBytes.Slice.carF_fib
#print axioms OnBytes.Slice.carT_none
#print axioms OnBytes.Slice.carF_none
#print axioms OnBytes.Slice.carF_some
#print axioms OnBytes.Slice.phi_fillT
#print axioms OnBytes.Slice.carT_some
#print axioms OnBytes.Slice.slOut_mid
#print axioms OnBytes.Slice.fold_block_sem
#print axioms OnBytes.Slice.takeRounds_rsOf
#print axioms OnBytes.Slice.claimOf_cons
#print axioms OnBytes.Slice.toE_sent
#print axioms OnBytes.Slice.toE_els
#print axioms OnBytes.Slice.rvOf_one
#print axioms OnBytes.Slice.claimF_eq
#print axioms OnBytes.Slice.ptF_eq
#print axioms OnBytes.Slice.slOut_eq
#print axioms OnBytes.Slice.fold_block
