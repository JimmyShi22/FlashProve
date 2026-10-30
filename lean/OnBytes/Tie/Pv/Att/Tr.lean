-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/Tr.lean: the typed transcript of a plain sumcheck, made from what the port has
heard, and the block's output on it.

The block of Cb/Pv/Att/Ride.lean runs on a typed transcript. The port's routines hear rounds: lists
of elements and drawn elements. This file makes the first from the second, for the parameters of
Cb/Pv/Att/Plain.lean and a reading of the port's elements in the field, and says what the short
sumcheck's verifier (`TWhole.shortV`, Cb/G6/Value.lean) puts out on it.

Main names:
  `lastTr`: the round of the further variable and the round of the end values. The challenge of the
    further variable has the type of the elements other than 0: so the reading of the port's beta
    must be other than 0, which is a premise here.
  `cubeTr`: the rounds of k cube variables before further rounds.
  `plainTr`: the rounds of a plain sumcheck behind its first round.
  `plain_reads`: the port's rounds are read as that transcript (`ReadsAs`,
    OnBytes/Tie/Pv/Psc/PscTie.lean), if each round has as many scalars as its degree says.
  `plain_vals`, `plain_ini`, `plain_last`, `plain_fin`: on that transcript the output's end values
    are those that were put in; its point is the reading of the port's challenges, in the order of
    the rounds, then the reading of beta; its last value is the reading of the port's running claim
    (OnBytes.Psc.claimAfter under the weights of OnBytes/Tie/Pv/Att/PlainFits.lean).

Limits: on lists and transcripts alone. That a run of the port's routines has heard such lists, and
that its record's claim is claimAfter of them, is said in OnBytes/Tie/Pv/Att/Seams.lean. That the
reading of beta is other than 0 is proved nowhere here.
-/
import OnBytes.Tie.Pv.Att.PlainFits
import Cb.G6.Value

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- The round of the further variable and the round of the end values. -/
def lastTr (DY : ℕ) (A : Type) (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0) (vals : A → K) :
    Tr (sRound (pDummy K DY) :: [pRoundV K A]) :=
  (((), rd ρ DY sentY), ⟨ρ.val beta, hβ⟩, (((), vals), (), ()))

/-- The rounds of k cube variables, then the rounds of last. -/
def cubeTr (g : PFmt K) (t : Shape) : (k : ℕ) → (n : Fin k → ℕ) → List (List E × E) →
    Tr (sRound g :: t) → Tr (sRounds (ldPartFmt K k n ++ [g]) ++ t)
  | 0, _, _, last => last
  | k + 1, n, rs, last =>
    (((), rd ρ (n 0) (rs.headD ([], zeroE)).1), ρ.val (rs.headD ([], zeroE)).2,
      cubeTr g t k (fun i => n i.succ) rs.tail last)

/-- The rounds of a plain sumcheck behind its first round. -/
noncomputable def plainTr (T : PlainSc K) (rs : List (List E × E)) (sentY : List E) (beta : E)
    (hβ : ρ.val beta ≠ 0) (vals : T.A → K) :
    Tr (sRounds T.our.par.fmt ++ [pRoundV K T.our.par.A]) :=
  cubeTr ρ (pDummy K T.DY) [pRoundV K T.A] T.nv T.deg rs (lastTr ρ T.DY T.A sentY beta hβ vals)

theorem cubeTr_reads (g : PFmt K) (t : Shape) (y : List E × E) (last : Tr (sRound g :: t))
    (hl : ReadsAs ρ [y] [g] t last) : ∀ (k : ℕ) (n : Fin k → ℕ) (rs : List (List E × E)),
    rs.map (·.1.length) = List.ofFn n →
    ReadsAs ρ (rs ++ [y]) (ldPartFmt K k n ++ [g]) t (cubeTr ρ g t k n rs last)
  | 0, _, [], _ => hl
  | 0, _, _ :: _, h => by simp at h
  | k + 1, n, [], h => by simp [List.ofFn_succ] at h
  | k + 1, n, (sent, r) :: rs, h => by
    rw [List.ofFn_succ, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    exact ⟨h1, rfl, rfl, cubeTr_reads g t y last hl k (fun i => n i.succ) rs h2⟩

theorem plain_reads (T : PlainSc K) (rs : List (List E × E)) (sentY : List E) (beta : E)
    (hβ : ρ.val beta ≠ 0) (vals : T.A → K) (hl : rs.map (·.1.length) = List.ofFn T.deg)
    (hY : sentY.length = T.DY) :
    ReadsAs ρ (rs ++ [(sentY, beta)]) T.our.par.fmt [pRoundV K T.our.par.A]
      (plainTr ρ T rs sentY beta hβ vals) :=
  cubeTr_reads ρ _ _ (sentY, beta) _ ⟨hY, rfl, rfl, trivial⟩ T.nv T.deg rs hl

/-! ## The output -/

theorem cubeTr_tail (g : PFmt K) (t : Shape) (last : Tr (sRound g :: t)) :
    ∀ (k : ℕ) (n : Fin k → ℕ) (d : PDats (ldPartFmt K k n ++ [g]))
      (F : HFixs (pVars (ldPartFmt K k n ++ [g]) d)) (σ : K) (rs : List (List E × E)),
    (vFinT (ldPartFmt K k n ++ [g]) d F σ t (cubeTr ρ g t k n rs last)).2 = last.2.2
  | 0, _, _, _, _, _ => rfl
  | k + 1, n, d, F, _, rs => cubeTr_tail g t last k (fun i => n i.succ) d.2 F.2 _ rs.tail

theorem cubeTr_ini (g : PFmt K) (t : Shape) (last : Tr (sRound g :: t)) :
    ∀ (k : ℕ) (n : Fin k → ℕ) (d : PDats (ldPartFmt K k n ++ [g]))
      (F : HFixs (pVars (ldPartFmt K k n ++ [g]) d)) (σ : K) (rs : List (List E × E)) (i : Fin k),
    ldPartIni k n g (vFinT (ldPartFmt K k n ++ [g]) d F σ t (cubeTr ρ g t k n rs last)).1.2 i =
      ρ.val (rs.getD i.1 ([], zeroE)).2
  | 0, _, _, _, _, _, i => i.elim0
  | k + 1, n, d, F, σ, rs, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · cases rs <;> rfl
    · have h := cubeTr_ini g t last k (fun i => n i.succ) d.2 F.2
        (hev (hFill ((pfCube K (n 0)).var d.1) F.1 σ (rd ρ (n 0) (rs.headD ([], zeroE)).1))
          (ρ.val (rs.headD ([], zeroE)).2)) rs.tail j
      have e : rs.tail.getD j.1 ([], zeroE) = rs.getD j.succ.1 ([], zeroE) := by
        cases rs <;> simp
      rw [← e]
      exact h

theorem cubeTr_last (g : PFmt K) (t : Shape) (last : Tr (sRound g :: t)) :
    ∀ (k : ℕ) (n : Fin k → ℕ) (d : PDats (ldPartFmt K k n ++ [g]))
      (F : HFixs (pVars (ldPartFmt K k n ++ [g]) d)) (σ : K) (rs : List (List E × E)),
    ldPartLast k n g (vFinT (ldPartFmt K k n ++ [g]) d F σ t (cubeTr ρ g t k n rs last)).1.2 =
      g.val last.2.1
  | 0, _, _, _, _, _ => rfl
  | k + 1, n, d, F, _, rs => cubeTr_last g t last k (fun i => n i.succ) d.2 F.2 _ rs.tail

section Out
variable (T : PlainSc K) (st : T.St) (target mu eps : E) (rs : List (List E × E)) (sentY : List E)
  (beta : E) (hβ : ρ.val beta ≠ 0) (vals : T.A → K)

/-- The short sumcheck's output on the transcript that is made from what the port has heard. -/
noncomputable def plainOut : T.our.par.Out :=
  shortV T.our.par T.fix (ρ.val target, st)
    (((), ρ.val mu), ρ.val eps, plainTr ρ T rs sentY beta hβ vals)

theorem plain_st : (plainOut ρ T st target mu eps rs sentY beta hβ vals).st = st := rfl

theorem plain_eps : (plainOut ρ T st target mu eps rs sentY beta hβ vals).eps = ρ.val eps := rfl

theorem plain_vals : (plainOut ρ T st target mu eps rs sentY beta hβ vals).vals = vals :=
  congrArg (fun τ : Tr [pRoundV K T.A] => τ.1.2)
    (cubeTr_tail ρ (pDummy K T.DY) [pRoundV K T.A] (lastTr ρ T.DY T.A sentY beta hβ vals) T.nv T.deg
      (T.our.par.dat st) (T.fix st) _ rs)

theorem plain_ini (i : Fin T.nv) :
    ldPartIni T.nv T.deg (pDummy K T.DY)
        (plainOut ρ T st target mu eps rs sentY beta hβ vals).pt i =
      ρ.val (rs.getD i.1 ([], zeroE)).2 :=
  cubeTr_ini ρ (pDummy K T.DY) [pRoundV K T.A] (lastTr ρ T.DY T.A sentY beta hβ vals) T.nv T.deg
    (T.our.par.dat st) (T.fix st) _ rs i

theorem plain_last :
    ldPartLast T.nv T.deg (pDummy K T.DY)
        (plainOut ρ T st target mu eps rs sentY beta hβ vals).pt = ρ.val beta :=
  cubeTr_last ρ (pDummy K T.DY) [pRoundV K T.A] (lastTr ρ T.DY T.A sentY beta hβ vals) T.nv T.deg
    (T.our.par.dat st) (T.fix st) _ rs

theorem plain_fin (h1 : ∀ i, 1 ≤ T.deg i) (hl : rs.map (·.1.length) = List.ofFn T.deg)
    (hY : sentY.length = T.DY) :
    (plainOut ρ T st target mu eps rs sentY beta hβ vals).fin =
      ρ.val (OnBytes.Psc.claimAfter (plainWs (List.ofFn T.deg) T.DY) (rs ++ [(sentY, beta)])
        (addE mu (mulE eps target))) := by
  rw [claimAfter_hFin ρ _ _ T.our.par.fmt (T.our.par.dat st) (T.fix st) [pRoundV K T.our.par.A]
    (plainTr ρ T rs sentY beta hβ vals) _ (plain_fits ρ T h1 st)
    (plain_reads ρ T rs sentY beta hβ vals hl hY), vFinT_fin, ρ.add, ρ.mul]
  rfl

end Out

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.plain_reads
#print axioms OnBytes.Tie.Pv.Att.plain_vals
#print axioms OnBytes.Tie.Pv.Att.plain_ini
#print axioms OnBytes.Tie.Pv.Att.plain_last
#print axioms OnBytes.Tie.Pv.Att.plain_fin
