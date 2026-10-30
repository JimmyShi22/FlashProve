-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SumReads.lean: THE FORMULAS OF THE MASKED SUMCHECK's PART, READ IN
A FIELD, at a call of n variables that are summed plainly, with round polynomials of three
coefficients, without a lead and without end values. `plainFirst` and `plainRound` ARE THIS FILE's
OWN COPY OF THE INNER TEXT OF `sumPart` (Honest/Sum.lean) at such a call: made of that file's
`tailSum`, `hAt`, `wOf`, `sentOfL`, which compute in the program's type on lists. NO STATEMENT OF
THIS FILE NAMES `sumPart`: that its moves, played, send these formulas is held by the toy of this
folder at two sizes, by evaluation, and is no theorem here. What is shown: the formulas read as the
functions of Johnson/Desc/K13/Honest/Moves.lean (`sumU`, `sentL`). Statements with their proofs. The
summand is a parameter: any function from the challenges so far to three coefficients.

Why. The kind K13's statements on its honest prover stand at `sumU` and `sent`. The part that the
frame plays is `sumPart`. This file is one of the two links between the two texts.
Main names:
  `plains n`: n variables, summed plainly, three coefficients each. `vwOf n u`: these with their
    shares of the hiding polynomial, of a stretch of coins; `vwOf_one`, `vwOf_succ`.
  `padTo_two`, `padTo_three`, `getD_drop_two`: a list cut or filled; a list without its first two.
  `sumOf_reads`, `tail_reads`: **the sum of the hiding polynomial, read.**
  `plainFirst`, `plainRound`: the copy of the part's inner text: the first message; the message for
    the next variable; as functions of the stretch of coins, the challenges and the summand's
    coefficients. `plainFrom`: the like from an accumulator on. `readPair`: two elements, read.
  `round_last`, `round_first`: **a round's two scalars, read**, at the last variable and at another.
  `hAt_cons`, `plainFrom_cons`: behind a challenge the walk goes on at the variables that are left.
  `ReadsAs`: the summand's coefficients, in the program's type, read as a given function.
  `rounds_read`: **all rounds: they read as `sentL`.**

What is not claimed. That `sumPart`'s moves, played, yield `plainFirst` and `plainRound`: that is by
the part's text, and is not stated here. Other shapes of a call. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.K13.Honest.SumLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (Var valueAt total psiAt)
open VerifiableInference.Desc.K13.Honest (tailU sumU sentL)

/-- n variables, summed plainly, three coefficients each. -/
def plains (n : Nat) : List Var := List.replicate n (.plain 3)

/-- A list cut or filled to two members. -/
theorem padTo_two : ∀ u : List E, padTo 2 u = [u.getD 0 zeroE, u.getD 1 zeroE]
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- A list cut or filled to three members. -/
theorem padTo_three : ∀ u : List E,
    padTo 3 u = [u.getD 0 zeroE, u.getD 1 zeroE, u.getD 2 zeroE]
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- A member of a list without its first two. -/
theorem getD_drop_two (u : List E) (j : Nat) : (u.drop 2).getD j zeroE = u.getD (j + 2) zeroE := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

variable {K : Type} [Field K] (ρ : Reading K)

/-- The variables with their polynomials, of a stretch of coins. -/
def vwOf (n : Nat) (u : List E) : List (Var × List E) := (plains n).zip (wOf (plains n) u)

/-- At the last variable. -/
theorem vwOf_one (u : List E) :
    vwOf 1 u = [(.plain 3, [u.getD 0 zeroE, u.getD 1 zeroE, u.getD 2 zeroE])] := by
  show [((.plain 3 : Var), padTo 3 u)] = _
  rw [padTo_three]

/-- At a variable that is not the last. -/
theorem vwOf_succ (n : Nat) (u : List E) :
    vwOf (n + 2) u =
      (.plain 3, [zeroE, u.getD 0 zeroE, u.getD 1 zeroE]) :: vwOf (n + 1) (u.drop 2) := by
  show ((.plain 3 : Var), zeroE :: padTo 2 u) :: vwOf (n + 1) (u.drop 2) = _
  rw [padTo_two]

/-- The sum of a polynomial of three coefficients in a variable that is summed plainly, read. -/
theorem sumOf_reads (a b c : E) :
    ρ.val (sumOf (.plain 3) [a, b, c]) = 2 * ρ.val a + ρ.val b + ρ.val c := by
  have e : sumOf (.plain 3) [a, b, c] =
      addE (addE (addE zeroE (mulE a (addE oneE oneE))) (mulE b oneE)) (mulE c oneE) := rfl
  rw [e]
  simp only [ρ.add, ρ.mul, ρ.zero, ρ.one]
  ring

/-- **The sum of the hiding polynomial, read.** f: the coins' readings by their number, from i on;
asked of the 2 n + 1 coins alone. -/
theorem tail_reads (f : Nat → K) : ∀ (n : Nat) (u : List E) (i : Nat),
    (∀ j, j < 2 * n + 1 → ρ.val (u.getD j zeroE) = f (i + j)) →
    ρ.val (tailSum (vwOf n u)) = tailU f n i
  | 0, _, _, _ => ρ.zero
  | 1, u, i, h => by
    rw [vwOf_one]
    show ρ.val (addE (sumOf (.plain 3) _) (mulE (addE oneE oneE) zeroE)) =
      2 * f i + f (i + 1) + f (i + 2)
    rw [ρ.add, ρ.mul, ρ.zero, sumOf_reads, h 0 (by omega), h 1 (by omega), h 2 (by omega)]
    simp
  | n + 2, u, i, h => by
    rw [vwOf_succ]
    show ρ.val (addE (sumOf (.plain 3) _)
        (mulE (addE oneE oneE) (tailSum (vwOf (n + 1) (u.drop 2))))) =
      f i + f (i + 1) + 2 * tailU f (n + 1) (i + 2)
    rw [ρ.add, ρ.mul, ρ.add, ρ.one, sumOf_reads, ρ.zero, h 0 (by omega), h 1 (by omega),
      tail_reads f (n + 1) (u.drop 2) (i + 2) (fun j hj => by
        rw [getD_drop_two, h (j + 2) (by omega)]
        congr 1
        omega)]
    simp only [Nat.add_zero]
    ring

/-- What the part's first move sends at such a call. -/
def plainFirst (n : Nat) (u : List E) : E := tailSum (vwOf n u)

/-- What its move for the variable behind the challenges rs sends. eps: the first challenge. g: the
summand's three coefficients. -/
def plainRound (n : Nat) (u : List E) (eps : E) (rs g : List E) : List E :=
  sentOfL (.plain 3) (addL (hAt (vwOf n u) rs zeroE) (scaleL eps g))

/-- The like from an accumulator a on. -/
def plainFrom (n : Nat) (u : List E) (eps : E) (rs g : List E) (a : E) : List E :=
  sentOfL (.plain 3) (addL (hAt (vwOf n u) rs a) (scaleL eps g))

/-- A pair of the program's elements, read. -/
def readPair (l : List E) : K × K := (ρ.val (l.getD 0 zeroE), ρ.val (l.getD 1 zeroE))

/-- At the last variable, no challenge in front. -/
theorem round_last (f : Nat → K) (u : List E) (i : Nat)
    (h : ∀ j, j < 3 → ρ.val (u.getD j zeroE) = f (i + j)) (eps g0 g1 g2 a : E) :
    readPair ρ (plainFrom 1 u eps [] [g0, g1, g2] a) =
      (f i + ρ.val eps * ρ.val g0, f (i + 2) + ρ.val eps * ρ.val g2) := by
  unfold plainFrom
  rw [vwOf_one]
  have e : sentOfL (.plain 3) (addL (hAt [((.plain 3 : Var),
        [u.getD 0 zeroE, u.getD 1 zeroE, u.getD 2 zeroE])] [] a) (scaleL eps [g0, g1, g2])) =
      [addE (addE (addE (mulE a zeroE) (u.getD 0 zeroE)) zeroE) (mulE eps g0),
       addE (u.getD 2 zeroE) (mulE eps g2)] := rfl
  rw [e]
  show (ρ.val (addE (addE (addE (mulE a zeroE) (u.getD 0 zeroE)) zeroE) (mulE eps g0)),
    ρ.val (addE (u.getD 2 zeroE) (mulE eps g2))) = _
  simp only [ρ.add, ρ.mul, ρ.zero, h 0 (by omega), h 2 (by omega)]
  simp

/-- At a variable that is not the last, no challenge in front. -/
theorem round_first (f : Nat → K) (n : Nat) (u : List E) (i : Nat)
    (h : ∀ j, j < 2 * (n + 2) + 1 → ρ.val (u.getD j zeroE) = f (i + j)) (eps g0 g1 g2 a : E) :
    readPair ρ (plainFrom (n + 2) u eps [] [g0, g1, g2] a) =
      (tailU f (n + 1) (i + 2) + ρ.val eps * ρ.val g0, f (i + 1) + ρ.val eps * ρ.val g2) := by
  unfold plainFrom
  rw [vwOf_succ]
  have e : sentOfL (.plain 3) (addL (hAt (((.plain 3 : Var),
        [zeroE, u.getD 0 zeroE, u.getD 1 zeroE]) :: vwOf (n + 1) (u.drop 2)) [] a)
        (scaleL eps [g0, g1, g2])) =
      [addE (addE (addE (mulE a zeroE) zeroE) (tailSum (vwOf (n + 1) (u.drop 2)))) (mulE eps g0),
       addE (u.getD 1 zeroE) (mulE eps g2)] := rfl
  rw [e]
  show (ρ.val (addE (addE (addE (mulE a zeroE) zeroE) (tailSum (vwOf (n + 1) (u.drop 2))))
    (mulE eps g0)), ρ.val (addE (u.getD 1 zeroE) (mulE eps g2))) = _
  simp only [ρ.add, ρ.mul, ρ.zero, h 1 (by omega)]
  rw [tail_reads ρ f (n + 1) (u.drop 2) (i + 2) (fun j hj => by
    rw [getD_drop_two, h (j + 2) (by omega)]
    congr 1
    omega)]
  simp

/-- One step of the hiding polynomial's walk. -/
theorem hAt_cons (v : Var) (w : List E) (rest : List (Var × List E)) (r : E) (rs : List E) (a : E) :
    hAt ((v, w) :: rest) (r :: rs) a = hAt rest rs (addE (mulE a (psiAt v r)) (valueAt w r)) := by
  rw [hAt.eq_def]

/-- Behind a challenge the walk goes on at the variables that are left. -/
theorem plainFrom_cons (n : Nat) (u : List E) (eps r : E) (rs g : List E) (a : E) :
    plainFrom (n + 2) u eps (r :: rs) g a =
      plainFrom (n + 1) (u.drop 2) eps rs g
        (addE (mulE a r) (valueAt [zeroE, u.getD 0 zeroE, u.getD 1 zeroE] r)) := by
  unfold plainFrom
  rw [vwOf_succ, hAt_cons]
  have e : psiAt (.plain 3) r = r := rfl
  rw [e]

/-- The summand's coefficients, in the program's type, read as the function q, behind fewer than N
challenges. -/
def ReadsAs (N : Nat) (G : List E → List E) (q : List K → K × K × K) : Prop :=
  ∀ rs, rs.length < N →
    ∃ g0 g1 g2, G rs = [g0, g1, g2] ∧ q (rs.map ρ.val) = (ρ.val g0, ρ.val g1, ρ.val g2)

/-- **All rounds, read: they are what `sentL` sends.** seen: the challenges of variables that were
passed; gs: those of the n variables that are left. -/
theorem rounds_read (f : Nat → K) (eps : E) {N : Nat} {G : List E → List E}
    {q : List K → K × K × K} (hG : ReadsAs ρ N G q) :
    ∀ (n : Nat) (u : List E) (i : Nat) (seen gs : List E) (a : E), seen.length + n = N →
    (∀ j, j < 2 * n + 1 → ρ.val (u.getD j zeroE) = f (i + j)) → gs.length = n →
    (List.range n).map (fun t =>
        readPair ρ (plainFrom n u eps (gs.take t) (G (seen ++ gs.take t)) a)) =
      sentL f (ρ.val eps) q n i (seen.map ρ.val) (gs.map ρ.val)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | 1, u, i, seen, gs, a, hN, h, _ => by
    obtain ⟨g0, g1, g2, e1, e2⟩ := hG seen (by omega)
    show [readPair ρ (plainFrom 1 u eps (gs.take 0) (G (seen ++ gs.take 0)) a)] =
      [(f i + ρ.val eps * (q (seen.map ρ.val)).1, f (i + 2) + ρ.val eps * (q (seen.map ρ.val)).2.2)]
    rw [List.take_zero, List.append_nil, e1, e2, round_last ρ f u i h]
  | n + 2, u, i, seen, g :: gs, a, hN, h, hg => by
    obtain ⟨g0, g1, g2, e1, e2⟩ := hG seen (by omega)
    have ih := rounds_read f eps hG (n + 1) (u.drop 2) (i + 2) (seen ++ [g]) gs
      (addE (mulE a g) (valueAt [zeroE, u.getD 0 zeroE, u.getD 1 zeroE] g))
      (by rw [List.length_append, List.length_singleton]; omega)
      (fun j hj => by
        rw [getD_drop_two, h (j + 2) (by omega)]
        congr 1
        omega)
      (by simp only [List.length_cons] at hg; omega)
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show readPair ρ (plainFrom (n + 2) u eps [] (G (seen ++ [])) a) ::
        (List.range (n + 1)).map (fun t => readPair ρ (plainFrom (n + 2) u eps (g :: gs.take t)
          (G (seen ++ g :: gs.take t)) a)) =
      (tailU f (n + 1) (i + 2) + ρ.val eps * (q (seen.map ρ.val)).1,
          f (i + 1) + ρ.val eps * (q (seen.map ρ.val)).2.2) ::
        sentL f (ρ.val eps) q (n + 1) (i + 2) (seen.map ρ.val ++ [ρ.val g]) (gs.map ρ.val)
    rw [List.append_nil, e1, e2, round_first ρ f n u i h]
    have e3 : seen.map ρ.val ++ [ρ.val g] = (seen ++ [g]).map ρ.val := by simp
    rw [e3, ← ih]
    refine congrArg (List.cons _) (List.map_congr_left fun t _ => ?_)
    rw [plainFrom_cons]
    have e4 : seen ++ g :: gs.take t = seen ++ [g] ++ gs.take t := by simp
    rw [e4]
  | _ + 2, _, _, _, [], _, _, _, hg => by simp only [List.length_nil] at hg; omega

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.padTo_two
#print axioms ProofFile.Honest.K13.padTo_three
#print axioms ProofFile.Honest.K13.getD_drop_two
#print axioms ProofFile.Honest.K13.vwOf_one
#print axioms ProofFile.Honest.K13.vwOf_succ
#print axioms ProofFile.Honest.K13.sumOf_reads
#print axioms ProofFile.Honest.K13.tail_reads
#print axioms ProofFile.Honest.K13.round_last
#print axioms ProofFile.Honest.K13.round_first
#print axioms ProofFile.Honest.K13.hAt_cons
#print axioms ProofFile.Honest.K13.plainFrom_cons
#print axioms ProofFile.Honest.K13.rounds_read
