-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookSum.lean

One masked sumcheck of the lookup, on plain lists: what TwV.takeSc reads off the rounds that
Johnson/HonestTrace/LookDefs.lean defines, and that the row which TwV makes of it holds.

Cb/G9/FlatStep.lean has "TwV.takeSc": a function on plain data, written after the verifier of a
short sumcheck. It reads a first round (a scalar and the draw eps), one round for each variable (all
coefficients of the round's polynomial but the constant, and the challenge), and a round of shown
values if there is one. It completes each polynomial at the constant that is not sent, and leaves
eps, the challenges, the last value and the shown values ("TwV.Sc"). LookDefs.lean defines what is
sent: "honSc", of the mask entries (a reading μ of the places of "TwV.Led"), the round polynomials
gs of the summand, and the challenges; and "runJob", the same for a "Job". This file shows what
"takeSc" leaves of them.

The point. What is sent reads no target and no sum. "takeSc" is handed a target tg, which on a run
is 0 or is made of SHOWN values (a shown value is a true value plus a multiple of a mask entry),
while the summand's polynomials sum to the TRUE sum C. The difference tg - C goes wholly into the
constants that are not sent. So the last value is H(xs) + eps (gfin + (tg - C)), with H the
polynomial of the mask entries ("TwV.hide") and gfin the summand's last value; and the row
"TwV.rowU" holds as soon as the incoming form is worth tg - C at μ.

Main theorems:
* "takeSc_hon": if the polynomials qs are "Chained" from hs + eps tg to fin, "takeSc" on their
  rounds "scRounds", followed by any rest, returns (eps, xs, fin, the values) and the rest.
* "honSc_eq": at lists of one length "honSc" is "scRounds" of the masked polynomials "maskedGo", for
  every constant c.
* "masked_chained": if dg has the length of zs and gs is "Chained" from C to gfin, the masked
  polynomials at c = tg - C are "Chained" from (the sum of H) + eps tg to H(xs) + eps (gfin + (tg -
  C)).
* "rowU_hon": if the incoming form is worth tg - C at μ, the row "TwV.rowU" of a value of "TwV.Sc"
  with the last value H(xs) + eps (S0 + (tg - C)) holds at μ.
* "takeSc_job": on the rounds "runJob" of a lawful job with as many degrees as points, followed by
  any rest, at as many challenges as it has rounds and at ANY target tg, "takeSc" leaves "scJob" at
  tg, and the rest.
Helpers: "Chained.lengths", "Chained.append", "runVars_chained", "addP_sum", "evalGo_addP",
"evalGo_smul", "evalGo_append", "valS_part", "sentGo_eq", "maskedGo_chained", "Job.gs_length".

Limits. K is any field; mask entries and challenges are arguments, nothing is drawn. The statements
are about the functions of TwV on lists; that these compute what a typed verifier or a program
computes is not said here. That any job is lawful is not shown here. No degree is asked: a round's
polynomial is taken at the length of its list, as "takeSc" takes it.

Not claimed: anything on soundness, completeness or what the masks conceal.

-/
import Johnson.HonestTrace.LookDefs

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open TwV

section
variable {K : Type} [Field K] {P : Type}

/-! ## Lists of one length -/

/-- In a run the three lists have one length. -/
theorem Chained.lengths : ∀ {σ : K} {zs : List K} {qs : List (List K)} {xs : List K} {fin : K},
    Chained σ zs qs xs fin → qs.length = zs.length ∧ xs.length = zs.length
  | _, [], [], [], _, _ => ⟨rfl, rfl⟩
  | _, _ :: _, _ :: _, _ :: _, _, h => by
    obtain ⟨a, b⟩ := Chained.lengths h.2
    exact ⟨by rw [List.length_cons, List.length_cons, a],
      by rw [List.length_cons, List.length_cons, b]⟩
  | _, [], [], _ :: _, _, h => h.elim
  | _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, [], _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, h => h.elim

/-- A run from σ to mid, followed by a run from mid to fin, is a run from σ to fin. -/
theorem Chained.append : ∀ {σ : K} {zs : List K} {qs : List (List K)} {xs : List K} {mid : K}
    {zs' : List K} {qs' : List (List K)} {xs' : List K} {fin : K},
    Chained σ zs qs xs mid → Chained mid zs' qs' xs' fin →
      Chained σ (zs ++ zs') (qs ++ qs') (xs ++ xs') fin
  | _, [], [], [], _, _, _, _, _, h, h' => by
    have e : _ = _ := h
    subst e
    exact h'
  | _, _ :: _, _ :: _, _ :: _, _, _, _, _, _, h, h' => ⟨h.1, Chained.append h.2 h'⟩
  | _, [], [], _ :: _, _, _, _, _, _, h, _ => h.elim
  | _, [], _ :: _, _, _, _, _, _, _, h, _ => h.elim
  | _, _ :: _, [], _, _, _, _, _, _, h, _ => h.elim
  | _, _ :: _, _ :: _, [], _, _, _, _, _, h, _ => h.elim

/-! ## What takeSc reads off a run -/

/-- If qs is "Chained" from σ to fin, "TwV.runVars" from σ on the variables' rounds of qs (all
coefficients but the constant, and the challenge), whatever follows them, returns fin and the
challenges. -/
theorem runVars_chained : ∀ (σ : K) (zs : List K) (qs : List (List K)) (xs : List K) (fin : K)
    (more : Rounds K), Chained σ zs qs xs fin →
    runVars σ zs (List.zipWith (fun q x => (q.tail, [x])) qs xs ++ more) = (fin, xs)
  | σ, [], [], [], fin, more, h => by
    have e : fin = σ := h
    subst e
    cases more <;> rfl
  | σ, z :: zs, q :: qs, x :: xs, fin, more, h => by
    have ih := runVars_chained (evalP q x) zs qs xs fin more h.2
    have e : σ - z * q.tail.sum + evalGo x 0 q.tail = evalP q x := by
      rw [← h.1]
      unfold wsum evalP
      ring
    show (let x' := ([x] : List K).headD 0
      let r := runVars (σ - z * q.tail.sum + evalGo x' 0 q.tail) zs
        (List.zipWith (fun q x => (q.tail, [x])) qs xs ++ more)
      (r.1, x' :: r.2)) = (fin, x :: xs)
    show ((runVars (σ - z * q.tail.sum + evalGo x 0 q.tail) zs
        (List.zipWith (fun q x => (q.tail, [x])) qs xs ++ more)).1,
      x :: (runVars (σ - z * q.tail.sum + evalGo x 0 q.tail) zs
        (List.zipWith (fun q x => (q.tail, [x])) qs xs ++ more)).2) = (fin, x :: xs)
    rw [e, ih]
  | _, [], [], _ :: _, _, _, h => h.elim
  | _, [], _ :: _, _, _, _, h => h.elim
  | _, _ :: _, [], _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, h => h.elim

/-- **What "TwV.takeSc" reads off a run.** If qs is "Chained" from hs + eps tg to fin at the points
zs and the challenges xs, then "takeSc" at the target tg on "scRounds hs eps qs xs vals", followed
by any rest, returns eps, xs, fin and the shown values (none: the empty list), and leaves the rest.
-/
theorem takeSc_hon (hs eps tg fin : K) (zs : List K) (qs : List (List K)) (xs : List K)
    (vals : Option (List K)) (rest : Rounds K) (h : Chained (hs + eps * tg) zs qs xs fin) :
    takeSc (scRounds hs eps qs xs vals ++ rest) tg zs vals.isSome =
      (⟨eps, xs, fin, vals.getD []⟩, rest) := by
  obtain ⟨lq, lx⟩ := h.lengths
  have lz : (List.zipWith (fun (q : List K) (x : K) => (q.tail, [x])) qs xs).length =
      zs.length := by
    rw [List.length_zipWith, lq, lx, Nat.min_self]
  cases vals with
  | none =>
    have e : scRounds hs eps qs xs none ++ rest =
        ([hs], [eps]) :: (List.zipWith (fun q x => (q.tail, [x])) qs xs ++ rest) := by
      unfold scRounds
      simp
    rw [e]
    unfold takeSc
    simp only [List.headD_cons, List.tail_cons, Option.isSome_none, Bool.false_eq_true, if_false,
      Option.getD_none, Nat.add_zero]
    rw [runVars_chained _ zs qs xs fin rest h]
    refine Prod.ext rfl ?_
    show List.drop (1 + zs.length) (([hs], [eps]) ::
      (List.zipWith (fun (q : List K) (x : K) => (q.tail, [x])) qs xs ++ rest)) = rest
    rw [Nat.add_comm, List.drop_succ_cons, ← lz, List.drop_left]
  | some v =>
    have e : scRounds hs eps qs xs (some v) ++ rest =
        ([hs], [eps]) :: (List.zipWith (fun q x => (q.tail, [x])) qs xs ++ ((v, []) :: rest)) := by
      unfold scRounds
      simp
    rw [e]
    unfold takeSc
    simp only [List.headD_cons, List.tail_cons, Option.isSome_some, if_true, Option.getD_some]
    rw [runVars_chained _ zs qs xs fin _ h]
    refine Prod.ext ?_ ?_
    · show (⟨eps, xs, fin, _⟩ : Sc K) = ⟨eps, xs, fin, v⟩
      congr 1
      rw [Nat.add_comm, List.getD_cons_succ, ← lz, List.getD_append_right _ _ _ _ (Nat.le_refl _),
        Nat.sub_self]
      rfl
    · show List.drop (1 + zs.length + 1) (([hs], [eps]) ::
        (List.zipWith (fun (q : List K) (x : K) => (q.tail, [x])) qs xs ++ ((v, []) :: rest))) =
          rest
      rw [show 1 + zs.length + 1 = (zs.length + 1) + 1 by omega, List.drop_succ_cons, ← lz,
        List.drop_append, List.drop_eq_nil_of_le (Nat.le_succ _)]
      simp

/-! ## Sums and values of sums of polynomials -/

/-- The coefficients of a sum of two polynomials sum to the two sums. -/
theorem addP_sum : ∀ a b : List K, (addP a b).sum = a.sum + b.sum
  | [], b => by simp [addP]
  | x :: a, [] => by simp [addP]
  | x :: a, y :: b => by
    show (x + y + (addP a b).sum) = (x + a.sum) + (y + b.sum)
    rw [addP_sum a b]
    ring

/-- "TwV.evalGo" is additive over "addP". -/
theorem evalGo_addP (x : K) : ∀ (t : ℕ) (a b : List K),
    evalGo x t (addP a b) = evalGo x t a + evalGo x t b
  | t, [], b => by simp [addP, evalGo]
  | t, y :: a, [] => by simp [addP, evalGo]
  | t, y :: a, y' :: b => by
    show (y + y') * x ^ (t + 1) + evalGo x (t + 1) (addP a b) =
      (y * x ^ (t + 1) + evalGo x (t + 1) a) + (y' * x ^ (t + 1) + evalGo x (t + 1) b)
    rw [evalGo_addP x (t + 1) a b]
    ring

/-- "TwV.evalGo" of the list scaled by c is c times "evalGo" of the list. -/
theorem evalGo_smul (x c : K) : ∀ (t : ℕ) (a : List K),
    evalGo x t (a.map (c * ·)) = c * evalGo x t a
  | t, [] => by simp [evalGo]
  | t, y :: a => by
    show c * y * x ^ (t + 1) + evalGo x (t + 1) (a.map (c * ·)) =
      c * (y * x ^ (t + 1) + evalGo x (t + 1) a)
    rw [evalGo_smul x c (t + 1) a]
    ring

/-- "TwV.evalGo" of two lists in a row: the second goes on at the power where the first ends. -/
theorem evalGo_append (x : K) : ∀ (t : ℕ) (a b : List K),
    evalGo x t (a ++ b) = evalGo x t a + evalGo x (t + a.length) b
  | t, [], b => by simp [evalGo]
  | t, y :: a, b => by
    show y * x ^ (t + 1) + evalGo x (t + 1) (a ++ b) =
      (y * x ^ (t + 1) + evalGo x (t + 1) a) + evalGo x (t + (a.length + 1)) b
    rw [evalGo_append x (t + 1) a b, show t + 1 + a.length = t + (a.length + 1) by omega]
    ring

/-- The part of round r of the form "TwV.hideGo" (x^(t+1) at the place of power t + 1, t < n) is
worth at μ what "evalGo" gives at x on the coefficients "wCoef". -/
theorem valS_part (L : Led P) (μ : P → K) (r : ℕ) (x : K) : ∀ n : ℕ,
    _root_.Fo.valS ((List.range n).map fun t => (L.pw r t, x ^ (t + 1))) μ =
      evalGo x 0 (wCoef L μ r n)
  | 0 => rfl
  | n + 1 => by
    unfold wCoef
    rw [List.range_succ, List.map_append, List.map_append, _root_.Fo.valS_append,
      evalGo_append, valS_part L μ r x n]
    unfold wCoef
    congr 1
    simp [_root_.Fo.valS, evalGo, mul_comm]

/-! ## What is sent is the masked polynomials without their constants -/

/-- At lists of one length, what is sent in the variables' rounds from round r on ("sentGo") is the
masked polynomials "maskedGo" without their constants, each with its challenge: for every c and
acc, which stand in the constants alone. -/
theorem sentGo_eq (L : Led P) (μ : P → K) (eps c : K) : ∀ (zs : List K) (r : ℕ) (acc : K)
    (dg : List ℕ) (gs : List (List K)) (xs : List K), dg.length = zs.length →
    gs.length = zs.length → xs.length = zs.length →
    sentGo L μ eps r dg gs xs =
      List.zipWith (fun q x => (q.tail, [x])) (maskedGo L μ eps c r acc dg zs gs xs) xs
  | [], r, acc, dg, gs, xs, hd, hg, hx => by
    obtain rfl := List.length_eq_zero_iff.1 hd
    rfl
  | z :: zs, r, acc, n :: dg, g :: gs, x :: xs, hd, hg, hx => by
    show (addP (wCoef L μ r n) (g.tail.map (eps * ·)), [x]) :: sentGo L μ eps (r + 1) dg gs xs =
      ((addP ((acc + hTail L μ (r + 1) dg zs) :: wCoef L μ r n)
        ((eps * (g.headD 0 + c)) :: g.tail.map (eps * ·))).tail, [x]) ::
      List.zipWith (fun q x => (q.tail, [x]))
        (maskedGo L μ eps c (r + 1) (acc + evalGo x 0 (wCoef L μ r n)) dg zs gs xs) xs
    rw [sentGo_eq L μ eps c zs (r + 1) (acc + evalGo x 0 (wCoef L μ r n)) dg gs xs
      (Nat.succ.inj hd) (Nat.succ.inj hg) (Nat.succ.inj hx)]
    rfl
  | _ :: _, _, _, [], _, _, hd, _, _ => absurd hd (by simp)
  | _ :: _, _, _, _ :: _, [], _, _, hg, _ => absurd hg (by simp)
  | _ :: _, _, _, _ :: _, _ :: _, [], _, _, hx => absurd hx (by simp)

/-- **What is sent is the rounds of the masked polynomials, whatever the constant c.** At lists dg,
zs, gs, xs of one length, "honSc" is "scRounds" of "maskedGo" at c. The constant c lies in the
coefficients that are not sent. -/
theorem honSc_eq (L : Led P) (μ : P → K) (dg : List ℕ) (zs : List K) (eps c : K)
    (gs : List (List K)) (xs : List K) (vals : Option (List K)) (hd : dg.length = zs.length)
    (hg : gs.length = zs.length) (hx : xs.length = zs.length) :
    honSc L μ dg zs eps gs xs vals =
      scRounds (μ L.c0 + hTail L μ 0 dg zs) eps (maskedGo L μ eps c 0 (μ L.c0) dg zs gs xs) xs
        vals := by
  unfold honSc scRounds
  rw [sentGo_eq L μ eps c zs 0 (μ L.c0) dg gs xs hd hg hx]

/-! ## A true run, masked -/

/-- The masked run from any round r on. If gs is "Chained" from σ to gfin and dg has the length of
zs, then "maskedGo" at c, r and acc is "Chained" from acc + (the sum of H's parts from round r on) +
eps (σ + c) to acc + (these parts at xs) + eps (gfin + c). acc stands for H's constant and its parts
at the challenges in front. -/
theorem maskedGo_chained (L : Led P) (μ : P → K) (eps c gfin : K) : ∀ (zs : List K) (r : ℕ)
    (acc : K) (dg : List ℕ) (gs : List (List K)) (xs : List K) (σ : K), dg.length = zs.length →
    Chained σ zs gs xs gfin →
    Chained (acc + hTail L μ r dg zs + eps * (σ + c)) zs (maskedGo L μ eps c r acc dg zs gs xs) xs
      (acc + _root_.Fo.valS (hideGo L.pw r dg xs) μ + eps * (gfin + c))
  | [], r, acc, dg, [], [], σ, hd, h => by
    obtain rfl := List.length_eq_zero_iff.1 hd
    have e : gfin = σ := h
    subst e
    show acc + _root_.Fo.valS [] μ + eps * (gfin + c) = acc + 0 + eps * (gfin + c)
    simp [_root_.Fo.valS]
  | z :: zs, r, acc, n :: dg, g :: gs, x :: xs, σ, hd, h => by
    have ih := maskedGo_chained L μ eps c gfin zs (r + 1) (acc + evalGo x 0 (wCoef L μ r n)) dg gs
      xs (evalP g x) (Nat.succ.inj hd) h.2
    have hw : g.headD 0 + z * g.tail.sum = σ := h.1
    refine ⟨?_, ?_⟩
    · show (acc + hTail L μ (r + 1) dg zs + eps * (g.headD 0 + c)) +
          z * (addP (wCoef L μ r n) (g.tail.map (eps * ·))).sum =
        acc + (z * (wCoef L μ r n).sum + hTail L μ (r + 1) dg zs) + eps * (σ + c)
      rw [addP_sum, List.sum_map_mul_left, List.map_id', ← hw]
      ring
    · have e1 : evalP (addP ((acc + hTail L μ (r + 1) dg zs) :: wCoef L μ r n)
          ((eps * (g.headD 0 + c)) :: g.tail.map (eps * ·))) x =
          acc + evalGo x 0 (wCoef L μ r n) + hTail L μ (r + 1) dg zs + eps * (evalP g x + c) := by
        show (acc + hTail L μ (r + 1) dg zs + eps * (g.headD 0 + c)) +
          evalGo x 0 (addP (wCoef L μ r n) (g.tail.map (eps * ·))) = _
        rw [evalGo_addP, evalGo_smul]
        unfold evalP
        ring
      have e2 : acc + _root_.Fo.valS (hideGo L.pw r (n :: dg) (x :: xs)) μ + eps * (gfin + c) =
          acc + evalGo x 0 (wCoef L μ r n) + _root_.Fo.valS (hideGo L.pw (r + 1) dg xs) μ +
            eps * (gfin + c) := by
        show acc + _root_.Fo.valS (((List.range n).map fun t => (L.pw r t, x ^ (t + 1))) ++
          hideGo L.pw (r + 1) dg xs) μ + eps * (gfin + c) = _
        rw [_root_.Fo.valS_append, valS_part]
        ring
      show Chained (evalP (addP ((acc + hTail L μ (r + 1) dg zs) :: wCoef L μ r n)
          ((eps * (g.headD 0 + c)) :: g.tail.map (eps * ·))) x) zs
        (maskedGo L μ eps c (r + 1) (acc + evalGo x 0 (wCoef L μ r n)) dg zs gs xs) xs _
      rw [e1, e2]
      exact ih
  | [], _, _, _, [], _ :: _, _, _, h => h.elim
  | [], _, _, _, _ :: _, _, _, _, h => h.elim
  | _ :: _, _, _, _, [], _, _, _, h => h.elim
  | _ :: _, _, _, _, _ :: _, [], _, _, h => h.elim
  | _ :: _, _, _, [], _ :: _, _ :: _, _, hd, _ => absurd hd (by simp)

/-- **A true run, masked.** If gs is "Chained" from C to gfin and dg has the length of zs, the
masked polynomials at c = tg - C are "Chained" from (the sum of H) + eps tg to H(xs) + eps (gfin +
(tg - C)), where H(xs) is the value at μ of the form "TwV.hide L dg xs". -/
theorem masked_chained (L : Led P) (μ : P → K) (dg : List ℕ) (zs : List K) (eps tg C gfin : K)
    (gs : List (List K)) (xs : List K) (hd : dg.length = zs.length)
    (h : Chained C zs gs xs gfin) :
    Chained (μ L.c0 + hTail L μ 0 dg zs + eps * tg) zs
      (maskedGo L μ eps (tg - C) 0 (μ L.c0) dg zs gs xs) xs
      (_root_.Fo.valS (hide L dg xs) μ + eps * (gfin + (tg - C))) := by
  have k := maskedGo_chained L μ eps (tg - C) gfin zs 0 (μ L.c0) dg gs xs C hd h
  have e1 : C + (tg - C) = tg := by ring
  have e2 : _root_.Fo.valS (hide L dg xs) μ = μ L.c0 + _root_.Fo.valS (hideGo L.pw 0 dg xs) μ := by
    unfold hide
    rw [_root_.Fo.valS_append]
    simp [_root_.Fo.valS, add_comm]
  rw [e1] at k
  rw [e2]
  exact k

/-! ## The row -/

/-- **The row holds.** If the incoming form inc is worth tg - C at μ, the row "TwV.rowU L dg s inc
S0" holds at μ for s with the coefficient eps, the challenges xs and the last value H(xs) + eps (S0
+ (tg - C)); the shown values of s are not read. -/
theorem rowU_hon (L : Led P) (μ : P → K) (dg : List ℕ) (eps tg C S0 : K) (xs vals : List K)
    (inc : List (P × K)) (hinc : _root_.Fo.valS inc μ = tg - C) :
    _root_.Fo.SRowHolds
      (rowU L dg ⟨eps, xs, _root_.Fo.valS (hide L dg xs) μ + eps * (S0 + (tg - C)), vals⟩ inc S0)
      μ := by
  show _root_.Fo.valS (hide L dg xs ++ scale eps inc) μ =
    _root_.Fo.valS (hide L dg xs) μ + eps * (S0 + (tg - C)) - eps * S0
  rw [_root_.Fo.valS_append, _root_.Fo.valS_scale, hinc]
  ring

/-! ## A lawful job -/

omit [Field K] in
/-- A job has one round polynomial for each of its variables. -/
theorem Job.gs_length (J : Job K) (xs : List K) : (J.gs xs).length = J.zs.length := by
  unfold Job.gs
  simp

/-- **"TwV.takeSc" on a lawful job's rounds.** If J is lawful and has as many degrees as points,
then at as many challenges xs as J has rounds (that of Y last, where J has end values) and at ANY
target tg, "takeSc" on "runJob L μ J eps xs", followed by any rest, leaves "scJob L μ J eps tg xs"
and the rest. -/
theorem takeSc_job (L : Led P) (μ : P → K) (J : Job K) (hJ : J.Lawful)
    (hd : J.dg.length = J.zs.length) (eps tg : K) (xs : List K)
    (hx : xs.length = J.zs.length + (if J.dY.isSome then 1 else 0)) (rest : Rounds K) :
    takeSc (runJob L μ J eps xs ++ rest) tg (J.zs ++ if J.dY.isSome then [0] else [])
      J.dY.isSome = (scJob L μ J eps tg xs, rest) := by
  cases hY : J.dY with
  | none =>
    rw [hY] at hx
    have hx' : xs.length = J.zs.length := by simpa using hx
    have c := masked_chained L μ J.dg J.zs eps tg J.sum (J.fin xs) (J.gs xs) xs hd (hJ.1 xs hx')
    have t := takeSc_hon _ eps tg _ J.zs _ xs none rest c
    unfold runJob scJob
    rw [hY]
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, List.append_nil]
    rw [honSc_eq L μ J.dg J.zs eps (tg - J.sum) (J.gs xs) xs none hd (J.gs_length xs) hx']
    exact t
  | some dY =>
    rw [hY] at hx
    have hx' : xs.length = J.zs.length + 1 := by simpa using hx
    have hne : xs ≠ [] := fun e => by rw [e] at hx'; simp at hx'
    have hsplit : xs.dropLast ++ [xs.getLastD 0] = xs := by
      rw [List.getLastD_eq_getLast? , List.getLast?_eq_some_getLast hne]
      exact List.dropLast_append_getLast hne
    have hl : xs.dropLast.length = J.zs.length := by
      rw [List.length_dropLast, hx']
      rfl
    obtain ⟨y1, y2⟩ := hJ.2 (by rw [hY]; rfl) xs.dropLast
      (masksOf L μ (J.ends xs.dropLast).length) (xs.getLastD 0) hl (by simp [masksOf])
    have c0 : Chained J.sum (J.zs ++ [0])
        (J.gs xs.dropLast ++ [J.inY xs.dropLast (masksOf L μ (J.ends xs.dropLast).length)])
        (xs.dropLast ++ [xs.getLastD 0]) (J.S0 (shownOf L μ J xs)) :=
      (hJ.1 xs.dropLast hl).append ⟨y1, y2.symm⟩
    rw [hsplit] at c0
    have hd' : (J.dg ++ [dY]).length = (J.zs ++ [0]).length := by simp [hd]
    have c := masked_chained L μ (J.dg ++ [dY]) (J.zs ++ [0]) eps tg J.sum _ _ xs hd' c0
    have t := takeSc_hon _ eps tg _ (J.zs ++ [0]) _ xs (some (shownOf L μ J xs)) rest c
    unfold runJob scJob
    rw [hY]
    simp only [Option.isSome_some, if_true]
    rw [honSc_eq L μ (J.dg ++ [dY]) (J.zs ++ [0]) eps (tg - J.sum) _ xs _ hd'
      (by simp [J.gs_length]) (by simp [hx'])]
    exact t

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.Chained.lengths
#print axioms OnBytes.HonestTrace.Look.Chained.append
#print axioms OnBytes.HonestTrace.Look.runVars_chained
#print axioms OnBytes.HonestTrace.Look.takeSc_hon
#print axioms OnBytes.HonestTrace.Look.addP_sum
#print axioms OnBytes.HonestTrace.Look.evalGo_addP
#print axioms OnBytes.HonestTrace.Look.evalGo_smul
#print axioms OnBytes.HonestTrace.Look.evalGo_append
#print axioms OnBytes.HonestTrace.Look.valS_part
#print axioms OnBytes.HonestTrace.Look.sentGo_eq
#print axioms OnBytes.HonestTrace.Look.honSc_eq
#print axioms OnBytes.HonestTrace.Look.maskedGo_chained
#print axioms OnBytes.HonestTrace.Look.masked_chained
#print axioms OnBytes.HonestTrace.Look.rowU_hon
#print axioms OnBytes.HonestTrace.Look.Job.gs_length
#print axioms OnBytes.HonestTrace.Look.takeSc_job
