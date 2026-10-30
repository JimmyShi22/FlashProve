-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumSound.lean: THE MASKED SUMCHECK's SOUNDNESS LAW, round by round, over the
part's own text (Johnson/Desc/Part/MaskedSum4.lean: `complete`, `after`, `hidingAt`, `row`, `hear`).
Definitions, statements and proofs.

The algebra is OnBytes/Desc/First/P1/SumCore.lean's (`IsSum`, `Chain`, `masked`); here the text is
read into it. ρ: a reading of the program's field elements in a field K; W: a world, which gives
every
hidden value a value in K (OnBytes/Model/HideLaws.lean).
  `Var.wt`: a variable as a linear functional. `polyOf`: a list of coefficients as a polynomial.
  `complete_sum`: the round's polynomial, as the text completes it, has the running claim as its
  sum.
  `chain_after`: the text's fold `after` is a run of the algebra's.
  `hidingAt_val`: the text's `hidingAt` is the design's hiding polynomial and product of psi.
  `row_value`: the value of the one claim that is left.
  `sound`: THE LAW. Fixed first: the variables (with their points), the hiding polynomial's
    coefficients (AS MANY AS THE SUMCHECK HAS SLOTS OF ITS OWN, `ownSlots`: of the slots behind
    these, which hold the end values and are laid after eps and beta, nothing is asked), the summand
    S as a function of the challenges with its sum sigma (`IsSum`), the
    value T of the claimed form on what was shown and its value Cv at the hidden values. Then there
    are: for each mu at most one bad eps; for each mu, eps, rounds in front and round's polynomial
    fewer than d bad challenges; such that: a record as the hearing gives it, whose row is 0 in the
    world, where S at the challenges is the end term S0 plus what is kept, and no bad element was
    drawn, has Cv = sigma: THE CLAIMED FORM's VALUE IS THE SUM.
  `sound_hear`: the same from `hear`'s own return.

WHAT A CALLER OWES: `IsSum` of its summand over its variables WITH THE FURTHER VARIABLE Y LAST, and
that S at the challenges (beta last) is its end term on the SHOWN end values plus what it keeps.
REACH. THE LAW SPEAKS OF THIS PART's OWN TEXT. It does not yet speak of a verifier that runs: a kind
of block that hears its sumchecks through other functions (OnBytes/K/Kc/Flat.lean's) is not reached
by it; for these see OnBytes/Desc/First/P1/PscSound.lean.
NOT HERE: that the world's hidden values are what the ledger's marks say (shown less factor times
mask): the ledger's law. That the letters which stand first are fixed in time before the rounds:
owed where the blocks are laid in a link. That beta is not 0: not needed here. Nothing on
probabilities:
sets are counted. Nothing on an honest prover or on hiding.
-/
import OnBytes.Desc.First.P1.SumCore
import Johnson.Desc.Part.MaskedSumShape
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model Polynomial
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### A variable, a polynomial -/

/-- A variable as a linear functional on polynomials, with its psi. -/
def Var.wt : Var → Wt K
  | .plain d => { d := d, mom := fun i => if i = 0 then 2 else 1, psi := X }
  | .point z d => { d := d, mom := fun i => if i = 0 then 1 else ρ.val z, psi := 1 }

theorem Var.wt_d (v : Var) : (v.wt ρ).d = v.d := by cases v <;> rfl

/-- A list of coefficients, lowest first, as a polynomial. -/
def polyOf : List E → K[X]
  | [] => 0
  | c :: g => C (ρ.val c) + X * polyOf g

theorem polyOf_eval (x : E) : ∀ g : List E, (polyOf ρ g).eval (ρ.val x) = ρ.val (valueAt g x)
  | [] => by simp [polyOf, valueAt, ρ.zero]
  | c :: g => by
    have hv : valueAt (c :: g) x = addE (mulE (valueAt g x) x) c := rfl
    rw [hv, ρ.add, ρ.mul, polyOf, eval_add, eval_C, eval_mul, eval_X, polyOf_eval x g]
    ring

theorem polyOf_coeff : ∀ (g : List E) (i : ℕ), (polyOf ρ g).coeff i = ρ.val (g.getD i zeroE)
  | [], i => by simp [polyOf, ρ.zero]
  | c :: g, 0 => by simp [polyOf]
  | c :: g, i + 1 => by
    rw [polyOf, coeff_add, coeff_C_succ, coeff_X_mul, polyOf_coeff g i]
    simp

theorem polyOf_natDegree_lt (g : List E) (h : 0 < g.length) :
    (polyOf ρ g).natDegree < g.length := by
  have hle : (polyOf ρ g).natDegree ≤ g.length - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [polyOf_coeff]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show g.length ≤ N by omega), ρ.zero]
  omega

/-- The sum of a list's readings. -/
def sumVal (l : List E) : K := (l.map ρ.val).sum

theorem total_val (l : List E) : ρ.val (total l) = sumVal ρ l := by
  have gen : ∀ (l : List E) (a : E), ρ.val (l.foldl addE a) = ρ.val a + sumVal ρ l := by
    intro l
    induction l with
    | nil => intro a; simp [sumVal]
    | cons x l ih =>
      intro a
      rw [List.foldl_cons, ih, ρ.add]
      simp only [sumVal, List.map_cons, List.sum_cons]
      ring
  rw [total, gen, ρ.zero, zero_add]

theorem sum_range_getD (c : K) : ∀ l : List E,
    ∑ i ∈ Finset.range l.length, c * ρ.val (l.getD i zeroE) = c * sumVal ρ l
  | [] => by simp [sumVal]
  | x :: l => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_range_getD c l]
    simp only [sumVal, List.map_cons, List.sum_cons]
    ring

/-- **The round's equation**: the polynomial that the text completes has the running claim as its
sum. -/
theorem complete_sum (v : Var) (sent : List E) (c : E) (hl : sent.length + 1 = v.d)
    (h2 : 2 ≤ v.d) : (v.wt ρ).sum (polyOf ρ (complete v sent c)) = ρ.val c := by
  cases v with
  | plain d =>
    have hd : sent.length + 1 = d := hl
    cases sent with
    | nil =>
      have : (2 : ℕ) ≤ d := h2
      simp at hd
      omega
    | cons g0 high =>
      have hc : complete (.plain d) (g0 :: high) c =
          g0 :: subE c (addE (addE g0 g0) (total high)) :: high := rfl
      have hdd : d = high.length + 1 + 1 := by simpa using hd.symm
      rw [hc, Wt.sum]
      show ∑ i ∈ Finset.range d, (if i = 0 then (2 : K) else 1) * _ = _
      rw [hdd, Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [polyOf_coeff, List.getD_cons_succ, List.getD_cons_zero, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, if_false, if_true, zero_add]
      rw [sum_range_getD ρ 1 high, ρ.sub, ρ.add, ρ.add, total_val]
      ring
  | point z d =>
    have hd : sent.length + 1 = d := hl
    have hc : complete (.point z d) sent c = subE c (mulE z (total sent)) :: sent := rfl
    rw [hc, Wt.sum]
    show ∑ i ∈ Finset.range d, (if i = 0 then (1 : K) else ρ.val z) * _ = _
    rw [← hd, Finset.sum_range_succ']
    simp only [polyOf_coeff, List.getD_cons_succ, List.getD_cons_zero, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, if_false, if_true]
    rw [sum_range_getD ρ (ρ.val z) sent, ρ.sub, ρ.mul, total_val]
    ring

theorem complete_length (v : Var) (sent : List E) (c : E) (hl : sent.length + 1 = v.d)
    (h2 : 2 ≤ v.d) : (complete v sent c).length = v.d := by
  cases v with
  | plain d =>
    cases sent with
    | nil =>
      have h1 : (0 : ℕ) + 1 = d := hl
      have : (2 : ℕ) ≤ d := h2
      omega
    | cons g0 high =>
      have hd : (g0 :: high).length + 1 = d := hl
      show (g0 :: subE c (addE (addE g0 g0) (total high)) :: high).length = d
      simpa using hd
  | point z d =>
    have hd : sent.length + 1 = d := hl
    show (subE c (mulE z (total sent)) :: sent).length = d
    simpa using hd

/-! ### The fold is a run -/

/-- As many rounds as variables; in each one scalar fewer than the polynomial has coefficients. -/
def Lens : List Var → List (List E × E) → Prop
  | [], [] => True
  | v :: vs, x :: l => x.1.length + 1 = v.d ∧ 2 ≤ v.d ∧ Lens vs l
  | _, _ => False

/-- The rounds' polynomials, as the text completes them, and the challenges, read. -/
def movesOf : List Var → List (List E × E) → E → List (K[X] × K)
  | v :: vs, x :: l, c =>
    (polyOf ρ (complete v x.1 c), ρ.val x.2) :: movesOf vs l (valueAt (complete v x.1 c) x.2)
  | _, _, _ => []

theorem chain_after : ∀ (vs : List Var) (l : List (List E × E)) (c : E), Lens vs l →
    Chain (vs.map (Var.wt ρ)) (movesOf ρ vs l c) (ρ.val c) (ρ.val (after vs l c))
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | v :: vs, x :: l, c, ⟨hl, h2, hr⟩ => by
    obtain ⟨sent, r⟩ := x
    refine ⟨?_, complete_sum ρ v sent c hl h2, ?_⟩
    · show (polyOf ρ (complete v sent c)).natDegree < (v.wt ρ).d
      rw [Var.wt_d, ← complete_length v sent c hl h2]
      exact polyOf_natDegree_lt ρ _ (by rw [complete_length v sent c hl h2]; omega)
    · show Chain _ _ ((polyOf ρ (complete v sent c)).eval (ρ.val r)) _
      rw [polyOf_eval]
      exact chain_after vs l _ hr

theorem movesOf_chal : ∀ (vs : List Var) (l : List (List E × E)) (c : E), Lens vs l →
    (movesOf ρ vs l c).map (·.2) = l.map fun x => ρ.val x.2
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | v :: vs, x :: l, c, ⟨_, _, hr⟩ => by
    show ρ.val x.2 :: (movesOf ρ vs l _).map (·.2) = ρ.val x.2 :: l.map fun x => ρ.val x.2
    rw [movesOf_chal vs l _ hr]

/-! ### The hiding polynomial -/

/-- The list u applied to the values h 0, h 1, ... -/
def dotFrom (h : ℕ → K) : List E → K
  | [] => 0
  | x :: u => ρ.val x * h 0 + dotFrom (fun i => h (i + 1)) u

theorem dotFrom_append : ∀ (a b : List E) (h : ℕ → K),
    dotFrom ρ h (a ++ b) = dotFrom ρ h a + dotFrom ρ (fun i => h (a.length + i)) b
  | [], b, h => by simp [dotFrom]
  | x :: a, b, h => by
    have hf : (fun i => h (a.length + i + 1)) = fun i => h ((x :: a).length + i) := by
      funext i
      congr 1
      show a.length + i + 1 = a.length + 1 + i
      omega
    rw [List.cons_append, dotFrom, dotFrom, dotFrom_append a b, add_assoc, hf]

/-- It reads h at the list's places alone. -/
theorem dotFrom_congr : ∀ (u : List E) (h h' : ℕ → K), (∀ i, i < u.length → h i = h' i) →
    dotFrom ρ h u = dotFrom ρ h' u
  | [], _, _, _ => rfl
  | x :: u, h, h', H => by
    rw [dotFrom, dotFrom, H 0 (by simp),
      dotFrom_congr u (fun i => h (i + 1)) (fun i => h' (i + 1)) fun i hi =>
        H (i + 1) (by simpa using hi)]

theorem powersFrom_length (r : E) : ∀ (n : ℕ) (a : E), (powersFrom r n a).length = n
  | 0, _ => rfl
  | n + 1, a => by rw [powersFrom, List.length_cons, powersFrom_length r n]

theorem dotFrom_powers (r : E) : ∀ (n : ℕ) (a : E) (h : ℕ → K),
    dotFrom ρ h (powersFrom r n a) = ρ.val a * ∑ i ∈ Finset.range n, h i * ρ.val r ^ i
  | 0, _, _ => by simp [powersFrom, dotFrom]
  | n + 1, a, h => by
    rw [powersFrom, dotFrom, dotFrom_powers r n, Finset.sum_range_succ', ρ.mul, Finset.mul_sum,
      mul_add, Finset.mul_sum, pow_zero, mul_one, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

theorem eval_polyFrom (h : ℕ → K) (s n : ℕ) (x : K) :
    (polyFrom h s n).eval x = ∑ i ∈ Finset.range n, h i * x ^ (s + i) := by
  simp [polyFrom, eval_finset_sum]

theorem psiAt_val (v : Var) (r : E) : (v.wt ρ).psi.eval (ρ.val r) = ρ.val (psiAt v r) := by
  cases v <;> simp [Var.wt, psiAt, ρ.one]

/-- **The text's hidingAt is the design's two polynomials**, at the challenges read. -/
theorem hidingAt_val : ∀ (vr : List (Var × E)) (h : ℕ → K),
    dotFrom ρ h (hidingAt vr).1 =
        hid (vr.map fun x => x.1.wt ρ) h (vr.map fun x => ρ.val x.2) ∧
      ρ.val (hidingAt vr).2 = psiProd (vr.map fun x => x.1.wt ρ) (vr.map fun x => ρ.val x.2)
  | [], h => by simp [hidingAt, dotFrom, hid, psiProd, ρ.one]
  | [(v, r)], h => by
    constructor
    · show dotFrom ρ h (powersFrom r v.d oneE) = (polyFrom h 0 (v.wt ρ).d).eval (ρ.val r)
      rw [dotFrom_powers, eval_polyFrom, ρ.one, one_mul, Var.wt_d]
      simp
    · show ρ.val (psiAt v r) = 1 * (v.wt ρ).psi.eval (ρ.val r)
      rw [psiAt_val, one_mul]
  | (v, r) :: y :: rest, h => by
    obtain ⟨ih1, ih2⟩ := hidingAt_val (y :: rest) fun i => h ((v.wt ρ).d - 1 + i)
    constructor
    · show dotFrom ρ h (powersFrom r (v.d - 1) (mulE (hidingAt (y :: rest)).2 r) ++
          (hidingAt (y :: rest)).1) =
        (polyFrom h 1 ((v.wt ρ).d - 1)).eval (ρ.val r) *
            psiProd ((y :: rest).map fun x => x.1.wt ρ) ((y :: rest).map fun x => ρ.val x.2) +
          hid ((y :: rest).map fun x => x.1.wt ρ) (fun i => h ((v.wt ρ).d - 1 + i))
            ((y :: rest).map fun x => ρ.val x.2)
      rw [dotFrom_append, dotFrom_powers, powersFrom_length, ← ih1, ← ih2, eval_polyFrom, ρ.mul,
        Var.wt_d]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · show ρ.val (mulE (hidingAt (y :: rest)).2 (psiAt v r)) =
        psiProd ((y :: rest).map fun x => x.1.wt ρ) ((y :: rest).map fun x => ρ.val x.2) *
          (v.wt ρ).psi.eval (ρ.val r)
      rw [ρ.mul, ih2, psiAt_val]

theorem ownSlots_eq (vs : List Var) : ownSlots vs = 1 + (vs.map fun v => v.d - 1).sum := by
  have gen : ∀ (vs : List Var) (n : ℕ),
      vs.foldl (fun n v => n + (v.d - 1)) n = n + (vs.map fun v => v.d - 1).sum := by
    intro vs
    induction vs with
    | nil => intro n; simp
    | cons v vs ih =>
      intro n
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      omega
  exact gen vs 1

/-- The hiding polynomial has at most as many coefficients as the sumcheck has slots of its own. -/
theorem hidingAt_length_le : ∀ vr : List (Var × E),
    (hidingAt vr).1.length ≤ ownSlots (vr.map (·.1))
  | [] => by simp [hidingAt]
  | [(v, r)] => by
    show (powersFrom r v.d oneE).length ≤ ownSlots [v]
    rw [powersFrom_length, ownSlots_eq]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | (v, r) :: y :: rest => by
    have ih := hidingAt_length_le (y :: rest)
    show (powersFrom r (v.d - 1) (mulE (hidingAt (y :: rest)).2 r) ++
      (hidingAt (y :: rest)).1).length ≤ ownSlots (v :: (y :: rest).map (·.1))
    rw [List.length_append, powersFrom_length, ownSlots_eq, List.map_cons, List.sum_cons]
    rw [ownSlots_eq] at ih
    omega

theorem psiOk_wt (vs : List Var) (hv : ∀ v ∈ vs, 2 ≤ v.d) : PsiOk (vs.map (Var.wt ρ)) := by
  intro w hw
  obtain ⟨v, hvm, rfl⟩ := List.mem_map.mp hw
  have h2 := hv v hvm
  cases v with
  | plain d =>
    have hd : 2 ≤ d := h2
    refine ⟨?_, ?_⟩
    · show (X : K[X]).natDegree < d
      rw [natDegree_X]
      omega
    · show ∑ i ∈ Finset.range d, (if i = 0 then (2 : K) else 1) * (X : K[X]).coeff i = 1
      rw [Finset.sum_eq_single 1]
      · simp
      · intro b _ hb
        rw [coeff_X, if_neg (Ne.symm hb), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
  | point z d =>
    have hd : 2 ≤ d := h2
    refine ⟨?_, ?_⟩
    · show (1 : K[X]).natDegree < d
      rw [natDegree_one]
      omega
    · show ∑ i ∈ Finset.range d, (if i = 0 then (1 : K) else ρ.val z) * (1 : K[X]).coeff i = 1
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb
        simp [coeff_one, hb]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ### The row -/

variable (W : World K)

theorem onSlots_value : ∀ (u : List E) (f : Aff) (first : Nat),
    (onSlots f first u).value ρ W = f.value ρ W + dotFrom ρ (fun i => W.slot (first + i)) u
  | [], f, first => by simp [onSlots, dotFrom]
  | x :: u, f, first => by
    have hs : onSlots f first (x :: u) = onSlots (Aff.addMul f (Aff.slot first) x) (first + 1) u :=
      rfl
    have hf : (fun i => W.slot (first + 1 + i)) = fun i => W.slot (first + (i + 1)) := by
      funext i
      congr 1
      omega
    rw [hs, onSlots_value u, Aff.value_addMul, Aff.value_slot, dotFrom, hf]
    simp only [Nat.add_zero]
    ring

/-- The value of the one claim that is left. -/
theorem row_value {h : Heard} {S0 : E} {kept : Aff} {F G : Fork} {f : Aff}
    (hr : row h S0 kept F = some (f, G)) :
    f.value ρ W =
      dotFrom ρ (fun i => W.slot (h.first + i)) (hidingAt (h.vars.zip h.r)).1 +
        ρ.val h.eps * ρ.val (hidingAt (h.vars.zip h.r)).2 *
          (ρ.val h.target - h.start.value ρ W) +
        ρ.val h.eps * kept.value ρ W - (ρ.val h.claim - ρ.val h.eps * ρ.val S0) := by
  unfold row at hr
  cases hG : F.hideRun h.first
      (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE) with
  | none => simp [hG] at hr
  | some G' =>
    simp only [hG, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at hr
    rw [← hr.1]
    simp only [Aff.value_addMul, onSlots_value, Aff.value_sub, Aff.value_ofConst, ρ.sub, ρ.mul,
      ρ.zero]
    ring

/-! ### The law -/

/-- **THE MASKED SUMCHECK's SOUNDNESS LAW.** -/
theorem sound (vs : List Var) (hv : ∀ v ∈ vs, 2 ≤ v.d) (hcoef : ℕ → K) (S : List K → K)
    (sigma : K) (hS : IsSum (vs.map (Var.wt ρ)) S sigma) (T Cv : K) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card < dAt (vs.map (Var.wt ρ)) pre.length) ∧
      ∀ (W : World K) (h : Heard) (mu : E) (l : List (List E × E)) (S0 : E) (kept : Aff)
        (F G : Fork) (f : Aff),
        h.vars = vs → Lens vs l → h.r = l.map (·.2) →
        h.claim = after vs l (addE mu (mulE h.eps h.target)) →
        ρ.val h.target = T → h.start.value ρ W = Cv →
        (∀ i, i < ownSlots vs → W.slot (h.first + i) = hcoef i) →
        row h S0 kept F = some (f, G) → f.value ρ W = 0 →
        S (l.map fun x => ρ.val x.2) = ρ.val S0 + kept.value ρ W →
        ρ.val h.eps ∉ badE (ρ.val mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val mu) (ρ.val h.eps))
          (movesOf ρ vs l (addE mu (mulE h.eps h.target)))) →
        Cv = sigma := by
  classical
  have hpsi := psiOk_wt ρ vs hv
  obtain ⟨muT, hU⟩ := isSum_hid (vs.map (Var.wt ρ)) hcoef hpsi (by
    intro w hw
    obtain ⟨v, hvm, rfl⟩ := List.mem_map.mp hw
    rw [Var.wt_d]
    have := hv v hvm
    omega)
  choose badE bad hE hB hrun using fun mu =>
    masked (vs.map (Var.wt ρ)) (hid (vs.map (Var.wt ρ)) hcoef) S (psiProd (vs.map (Var.wt ρ))) muT
      sigma hU hS (isSum_psiProd _ hpsi) mu T Cv
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro W h mu l S0 kept F G f hvars hlens hr hclaim hT hC hslots hrow hzero hend hne hnb
  have hch := chain_after ρ vs l (addE mu (mulE h.eps h.target)) hlens
  rw [ρ.add, ρ.mul, hT] at hch
  have hmv := movesOf_chal ρ vs l (addE mu (mulE h.eps h.target)) hlens
  have hfst : (h.vars.zip h.r).map (·.1) = vs := by
    rw [hvars, hr]
    have gen : ∀ (vs : List Var) (l : List (List E × E)), Lens vs l →
        (vs.zip (l.map (·.2))).map (·.1) = vs := by
      intro vs
      induction vs with
      | nil => intro l _; rfl
      | cons v vs ih =>
        intro l hl
        cases l with
        | nil => exact hl.elim
        | cons x l =>
          simp only [List.map_cons, List.zip_cons_cons]
          rw [ih l hl.2.2]
    exact gen vs l hlens
  have hzip : (h.vars.zip h.r).map (fun x => x.1.wt ρ) = vs.map (Var.wt ρ) ∧
      (h.vars.zip h.r).map (fun x => ρ.val x.2) = l.map fun x => ρ.val x.2 := by
    rw [hvars, hr]
    have gen : ∀ (vs : List Var) (l : List (List E × E)), Lens vs l →
        (vs.zip (l.map (·.2))).map (fun x => x.1.wt ρ) = vs.map (Var.wt ρ) ∧
          (vs.zip (l.map (·.2))).map (fun x => ρ.val x.2) = l.map fun x => ρ.val x.2 := by
      intro vs
      induction vs with
      | nil =>
        intro l hl
        cases l with
        | nil => exact ⟨rfl, rfl⟩
        | cons _ _ => exact hl.elim
      | cons v vs ih =>
        intro l hl
        cases l with
        | nil => exact hl.elim
        | cons x l =>
          obtain ⟨a, b⟩ := ih l hl.2.2
          constructor
          · simp only [List.map_cons, List.zip_cons_cons]
            rw [a]
          · simp only [List.map_cons, List.zip_cons_cons]
            rw [b]
    exact gen vs l hlens
  obtain ⟨hu1, hu2⟩ := hidingAt_val ρ (h.vars.zip h.r) hcoef
  rw [hzip.1, hzip.2] at hu1 hu2
  have hv0 := row_value ρ W hrow
  rw [hzero, hT, hC, hu2] at hv0
  have hdot : dotFrom ρ (fun i => W.slot (h.first + i)) (hidingAt (h.vars.zip h.r)).1 =
      dotFrom ρ hcoef (hidingAt (h.vars.zip h.r)).1 :=
    dotFrom_congr ρ _ _ _ fun i hi => hslots i (by
      have := hidingAt_length_le (h.vars.zip h.r)
      rw [hfst] at this
      omega)
  rw [hdot, hu1] at hv0
  refine hrun (ρ.val mu) (ρ.val h.eps) _ _ hch ?_ hne (by convert hnb)
  rw [hmv, ← hclaim, hend]
  linear_combination hv0

/-! ### From the hearing's own return -/

theorem lens_of_read : ∀ {vs : List Var} {used : List Fmt.RoundView} {l : List (List E × E)},
    VarsRead vs used l → (∀ v ∈ vs, 2 ≤ v.d) → Lens vs l
  | [], [], [], _, _ => trivial
  | v :: vs, _ :: _, (s, g) :: l, h, hv => by
    have h2 : 2 ≤ v.d := hv v (by simp)
    have hs : s.length = v.d - 1 := h.1.2.1
    exact ⟨by show s.length + 1 = v.d; omega, h2,
      lens_of_read h.2 fun u hu => hv u (by simp [hu])⟩
  | [], [], _ :: _, h, _ => h.elim
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], h, _ => h.elim

theorem two_le_all {lead : Nat} {vs : List Var} {e : Ends}
    (hk : shapeOk ⟨lead, vs, some e⟩ = true) :
    ∀ v ∈ (⟨lead, vs, some e⟩ : Call).all, 2 ≤ v.d := by
  simp only [shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
  intro v hv
  have hm : v ∈ vs ++ [Var.point zeroE (e.dY + 1)] := hv
  rcases List.mem_append.mp hm with h | h
  · exact (hk.1 v h).1
  · rw [List.mem_singleton] at h
    subst h
    show 2 ≤ e.dY + 1
    have := hk.2.1
    omega

/-- **THE LAW, FROM THE HEARING's OWN RETURN**, for a call with ends. Fixed first: the call, the
hiding polynomial's coefficients, the summand with its sum over the call's variables (Y last), and
the two values of the claimed form. R: what the hearing read of its rounds. -/
theorem sound_hear (lead : Nat) (vs : List Var) (e : Ends)
    (hk : shapeOk ⟨lead, vs, some e⟩ = true) (hcoef : ℕ → K) (S : List K → K) (sigma : K)
    (hS : IsSum ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) S sigma) (T Cv : K) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card <
        dAt ((⟨lead, vs, some e⟩ : Call).all.map (Var.wt ρ)) pre.length) ∧
      ∀ (W : World K) (C : Aff) (F G : Fork) (rs : List Fmt.RoundView) (h : Heard) (R : Read) (S0 : E)
        (kept : Aff) (F' G' : Fork) (f : Aff),
        hear C ⟨lead, vs, some e⟩ F rs = some (h, G) → readAll ⟨lead, vs, some e⟩ rs = some R →
        ρ.val h.target = T → C.value ρ W = Cv →
        (∀ i, i < ownSlots (⟨lead, vs, some e⟩ : Call).all → W.slot (h.first + i) = hcoef i) →
        row h S0 kept F' = some (f, G') → f.value ρ W = 0 →
        S (h.r.map ρ.val) = ρ.val S0 + kept.value ρ W →
        ρ.val R.eps ∉ badE (ρ.val R.mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val R.mu) (ρ.val R.eps))
          (movesOf ρ (⟨lead, vs, some e⟩ : Call).all R.rounds
            (addE R.mu (mulE R.eps h.target)))) →
        Cv = sigma := by
  obtain ⟨badE, bad, hE, hB, hrun⟩ :=
    sound ρ (⟨lead, vs, some e⟩ : Call).all (two_le_all hk) hcoef S sigma hS T Cv
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro W C F G rs h R S0 kept F' G' f hh hR hT hC hslots hrow hzero hend hne hnb
  obtain ⟨_, T', R', _, hR', hrec, _⟩ := hear_spec hh
  have hRR : R' = R := by
    rw [hR] at hR'
    exact (Option.some.inj hR').symm
  subst hRR
  obtain ⟨_, _, _, _, _, _, _, hvr, _⟩ := readAll_spec hR
  have hl : Lens (⟨lead, vs, some e⟩ : Call).all R'.rounds := lens_of_read hvr (two_le_all hk)
  have e1 : h.vars = (⟨lead, vs, some e⟩ : Call).all := by rw [hrec]
  have e2 : h.r = R'.rounds.map (·.2) := by rw [hrec]
  have e3 : h.eps = R'.eps := by rw [hrec]
  have e4 : h.start = C := by rw [hrec]
  have e5 : h.claim = after (⟨lead, vs, some e⟩ : Call).all R'.rounds
      (addE R'.mu (mulE h.eps h.target)) := by rw [hrec]
  refine hrun W h R'.mu R'.rounds S0 kept F' G' f e1 hl e2 e5 hT (by rw [e4]; exact hC) hslots hrow
    hzero ?_ (by rw [e3]; exact hne) (by rw [e3]; exact hnb)
  rw [← hend, e2, List.map_map]
  rfl

end VerifiableInference.Desc.Part.MaskedSum
