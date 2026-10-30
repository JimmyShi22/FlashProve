-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/PscSound.lean: THE MASKED SUMCHECK's SOUNDNESS LAW, ROUND BY ROUND, over the
plain functions and the plain record of the sumcheck: the weights, `complete`, `polyAt`,
`hidingWalk` of OnBytes/Iop/Psc.lean and the record `Psc` with `walk` and `rowForm` of
OnBytes/Model/Psc.lean. No routine of a verifier, no monad and no context is named. Definitions,
statements and proofs.

The algebra is OnBytes/Desc/First/P1/SumCore.lean's; the reading of lists as polynomials is
OnBytes/Desc/First/P1/ReadPoly.lean's; the value of the row and the round's equation are
OnBytes/Model/HideLaws.lean's (`Psc.rowForm_value`, `complete_sum`).
  `Held w`: the two tests that every round makes of its weight (`Weight.fits`, `weightHeld`).
  `claimAfter`, `movesP`, `chainP`: the running claim along rounds (weight, what was sent,
    challenge) is a run of the algebra's.
  `hidingWalk_val`: `hidingWalk` is the design's hiding polynomial and product of psi.
  `psc_sound`: THE LAW. Fixed first: the weights; the hiding coefficients (`hidingEntries` many: of
    the slots behind them nothing is asked); the summand S, a function of the challenges, with its
    sum sigma (`IsSum`); the value T of the claimed form on what was shown and its value Cv at the
    hidden values. Then there are: for each mu at most one bad eps; for each mu, eps, rounds in
    front and round's polynomial fewer than d bad challenges; such that a record p over these
    weights, in each of whose rounds one scalar fewer was sent than the polynomial has
    coefficients, whose claim is the running claim behind the rounds ms from mu + eps * target,
    whose row is 0 in a world, where S at the challenges is the end term S0 plus what is kept, and
    no bad element was drawn, has Cv = sigma: the claimed form's value is the sum.

REACH. The law speaks of the plain record. THAT A RECORD p, THE ROUNDS ms AND mu ARE WHAT A
VERIFIER's FUNCTIONS HAVE LEFT AND HAVE READ OFF ITS ROUNDS is the caller's to show: the law is
silent of a verifier that runs until that is shown.
NOT HERE: that the world's hidden values are what a ledger's marks say (shown less factor times
mask). That the letters which stand first are fixed in time before the rounds. That the row is 0.
The caller's `IsSum` and the truth of its end values. Nothing on probabilities: sets are counted.
Nothing on an honest prover or on hiding.
-/
import OnBytes.Desc.First.P1.ReadPoly
import OnBytes.Model.Psc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model Polynomial

variable {K : Type} [Field K] (ρ : Reading K)

/-- A weight read in K. -/
def wtOf (w : OnBytes.Psc.Weight) : Wt K :=
  { d := w.d, mom := fun i => ρ.val (w.moment.getD i zeroE), psi := polyOf ρ w.psi }

/-- The two tests that every round makes of its weight. -/
def Held (w : OnBytes.Psc.Weight) : Prop := w.fits = true ∧ Model.weightHeld w = true

theorem Held.spec {w : OnBytes.Psc.Weight} (h : Held w) :
    2 ≤ w.d ∧ w.moment.length = w.d ∧ w.psi.length ≤ w.d ∧ w.fixed < w.d ∧
      mulE (w.moment.getD w.fixed zeroE) w.fixedInv = oneE ∧
      OnBytes.Psc.dot w.moment w.psi = oneE := by
  obtain ⟨h1, h2⟩ := h
  simp only [OnBytes.Psc.Weight.fits, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  simp only [Model.weightHeld, Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, h2.1, h2.2⟩

theorem sum_getD_dot : ∀ (m q : List E),
    ∑ i ∈ Finset.range m.length, ρ.val (m.getD i zeroE) * ρ.val (q.getD i zeroE) =
      dotValue ρ m q
  | [], _ => by simp [dotValue]
  | a :: m, [] => by simp [dotValue, ρ.zero]
  | a :: m, b :: q => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_getD_dot m q]
    simp only [dotValue, List.zip_cons_cons, List.map_cons, List.sum_cons]
    ring

theorem sum_poly (w : OnBytes.Psc.Weight) (hm : w.moment.length = w.d) (q : List E) :
    (wtOf ρ w).sum (polyOf ρ q) = ρ.val (OnBytes.Psc.dot w.moment q) := by
  rw [ρ.dot, ← sum_getD_dot, hm, Wt.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [polyOf_coeff]
  rfl

theorem complete_length (w : OnBytes.Psc.Weight) (sent : List E) (c : E)
    (h : w.fixed ≤ sent.length) : (w.complete sent c).length = sent.length + 1 := by
  unfold OnBytes.Psc.Weight.complete
  simp only [List.length_append, List.length_cons, List.length_take, List.length_drop]
  omega

/-! ### The rounds -/

/-- A round: its weight, what was sent, the challenge. -/
abbrev Rnd : Type := OnBytes.Psc.Weight × List E × E

/-- The running claim behind the rounds. -/
def claimAfter : List Rnd → E → E
  | [], c => c
  | m :: ms, c => claimAfter ms (OnBytes.Psc.polyAt (m.1.complete m.2.1 c) m.2.2)

/-- The rounds' polynomials and challenges, read. -/
def movesP : List Rnd → E → List (K[X] × K)
  | [], _ => []
  | m :: ms, c =>
    (polyOf ρ (m.1.complete m.2.1 c), ρ.val m.2.2) ::
      movesP ms (OnBytes.Psc.polyAt (m.1.complete m.2.1 c) m.2.2)

/-- Every round's weight has passed its tests, and one scalar fewer was sent than the polynomial has
coefficients. -/
def OkRnds (ms : List Rnd) : Prop := ∀ m ∈ ms, Held m.1 ∧ m.2.1.length + 1 = m.1.d

theorem chainP : ∀ (ms : List Rnd) (c : E), OkRnds ms →
    Chain (ms.map fun m => wtOf ρ m.1) (movesP ρ ms c) (ρ.val c) (ρ.val (claimAfter ms c))
  | [], _, _ => rfl
  | m :: ms, c, h => by
    obtain ⟨hh, hl⟩ := h m (by simp)
    obtain ⟨h2, hm, _, hf, hinv, _⟩ := hh.spec
    have hfix : m.1.fixed ≤ m.2.1.length := by omega
    refine ⟨?_, ?_, ?_⟩
    · show (polyOf ρ (m.1.complete m.2.1 c)).natDegree < m.1.d
      have hlen := complete_length m.1 m.2.1 c hfix
      have := polyOf_natDegree_lt ρ (m.1.complete m.2.1 c) (by omega)
      omega
    · show (wtOf ρ m.1).sum (polyOf ρ (m.1.complete m.2.1 c)) = ρ.val c
      rw [sum_poly ρ m.1 hm]
      exact Model.complete_sum ρ m.1 m.2.1 c hfix hinv
    · show Chain _ _ ((polyOf ρ (m.1.complete m.2.1 c)).eval (ρ.val m.2.2)) _
      rw [polyOf_eval]
      exact chainP ms _ fun x hx => h x (by simp [hx])

theorem movesP_chal : ∀ (ms : List Rnd) (c : E),
    (movesP ρ ms c).map (·.2) = ms.map fun m => ρ.val m.2.2
  | [], _ => rfl
  | m :: ms, c => by
    show ρ.val m.2.2 :: (movesP ρ ms _).map (·.2) = ρ.val m.2.2 :: ms.map fun m => ρ.val m.2.2
    rw [movesP_chal ms]

/-! ### The hiding polynomial -/

theorem powersLoop_eq (x : E) : ∀ (n : ℕ) (c : E) (done : List E),
    OnBytes.Psc.powersLoop x n c done = done.reverse ++ powersFrom x n c
  | 0, _, done => by simp [OnBytes.Psc.powersLoop, powersFrom]
  | n + 1, c, done => by
    rw [OnBytes.Psc.powersLoop, powersLoop_eq x n, powersFrom]
    simp

theorem powers_eq (c x : E) (n : ℕ) : OnBytes.Psc.powers c x n = powersFrom x n c := by
  rw [OnBytes.Psc.powers, powersLoop_eq]
  rfl

theorem psi_val (w : OnBytes.Psc.Weight) (g : E) :
    (wtOf ρ w).psi.eval (ρ.val g) = ρ.val (OnBytes.Psc.polyAt w.psi g) := polyOf_eval ρ g w.psi

/-- **hidingWalk is the design's two polynomials**, at the challenges read. -/
theorem hidingWalk_val : ∀ (vr : List (OnBytes.Psc.Weight × E)) (h : ℕ → K),
    dotFrom ρ h (OnBytes.Psc.hidingWalk vr).1 =
        hid (vr.map fun x => wtOf ρ x.1) h (vr.map fun x => ρ.val x.2) ∧
      ρ.val (OnBytes.Psc.hidingWalk vr).2 =
        psiProd (vr.map fun x => wtOf ρ x.1) (vr.map fun x => ρ.val x.2)
  | [], h => by simp [OnBytes.Psc.hidingWalk, dotFrom, hid, psiProd, ρ.one]
  | [(w, g)], h => by
    constructor
    · show dotFrom ρ h (OnBytes.Psc.powers oneE g w.d) = (polyFrom h 0 w.d).eval (ρ.val g)
      rw [powers_eq, dotFrom_powers, eval_polyFrom, ρ.one, one_mul]
      simp
    · show ρ.val (OnBytes.Psc.polyAt w.psi g) = 1 * (wtOf ρ w).psi.eval (ρ.val g)
      rw [psi_val, one_mul]
  | (w, g) :: y :: rest, h => by
    obtain ⟨ih1, ih2⟩ := hidingWalk_val (y :: rest) fun i => h (w.d - 1 + i)
    constructor
    · show dotFrom ρ h (OnBytes.Psc.powers (mulE (OnBytes.Psc.hidingWalk (y :: rest)).2 g) g
          (w.d - 1) ++ (OnBytes.Psc.hidingWalk (y :: rest)).1) =
        (polyFrom h 1 (w.d - 1)).eval (ρ.val g) *
            psiProd ((y :: rest).map fun x => wtOf ρ x.1) ((y :: rest).map fun x => ρ.val x.2) +
          hid ((y :: rest).map fun x => wtOf ρ x.1) (fun i => h (w.d - 1 + i))
            ((y :: rest).map fun x => ρ.val x.2)
      rw [powers_eq, dotFrom_append, dotFrom_powers, powersFrom_length, ← ih1, ← ih2,
        eval_polyFrom, ρ.mul]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · show ρ.val (mulE (OnBytes.Psc.hidingWalk (y :: rest)).2 (OnBytes.Psc.polyAt w.psi g)) =
        psiProd ((y :: rest).map fun x => wtOf ρ x.1) ((y :: rest).map fun x => ρ.val x.2) *
          (wtOf ρ w).psi.eval (ρ.val g)
      rw [ρ.mul, ih2, psi_val]

/-- The hiding polynomial has at most `hidingEntries` coefficients. -/
theorem hidingWalk_length_le : ∀ vr : List (OnBytes.Psc.Weight × E),
    (OnBytes.Psc.hidingWalk vr).1.length ≤ OnBytes.Psc.hidingEntries (vr.map (·.1))
  | [] => by simp [OnBytes.Psc.hidingWalk]
  | [(w, g)] => by
    show (OnBytes.Psc.powers oneE g w.d).length ≤ 1 + ([w].map fun w => w.d - 1).sum
    rw [powers_eq, powersFrom_length]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | (w, g) :: y :: rest => by
    have ih := hidingWalk_length_le (y :: rest)
    show (OnBytes.Psc.powers (mulE (OnBytes.Psc.hidingWalk (y :: rest)).2 g) g (w.d - 1) ++
      (OnBytes.Psc.hidingWalk (y :: rest)).1).length ≤
        1 + ((w :: (y :: rest).map (·.1)).map fun w => w.d - 1).sum
    rw [List.length_append, powers_eq, powersFrom_length, List.map_cons, List.sum_cons]
    unfold OnBytes.Psc.hidingEntries at ih
    omega

theorem psiOk_of_held (ws : List OnBytes.Psc.Weight) (hw : ∀ w ∈ ws, Held w) :
    PsiOk (ws.map (wtOf ρ)) := by
  intro v hv
  obtain ⟨w, hwm, rfl⟩ := List.mem_map.mp hv
  obtain ⟨h2, hm, hp, _, _, hd⟩ := (hw w hwm).spec
  refine ⟨?_, ?_⟩
  · show (polyOf ρ w.psi).natDegree < w.d
    by_cases h0 : w.psi.length = 0
    · have : w.psi = [] := List.eq_nil_of_length_eq_zero h0
      rw [this]
      show (0 : K[X]).natDegree < w.d
      rw [natDegree_zero]
      omega
    · have := polyOf_natDegree_lt ρ w.psi (by omega)
      omega
  · show (wtOf ρ w).sum (polyOf ρ w.psi) = 1
    rw [sum_poly ρ w hm, hd, ρ.one]

theorem sumFrom_dotFrom (W : World K) : ∀ (l : List E) (first : ℕ),
    sumFrom (fun j x => ρ.val x * W.slot j) first l = dotFrom ρ (fun i => W.slot (first + i)) l
  | [], _ => rfl
  | x :: l, first => by
    have hf : (fun i => W.slot (first + 1 + i)) = fun i => W.slot (first + (i + 1)) := by
      funext i
      congr 1
      omega
    rw [sumFrom, sumFrom_dotFrom W l, dotFrom, hf]
    simp only [Nat.add_zero]

theorem zip_maps {α β γ : Type} (f : α → β) (g : α → γ) : ∀ l : List α,
    (l.map f).zip (l.map g) = l.map fun x => (f x, g x)
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.map_cons, List.zip_cons_cons, zip_maps f g l, List.map_cons]

/-! ### The law -/

/-- **THE LAW over the record Psc.** -/
theorem psc_sound (ws : List OnBytes.Psc.Weight) (hw : ∀ w ∈ ws, Held w) (hcoef : ℕ → K)
    (S : List K → K) (sigma : K) (hS : IsSum (ws.map (wtOf ρ)) S sigma) (T Cv : K) :
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧
      (∀ mu eps pre g, (bad mu eps pre g).card < dAt (ws.map (wtOf ρ)) pre.length) ∧
      ∀ (W : World K) (p : Psc) (mu : E) (ms : List Rnd) (S0 : E) (kept : Aff),
        ms.map (·.1) = ws → (∀ m ∈ ms, m.2.1.length + 1 = m.1.d) →
        p.vars.toList = ws → p.r.toList = ms.map (·.2.2) →
        p.claim = claimAfter ms (addE mu (mulE p.eps p.target)) →
        ρ.val p.target = T → p.start.value ρ W = Cv →
        (∀ i, i < OnBytes.Psc.hidingEntries ws → W.slot (p.first + i) = hcoef i) →
        (p.rowForm S0 kept).value ρ W = 0 →
        S (ms.map fun m => ρ.val m.2.2) = ρ.val S0 + kept.value ρ W →
        ρ.val p.eps ∉ badE (ρ.val mu) →
        (haveI := Classical.decEq K
         NoBad (bad (ρ.val mu) (ρ.val p.eps)) (movesP ρ ms (addE mu (mulE p.eps p.target)))) →
        Cv = sigma := by
  classical
  have hpsi := psiOk_of_held ρ ws hw
  obtain ⟨muT, hU⟩ := isSum_hid (ws.map (wtOf ρ)) hcoef hpsi (by
    intro v hv
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.mp hv
    have := (hw w hwm).spec.1
    show 1 ≤ w.d
    omega)
  choose badE bad hE hB hrun using fun mu =>
    masked (ws.map (wtOf ρ)) (hid (ws.map (wtOf ρ)) hcoef) S (psiProd (ws.map (wtOf ρ))) muT
      sigma hU hS (isSum_psiProd _ hpsi) mu T Cv
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro W p mu ms S0 kept hms hlen hvars hr hclaim hT hC hslots hzero hend hne hnb
  have hok : OkRnds ms := fun m hm =>
    ⟨hw m.1 (by rw [← hms]; exact List.mem_map_of_mem hm), hlen m hm⟩
  have hch := chainP ρ ms (addE mu (mulE p.eps p.target)) hok
  have hmap : (ms.map fun m => wtOf ρ m.1) = ws.map (wtOf ρ) := by
    rw [← hms, List.map_map]
    rfl
  rw [hmap, ρ.add, ρ.mul, hT] at hch
  have hmv := movesP_chal ρ ms (addE mu (mulE p.eps p.target))
  have hzipl : p.vars.toList.zip p.r.toList = ms.map fun m => (m.1, m.2.2) := by
    rw [hvars, hr, ← hms]
    exact zip_maps _ _ ms
  obtain ⟨hu1, hu2⟩ := hidingWalk_val ρ (p.vars.toList.zip p.r.toList) hcoef
  have hz1 : (p.vars.toList.zip p.r.toList).map (fun x => wtOf ρ x.1) = ws.map (wtOf ρ) := by
    rw [hzipl, List.map_map, ← hmap]
    rfl
  have hz2 : (p.vars.toList.zip p.r.toList).map (fun x => ρ.val x.2) =
      ms.map fun m => ρ.val m.2.2 := by
    rw [hzipl, List.map_map]
    rfl
  rw [hz1, hz2] at hu1 hu2
  have hwalk : p.walk = OnBytes.Psc.hidingWalk (p.vars.toList.zip p.r.toList) := by
    rw [Psc.walk, zipT_eq]
  have hv0 := Psc.rowForm_value ρ W p S0 kept
  rw [hzero, hT, hC, sumFrom_dotFrom, hwalk, hu2] at hv0
  have hdot : dotFrom ρ (fun i => W.slot (p.first + i))
      (OnBytes.Psc.hidingWalk (p.vars.toList.zip p.r.toList)).1 =
      dotFrom ρ hcoef (OnBytes.Psc.hidingWalk (p.vars.toList.zip p.r.toList)).1 :=
    dotFrom_congr ρ _ _ _ fun i hi => hslots i (by
      have hle := hidingWalk_length_le (p.vars.toList.zip p.r.toList)
      have hf1 : (p.vars.toList.zip p.r.toList).map (·.1) = ws := by
        rw [hzipl, List.map_map, ← hms]
        rfl
      rw [hf1] at hle
      omega)
  rw [hdot, hu1] at hv0
  refine hrun (ρ.val mu) (ρ.val p.eps) _ _ hch ?_ hne (by convert hnb)
  rw [hmv, ← hclaim, hend]
  linear_combination hv0

end OnBytes.Desc.First.P1
