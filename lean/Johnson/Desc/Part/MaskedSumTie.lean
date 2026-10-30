-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumTie.lean: THE PART «THE MASKED SUMCHECK»: THE TIE. Proofs of the three statements that
Johnson/Desc/Part/MaskedSumLaw.lean lays down (PartHearLaw, PartRowLaw, PartReturns), to the letter, over
Part/MaskedSum4.lean, unturned.
  Var.weight            : `verify-on-bytes`'s weight of a variable (plain d: Weight.plain d; point z d: Weight.equality z d).
  complete_read         : a round's completed polynomial, read, is `verify-on-bytes`'s, where d - 1 scalars were sent.
  after_read            : the fold «after», read, is `verify-on-bytes`'s claimAfter.
  partHearLaw           : PartHearLaw (by after_read and plain_fin).
  hidingAt_read         : the hiding polynomial's linear form and P, read, are `verify-on-bytes`'s hidingWalk.
  row_spec, rowAff_value: where «row» returns, its form is rowAff; what rowAff is worth in a world.
  partRowLaw            : PartRowLaw (by Psc.rowForm_value and plain_row).
  readAll_ret, hideRun_ret, partReturns : PartReturns.
WHAT IS NOT SAID. Nothing on soundness, on an honest prover or on hiding. Every equation is between readings, not between
the program's elements. PartRowLaw is an implication: that its premises can be met together at a real kind is not shown here.

-/
import Johnson.Desc.Part.MaskedSumLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model
open Iop Prob Cb TWhole Johnson.L5.Layers Cb.Pv.Att OnBytes.Tie.Pv.Att

/-! ## The fold -/

/-- `verify-on-bytes`'s weight of a variable. -/
def Var.weight : Var → OnBytes.Psc.Weight
  | .plain d => OnBytes.Psc.Weight.plain d
  | .point z d => OnBytes.Psc.Weight.equality z d

theorem Var.weight_d (v : Var) : v.weight.d = v.d := by cases v <;> rfl

section Read
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem total_read (l : List E) : ρ.val (total l) = (l.map ρ.val).sum := by
  have h := foldl_adds ρ.val addE ρ.val ρ.add l zeroE
  rw [ρ.zero, zero_add] at h
  exact h

theorem dotValue_cons (a b : E) (m l : List E) :
    dotValue ρ (a :: m) (b :: l) = ρ.val a * ρ.val b + dotValue ρ m l := by
  simp only [dotValue, List.zip_cons_cons, List.map_cons, List.sum_cons]

/-- A polynomial's value, read, hangs on the readings of its coefficients alone. -/
theorem polyAt_congr (x : E) : ∀ (g g' : List E), g.map ρ.val = g'.map ρ.val →
    ρ.val (OnBytes.Psc.polyAt g x) = ρ.val (OnBytes.Psc.polyAt g' x)
  | [], [], _ => rfl
  | a :: g, b :: g', h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    have ih := polyAt_congr x g g' h2
    show ρ.val (addE (mulE (OnBytes.Psc.polyAt g x) x) a) = ρ.val (addE (mulE (OnBytes.Psc.polyAt g' x) x) b)
    simp only [ρ.add, ρ.mul, ih, h1]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **A round's completed polynomial, read, is `verify-on-bytes`'s.** -/
theorem complete_read (v : Var) (s : List E) (c c' : E) (hl : s.length + 1 = v.d) (h : ρ.val c = ρ.val c') :
    (complete v s c).map ρ.val = (v.weight.complete s c').map ρ.val := by
  cases v with
  | plain d =>
    have hd : s.length + 1 = d := hl
    cases s with
    | nil =>
      have e1 : ρ.val (OnBytes.Psc.dot (OnBytes.Psc.Weight.plain d).moment [zeroE]) = 0 := by
        rw [ρ.dot]
        show dotValue ρ (addE oneE oneE :: List.replicate (d - 1) oneE) (zeroE :: []) = 0
        rw [dotValue_cons ρ, ρ.zero]
        simp [dotValue]
      show [ρ.val c] =
        [ρ.val (mulE (subE c' (OnBytes.Psc.dot (OnBytes.Psc.Weight.plain d).moment [zeroE])) oneE)]
      rw [ρ.mul, ρ.sub, ρ.one, e1, h]
      simp
    | cons g0 high =>
      have hlen : (zeroE :: high).length ≤ d - 1 := by
        simp only [List.length_cons] at hd ⊢
        omega
      have e1 : ρ.val (OnBytes.Psc.dot (OnBytes.Psc.Weight.plain d).moment (g0 :: zeroE :: high)) =
          (1 + 1) * ρ.val g0 + (high.map ρ.val).sum := by
        rw [ρ.dot]
        show dotValue ρ (addE oneE oneE :: List.replicate (d - 1) oneE) (g0 :: zeroE :: high) = _
        rw [dotValue_cons ρ, dotValue_replicate ρ oneE (d - 1) (zeroE :: high) hlen, ρ.add, ρ.one,
          List.map_cons, List.sum_cons, ρ.zero]
        ring
      have e2 : ρ.val (subE c (addE (addE g0 g0) (total high))) =
          ρ.val (mulE (subE c' (OnBytes.Psc.dot (OnBytes.Psc.Weight.plain d).moment (g0 :: zeroE :: high))) oneE) := by
        rw [ρ.mul, ρ.sub c', e1, ρ.one, ρ.sub c, ρ.add, ρ.add, total_read ρ, h]
        ring
      show ρ.val g0 :: ρ.val (subE c (addE (addE g0 g0) (total high))) :: high.map ρ.val =
        ρ.val g0 :: ρ.val (mulE (subE c'
          (OnBytes.Psc.dot (OnBytes.Psc.Weight.plain d).moment (g0 :: zeroE :: high))) oneE) :: high.map ρ.val
      rw [e2]
  | point z d =>
    have hd : s.length + 1 = d := hl
    have hlen : s.length ≤ d - 1 := by omega
    have e1 : ρ.val (OnBytes.Psc.dot (OnBytes.Psc.Weight.equality z d).moment (zeroE :: s)) =
        ρ.val z * (s.map ρ.val).sum := by
      rw [ρ.dot]
      show dotValue ρ (oneE :: List.replicate (d - 1) z) (zeroE :: s) = _
      rw [dotValue_cons ρ, dotValue_replicate ρ z (d - 1) s hlen, ρ.zero]
      ring
    have e2 : ρ.val (subE c (mulE z (total s))) =
        ρ.val (mulE (subE c' (OnBytes.Psc.dot (OnBytes.Psc.Weight.equality z d).moment (zeroE :: s))) oneE) := by
      rw [ρ.mul _ oneE, ρ.sub c', e1, ρ.one, ρ.sub c, ρ.mul, total_read ρ, h]
      ring
    show ρ.val (subE c (mulE z (total s))) :: s.map ρ.val =
      ρ.val (mulE (subE c' (OnBytes.Psc.dot (OnBytes.Psc.Weight.equality z d).moment (zeroE :: s))) oneE) ::
        s.map ρ.val
    rw [e2]

/-- Each round has as many scalars as its variable asks: d - 1. As far as the shorter list goes. -/
def LensT : List Var → List (List E × E) → Prop
  | v :: vs, (s, _) :: rs => s.length + 1 = v.d ∧ LensT vs rs
  | _, _ => True

/-- **The fold, read, is `verify-on-bytes`'s.** -/
theorem after_read : ∀ (vs : List Var) (rs : List (List E × E)) (c c' : E), LensT vs rs → ρ.val c = ρ.val c' →
    ρ.val (after vs rs c) = ρ.val (OnBytes.Psc.claimAfter (vs.map Var.weight) rs c')
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, _, h => h
  | _ :: _, [], _, _, _, h => h
  | v :: vs, (s, r) :: rs, c, c', hL, h => by
    have e := complete_read ρ v s c c' hL.1 h
    show ρ.val (after vs rs (OnBytes.Psc.polyAt (complete v s c) r)) =
      ρ.val (OnBytes.Psc.claimAfter (vs.map Var.weight) rs (OnBytes.Psc.polyAt (v.weight.complete s c') r))
    exact after_read vs rs _ _ hL.2 (polyAt_congr ρ r _ _ e)

end Read

theorem weights_varsOf : ∀ (degs : List Nat) (DY : Nat), (varsOf degs DY).map Var.weight = plainWs degs DY
  | [], _ => rfl
  | d :: degs, DY => congrArg (OnBytes.Psc.Weight.plain (d + 1) :: ·) (weights_varsOf degs DY)

theorem lens_varsOf (DY : Nat) (sentY : List E) (beta : E) (hY : sentY.length = DY) :
    ∀ (rs : List (List E × E)) (degs : List Nat), rs.map (·.1.length) = degs →
      LensT (varsOf degs DY) (rs ++ [(sentY, beta)])
  | [], degs, h => by
    subst h
    exact ⟨congrArg (· + 1) hY, trivial⟩
  | (s, r) :: rs, degs, h => by
    subst h
    exact ⟨rfl, lens_varsOf DY sentY beta hY rs _ rfl⟩

/-- **PartHearLaw.** -/
theorem partHearLaw : PartHearLaw := by
  intro K _ _ ρ T st t mu eps rs sentY beta hβ vals h1 hl hY
  rw [plain_fin ρ T st t mu eps rs sentY beta hβ vals h1 hl hY, ← weights_varsOf]
  exact (after_read ρ _ _ _ _ (lens_varsOf T.DY sentY beta hY rs _ hl) rfl).symm

/-! ## The row -/

section Read2
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- `verify-on-bytes`'s loop of powers gives our list. -/
theorem powersLoop_eq (x : E) : ∀ (n : Nat) (c : E) (done : List E),
    OnBytes.Psc.powersLoop x n c done = done.reverse ++ powersFrom x n c
  | 0, _, done => by simp [OnBytes.Psc.powersLoop, powersFrom]
  | n + 1, c, done => by
    simp [OnBytes.Psc.powersLoop, powersFrom, powersLoop_eq x n (mulE c x) (c :: done)]

theorem powers_eq (c x : E) (n : Nat) : OnBytes.Psc.powers c x n = powersFrom x n c := by
  simp [OnBytes.Psc.powers, powersLoop_eq]

theorem powersFrom_congr (x : E) : ∀ (n : Nat) (a a' : E), ρ.val a = ρ.val a' →
    (powersFrom x n a).map ρ.val = (powersFrom x n a').map ρ.val
  | 0, _, _, _ => rfl
  | n + 1, a, a', h => by
    have ih := powersFrom_congr x n (mulE a x) (mulE a' x) (by rw [ρ.mul, ρ.mul, h])
    show ρ.val a :: (powersFrom x n (mulE a x)).map ρ.val = ρ.val a' :: (powersFrom x n (mulE a' x)).map ρ.val
    rw [ih, h]

theorem psiAt_read (v : Var) (r : E) : ρ.val (psiAt v r) = ρ.val (OnBytes.Psc.polyAt v.weight.psi r) := by
  cases v with
  | plain d =>
    show ρ.val r = ρ.val (addE (mulE (addE (mulE zeroE r) oneE) r) zeroE)
    simp only [ρ.add, ρ.mul, ρ.zero, ρ.one]
    ring
  | point z d =>
    show ρ.val oneE = ρ.val (addE (mulE zeroE r) oneE)
    simp only [ρ.add, ρ.mul, ρ.zero, ρ.one]
    ring

/-- A variable with its challenge, as `verify-on-bytes` has the pair. -/
def asW (p : Var × E) : OnBytes.Psc.Weight × E := (p.1.weight, p.2)

/-- **The hiding polynomial's linear form and P, read, are `verify-on-bytes`'s.** -/
theorem hidingAt_read : ∀ (l : List (Var × E)),
    (hidingAt l).1.map ρ.val = (OnBytes.Psc.hidingWalk (l.map asW)).1.map ρ.val ∧
      ρ.val (hidingAt l).2 = ρ.val (OnBytes.Psc.hidingWalk (l.map asW)).2
  | [] => ⟨rfl, rfl⟩
  | [(v, r)] => by
    refine ⟨?_, psiAt_read ρ v r⟩
    show (powersFrom r v.d oneE).map ρ.val = (OnBytes.Psc.powers oneE r v.weight.d).map ρ.val
    rw [powers_eq, Var.weight_d]
  | (v, r) :: q :: rest => by
    obtain ⟨i1, i2⟩ := hidingAt_read (q :: rest)
    constructor
    · show (powersFrom r (v.d - 1) (mulE (hidingAt (q :: rest)).2 r) ++ (hidingAt (q :: rest)).1).map ρ.val =
        (OnBytes.Psc.powers (mulE (OnBytes.Psc.hidingWalk ((q :: rest).map asW)).2 r) r (v.weight.d - 1) ++
          (OnBytes.Psc.hidingWalk ((q :: rest).map asW)).1).map ρ.val
      rw [powers_eq, Var.weight_d, List.map_append, List.map_append, i1,
        powersFrom_congr ρ r (v.d - 1) _ _ (show ρ.val (mulE (hidingAt (q :: rest)).2 r) =
          ρ.val (mulE (OnBytes.Psc.hidingWalk ((q :: rest).map asW)).2 r) by rw [ρ.mul, ρ.mul, i2])]
    · show ρ.val (mulE (hidingAt (q :: rest)).2 (psiAt v r)) =
        ρ.val (mulE (OnBytes.Psc.hidingWalk ((q :: rest).map asW)).2 (OnBytes.Psc.polyAt v.weight.psi r))
      rw [ρ.mul, ρ.mul, i2, psiAt_read ρ v r]

theorem zip_weight : ∀ (vs : List Var) (r : List E), (vs.map Var.weight).zip r = (vs.zip r).map asW
  | [], _ => by simp
  | _ :: _, [] => by simp
  | v :: vs, x :: r => congrArg ((v.weight, x) :: ·) (zip_weight vs r)

theorem sumFrom_congr : ∀ (l l' : List E) (s : Nat), l.map ρ.val = l'.map ρ.val →
    sumFrom (fun j x => ρ.val x * W.slot j) s l = sumFrom (fun j x => ρ.val x * W.slot j) s l'
  | [], [], _, _ => rfl
  | a :: l, b :: l', s, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    simp only [sumFrom]
    rw [sumFrom_congr l l' (s + 1) h2, h1]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem onSlots_sumFrom (a : Aff) (first : Nat) (u : List E) :
    (onSlots a first u).value ρ W = a.value ρ W + sumFrom (fun j x => ρ.val x * W.slot j) first u := by
  unfold onSlots
  induction u generalizing a first with
  | nil => simp [sumFrom]
  | cons x l ih =>
    simp only [List.foldl_cons, sumFrom]
    rw [ih, Aff.value_addMul, Aff.value_slot]
    ring

end Read2

/-- The form that «row» hands back. -/
def rowAff (h : Heard) (S0 : E) (kept : Aff) : Aff :=
  Aff.addMul
    (Aff.addMul
      (onSlots (Aff.ofConst (subE zeroE (subE h.claim (mulE h.eps S0)))) h.first (hidingAt (h.vars.zip h.r)).1)
      (Aff.ofConst h.target - h.start) (mulE h.eps (hidingAt (h.vars.zip h.r)).2))
    kept h.eps

/-- Where «row» returns, its form is rowAff. -/
theorem row_spec {h : Heard} {S0 : E} {kept : Aff} {F G : Fork} {f : Aff} (hr : row h S0 kept F = some (f, G)) :
    f = rowAff h S0 kept := by
  unfold row at hr
  cases ho : F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE) with
  | none => simp [ho] at hr
  | some G' =>
    simp only [ho, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hr
    exact hr.1.symm

/-- What rowAff is worth in a world. -/
theorem rowAff_value {K : Type} [CommRing K] (ρ : Reading K) (W : World K) (h : Heard) (S0 : E) (kept : Aff) :
    (rowAff h S0 kept).value ρ W =
      sumFrom (fun j x => ρ.val x * W.slot j) h.first (hidingAt (h.vars.zip h.r)).1 +
        ρ.val h.eps * ρ.val (hidingAt (h.vars.zip h.r)).2 * (ρ.val h.target - h.start.value ρ W) +
        ρ.val h.eps * kept.value ρ W - (ρ.val h.claim - ρ.val h.eps * ρ.val S0) := by
  simp only [rowAff, Aff.value_addMul, onSlots_sumFrom, Aff.value_sub, Aff.value_ofConst, ρ.sub, ρ.mul, ρ.zero]
  ring

/-- `verify-on-bytes`'s record with what the hearing handed back in it. ws: the weights. c: the running claim. -/
def older (h : Heard) (ws : List OnBytes.Psc.Weight) (c : E) : OnBytes.Model.Psc :=
  { start := h.start, target := h.target, eps := h.eps, claim := c, first := h.first, vars := ws.toArray,
    r := h.r.toArray }

/-- **PartRowLaw.** -/
theorem partRowLaw : PartRowLaw := by
  intro K _ _ ρ T h1 hF W h rs sentY beta hβ vals mu S0 st m F G f hA hl hY hrow D1 D2 D4
  have hf : f = rowAff h S0 {} := row_spec hrow
  have hL := lens_varsOf T.DY sentY beta hY rs _ hl
  have hc : ρ.val h.claim = ρ.val (OnBytes.Psc.claimAfter (plainWs (List.ofFn T.deg) T.DY)
      (rs ++ [(sentY, beta)]) (addE mu (mulE h.eps h.target))) := by
    rw [hA.claim, ← weights_varsOf]
    exact after_read ρ _ _ _ _ hL rfl
  have hp : PscAt (older h (plainWs (List.ofFn T.deg) T.DY) (OnBytes.Psc.claimAfter
      (plainWs (List.ofFn T.deg) T.DY) (rs ++ [(sentY, beta)]) (addE mu (mulE h.eps h.target))))
      (plainWs (List.ofFn T.deg) T.DY) (rs ++ [(sentY, beta)]) mu :=
    ⟨by simp [older], by simp [older, hA.r], rfl⟩
  have key := plain_row ρ T h1 hF (⟨Unit, Empty, Unit, fun _ e => e.elim⟩ : Iop.ExtSpec) () W _ rs sentY beta hβ
    vals mu S0 st m hp (plain_reads ρ T rs sentY beta hβ vals hl hY) D1 D2 D4
  have hw : (older h (plainWs (List.ofFn T.deg) T.DY) (OnBytes.Psc.claimAfter
      (plainWs (List.ofFn T.deg) T.DY) (rs ++ [(sentY, beta)]) (addE mu (mulE h.eps h.target)))).walk =
      OnBytes.Psc.hidingWalk ((h.vars.zip h.r).map asW) := by
    unfold OnBytes.Model.Psc.walk
    rw [OnBytes.zipT_eq, ← zip_weight, hA.vars, weights_varsOf]
    simp [older]
  obtain ⟨a1, a2⟩ := hidingAt_read ρ (h.vars.zip h.r)
  have hv : f.value ρ W = ((older h (plainWs (List.ofFn T.deg) T.DY) (OnBytes.Psc.claimAfter
      (plainWs (List.ofFn T.deg) T.DY) (rs ++ [(sentY, beta)]) (addE mu (mulE h.eps h.target)))).rowForm S0
      {}).value ρ W := by
    rw [hf, rowAff_value, Psc.rowForm_value, hw, sumFrom_congr ρ W _ _ _ a1, a2]
    simp only [older, hc]
  rw [hv]
  exact key

/-! ## The hearing returns -/

theorem one_of_length {α : Type} : ∀ (l : List α), l.length = 1 → ∃ a, l = [a]
  | [a], _ => ⟨a, rfl⟩
  | [], h => by simp at h
  | _ :: _ :: _, h => by
    simp only [List.length_cons] at h
    omega

/-- A round that fits an entry of n scalars and k draws is read. -/
theorem roundOf_ret {name : String} {n k nz : Nat} {r : Fmt.RoundView} (h : Fit (entry name n k nz) r) :
    ∃ s, roundOf n k r = some (s, r.drawn.elems.map E.ofTriple) ∧ s.length = n := by
  obtain ⟨⟨s, h1, h2⟩, h3⟩ := h
  have e2 : s.length = n := by
    have h2' : 24 * n = 24 * s.length := h2
    omega
  have e3 : r.drawn.elems.length = k := h3
  refine ⟨s, ?_, e2⟩
  unfold roundOf
  rw [h1]
  simp [e2, e3]

/-- The rounds fit the variables, one each. -/
def FitV : List Var → List Fmt.RoundView → Prop
  | [], [] => True
  | v :: vs, r :: rs => Fit (entry "PSC round" (v.d - 1) 1 0) r ∧ FitV vs rs
  | _, _ => False

theorem varRounds_ret : ∀ (vs : List Var) (used rest : List Fmt.RoundView), FitV vs used →
    ∃ l, varRounds vs (used ++ rest) = some (l, rest)
  | [], [], _, _ => ⟨[], rfl⟩
  | v :: vs, r :: used, rest, h => by
    obtain ⟨s, a1, _⟩ := roundOf_ret h.1
    obtain ⟨g, a2⟩ := one_of_length (r.drawn.elems.map E.ofTriple) (by rw [List.length_map]; exact h.1.2)
    obtain ⟨l, a3⟩ := varRounds_ret vs used rest h.2
    rw [a2] at a1
    refine ⟨(s, g) :: l, ?_⟩
    show varRounds (v :: vs) (r :: (used ++ rest)) = some ((s, g) :: l, rest)
    simp only [varRounds, a1, a3]
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem FitV.snoc : ∀ {vs : List Var} {used : List Fmt.RoundView} (v : Var) (r : Fmt.RoundView),
    Fits (vs.map fun v => entry "PSC round" (v.d - 1) 1 0) used → Fit (entry "PSC round" (v.d - 1) 1 0) r →
    FitV (vs ++ [v]) (used ++ [r])
  | [], [], _, _, _, h => ⟨h, trivial⟩
  | _ :: _, _ :: _, v, r, h1, h => ⟨h1.1, FitV.snoc v r h1.2 h⟩
  | [], _ :: _, _, _, h1, _ => h1.elim
  | _ :: _, [], _, _, h1, _ => h1.elim

theorem Fits.cut : ∀ {a b : List Fmt.Entry} {x : List Fmt.RoundView}, Fits (a ++ b) x →
    ∃ x1 x2, x = x1 ++ x2 ∧ Fits a x1 ∧ Fits b x2
  | [], _, x, h => ⟨[], x, rfl, trivial, h⟩
  | _ :: _, _, r :: _, h => by
    obtain ⟨x1, x2, e, h1, h2⟩ := Fits.cut h.2
    exact ⟨r :: x1, x2, congrArg (r :: ·) e, ⟨h.1, h1⟩, h2⟩
  | _ :: _, _, [], h => h.elim

theorem Fits.one {a : Fmt.Entry} {x : List Fmt.RoundView} (h : Fits [a] x) : ∃ r, x = [r] ∧ Fit a r := by
  match x, h with
  | [r], h => exact ⟨r, rfl, h.1⟩
  | [], h => exact h.elim
  | _ :: _ :: _, h => exact h.2.elim

theorem Fits.two {a b : Fmt.Entry} {x : List Fmt.RoundView} (h : Fits [a, b] x) :
    ∃ r r', x = [r, r'] ∧ Fit a r ∧ Fit b r' := by
  match x, h with
  | [r, r'], h => exact ⟨r, r', rfl, h.1, h.2.1⟩
  | [], h => exact h.elim
  | [_], h => exact h.2.elim
  | _ :: _ :: _ :: _, h => exact h.2.2.elim

/-- **Rounds that fit the call's entries are read.** -/
theorem readAll_ret {lead : Nat} {vs : List Var} {e : Ends} {rs : List Fmt.RoundView}
    (h : Fits (entries ⟨lead, vs, some e⟩) rs) :
    ∃ R, readAll ⟨lead, vs, some e⟩ rs = some R ∧ R.values.length = e.n := by
  have h' : Fits (([entry "PSC epsilon" (lead + 1) 1 0] ++ (vs.map fun v => entry "PSC round" (v.d - 1) 1 0)) ++
      [entry "PSC Y" e.dY 1 1, entry "PSC values" e.n 0 0]) rs := h
  obtain ⟨x, y, e1, hx, hy⟩ := Fits.cut h'
  obtain ⟨x0, u, e2, h0, hu⟩ := Fits.cut hx
  obtain ⟨r0, e3, f0⟩ := h0.one
  obtain ⟨rY, rv, e4, fY, fv⟩ := hy.two
  subst e3 e4 e2 e1
  obtain ⟨s0, b1, b2⟩ := roundOf_ret f0
  obtain ⟨eps, b3⟩ := one_of_length (r0.drawn.elems.map E.ofTriple) (by rw [List.length_map]; exact f0.2)
  obtain ⟨mu, b4⟩ := one_of_length (s0.drop lead) (by rw [List.length_drop, b2]; omega)
  rw [b3] at b1
  have fY' : Fit (entry "PSC round" ((Var.point zeroE (e.dY + 1)).d - 1) 1 0) rY := by
    obtain ⟨⟨s, c1, c2⟩, c3⟩ := fY
    refine ⟨⟨s, c1, ?_⟩, c3⟩
    have c2' : 24 * e.dY = 24 * s.length := c2
    show 24 * (e.dY + 1 - 1) = 24 * s.length
    omega
  obtain ⟨l, b5⟩ := varRounds_ret _ (u ++ [rY]) [rv] (FitV.snoc _ _ hu fY')
  obtain ⟨sv, b6, b7⟩ := roundOf_ret fv
  have hfirst : firstRound ⟨lead, vs, some e⟩ r0 = some (s0.take lead, [mu], [eps]) := by
    simp only [firstRound, b1, Option.map_some, b4]
  have hall : varRounds (Call.all ⟨lead, vs, some e⟩) ((u ++ [rY]) ++ [rv]) = some (l, [rv]) := b5
  refine ⟨⟨mu, eps, l, sv⟩, ?_, b7⟩
  have hrs : [r0] ++ u ++ [rY, rv] = r0 :: ((u ++ [rY]) ++ [rv]) := by simp
  rw [hrs]
  simp only [readAll, hfirst, hall, b6, Option.map_some]

/-- An entry that was not written. (As OnBytes/Tie/Pv/Psc/PscFork.lean's getD_set_other.) -/
theorem getD_set_else {α : Type} (a : Array α) (j i : Nat) (x d : α) (h : i ≠ j) :
    (a.set! j x).getD i d = a.getD i d := by
  simp [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Ne.symm h]

/-- The ledger with y under slot j. -/
def hidden (F : Fork) (j : Nat) (y factor : E) : Fork :=
  { F with gotF := F.gotF.set! j true, vp := F.vp.set! j y, mf := F.mf.set! j factor }

theorem hide_ret (F : Fork) (j : Nat) (y factor : E) (hs : F.gotF.size = F.ns) (hj : j < F.ns)
    (h0 : F.gotF.getD j true = false) : F.hide j y factor = some (hidden F j y factor) := by
  have hc : (decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true) = true := by
    rw [h0, hs]
    simp [hj]
  unfold Fork.hide
  rw [if_pos hc]
  try rfl

theorem hideSteps_ret (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork), F.gotF.size = F.ns →
    first + l.length ≤ F.ns → (∀ j, first ≤ j → j < first + l.length → F.gotF.getD j true = false) →
    ∃ x, l.foldlM (Fork.hideStep factor) (first, F) = some x
  | [], first, F, _, _, _ => ⟨(first, F), rfl⟩
  | y :: l, first, F, hs, hn, hf => by
    have hn' : first + (l.length + 1) ≤ F.ns := hn
    have hh := hide_ret F first y factor hs (by omega)
      (hf first (Nat.le_refl _) (by simp only [List.length_cons]; omega))
    have hq : Fork.hideStep factor (first, F) y = some (first + 1, hidden F first y factor) := by
      simp only [Fork.hideStep, hh, Option.map_some]
    have s1 : (hidden F first y factor).gotF.size = (hidden F first y factor).ns := by
      show (F.gotF.set! first true).size = F.ns
      simp [hs]
    have s2 : first + 1 + l.length ≤ (hidden F first y factor).ns := by
      show first + 1 + l.length ≤ F.ns
      omega
    have s3 : ∀ j, first + 1 ≤ j → j < first + 1 + l.length →
        (hidden F first y factor).gotF.getD j true = false := by
      intro j a b
      show (F.gotF.set! first true).getD j true = false
      rw [getD_set_else _ _ _ _ _ (by omega : j ≠ first)]
      exact hf j (by omega) (by simp only [List.length_cons]; omega)
    obtain ⟨x, hx⟩ := hideSteps_ret factor l (first + 1) (hidden F first y factor) s1 s2 s3
    refine ⟨x, ?_⟩
    rw [List.foldlM_cons, hq]
    simpa using hx

/-- **A run of values goes under slots that are there and free.** -/
theorem hideRun_ret (F : Fork) (first : Nat) (l : List E) (factor : E) (hs : F.gotF.size = F.ns)
    (hn : first + l.length ≤ F.ns) (hf : ∀ j, first ≤ j → j < first + l.length → F.gotF.getD j true = false) :
    ∃ G, F.hideRun first l.toArray factor = some G := by
  obtain ⟨x, hx⟩ := hideSteps_ret factor l first F hs hn hf
  have e : l.toArray.foldlM (Fork.hideStep factor) (first, F) = some x := by
    rw [← Array.foldlM_toList]
    simpa using hx
  refine ⟨x.2, ?_⟩
  unfold Fork.hideRun
  rw [e]

/-- **PartReturns.** -/
theorem partReturns : PartReturns := by
  intro C lead vs e F rs hs hfit hpub hfree
  obtain ⟨R, hR, hn⟩ := readAll_ret hfit
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 hpub
  obtain ⟨g1, g2, g3⟩ := hfree
  obtain ⟨G, hG⟩ := hideRun_ret
    ({ F with next := F.next + ownSlots (Call.all ⟨lead, vs, some e⟩) + R.values.length } : Fork)
    (F.next + ownSlots (Call.all ⟨lead, vs, some e⟩)) R.values ((R.rounds.map (·.2)).getLastD zeroE) g1
    (by rw [hn]; exact g2) (fun j a b => g3 j a (by rw [← hn]; exact b))
  unfold hear
  simp only [hs, hT, hR, guard, if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [hG]
  try rfl

end VerifiableInference.Desc.Part.MaskedSum

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms VerifiableInference.Desc.Part.MaskedSum.partHearLaw
#print axioms VerifiableInference.Desc.Part.MaskedSum.partRowLaw
#print axioms VerifiableInference.Desc.Part.MaskedSum.partReturns
