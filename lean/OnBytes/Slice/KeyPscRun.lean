-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyPscRun.lean: what one run of the zero-knowledge sumcheck hands on, in the field.

OnBytes/Iop/Psc.lean computes, from a claim, a summand, fresh mask entries and what was heard in the
rounds, one row and one claim for each shown map (Psc.run). This file has the same function on lists
over the field, with the same text (PscF.run), and says what its output means.

The setting. All sent messages are fixed. A world (World) gives each mask entry its value; it is a
parameter here. V j and
Kp i are the shown and the kept maps of the summand, as functions of a point. A claim on a map holds
if the map at the point plus the value of the claim's mask form is the claim's value
(PointClaim.Holds). What a run hands on holds (Out.Holds) if its row holds and each of its claims
holds of its shown map.

The summand as a tower (Sums). The sumcheck runs on the variables of the claim and, if a map is
shown, on one more variable Y. T is a tower over these variables (OnBytes/Slice/KeyPscF.lean) whose
value at a full list of challenges is the summand at the point, at the shown maps' values each plus
the last challenge times its own mask entry, and at the kept maps' values (summandAt).

The result (run_end). If what a run hands on holds, then the running claim after the rounds is the
value, at the challenges, of the polynomial of the sumcheck: the hiding polynomial plus eps times
the summand plus eps times the claim's mask form times the product of the polynomials psi.

Main definitions: MaskForm, PointClaim, Claim, Summand, varsOf, masksOf, formOK, Heard, Out, run,
tests, outOf, World, World.form, PointClaim.Holds, Out.Holds, summandAt, Sums, whole.

Main theorems: run_eq, World.form_append, form_scale, form_zip, hidingWalk_length,
outOf_ends_point, outOf_ends_length, outOf_point_length, run_end.

Not claimed. That PscF.run is the reading of the program's Psc.run: the texts are the same, and no
theorem here compares them. Nothing on a protocol. Nothing on hiding.

-/
import OnBytes.Slice.KeyPscF
import OnBytes.Iop.Psc

set_option autoImplicit false

namespace OnBytes.Slice.PscF
open Prob Cb

/-! ## Claim, summand, and what is handed on -/

/-- A linear form in mask entries: each entry with its coefficient. -/
abbrev MaskForm : Type := List (Slot × GE)

/-- Every coefficient of a mask form times c. -/
def scaleForm (c : GE) (m : MaskForm) : MaskForm := m.map fun t => (t.1, c * t.2)

/-- A claim on a map V of the witness: V(point) plus the mask form equals the value. -/
structure PointClaim where
  point : List GE
  masks : MaskForm
  value : GE

/-- The claim: the sum of the summand under these weights, plus the mask form, is the target. -/
structure Claim where
  vars : List Weight
  masks : MaskForm
  target : GE

/-- The public polynomial S. shown: the number of maps whose value at the last point is shown. kept:
the number of maps in which S is affine and whose values are not shown. degree: at least the total
degree of S in its shown maps. coeffs: S at a point and at values of the shown maps, as an affine
form in the kept maps: the constant, then one coefficient for each kept map. -/
structure Summand where
  shown : ℕ
  kept : ℕ
  degree : ℕ
  coeffs : List GE → List GE → List GE

/-- The variables of the masked sumcheck: those of the claim and, if a map is shown, Y. -/
def varsOf (c : Claim) (S : Summand) : List Weight :=
  if S.shown == 0 then c.vars else c.vars ++ [Weight.atZero (S.degree + 1)]

/-- The number of mask entries that one run uses. -/
def masksOf (c : Claim) (S : Summand) : ℕ := hidingEntries (varsOf c S) + S.shown

/-- The sizes of a weight fit each other. -/
def Weight.fits (w : Weight) : Bool :=
  decide (2 ≤ w.d) && w.moment.length == w.d && decide (w.psi.length ≤ w.d) &&
  decide (w.fixed < w.d)

/-- Claim and summand have an allowed form. -/
def formOK (c : Claim) (S : Summand) : Bool :=
  ((S.shown == 0) == (S.degree == 0)) && (decide (0 < S.shown) || !c.vars.isEmpty) &&
  c.vars.all Weight.fits

/-- What the verifier has heard and said in one run. mu: the sum of the hiding polynomial. eps: the
element that joins the hiding polynomial to the claim. rounds: for each variable, Y last, the
coefficients sent and the challenge. values: the shown values. -/
structure Heard where
  mu : GE
  eps : GE
  rounds : List (List GE × GE)
  values : List GE

/-- What one run hands on. The row says: the mask form rowMasks, plus the sum over the kept maps of
rowMaps[i] times map i at the point, equals rowTarget. -/
structure Out where
  point : List GE
  rowMasks : MaskForm
  rowMaps : List GE
  rowTarget : GE
  ends : List PointClaim
  eps : GE
  beta : Option GE

/-- Computes what is handed on. fresh: mask entries just taken from an oracle message's ledger. -/
def run (c : Claim) (S : Summand) (fresh : List Slot) (h : Heard) : Option Out :=
  let vars := varsOf c S
  let challenges := h.rounds.map (·.2)
  let point := challenges.take c.vars.length
  let a := S.coeffs point h.values
  let hw := hidingWalk (vars.zip challenges)
  let last := claimAfter vars h.rounds (h.mu + h.eps * c.target)
  let beta := if S.shown == 0 then none else challenges.getLast?
  if formOK c S && fresh.length == masksOf c S && h.rounds.length == vars.length &&
      h.values.length == S.shown && a.length == 1 + S.kept &&
      ((vars.zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d) then
    some {
      point := point
      rowMasks := fresh.zip hw.1 ++ scaleForm (h.eps * hw.2) c.masks
      rowMaps := (a.drop 1).map fun x => h.eps * x
      rowTarget := last - h.eps * a.headD 0
      ends := ((fresh.drop hw.1.length).zip h.values).map fun p =>
        ⟨point, [(p.1, beta.getD 0)], p.2⟩
      eps := h.eps
      beta := beta }
  else none

/-- What run tests. -/
def tests (c : Claim) (S : Summand) (fresh : List Slot) (h : Heard) : Bool :=
  formOK c S && fresh.length == masksOf c S && h.rounds.length == (varsOf c S).length &&
    h.values.length == S.shown &&
    (S.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).length == 1 + S.kept &&
    (((varsOf c S).zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d)

/-- What run returns if its tests pass. -/
def outOf (c : Claim) (S : Summand) (fresh : List Slot) (h : Heard) : Out :=
  let vars := varsOf c S
  let challenges := h.rounds.map (·.2)
  let point := challenges.take c.vars.length
  let a := S.coeffs point h.values
  let hw := hidingWalk (vars.zip challenges)
  let last := claimAfter vars h.rounds (h.mu + h.eps * c.target)
  let beta := if S.shown == 0 then none else challenges.getLast?
  { point := point
    rowMasks := fresh.zip hw.1 ++ scaleForm (h.eps * hw.2) c.masks
    rowMaps := (a.drop 1).map fun x => h.eps * x
    rowTarget := last - h.eps * a.headD 0
    ends := ((fresh.drop hw.1.length).zip h.values).map fun p =>
      ⟨point, [(p.1, beta.getD 0)], p.2⟩
    eps := h.eps
    beta := beta }

/-- run, in two parts. -/
theorem run_eq (c : Claim) (S : Summand) (fresh : List Slot) (h : Heard) :
    run c S fresh h = if tests c S fresh h then some (outOf c S fresh h) else none := rfl

/-! ## What it means -/

/-- The values of the mask entries of the sent messages. -/
structure World where
  mask : Slot → GE

namespace World
variable (W : World)

/-- The value of a mask form. -/
def form (m : MaskForm) : GE := (m.map fun t => t.2 * W.mask t.1).sum

/-- The empty form has the value 0. -/
theorem form_nil : W.form [] = 0 := rfl

/-- The value of a form, split at its first entry. -/
theorem form_cons (t : Slot × GE) (m : MaskForm) :
    W.form (t :: m) = t.2 * W.mask t.1 + W.form m := by
  unfold form
  rw [List.map_cons, List.sum_cons]

/-- The value of two forms joined is the sum of their values. -/
theorem form_append (m m' : MaskForm) : W.form (m ++ m') = W.form m + W.form m' := by
  unfold form
  rw [List.map_append, List.sum_append]

/-- The value of a form times c is c times its value. -/
theorem form_scale (c : GE) (m : MaskForm) : W.form (scaleForm c m) = c * W.form m := by
  induction m with
  | nil => simp [scaleForm, form]
  | cons t m ih =>
    have h : scaleForm c (t :: m) = (t.1, c * t.2) :: scaleForm c m := rfl
    rw [h, form_cons, form_cons, ih]
    ring

/-- Entries with coefficients from a list: the sum of products with the entries' values. -/
theorem form_zip : ∀ (fr : List Slot) (l : List GE), W.form (fr.zip l) = dot l (fr.map W.mask)
  | [], l => by simp [form, dot_nil_right]
  | _ :: _, [] => by simp [form, dot_nil_left]
  | s :: fr, a :: l => by
    rw [List.zip_cons_cons, form_cons, List.map_cons, dot_cons, form_zip fr l]

end World

/-- The claim holds of the map V. -/
def PointClaim.Holds (W : World) (V : List GE → GE) (c : PointClaim) : Prop :=
  V c.point + W.form c.masks = c.value

/-- **What a run hands on holds**: its row, and each of its claims of its shown map. -/
structure Out.Holds (W : World) (V Kp : ℕ → List GE → GE) (kept : ℕ) (o : Out) : Prop where
  row : W.form o.rowMasks + dot o.rowMaps ((List.range kept).map fun i => Kp i o.point) =
    o.rowTarget
  ends : ∀ (j : ℕ) (e : PointClaim), o.ends[j]? = some e → e.Holds W (V j)

/-- **The summand at a full list of challenges**: at the point, at each shown map's value plus the
last challenge times the map's own mask entry, and at the kept maps' values. -/
def summandAt (W : World) (V Kp : ℕ → List GE → GE) (c : Claim) (S : Summand) (fresh : List Slot)
    (γ : List GE) : GE :=
  let point := γ.take c.vars.length
  let beta := (if S.shown == 0 then none else γ.getLast?).getD 0
  let slots := fresh.drop (hidingEntries (varsOf c S))
  let vals := (List.range S.shown).map fun j => V j point + beta * W.mask (slots.getD j default)
  let a := S.coeffs point vals
  a.headD 0 + dot (a.drop 1) ((List.range S.kept).map fun i => Kp i point)

/-- **T is the summand's tower.** -/
structure Sums (W : World) (V Kp : ℕ → List GE → GE) (c : Claim) (S : Summand)
    (fresh : List Slot) (T : List GE → GE) : Prop where
  tower : Tower (varsOf c S) T
  last : ∀ γ : List GE, γ.length = (varsOf c S).length → T γ = summandAt W V Kp c S fresh γ

/-- **The polynomial of the sumcheck**, as a tower: the hiding polynomial, plus eps times the
summand, plus eps times the claim's mask form times the product of the polynomials psi. -/
def whole (W : World) (c : Claim) (S : Summand) (fresh : List Slot) (T : List GE → GE) (eps : GE)
    (p : List GE) : GE :=
  hideT (varsOf c S) (fresh.map W.mask) p + eps * (T p + W.form c.masks * psiT (varsOf c S) p)

/-- The number of coefficients in the linear form that hidingWalk computes. -/
theorem hidingWalk_length : ∀ (ws : List Weight) (γ : List GE), ws ≠ [] → ws.length = γ.length →
    (∀ w ∈ ws, 1 ≤ w.d) → (hidingWalk (ws.zip γ)).1.length = hidingEntries ws
  | [], _, h, _, _ => absurd rfl h
  | [w], [g], _, _, hd => by
    show (powers 1 g w.d).length = 1 + ((w.d - 1) + 0)
    have := hd w List.mem_cons_self
    rw [powers_length]
    omega
  | w :: w' :: ws, g :: g' :: γ, _, h, hd => by
    show (powers _ g (w.d - 1) ++ (hidingWalk ((w' :: ws).zip (g' :: γ))).1).length =
      1 + ((w.d - 1) + ((w' :: ws).map fun w => w.d - 1).sum)
    rw [List.length_append, powers_length,
      hidingWalk_length (w' :: ws) (g' :: γ) (List.cons_ne_nil _ _) (Nat.succ.inj h)
        fun v hv => hd v (List.mem_cons_of_mem _ hv)]
    unfold hidingEntries
    omega

/-- A list of coefficients times e. -/
theorem dot_map_mul (e : GE) : ∀ l k : List GE, dot (l.map fun x => e * x) k = e * dot l k
  | [], k => by simp [dot_nil_left]
  | _ :: _, [] => by simp [dot_nil_right]
  | a :: l, b :: k => by
    rw [List.map_cons, dot_cons, dot_cons, dot_map_mul e l k]
    ring

/-- There is a variable, if the form is allowed. -/
theorem varsOf_ne_nil {c : Claim} {S : Summand} (h : formOK c S = true) : varsOf c S ≠ [] := by
  unfold formOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  unfold varsOf
  split
  · next h0 =>
    have h1 : S.shown = 0 := by simpa using h0
    rcases h.1.2 with h2 | h2
    · omega
    · intro h3
      rw [h3] at h2
      simp at h2
  · simp

/-- Each claim that a run hands on is at the run's point. -/
theorem outOf_ends_point (c : Claim) (S : Summand) (fresh : List Slot) (h : Heard) :
    ∀ e ∈ (outOf c S fresh h).ends, e.point = (outOf c S fresh h).point := by
  intro e he
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 he
  rfl

/-- If the tests pass, a run hands on one claim for each shown map. -/
theorem outOf_ends_length {c : Claim} {S : Summand} {fresh : List Slot} {h : Heard}
    (ht : tests c S fresh h = true) (hw : ∀ w ∈ varsOf c S, w.OK) :
    (outOf c S fresh h).ends.length = S.shown := by
  unfold tests at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩ := ht
  have hlen : (varsOf c S).length = (h.rounds.map (·.2)).length := by
    rw [List.length_map, h3]
  have hwl := hidingWalk_length (varsOf c S) (h.rounds.map (·.2)) (varsOf_ne_nil h1) hlen
    fun w hm => Nat.le_trans (by decide) (hw w hm).two
  show (((fresh.drop (hidingWalk ((varsOf c S).zip (h.rounds.map (·.2)))).1.length).zip
    h.values).map _).length = S.shown
  rw [List.length_map, List.length_zip, hwl, List.length_drop, h2, h4]
  unfold masksOf
  omega

/-- If the tests pass, the run's point has one coordinate for each variable of the claim. -/
theorem outOf_point_length {c : Claim} {S : Summand} {fresh : List Slot} {h : Heard}
    (ht : tests c S fresh h = true) : (outOf c S fresh h).point.length = c.vars.length := by
  unfold tests at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, _⟩, _⟩ := ht
  show ((h.rounds.map (·.2)).take c.vars.length).length = c.vars.length
  rw [List.length_take, List.length_map, h3]
  unfold varsOf
  split
  · exact Nat.min_self _
  · rw [List.length_append]
    exact Nat.min_eq_left (Nat.le_add_right _ _)

/-- **If what a run hands on holds, the running claim after the rounds is the value of the
polynomial of the sumcheck at the challenges.** -/
theorem run_end (W : World) (V Kp : ℕ → List GE → GE) (c : Claim) (S : Summand)
    (fresh : List Slot) (h : Heard) (ht : tests c S fresh h = true)
    (hw : ∀ w ∈ varsOf c S, w.OK) (T : List GE → GE) (hS : Sums W V Kp c S fresh T)
    (ho : (outOf c S fresh h).Holds W V Kp S.kept) :
    claimAfter (varsOf c S) h.rounds (h.mu + h.eps * c.target) =
      whole W c S fresh T h.eps (h.rounds.map (·.2)) := by
  unfold tests at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩ := ht
  have hlen : (varsOf c S).length = (h.rounds.map (·.2)).length := by
    rw [List.length_map, h3]
  have hwl := hidingWalk_length (varsOf c S) (h.rounds.map (·.2)) (varsOf_ne_nil h1) hlen
    fun w hm => Nat.le_trans (by decide) (hw w hm).two
  -- the shown values are the shown maps' masked values
  have hv : h.values = (List.range S.shown).map fun j =>
      V j ((h.rounds.map (·.2)).take c.vars.length) +
        (if S.shown == 0 then none else (h.rounds.map (·.2)).getLast?).getD 0 *
          W.mask ((fresh.drop (hidingEntries (varsOf c S))).getD j default) := by
    have hsl : (fresh.drop (hidingEntries (varsOf c S))).length = S.shown := by
      rw [List.length_drop, h2]
      unfold masksOf
      omega
    refine List.ext_getElem (by rw [h4, List.length_map, List.length_range]) fun j hj _ => ?_
    have hj' : j < S.shown := h4 ▸ hj
    have he := ho.ends j ⟨(h.rounds.map (·.2)).take c.vars.length,
      [((fresh.drop (hidingEntries (varsOf c S)))[j]'(hsl ▸ hj'),
        (if S.shown == 0 then none else (h.rounds.map (·.2)).getLast?).getD 0)],
      h.values[j]⟩ (by
        show (((fresh.drop (hidingWalk ((varsOf c S).zip (h.rounds.map (·.2)))).1.length).zip
          h.values).map _)[j]? = _
        rw [hwl, List.getElem?_map, List.getElem?_eq_getElem (by
          rw [List.length_zip, hsl, h4]
          exact lt_min hj' hj'), List.getElem_zip]
        rfl)
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ (hsl ▸ hj')]
    have he' : V j ((h.rounds.map (·.2)).take c.vars.length) + W.form
        [((fresh.drop (hidingEntries (varsOf c S)))[j]'(hsl ▸ hj'),
          (if S.shown == 0 then none else (h.rounds.map (·.2)).getLast?).getD 0)] =
        h.values[j] := he
    rw [← he', World.form_cons, World.form_nil, add_zero]
  have hrow : W.form (fresh.zip (hidingWalk ((varsOf c S).zip (h.rounds.map (·.2)))).1 ++
        scaleForm (h.eps * (hidingWalk ((varsOf c S).zip (h.rounds.map (·.2)))).2) c.masks) +
      dot (((S.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).drop 1).map
          fun x => h.eps * x)
        ((List.range S.kept).map fun i => Kp i ((h.rounds.map (·.2)).take c.vars.length)) =
      claimAfter (varsOf c S) h.rounds (h.mu + h.eps * c.target) -
        h.eps * (S.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).headD 0 := ho.row
  rw [World.form_append, World.form_zip, World.form_scale, dot_map_mul,
    hidingWalk_fst _ _ _ hlen, hidingWalk_snd _ _ hlen] at hrow
  have hT := hS.last (h.rounds.map (·.2)) hlen.symm
  unfold summandAt at hT
  simp only [] at hT
  rw [← hv] at hT
  unfold whole
  rw [hT]
  linear_combination -hrow

end OnBytes.Slice.PscF
