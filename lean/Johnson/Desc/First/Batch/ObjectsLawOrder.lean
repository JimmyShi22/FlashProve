-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/ObjectsLawOrder.lean: THE SEAT's LISTS OF RUNS AND THE FRAME's `claimsIn`
ARE ONE CALL. No Mathlib.
Block.lean's `claimsIn bs order` calls, for each entry (n, name) of a link's order, the run "name"
that block number n STATES (Block.claims). A step of adding (Johnson/Desc/First/Batch/Objects.lean)
calls `gather` over
`runsBy states cut`. Here:
  `statesOf bs`: what block number b of a list of blocks states.
  `claimsIn_eq`: where runsBy (statesOf bs) order answers with a list, claimsIn bs order is gather
      over that list, without a window: the same claims, the same state, the same refusal to the
      letter.
  `steps_are_claimsIn`: FOR RUNS BLIND TO THE ADDING: two steps of adding in a row, over two
      stretches of an order, end in v JUST IF claimsIn over the whole order returns and its claims,
      added behind it, give v. (Without windows. By induction the like for three.)
Limits: it is not said that the blocks of a chain state their runs; nor that a real run is Blind;
nor what a step asks in front (its counts) and reads behind its adding. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.ObjectsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9

variable {T : Type}

/-- What block number b states. -/
def statesOf (bs : List (Block T Claim)) (b : Nat) : List (RunOf T) :=
  ((bs[b]?).map (·.claims)).getD []

/-- No window. -/
def noWs : T → List Window := fun _ => []

theorem lookup_of_find (name : String) : ∀ (l : List (RunOf T)) (r : RunOf T),
    l.find? (fun r => r.1 == name) = some r → l.lookup name = some r.2 ∧ r.1 = name := by
  intro l
  induction l with
  | nil => intro r h; simp at h
  | cons x xs ih =>
    intro r h
    obtain ⟨k, f⟩ := x
    rw [List.find?_cons] at h
    cases hx : (k == name) with
    | true =>
      simp only [hx] at h
      injection h with h'
      have hk : k = name := by simpa using hx
      subst h'
      subst hk
      simp [List.lookup_cons]
    | false =>
      simp only [hx] at h
      have hk : k ≠ name := by simpa using hx
      have hk' : (name == k) = false := by
        simp
        exact fun e => hk e.symm
      have := ih r h
      simp [List.lookup_cons, hk', this.1, this.2]

theorem lookup_none_of_find (name : String) : ∀ (l : List (RunOf T)),
    l.find? (fun r => r.1 == name) = none → l.lookup name = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    obtain ⟨k, f⟩ := x
    rw [List.find?_cons] at h
    cases hx : (k == name) with
    | true => simp [hx] at h
    | false =>
      simp only [hx] at h
      have hk : k ≠ name := by simpa using hx
      have hk' : (name == k) = false := by
        simp
        exact fun e => hk e.symm
      simp [List.lookup_cons, hk', ih h]

/-- What claimsIn looks up is what statesOf's list holds. -/
theorem lookup_statesOf (bs : List (Block T Claim)) (o : Nat × String) :
    ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = (statesOf bs o.1).lookup o.2 := by
  unfold statesOf
  cases bs[o.1]? with
  | none => rfl
  | some b => rfl

/-- claimsIn's step. -/
def stepC (bs : List (Block T Claim)) (acc : Except String (List Claim × T)) (o : Nat × String) :
    Except String (List Claim × T) :=
  acc.bind fun x =>
    (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.claims.lookup o.2)).bind fun run =>
      match run x.1.length x.2 with
      | .ok y => .ok (x.1 ++ y.1, y.2)
      | .error e => .error (o.2 ++ ": " ++ e)

theorem claimsIn_fold (bs : List (Block T Claim)) (order : List (Nat × String)) (t : T) :
    claimsIn bs order t = order.foldl (stepC bs) (.ok ([], t)) := by
  unfold claimsIn claimsInBy
  apply congrArg (fun f => List.foldl f (Except.ok (([], t) : List Claim × T)) order)
  funext acc o
  unfold stepC claimsInStep
  cases acc with
  | error e => rfl
  | ok x =>
    simp only [Except.bind]
    cases named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.claims.lookup o.2) with
    | error e => rfl
    | ok run =>
      dsimp only
      cases run x.1.length x.2 <;> rfl

theorem stepC_error (bs : List (Block T Claim)) (e : String) : ∀ (order : List (Nat × String)),
    order.foldl (stepC bs) (.error e) = .error e := by
  intro order
  induction order with
  | nil => rfl
  | cons o l ih => exact ih

/-- A run guarded by no window is the run, with its name in front of a refusal. -/
theorem guarded_noWs (cut : List (Nat × String)) (r : RunOf T) (n : Nat) (t : T) :
    guarded noWs cut r n t =
      match r.2 n t with
      | .ok y => .ok y
      | .error e => .error (r.1 ++ ": " ++ e) := by
  unfold guarded noWs windowsOk
  cases r.2 n t with
  | error e => rfl
  | ok y => rfl

theorem claimsIn_from (bs : List (Block T Claim)) (cut : List (Nat × String)) :
    ∀ (order : List (Nat × String)) (runs : List (RunOf T)),
      runsBy (statesOf bs) order = some runs → ∀ (acc : List Claim) (t : T),
        order.foldl (stepC bs) (.ok (acc, t)) =
          match gatherFrom (runs.map (guarded noWs cut)) acc.length t with
          | .ok z => .ok (acc ++ z.1, z.2)
          | .error e => .error e := by
  intro order
  induction order with
  | nil =>
    intro runs h acc t
    simp [runsBy, pure] at h
    subst h
    simp [gatherFrom]
  | cons o l ih =>
    intro runs h acc t
    unfold runsBy at h
    rw [List.mapM_cons] at h
    cases hf : (statesOf bs o.1).find? (fun r => r.1 == o.2) with
    | none => simp [hf] at h
    | some r =>
      cases hl : l.mapM (fun o => (statesOf bs o.1).find? fun r => r.1 == o.2) with
      | none => simp [hf, hl] at h
      | some rs =>
        simp [hf, hl, pure] at h
        subst h
        obtain ⟨h1, h2⟩ := lookup_of_find o.2 _ r hf
        simp only [List.foldl_cons, List.map_cons, gatherFrom]
        have hstep : stepC bs (.ok (acc, t)) o =
            match guarded noWs cut r acc.length t with
            | .ok y => .ok (acc ++ y.1, y.2)
            | .error e => .error e := by
          unfold stepC
          rw [lookup_statesOf, h1, guarded_noWs, h2]
          simp only [Except.bind, named]
          cases r.2 acc.length t with
          | error e => rfl
          | ok y => rfl
        rw [hstep]
        cases guarded noWs cut r acc.length t with
        | error e => exact stepC_error bs e l
        | ok y =>
          dsimp only
          rw [ih rs hl (acc ++ y.1) y.2, List.length_append]
          cases gatherFrom (rs.map (guarded noWs cut)) (acc.length + y.1.length) y.2 with
          | error e => rfl
          | ok z => simp [List.append_assoc]

/-- **claimsIn is gather over the runs that the blocks state, in the order's order.** -/
theorem claimsIn_eq (bs : List (Block T Claim)) (order : List (Nat × String))
    (runs : List (RunOf T)) (h : runsBy (statesOf bs) order = some runs) (t : T) :
    claimsIn bs order t = gather noWs order runs t := by
  rw [claimsIn_fold, claimsIn_from bs order order runs h [] t, gather_eq]
  simp only [List.length_nil]
  cases gatherFrom (runs.map (guarded noWs order)) 0 t with
  | error e => rfl
  | ok z => simp

/-- runsBy over two stretches in a row. -/
theorem runsBy_append (states : Nat → List (RunOf T)) (a b : List (Nat × String))
    (ra rb : List (RunOf T)) (ha : runsBy states a = some ra) (hb : runsBy states b = some rb) :
    runsBy states (a ++ b) = some (ra ++ rb) := by
  unfold runsBy at *
  rw [List.mapM_append, ha, hb]
  rfl

/-- **Two steps of adding in a row = the frame's call over the whole order, its claims added behind
it.** -/
theorem steps_are_claimsIn (A : Adds T) (bs : List (Block T Claim)) (a b : List (Nat × String))
    (ra rb : List (RunOf T)) (ha : runsBy (statesOf bs) a = some ra)
    (hb : runsBy (statesOf bs) b = some rb)
    (hBa : ∀ r ∈ ra, Blind A r.2) (hBb : ∀ r ∈ rb, Blind A r.2)
    (t t₀ : T) (h0 : A.add t [] = some t₀) (v : T) :
    (∃ u, madeThenAdded A (ra.map (guarded noWs (a ++ b))) t = .ok u ∧
        madeThenAdded A (rb.map (guarded noWs (a ++ b))) u = .ok v) ↔
      ∃ z, claimsIn bs (a ++ b) t = .ok z ∧ A.add z.2 z.1 = some v := by
  have hw : ∀ (x x' : T) (cs : List Claim), A.add x cs = some x' → noWs x' = noWs x :=
    fun _ _ _ _ => rfl
  have hGa : ∀ f ∈ ra.map (guarded noWs (a ++ b)), Blind A f := by
    intro f hf
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
    exact guarded_blind A noWs (a ++ b) r (hBa r hr) hw
  have hGb : ∀ f ∈ rb.map (guarded noWs (a ++ b)), Blind A f := by
    intro f hf
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
    exact guarded_blind A noWs (a ++ b) r (hBb r hr) hw
  rw [steps_iff A _ _ hGa hGb t t₀ h0 v, ← List.map_append,
    claimsIn_eq bs (a ++ b) (ra ++ rb) (runsBy_append _ a b ra rb ha hb) t, gather_eq]
  unfold madeThenAdded
  cases gatherFrom ((ra ++ rb).map (guarded noWs (a ++ b))) 0 t with
  | error e => simp
  | ok z =>
    cases hz : A.add z.2 z.1 with
    | none => simp [hz]
    | some u => simp [hz]

end VerifiableInference.Desc.K9
