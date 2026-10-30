-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/ShapeOwnAgrees2.lean: the yardstick for ShapeOwn.lean, second part: THE
LOOKUP'S NUMBERS AND ITS PUBLIC TESTS ON THEM, IN THE DESCRIPTION'S OWN TEXT, ARE THE VERIFIER
PROGRAM'S, at every argument. Theorems alone. Without Mathlib.

Why. `shapeOwn` and `pubOk` are the description's own text for the numbers of a lookup and the
tests on them. Laws that were proved of the program's `Forest.shape` and `Forest.pubAsk`
(OnBytes/Model/Forest.lean) speak of a place that is made by the own text only through these
equations.

Main theorems:
  `callOk_eq`: the tests on one call: `callOk c = (Forest.callAsk c).toBool`.
  `pubOk_eq`: the tests on the numbers of padding keys:
    `pubOk h pub = (Forest.pubAsk h pub).toBool`.
  **`shapeOwn_eq`: `shapeOwn calls lid = (Forest.shape calls lid).toOption`**: the same shape, field
    for field, or none just where the program refuses.
  `shapeOwn_gives`, `pubOk_gives`: the one direction that a law spends: a shape of ours is the
    program's; a yes of ours is the program's.

Limits: a refusal's name is dropped: the program's answer is read as an option or as a Bool. Nothing
is said of what the numbers mean. No file of the description imports this one. The helpers are
private.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.ShapeOwnAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- A loop whose body only tests: it returns just if every member's test returns. -/
private theorem forIn_guard {α : Type} (f : α → Except String PUnit) : ∀ l : List α,
    (forIn l PUnit.unit (fun c _ =>
      (do f c
          pure (ForInStep.yield PUnit.unit) : Except String (ForInStep PUnit)))).toBool
      = l.all fun c => (f c).toBool
  | [] => rfl
  | c :: l => by
    rw [List.forIn_cons]
    cases hf : f c with
    | error e =>
      simp only [List.all_cons, hf]
      rfl
    | ok u =>
      simp only [List.all_cons, hf]
      exact forIn_guard f l

private theorem all_le_eq (k : Nat) : ∀ l : List Nat,
    (l.all fun x => decide (x ≤ k)) = !(l.any fun x => decide (x > k))
  | [] => rfl
  | x :: l => by
    rw [List.all_cons, List.any_cons, all_le_eq k l, Bool.not_or]
    congr 1
    by_cases hx : x ≤ k
    · have : ¬ (x > k) := Nat.not_lt.2 hx
      simp [hx, this]
    · have : x > k := Nat.lt_of_not_le hx
      simp [hx, this]

/-- A loop that only refuses: it returns just if no member is bad. -/
private theorem guardLoop {α : Type} (bad : α → Prop) [DecidablePred bad] (e : String) :
    ∀ l : List α,
    (forIn l PUnit.unit (fun c _ =>
      if bad c then
        (do throw e
            pure (ForInStep.yield PUnit.unit) : Except String (ForInStep PUnit))
      else
        (do pure PUnit.unit
            pure (ForInStep.yield PUnit.unit)))).toBool
      = l.all fun c => !decide (bad c)
  | [] => rfl
  | c :: l => by
    rw [List.forIn_cons, List.all_cons]
    by_cases hb : bad c
    · rw [if_pos hb, decide_eq_true hb]
      rfl
    · rw [if_neg hb, decide_eq_false hb]
      exact guardLoop bad e l

private theorem two_pures (x : Except String PUnit) :
    (do pure PUnit.unit
        pure PUnit.unit
        x
        pure PUnit.unit : Except String PUnit).toBool = x.toBool := by
  cases x <;> rfl

private theorem lt_eq_not_ge (a b : Nat) : decide (a < b) = !decide (a ≥ b) := by
  by_cases h : a < b
  · have h' : ¬ a ≥ b := Nat.not_le.2 h
    rw [decide_eq_true h, decide_eq_false h']
    rfl
  · have h' : a ≥ b := Nat.le_of_not_lt h
    rw [decide_eq_false h, decide_eq_true h']
    rfl

private theorem and_beq_eq (a b c d : Nat) : (a == b && c == d) = !(a != b || c != d) := by
  show (a == b && c == d) = !(!(a == b) || !(c == d))
  cases (a == b) <;> cases (c == d) <;> rfl

private theorem arr_all_le (k : Nat) (a : Array Nat) :
    (a.all fun x => decide (x ≤ k)) = !(a.any fun x => decide (x > k)) := by
  first
    | (rw [← Array.all_toList, ← Array.any_toList]; exact all_le_eq k a.toList)
    | (cases a with | mk l => simp only [List.all_toArray, List.any_toArray]; exact all_le_eq k l)
    | (cases a with | mk l => simp [all_le_eq])

/-- **The tests on the numbers of padding keys are the verifier program's.** -/
theorem pubOk_eq (h : Forest.Shape) (pub : Array Nat) :
    pubOk h pub = (Forest.pubAsk h pub).toBool := by
  unfold pubOk Forest.pubAsk
  rw [and_beq_eq, arr_all_le]
  cases h1 : (pub.size != h.NT || h.calls.size != h.NC)
  · cases h2 : (pub.any fun x => decide (x > 2 ^ h.dT))
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, lt_eq_not_ge]
      rw [two_pures]
      exact (guardLoop _ _ _).symm
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true, Bool.true_and,
        Bool.false_and]
      rfl
  · simp only [↓reduceIte, Bool.not_true, Bool.false_and]
    rfl


/-! ## The numbers of a group of calls -/

private theorem dle (a b : Nat) : decide (a ≤ b) = !decide (b < a) := by
  by_cases h : a ≤ b
  · have h' : ¬ b < a := Nat.not_lt.2 h
    rw [decide_eq_true h, decide_eq_false h']
    rfl
  · have h' : b < a := Nat.lt_of_not_le h
    rw [decide_eq_false h, decide_eq_true h']
    rfl

private theorem dle' (a b : Nat) : decide (a ≤ b) = !decide (a > b) := dle a b

private theorem list_all_not_any {α : Type} (p : α → Bool) : ∀ l : List α,
    l.all p = !(l.any fun x => !p x)
  | [] => rfl
  | x :: l => by
    rw [List.all_cons, List.any_cons, list_all_not_any p l, Bool.not_or, Bool.not_not]

private theorem arr_all_not_any {α : Type} (p : α → Bool) (a : Array α) :
    a.all p = !(a.any fun x => !p x) := by
  first
    | (rw [← Array.all_toList, ← Array.any_toList]; exact list_all_not_any p a.toList)
    | (cases a with
       | mk l => simp only [List.all_toArray, List.any_toArray]; exact list_all_not_any p l)

private theorem arr_forIn_guard {α : Type} (f : α → Except String PUnit) (a : Array α) :
    (forIn a PUnit.unit (fun c _ =>
      (do f c
          pure (ForInStep.yield PUnit.unit) : Except String (ForInStep PUnit)))).toBool
      = a.all fun c => (f c).toBool := by
  first
    | (rw [← Array.forIn_toList, ← Array.all_toList]; exact forIn_guard f a.toList)
    | (cases a with
       | mk l => simp only [List.forIn_toArray, List.all_toArray]; exact forIn_guard f l)

private theorem beq_eq_not_bne (a b : Nat) : (a == b) = !(a != b) := by
  show (a == b) = !(!(a == b))
  rw [Bool.not_not]

/-- **The tests on one call are the verifier program's.** -/
theorem callOk_eq (c : Call) : callOk c = (Forest.callAsk c).toBool := by
  unfold callOk Forest.callAsk
  rw [dle 5 c.k, dle' c.k 16, dle' c.fn 2, lt_eq_not_ge c.t0 (2 ^ c.k), dle 10 c.n, dle' c.n 62]
  cases c.tau with
  | none =>
    have e : (((none : Option (Array UInt64)).getD #[]).any fun x => !okF x) = false := by
      first | rfl | simp | decide
    rw [e]
    generalize decide (c.k < 5) = b1
    generalize decide (c.k > 16) = b2
    generalize decide (c.fn > 2) = b3
    generalize decide (c.t0 ≥ 2 ^ c.k) = b4
    generalize decide (c.n > 62) = b5
    rw [beq_eq_not_bne c.kappa 5]
    generalize (c.kappa != 5) = b8
    generalize c.heavy.isEmpty = b9
    by_cases h10 : c.n < 10
    · rw [decide_eq_true h10]
      simp only [if_pos h10]
      cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b8 <;> cases b9 <;> rfl
    · rw [decide_eq_false h10]
      simp only [if_neg h10]
      cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b8 <;> cases b9 <;> rfl
  | some t =>
    have e : (Option.all
        (fun t : Array UInt64 => t.size == 2 ^ c.k && t.all fun x => decide (x < pW))
        (some t)) = (t.size == 2 ^ c.k && !(t.any fun x => !okF x)) := by
      show (t.size == 2 ^ c.k && t.all fun x => decide (x < pW)) = _
      rw [arr_all_not_any (fun x => decide (x < pW)) t]
      rfl
    have e' : ((some t).getD #[]) = t := rfl
    have e'' : Option.any (fun t : Array UInt64 => t.size != 2 ^ c.k) (some t)
        = !(t.size == 2 ^ c.k) := rfl
    rw [e, e', e'']
    generalize decide (c.k < 5) = b1
    generalize decide (c.k > 16) = b2
    generalize decide (c.fn > 2) = b3
    generalize decide (c.t0 ≥ 2 ^ c.k) = b4
    generalize decide (c.n > 62) = b5
    generalize (t.size == 2 ^ c.k) = b6
    generalize (t.any fun x => !okF x) = b7
    rw [beq_eq_not_bne c.kappa 5]
    generalize (c.kappa != 5) = b8
    generalize c.heavy.isEmpty = b9
    by_cases h10 : c.n < 10
    · rw [decide_eq_true h10]
      simp only [if_pos h10]
      cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;>
        cases b8 <;> cases b9 <;> rfl
    · rw [decide_eq_false h10]
      simp only [if_neg h10]
      cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;>
        cases b8 <;> cases b9 <;> rfl

private theorem toOption_guard {β : Type} (x : Except String PUnit) (k : Except String β) :
    (x >>= fun _ => k).toOption = if x.toBool = true then k.toOption else none := by
  cases x <;> rfl

/-- The step of `places`, by name. -/
private def stepOwn (iota : Array Nat) (st : Option (Array Nat × Array Nat × Nat)) (c : Nat) :
    Option (Array Nat × Array Nat × Nat) :=
  st.bind fun x =>
    let trees := 2 ^ iota.getD c 0
    if x.2.2 % trees != 0 then none
    else some (x.1.setIfInBounds c x.2.2,
      (List.range trees).foldl (fun a b => a.setIfInBounds (x.2.2 + b) c) x.2.1,
      x.2.2 + trees)

private theorem foldl_stepOwn_none (iota : Array Nat) : ∀ l : List Nat,
    l.foldl (stepOwn iota) none = none
  | [] => rfl
  | _ :: l => by
    rw [List.foldl_cons]
    exact foldl_stepOwn_none iota l

/-- The program's loop over the calls in falling order, at any body that does what the program's
does, is `places`' fold. -/
private theorem placesLoop (iota : Array Nat)
    (B : Nat → MProd (Array Nat) (MProd (Array Nat) Nat) →
      Except String (ForInStep (MProd (Array Nat) (MProd (Array Nat) Nat))))
    (hB : ∀ c co fi fr, B c ⟨co, fi, fr⟩ =
      if (fr % 2 ^ iota.getD c 0 != 0) = true then Except.error "internal-forest-place"
      else Except.ok (ForInStep.yield
        ⟨(List.range (2 ^ iota.getD c 0)).foldl (fun a b => a.setIfInBounds (fr + b) c) co,
          fi.setIfInBounds c fr, fr + 2 ^ iota.getD c 0⟩)) :
    ∀ (l : List Nat) (co fi : Array Nat) (fr : Nat),
      (forIn l (⟨co, fi, fr⟩ : MProd (Array Nat) (MProd (Array Nat) Nat)) B).toOption =
        (l.foldl (stepOwn iota) (some (fi, co, fr))).map
          fun x => (⟨x.2.1, x.1, x.2.2⟩ : MProd (Array Nat) (MProd (Array Nat) Nat))
  | [], _, _, _ => rfl
  | c :: l, co, fi, fr => by
    rw [List.forIn_cons, hB, List.foldl_cons]
    by_cases h : (fr % 2 ^ iota.getD c 0 != 0) = true
    · have e : stepOwn iota (some (fi, co, fr)) c = none := by
        show (if (fr % 2 ^ iota.getD c 0 != 0) = true then none else _) = none
        rw [if_pos h]
      rw [if_pos h, e, foldl_stepOwn_none]
      rfl
    · have e : stepOwn iota (some (fi, co, fr)) c = some (fi.setIfInBounds c fr,
          (List.range (2 ^ iota.getD c 0)).foldl (fun a b => a.setIfInBounds (fr + b) c) co,
          fr + 2 ^ iota.getD c 0) := by
        show (if (fr % 2 ^ iota.getD c 0 != 0) = true then none else _) = _
        rw [if_neg h]
      rw [if_neg h, e]
      exact placesLoop iota B hB l _ _ _

private theorem toOption_bind {α β : Type} (x : Except String α) (f : α → Except String β) :
    (x >>= f).toOption = x.toOption.bind fun a => (f a).toOption := by
  cases x <;> rfl

/-- A loop that never refuses is a fold. -/
private theorem forIn_fold' {α β : Type} (g : β → α → β) : ∀ (l : List α) (b : β),
    (forIn l b (fun x r => (pure (ForInStep.yield (g r x)) : Except String (ForInStep β))))
      = pure (l.foldl g b)
  | [], _ => rfl
  | x :: l, b => by
    rw [List.forIn_cons]
    exact forIn_fold' g l (g b x)

/-- **The numbers of a group of calls are the verifier program's**, at every list of calls and every
cap: the same shape, or none where the program refuses. -/
theorem shapeOwn_eq (calls : Array Call) (lid : Nat) :
    shapeOwn calls lid = (Forest.shape calls lid).toOption := by
  unfold shapeOwn Forest.shape
  rw [toOption_guard, arr_forIn_guard Forest.callAsk calls]
  have hall : (calls.all fun c => (Forest.callAsk c).toBool) = calls.all callOk := by
    congr 1
    funext c
    exact (callOk_eq c).symm
  rw [hall]
  cases calls.all callOk
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize calls.foldl (fun m c => min m c.n) lid = dT
    generalize calls.foldl (fun m c => max m c.k) 0 = kT
    generalize calls.map (fun c => c.n - dT) = iota
    generalize iota.foldl (fun s i => s + 2 ^ i) 0 = NT
    generalize calls.size = NC
    by_cases c1 : (decide (NC < 1) || decide (NC > 16)) = true
    · have e : (decide (1 ≤ NC) && decide (NC ≤ 16)) = false := by
        rw [dle 1 NC, dle' NC 16, ← Bool.not_or, c1]
        rfl
      rw [if_pos c1, e]
      rfl
    · have e : (decide (1 ≤ NC) && decide (NC ≤ 16)) = true := by
        rw [dle 1 NC, dle' NC 16, ← Bool.not_or, Bool.eq_false_iff.2 c1]
        rfl
      rw [if_neg c1, e]
      by_cases c2 : dT < 10
      · rw [if_pos c2, dle 10 dT, decide_eq_true c2]
        rfl
      · rw [if_neg c2, dle 10 dT, decide_eq_false c2]
        by_cases c3 : NT > 256
        · rw [if_pos c3, dle' NT 256, decide_eq_true c3]
          rfl
        · rw [if_neg c3, dle' NT 256, decide_eq_false c3]
          by_cases c4 : dT + clog2 NT ≥ 32
          · have e4 : decide (dT + bitsFor NT < 32) = false := decide_eq_false (Nat.not_lt.2 c4)
            rw [if_pos c4, e4]
            rfl
          · have e4 : decide (dT + bitsFor NT < 32) = true := decide_eq_true (Nat.lt_of_not_le c4)
            rw [if_neg c4, e4]
            by_cases c5 : 2 ^ (kT + clog2 NC + 32) ≥ pW.toNat
            · have e5 : decide (2 ^ (kT + bitsFor NC + 32) < pW.toNat) = false :=
                decide_eq_false (Nat.not_lt.2 c5)
              rw [if_pos c5, e5]
              rfl
            · have e5 : decide (2 ^ (kT + bitsFor NC + 32) < pW.toNat) = true :=
                decide_eq_true (Nat.lt_of_not_le c5)
              rw [if_neg c5, e5]
              simp only [Bool.not_false, Bool.and_self, ↓reduceIte, pure_bind]
              rw [toOption_bind, placesLoop iota]
              · have hp : places NC NT iota =
                    ((byFallingKey NC fun c => iota.getD c 0).foldl (stepOwn iota)
                      (some (Array.replicate NC 0, Array.replicate NT 0, 0))).bind
                        fun x => if x.2.2 != NT then none else some (x.1, x.2.1) := rfl
                rw [hp]
                generalize List.foldl (stepOwn iota)
                  (some (Array.replicate NC 0, Array.replicate NT 0, 0))
                  (byFallingKey NC fun c => iota.getD c 0) = o
                cases o with
                | none => rfl
                | some x =>
                  obtain ⟨fi, co, fr⟩ := x
                  show Option.map _ (if (fr != NT) = true then none else some (fi, co)) =
                    Except.toOption (if (fr != NT) = true then _ else _)
                  by_cases h : (fr != NT) = true
                  · rw [if_pos h, if_pos h]
                    rfl
                  · rw [if_neg h, if_neg h]
                    rfl
              · intro c co fi fr
                dsimp only
                by_cases h : (fr % 2 ^ iota.getD c 0 != 0) = true
                · rw [if_pos h, if_pos h]
                  rfl
                · rw [if_neg h, if_neg h, forIn_fold']
                  rfl

/-- A shape of ours is the program's. -/
theorem shapeOwn_gives {calls : Array Call} {lid : Nat} {h0 : Forest.Shape}
    (h : shapeOwn calls lid = some h0) : Forest.shape calls lid = .ok h0 := by
  rw [shapeOwn_eq] at h
  cases hx : Forest.shape calls lid with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; cases h; rfl

/-- A yes of ours is the program's. -/
theorem pubOk_gives {h : Forest.Shape} {pub : Array Nat} (e : pubOk h pub = true) :
    Forest.pubAsk h pub = .ok () := by
  rw [pubOk_eq] at e
  cases hx : Forest.pubAsk h pub with
  | error m => rw [hx] at e; cases e
  | ok u => rfl

end VerifiableInference.Desc.First.Look
