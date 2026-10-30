-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/BatchFold.lean: THE GATHERING OF A LINK's CLAIMS (claimsInBy,
Johnson/Desc/Block.lean, with the test behind each run K9.eachAtS,
Johnson/Desc/First/Batch/EachAtS.lean) ON SHAPES, FROM THE RUNS' OWN LAWS (RunLaw,
Johnson/Desc/First/Batch/Shape/ClaimShape.lean). General laws; nothing is evaluated.

  **`eachS`**, **`each_iff`**: the test behind a run, on the claims' shapes and the state's shape: a
    run that is no owner of the smallness test's window names no slot of it; the first owner lays as
    many claims as the lookup on the digits has equations of its own. BOTH WAYS; no test on values.
  `RunsLaw bs order`: for each run that the order names: the run that the sub-protocols bs state
    under that pair, and its RunLaw.
  `stepG`, **`gatherG`**: THE GATHERING ON SHAPES: run by run in the order: the run on shapes at the
    number of claims so far; eachS behind it; the claims' shapes joined.
  `PreAll`: the runs' own premises, ALONG THE GATHERING: each run's pre at the state in front of it.
  `namesIn`, `namedBy_sh`, `gatherFrom`, `foldE`, `fold_error`, `fold_cons`, `gather_from`: tools.
  **`gather_follows`**: gatherG returns y at chainSh s, and PreAll holds from s: then the gathering
    returns some (cs, s') whose shapes are y.

Limits. IT IS WORTH WHAT THE RunLaws ARE WORTH: see ClaimShape.lean's limits: at a RunsLaw of idle
laws gather_follows holds emptily. PreAll is a premise at the states that the gathering itself
passes. One way: from the shapes to the gathering. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.ClaimShape
import Johnson.Desc.First.Batch.Shape.DoorCut
import Johnson.Desc.First.Batch.EachAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

/-! ## 1 The test behind a run -/

/-- A claim's shape names a slot of the stretch from a on, below b. -/
def namesIn (a b : Nat) (c : ClaimSh) : Bool :=
  c.form.slots.any fun j => decide (a ≤ j) && decide (j < b)

/-- **The test behind a run, on shapes.** Where the smallness test's structure is not there it
passes, as the library's own does. -/
def eachS (k : SegSort) (o : Nat × String) (cs : List ClaimSh) (a : ChainSh) : Bool :=
  match a.tl with
  | some t =>
    ((cutAt k 1).contains o || !cs.any (namesIn t.slotA t.slotB)) &&
      (if (cutAt k 1).head? == some o then cs.length == 31 + t.f9.v + t.f9.d + 1 else true)
  | none => true

theorem namedBy_sh (w : Window) (cl : Claim) :
    w.namedBy cl = namesIn w.first w.behind (claimSh cl) := by
  unfold Window.namedBy namesIn Window.holds
  show _ = (cl.form.slots.toList.map (·.1)).any _
  rw [List.any_map, ← Array.any_toList]
  rfl

theorem each_iff (k : SegSort) (o : Nat × String) (cls : List Claim) (s : S) :
    eachAtS k o cls s = .ok () ↔ eachS k o (cls.map claimSh) (chainSh s) = true := by
  unfold eachAtS eachRun k8Window dueAtS eachS windowsOk
  have e : (chainSh s).tl = s.tl?.map tailSh := rfl
  rw [e]
  cases s.tl? with
  | none =>
    have hn : (if ((cutAt k 1).head? == some o) = true then (none : Option (String × Nat))
        else none) = none := by
      split <;> rfl
    simp only [Option.map_none, Option.getD_none, hn]
    exact ⟨fun _ => by first | rfl | trivial, fun _ => rfl⟩
  | some tl =>
    simp only [Option.map_some, Option.getD_some]
    have ea : (cls.map claimSh).any (namesIn tl.slotA tl.slotB) =
        cls.any (Window.namedBy ⟨cutAt k 1, tl.slotA, tl.slotB⟩) := by
      rw [List.any_map]
      congr 1
      funext cl
      exact (namedBy_sh ⟨cutAt k 1, tl.slotA, tl.slotB⟩ cl).symm
    show ((need "K9.window" ((cutAt k 1).contains o ||
      !cls.any (Window.namedBy ⟨cutAt k 1, tl.slotA, tl.slotB⟩)) >>= fun _ => pure ()) >>=
      fun _ => _) = .ok () ↔
      (((cutAt k 1).contains o || !(cls.map claimSh).any (namesIn tl.slotA tl.slotB)) &&
        (if (cutAt k 1).head? == some o then
          (cls.map claimSh).length == 31 + tl.f9.v + tl.f9.d + 1 else true)) = true
    rw [ea, List.length_map, Bool.and_eq_true]
    simp only [ans_bind, need_ok, exists_const]
    by_cases ho : ((cutAt k 1).head? == some o) = true
    · simp only [ho, if_true, need_ok]
      exact ⟨fun ⟨_, ⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun h => ⟨(), ⟨h.1, rfl⟩, h.2⟩⟩
    · simp only [ho, Bool.false_eq_true, if_false]
      exact ⟨fun ⟨_, ⟨h1, _⟩, _⟩ => ⟨h1, trivial⟩, fun h => ⟨(), ⟨h.1, rfl⟩, rfl⟩⟩

/-! ## 2 The gathering on shapes -/

/-- **For each run that the order names: the run that the sub-protocols state, and its law.** -/
structure RunsLaw (bs : List (Block S Claim)) (order : List (Nat × String)) where
  run : Nat × String → Run
  law : ∀ o, RunLaw (run o)
  look : ∀ o ∈ order, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some (run o)

/-- One run on shapes, behind what is gathered so far. -/
def stepG (k : SegSort)
    (g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh))
    (x : List ClaimSh × ChainSh) (o : Nat × String) : Except String (List ClaimSh × ChainSh) :=
  (g o x.1.length x.2).bind fun y =>
    if eachS k o y.1 y.2 then .ok (x.1 ++ y.1, y.2)
    else .error (o.2 ++ ": behind the run: the shape")

/-- **THE GATHERING ON SHAPES**, from what is gathered so far. -/
def gatherFrom (k : SegSort)
    (g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)) :
    List (Nat × String) → List ClaimSh × ChainSh → Except String (List ClaimSh × ChainSh)
  | [], x => .ok x
  | o :: os, x => (stepG k g x o).bind (gatherFrom k g os)

/-- **THE GATHERING ON SHAPES.** -/
def gatherG (k : SegSort)
    (g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh))
    (order : List (Nat × String)) (a : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  gatherFrom k g order ([], a)

/-- The form of the library's gathering: a fold of steps that may refuse. -/
def foldE {α β : Type} (f : α → β → Except String α) (l : List β) (x : Except String α) :
    Except String α :=
  l.foldl (fun (acc : Except String α) o => acc.bind fun x => f x o) x

theorem fold_error {α β : Type} (f : α → β → Except String α) (e : String) : ∀ l : List β,
    foldE f l (.error e) = .error e
  | [] => rfl
  | _ :: l => fold_error f e l

theorem fold_cons {α β : Type} (f : α → β → Except String α) (x : α) (o : β) (l : List β) :
    foldE f (o :: l) (.ok x) = (f x o).bind fun y => foldE f l (.ok y) := by
  show foldE f l (f x o) = _
  cases f x o with
  | error e => exact fold_error f e l
  | ok y => rfl

/-- The runs' own premises, along the gathering. n: the number of claims gathered so far. -/
def PreAll {bs : List (Block S Claim)} {order : List (Nat × String)} (R : RunsLaw bs order) :
    List (Nat × String) → Nat → S → Prop
  | [], _, _ => True
  | o :: os, n, s =>
    (R.law o).pre n s ∧ ∀ cs s', R.run o n s = .ok (cs, s') → PreAll R os (n + cs.length) s'

theorem gather_from {bs : List (Block S Claim)} {order : List (Nat × String)} (k : SegSort)
    (R : RunsLaw bs order) :
    ∀ (os : List (Nat × String)), (∀ o ∈ os, o ∈ order) → ∀ (cs₀ : List Claim) (s : S)
      (y : List ClaimSh × ChainSh),
      gatherFrom k (fun o => (R.law o).runG) os (cs₀.map claimSh, chainSh s) = .ok y →
      PreAll R os cs₀.length s →
      ∃ cs s', foldE (claimsInStep (eachAtS k) bs) os (.ok (cs₀, s)) = .ok (cs, s') ∧
        y = (cs.map claimSh, chainSh s')
  | [], _, cs₀, s, y, h, _ => ⟨cs₀, s, rfl, (Except.ok.inj h).symm⟩
  | o :: os, hm, cs₀, s, y, h, hp => by
    have h' : (stepG k (fun o => (R.law o).runG) (cs₀.map claimSh, chainSh s) o).bind
      (gatherFrom k (fun o => (R.law o).runG) os) = .ok y := h
    cases hs : stepG k (fun o => (R.law o).runG) (cs₀.map claimSh, chainSh s) o with
    | error e => rw [hs] at h'; exact nomatch h'
    | ok x₁ =>
      rw [hs] at h'
      unfold stepG at hs
      dsimp only at hs
      rw [List.length_map] at hs
      cases hg : (R.law o).runG cs₀.length (chainSh s) with
      | error e => rw [hg] at hs; exact nomatch hs
      | ok z =>
        rw [hg] at hs
        have hs' : (if eachS k o z.1 z.2 then
          (.ok (cs₀.map claimSh ++ z.1, z.2) : Except String (List ClaimSh × ChainSh))
          else .error (o.2 ++ ": behind the run: the shape")) = .ok x₁ := hs
        by_cases he : eachS k o z.1 z.2 = true
        · rw [if_pos he] at hs'
          obtain rfl := Except.ok.inj hs'
          obtain ⟨cs₁, s₁, hr, rfl⟩ := (R.law o).follows cs₀.length s z hg hp.1
          have hstep : claimsInStep (eachAtS k) bs (cs₀, s) o = .ok (cs₀ ++ cs₁, s₁) := by
            unfold claimsInStep
            rw [R.look o (hm o (by simp))]
            have hn : named (o.2 ++ ": no such run") (some (R.run o)) = .ok (R.run o) := rfl
            rw [hn]
            dsimp only [Except.bind]
            rw [hr]
            dsimp only
            rw [(each_iff k o cs₁ s₁).2 he]
          have h'' : gatherFrom k (fun o => (R.law o).runG) os
              ((cs₀ ++ cs₁).map claimSh, chainSh s₁) = .ok y := by
            rw [List.map_append]
            exact h'
          obtain ⟨cs, s', hf, ey⟩ := gather_from k R os
            (fun o' ho' => hm o' (List.mem_cons_of_mem _ ho')) (cs₀ ++ cs₁) s₁ y h''
            (by rw [List.length_append]; exact hp.2 cs₁ s₁ hr)
          refine ⟨cs, s', ?_, ey⟩
          rw [fold_cons, hstep]
          exact hf
        · rw [if_neg he] at hs'
          exact nomatch hs'

/-- **WHERE THE GATHERING ON SHAPES RETURNS AND THE RUNS' PREMISES HOLD ALONG IT, THE GATHERING
RETURNS, WITH THESE SHAPES.** -/
theorem gather_follows {bs : List (Block S Claim)} {order : List (Nat × String)} (k : SegSort)
    (R : RunsLaw bs order) (s : S) (y : List ClaimSh × ChainSh)
    (h : gatherG k (fun o => (R.law o).runG) order (chainSh s) = .ok y)
    (hp : PreAll R order 0 s) :
    ∃ cs s', claimsInBy (eachAtS k) bs order s = .ok (cs, s') ∧
      y = (cs.map claimSh, chainSh s') :=
  gather_from k R order (fun _ h => h) [] s y h hp

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.gather_follows
#print axioms VerifiableInference.Desc.K9.Shape.each_iff
#print axioms VerifiableInference.Desc.K9.Shape.namesIn
#print axioms VerifiableInference.Desc.K9.Shape.eachS
#print axioms VerifiableInference.Desc.K9.Shape.namedBy_sh
#print axioms VerifiableInference.Desc.K9.Shape.RunsLaw
#print axioms VerifiableInference.Desc.K9.Shape.stepG
#print axioms VerifiableInference.Desc.K9.Shape.gatherFrom
#print axioms VerifiableInference.Desc.K9.Shape.gatherG
#print axioms VerifiableInference.Desc.K9.Shape.foldE
#print axioms VerifiableInference.Desc.K9.Shape.fold_error
#print axioms VerifiableInference.Desc.K9.Shape.fold_cons
#print axioms VerifiableInference.Desc.K9.Shape.PreAll
#print axioms VerifiableInference.Desc.K9.Shape.gather_from
