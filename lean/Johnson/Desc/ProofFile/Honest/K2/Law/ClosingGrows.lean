-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingGrows.lean: the kind "the code switch" (K2): THE CLOSING
(`closingFrom`, Honest/K2/Closing.lean) AT MORE STRETCHES AND MORE CHALLENGES: where it returns at
the carried stretches k, it returns THE SAME at every k' that gives each stretch that k gives, and
at every list of challenges that reads alike at the segments' own numbers. Two definitions, of
relations; statements with their proofs.

  `OkLe`   x y: whatever x returns, y returns: ONE-SIDED: where x refuses nothing is said
  `OkLe.refl`, `.bind`, `.map`, `.ite`, `.guard`, `.mapM_same`   it passes through the steps of a
           text with refusals
  `GivesAll`   k k': k' gives each stretch that k gives: `OkLe` at each number
  `rowsCore_le`, `segmentRows_le`, `segmentLeft_le`, `closingFrom_le`   step by step
  `closingFrom_append`   the closing over two lists of segments, one behind the other, is the
           closing over the first, then over the second from where the first ended

WHY ONE-SIDED. A later switch carries more stretches than an earlier one: beyond its own list the
earlier one's reader refuses where the later one's returns. But where the earlier closing RETURNED,
each stretch that it asked had returned: so no bound on a number is asked here.

Kin: `Alike` (Honest/K2/Law/Alike.lean) is two-sided: both return, or both refuse alike;
`rowsCore_alike` (Honest/K2/Law/SegmentAlike.lean) has the walk that `rowsCore_le` repeats.
`closingFrom_alike` (Honest/K2/Law/ReturnsTop.lean) is its sister at the top. THE HALF ON THE
CHALLENGES IS HAD ALREADY, AS AN EQUATION, REFUSALS AND ALL: `segmentLeft_congr`,
`closingFrom_congr` (Honest/K10/Pay/XchCongr.lean), under the same premise and others: not called:
here the two halves are walked at once, so that this file imports no more than it must.

Limits. On texts with refusals: no sentence on what a stretch holds. That k' gives what k gives, and
that the challenges read alike, are premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows zeroG)

variable {α β : Type}

/-- Whatever x returns, y returns. -/
def OkLe (x y : Except String α) : Prop := ∀ a, x = .ok a → y = .ok a

theorem OkLe.refl (x : Except String α) : OkLe x x := fun _ h => h

theorem OkLe.bind {x y : Except String α} {f g : α → Except String β} (h : OkLe x y)
    (hf : ∀ a, OkLe (f a) (g a)) : OkLe (x.bind f) (y.bind g) := by
  intro b hb
  cases x with
  | error e => cases hb
  | ok a =>
    rw [h a rfl]
    exact hf a b hb

theorem OkLe.map {x y : Except String α} (f : α → β) (h : OkLe x y) :
    OkLe (x.map f) (y.map f) := by
  intro b hb
  cases x with
  | error e => cases hb
  | ok a =>
    rw [h a rfl]
    exact hb

theorem OkLe.ite {c : Prop} [Decidable c] {x₀ x y₀ y : Except String α} (h₀ : OkLe x₀ y₀)
    (h : OkLe x y) : OkLe (if c then x₀ else x) (if c then y₀ else y) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact h₀
  · rw [if_neg hc, if_neg hc]
    exact h

theorem OkLe.guard {c : Prop} [Decidable c] {e : String} {f g : PUnit → Except String α}
    (h : OkLe (f PUnit.unit) (g PUnit.unit)) :
    OkLe (if c then (throw e : Except String PUnit) >>= f else pure PUnit.unit >>= f)
      (if c then (throw e : Except String PUnit) >>= g else pure PUnit.unit >>= g) :=
  OkLe.ite (OkLe.refl _) h

theorem OkLe.mapM_same {f g : α → Except String β} (h : ∀ a, OkLe (f a) (g a)) :
    ∀ l : List α, OkLe (l.mapM f) (l.mapM g)
  | [] => by
    rw [List.mapM_nil, List.mapM_nil]
    exact OkLe.refl _
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons]
    exact OkLe.bind (h a) fun _ => OkLe.bind (OkLe.mapM_same h l) fun _ => OkLe.refl _

/-- k' gives each stretch that k gives. -/
def GivesAll (k k' : Nat → Except String Stretch) : Prop := ∀ i, OkLe (k i) (k' i)

theorem rowsCore_le (table : FreshTable) (S : SegmentPub) (ps : Bool)
    (prevKept : List OnBytes.OracleShape) (A : List Laid) (B : List Laid × Nat)
    {k k' : Nat → Except String Stretch} (hk : GivesAll k k') (base : Nat) (withFresh : Bool) :
    OkLe (rowsCore table S ps prevKept A B k base withFresh)
      (rowsCore table S ps prevKept A B k' base withFresh) := by
  unfold rowsCore
  dsimp only
  refine OkLe.guard ?_
  refine OkLe.guard ?_
  refine OkLe.guard ?_
  refine OkLe.guard ?_
  refine OkLe.guard ?_
  refine OkLe.bind (OkLe.mapM_same (fun x => OkLe.bind (hk _) fun _ => OkLe.refl _) _) fun _ => ?_
  refine OkLe.ite ?_ ?_
  · refine OkLe.bind (OkLe.map _ (OkLe.bind (hk _) fun _ => OkLe.refl _)) fun _ => ?_
    exact OkLe.bind (OkLe.mapM_same (fun x => OkLe.bind (hk _) fun _ => OkLe.refl _) _)
      fun _ => OkLe.refl _
  · refine OkLe.bind (OkLe.refl _) fun _ => ?_
    exact OkLe.bind (OkLe.mapM_same (fun x => OkLe.bind (hk _) fun _ => OkLe.refl _) _)
      fun _ => OkLe.refl _

theorem segmentRows_le (table : FreshTable) (S : SegmentPub) (prev : Option Left)
    (prevKept : List OnBytes.OracleShape) (own : Nat → Nat → Nat → Cb.Gl.E)
    {k k' : Nat → Except String Stretch} (hk : GivesAll k k') (base : Nat) (withFresh : Bool) :
    OkLe (segmentGroupRows table S prev prevKept own k base withFresh)
      (segmentGroupRows table S prev prevKept own k' base withFresh) := by
  rw [segmentRows_eq, segmentRows_eq]
  exact rowsCore_le table S _ prevKept _ _ hk base withFresh

theorem segmentLeft_le (table : FreshTable) (S : SegmentPub) (prev : Option Left)
    (prevKept : List OnBytes.OracleShape) (own : Nat → Nat → Nat → Cb.Gl.E)
    {heard heard' : List Fmt.Drawn}
    (hγ : challengesOr0 heard S.gamma = challengesOr0 heard' S.gamma)
    {k k' : Nat → Except String Stretch} (hk : GivesAll k k') (base : Nat) :
    OkLe (segmentLeft table S prev prevKept own heard k base)
      (segmentLeft table S prev prevKept own heard' k' base) := by
  unfold segmentLeft
  dsimp only
  rw [hγ]
  exact OkLe.bind (segmentRows_le table S prev prevKept own hk base true) fun _ => OkLe.refl _

/-- **THE CLOSING, STEP BY STEP.** -/
theorem closingFrom_le (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    {heard heard' : List Fmt.Drawn} {k k' : Nat → Except String Stretch} (hk : GivesAll k k') :
    ∀ (segs : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape)),
      (∀ S ∈ segs, challengesOr0 heard S.gamma = challengesOr0 heard' S.gamma) →
      OkLe (closingFrom table own heard k segs j base prev)
        (closingFrom table own heard' k' segs j base prev)
  | [], _, _, _, _ => OkLe.refl _
  | S :: rest, j, base, prev, hg => by
    unfold closingFrom
    exact OkLe.bind
      (segmentLeft_le table S _ _ (own j) (hg S (List.mem_cons_self ..)) hk base)
      fun W => closingFrom_le table own hk rest (j + 1) (base + S.messages) (some W)
        fun T hT => hg T (List.mem_cons_of_mem _ hT)

/-- **ONE LIST BEHIND ANOTHER.** -/
theorem closingFrom_append (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) (k : Nat → Except String Stretch) (B : List SegmentPub) :
    ∀ (A : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape)),
      closingFrom table own heard k (A ++ B) j base prev =
        (closingFrom table own heard k A j base prev).bind fun x =>
          closingFrom table own heard k B (j + A.length) x.2 x.1
  | [], _, _, _ => rfl
  | S :: rest, j, base, prev => by
    show (segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k
        base).bind (fun W =>
          closingFrom table own heard k (rest ++ B) (j + 1) (base + S.messages) (some W)) =
      ((segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k
        base).bind fun W =>
          closingFrom table own heard k rest (j + 1) (base + S.messages) (some W)).bind fun x =>
        closingFrom table own heard k B (j + (S :: rest).length) x.2 x.1
    cases segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k base with
    | error e => rfl
    | ok W =>
      show closingFrom table own heard k (rest ++ B) (j + 1) (base + S.messages) (some W) =
        (closingFrom table own heard k rest (j + 1) (base + S.messages) (some W)).bind fun x =>
          closingFrom table own heard k B (j + (S :: rest).length) x.2 x.1
      have e : j + 1 + rest.length = j + (S :: rest).length := by
        rw [List.length_cons]
        omega
      rw [closingFrom_append table own heard k B rest (j + 1) (base + S.messages) (some W), e]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.OkLe
#print axioms ProofFile.Honest.K2.Law.OkLe.refl
#print axioms ProofFile.Honest.K2.Law.OkLe.bind
#print axioms ProofFile.Honest.K2.Law.OkLe.map
#print axioms ProofFile.Honest.K2.Law.OkLe.ite
#print axioms ProofFile.Honest.K2.Law.OkLe.guard
#print axioms ProofFile.Honest.K2.Law.OkLe.mapM_same
#print axioms ProofFile.Honest.K2.Law.GivesAll
#print axioms ProofFile.Honest.K2.Law.rowsCore_le
#print axioms ProofFile.Honest.K2.Law.segmentRows_le
#print axioms ProofFile.Honest.K2.Law.segmentLeft_le
#print axioms ProofFile.Honest.K2.Law.closingFrom_le
#print axioms ProofFile.Honest.K2.Law.closingFrom_append
