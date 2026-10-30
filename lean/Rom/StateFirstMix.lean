-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstMix.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): programs that mix typed and raw queries, and their interpretations.
Definitions, the facts that hold by unfolding, and the statement of the step's main lemma
(`Spec.mixClose`; proved in Rom/StateFirstClose.lean).

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The step leads from a family S of typed oracles, the first family, to the second, `stSpec S lam C`.
There a chain oracle returns only a state: the chaining value and the last block, hid, of its old
answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). The scheme's algorithms are required not to read hid (`HidFree`). The other oracles are
unchanged (`plain`).

A mixed program (over `mixSpec`) makes typed queries (the honest side's, to the first family) and
raw queries (an adversary's, to the second); `liftT` and `liftR` turn a program over the first
(second) family into a mixed one. The experiments of completeness, of index binding and the real
experiment of index privacy on `stateFirstArg C A` are real interpretations (`real`) of mixed
programs; the ideal interpretations (`ideal`) are programs over the first family, in which a
reduction answers the raw expansion queries from a table (`Book`).
-/
import Rom.StateFirst
import Rom.EagerLazy
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open ZKCP

/-- two families side by side -/
def OSpec.sum (S₁ S₂ : OSpec) : OSpec where
  ι := S₁.ι ⊕ S₂.ι
  Dom := fun x => match x with
    | .inl o => S₁.Dom o
    | .inr o => S₂.Dom o
  Rng := fun x => match x with
    | .inl o => S₁.Rng o
    | .inr o => S₂.Rng o
  finRng := fun x => match x with
    | .inl o => S₁.finRng o
    | .inr o => S₂.finRng o
  neRng := fun x => match x with
    | .inl o => S₁.neRng o
    | .inr o => S₂.neRng o

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o)) {α β : Type}

/-- typed and raw queries -/
abbrev mixSpec : OSpec := OSpec.sum S (stSpec S lam C)

def liftT : OComp S α → OComp (mixSpec C) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => liftT (k r)
  | .query o q k => .query (S := mixSpec C) (.inl o) q fun r => liftT (k r)

def liftR : OComp (stSpec S lam C) α → OComp (mixSpec C) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => liftR (k r)
  | .query x q k => .query (S := mixSpec C) (.inr x) q fun r => liftR (k r)

/-- The real interpretation: typed queries are expanded (state, then expansion queries); raw queries
stay. real (liftT c) = c.stateFirst C; real (liftR c) = c. -/
def real : OComp (mixSpec C) α → OComp (stSpec S lam C) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => real (k r)
  | .query (.inl o) q k => .query (S := stSpec S lam C) (.inl o) q fun a => (expand C (C o) a).bind fun r => real (k r)
  | .query (.inr x) q k => .query (S := stSpec S lam C) x q fun r => real (k r)

/-- The real interpretation in which a raw query for a state is also followed by the expansion
queries, whose answers are discarded. -/
def real' : OComp (mixSpec C) α → OComp (stSpec S lam C) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => real' (k r)
  | .query (.inl o) q k =>
    .query (S := stSpec S lam C) (.inl o) q fun a => (expand C (C o) a).bind fun r => real' (k r)
  | .query (.inr (.inl o)) q k =>
    .query (S := stSpec S lam C) (.inl o) q fun a => (expand C (C o) a).bind fun _ => real' (k a)
  | .query (.inr (.inr u)) q k => .query (S := stSpec S lam C) (.inr u) q fun r => real' (k r)

theorem real_liftT (c : OComp S α) : real C (liftT C c) = c.stateFirst C := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [liftT, real, OComp.stateFirst, ih]
  | query o q k ih => simp only [liftT, real, OComp.stateFirst, ih]

theorem real_liftR (c : OComp (stSpec S lam C) α) : real C (liftR C c) = c := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [liftR, real, ih]
  | query x q k ih => simp only [liftR, real, ih]

/-- an algorithm whose result is thrown away does not show, the family being fixed (exactly: running
it first does not change the output distribution) -/
theorem runEager_bind_const (f : Fam (stSpec S lam C))
    (c : OComp (stSpec S lam C) β) (d : OComp (stSpec S lam C) α) :
    (c.bind fun _ => d).runEager f = d.runEager f := by
  rw [OComp.runEager_bind]
  exact PMF.bind_const _ _

/-- For every fixed family the two real interpretations have the same output distribution. -/
theorem runEager_real' (f : Fam (stSpec S lam C)) (c : OComp (mixSpec C) α) :
    (real' C c).runEager f = (real C c).runEager f := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [real, real', OComp.runEager, ih]
  | query x q k ih =>
    match x, q, k, ih with
    | .inl o, q, k, ih => simp only [real, real', OComp.runEager, OComp.runEager_bind, ih]
    | .inr (.inl o), q, k, ih =>
      simp only [real, real', OComp.runEager]
      rw [runEager_bind_const, ih]
    | .inr (.inr u), q, k, ih => simp only [real, real', OComp.runEager, ih]

/-! ## The reduction's table -/

namespace Link
variable {R : Type}
/-- what the second family answers where the first answers r -/
def toAns : (c : Link lam R) → R → c.Ans
  | .plain, r => r
  | .chain _ e, r => (e r).2
end Link

/-- the reduction's table: the chain answers seen, oldest first, and the answers that it has itself
given for dr at other queries -/
structure Book (S : OSpec) (lam : ℕ) where
  made : List (QA S)
  loose : List (((Dg lam × Dg lam) × ℕ) × Dg lam)

/-- a chain answer is entered, once -/
def Book.note (b : Book S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o) : Book S lam :=
  if (C o).isPlain then b else
    match findMade b.made o q with
    | some _ => b
    | none => { b with made := b.made ++ [⟨o, q, r⟩] }

/-- the number of values of a hash block, 2^lam, less one -/
def nDg (lam : ℕ) : ℕ := 2 ^ lam - 1

theorem card_Dg (lam : ℕ) : Fintype.card (Dg lam) = nDg lam + 1 := by
  have h : 0 < 2 ^ lam := by positivity
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nDg]
  omega

/-- a uniform sample with 2^lam outcomes is a hash block -/
def digE (lam : ℕ) : Fin (nDg lam + 1) ≃ Dg lam :=
  (Fintype.equivFinOfCardEq (card_Dg lam)).symm

/-- what a table answers at a query to dr without a coin: its own earlier answer; else the hash
block of the oldest entered answer with that state that has such a hash block -/
def drVal (b : Book S lam) (p : (Dg lam × Dg lam) × ℕ) : Option (Dg lam) :=
  match b.loose.lookup p with
  | some r => some r
  | none => findBlock C b.made p.1 p.2

/-- The ideal interpretations. Typed queries go to the first family; a raw query for a state becomes
the typed query, of whose answer the state is returned; a raw expansion query is answered from the
table as the simulator `simSt` (Rom/StateFirst.lean) does, with coins. With all = false only the raw
queries are entered in the table (what a reduction can do): this is the interpretation that all
theorems use. With all = true typed queries are entered too: used by no theorem (`ideal_bind` alone
is stated for both values of all); the analysis keeps such a table as a ghost:
Rom/StateFirstHitDef.lean. -/
def ideal (all : Bool) : OComp (mixSpec C) α → Book S lam → OComp S (α × Book S lam)
  | .pure a, b => .pure (a, b)
  | .sample n k, b => .sample n fun r => ideal all (k r) b
  | .query (.inl o) q k, b => .query o q fun r => ideal all (k r) (if all then b.note C o q r else b)
  | .query (.inr (.inl o)) q k, b => .query o q fun r => ideal all (k ((C o).toAns r)) (b.note C o q r)
  | .query (.inr (.inr _)) p k, b =>
      match drVal C b p with
      | some r => ideal all (k r) b
      | none =>
        .sample (nDg lam) fun x =>
          ideal all (k (digE lam x)) { b with loose := (p, digE lam x) :: b.loose }

/-- the reduction's table, a shadow table in which typed queries are entered too, and a flag -/
structure Sh (S : OSpec) (lam : ℕ) where
  bT : Book S lam
  bF : Book S lam
  fl : Bool

/-- the two tables disagree at a query to dr -/
def Sh.dis (s : Sh S lam) (p : (Dg lam × Dg lam) × ℕ) : Bool :=
  decide (drVal C s.bT p ≠ drVal C s.bF p)

/-- The reduction's interpretation with a shadow: it answers as `ideal C false` does, from the table
bF; in addition it keeps the table bT of all chain answers, and raises the flag when the two tables
disagree at a query to dr that is made. -/
def shadow : OComp (mixSpec C) α → Sh S lam → OComp S (α × Sh S lam)
  | .pure a, s => .pure (a, s)
  | .sample n k, s => .sample n fun r => shadow (k r) s
  | .query (.inl o) q k, s => .query o q fun r => shadow (k r) { s with bT := s.bT.note C o q r }
  | .query (.inr (.inl o)) q k, s =>
    .query o q fun r =>
      shadow (k ((C o).toAns r)) { s with bT := s.bT.note C o q r, bF := s.bF.note C o q r }
  | .query (.inr (.inr _)) p k, s =>
      match drVal C s.bF p with
      | some r => shadow (k r) { s with fl := s.fl || s.dis C p }
      | none =>
        .sample (nDg lam) fun x =>
          shadow (k (digE lam x))
            ⟨{ s.bT with loose := (p, digE lam x) :: s.bT.loose },
              { s.bF with loose := (p, digE lam x) :: s.bF.loose },
              s.fl || s.dis C p⟩

/-- The shadow does not show: without it the interpretation is the reduction's. -/
theorem shadow_forget (c : OComp (mixSpec C) α) (s : Sh S lam) :
    ((shadow C c s).bind fun x => .pure (x.1, x.2.bF)) = ideal C false c s.bF := by
  induction c generalizing s with
  | pure a => rfl
  | sample n k ih => simp only [shadow, ideal, OComp.bind, ih]
  | query x q k ih =>
    match x, q, k, ih with
    | .inl o, q, k, ih => simp only [shadow, ideal, OComp.bind, ih, Bool.false_eq_true, if_false]
    | .inr (.inl o), q, k, ih => simp only [shadow, ideal, OComp.bind, ih]
    | .inr (.inr u), p, k, ih =>
      simp only [shadow, ideal]
      cases drVal C s.bF p with
      | some r => exact ih r _
      | none => simp only [OComp.bind, ih]

/-- on a program without raw queries the reduction's interpretation is the program itself -/
theorem ideal_liftT (c : OComp S α) (b : Book S lam) :
    ideal C false (liftT C c) b = c.bind fun a => .pure (a, b) := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [liftT, ideal, OComp.bind, ih]
  | query o q k ih =>
    simp only [liftT, ideal, OComp.bind, Bool.false_eq_true, if_false, ih]

theorem real_bind (c : OComp (mixSpec C) α) (g : α → OComp (mixSpec C) β) :
    real C (c.bind g) = (real C c).bind fun a => real C (g a) := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, real, ih]
  | query x q k ih =>
    match x, q, k, ih with
    | .inl o, q, k, ih => simp only [OComp.bind, real, ih, OComp.bind_assoc]
    | .inr x, q, k, ih => simp only [OComp.bind, real, ih]

theorem ideal_bind (all : Bool) (c : OComp (mixSpec C) α)
    (g : α → OComp (mixSpec C) β) (b : Book S lam) :
    ideal C all (c.bind g) b = (ideal C all c b).bind fun x => ideal C all (g x.1) x.2 := by
  induction c generalizing b with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, ideal, ih]
  | query x q k ih =>
    match x, q, k, ih with
    | .inl o, q, k, ih => simp only [OComp.bind, ideal, ih]
    | .inr (.inl o), q, k, ih => simp only [OComp.bind, ideal, ih]
    | .inr (.inr u), p, k, ih =>
      simp only [OComp.bind, ideal]
      cases drVal C b p with
      | some r => exact ih r b
      | none => simp only [OComp.bind, ih]

/-- on every path at most nT typed queries at chain oracles (typed queries at unchanged oracles are
free) and nR raw queries -/
def MixBound : OComp (mixSpec C) α → ℕ → ℕ → Prop
  | .pure _, _, _ => True
  | .sample _ k, t, r => ∀ x, MixBound (k x) t r
  | .query (.inl o) _ k, t, r =>
    if (C o).isPlain = true then
      ∀ x, MixBound (k x) t r else ∃ t', t = t' + 1 ∧ ∀ x, MixBound (k x) t' r
  | .query (.inr _) _ _, _, 0 => False
  | .query (.inr _) _ k, t, r + 1 => ∀ x, MixBound (k x) t r

/-- at a typed query the continuation does not depend on the hid of a chain answer -/
def HidFreeM : OComp (mixSpec C) α → Prop
  | .pure _ => True
  | .sample _ k => ∀ x, HidFreeM (k x)
  | .query (.inl o) _ k => (∀ r r', (C o).agH r r' → k r = k r') ∧ ∀ r, HidFreeM (k r)
  | .query (.inr _) _ k => ∀ r, HidFreeM (k r)

/-- Under `MixBound` and `HidFreeM`, the real and the reduction's interpretation of a mixed program
are within (nT + nR)² / 2^(2 lam) + nR nT / 2^lam. (One-sided for every event: so also the other
way, by the complement.) -/
def Spec.mixClose : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (C : ∀ o, Link lam (S.Rng o)) (α : Type)
      (c : OComp (mixSpec C) α) (nT nR : ℕ),
    MixBound C c nT nR → HidFreeM C c →
    ∀ E : Set α, Pr (real C c) (fun _ => E) ≤
      Pr (ideal C false c ⟨[], []⟩) (fun _ => {x | x.1 ∈ E}) +
        collP lam (nT + nR) (nT + nR) + hitP lam nR nT

end Rom
