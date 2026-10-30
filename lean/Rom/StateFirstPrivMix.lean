-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstPrivMix.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean), index privacy, part 2: the real privacy experiment on `stateFirstArg C A` as
a mixed program (Rom/StateFirstMix.lean), `mixExp`: `A.C` and `A.P` make typed queries, the
adversarial verifier raw ones; its real interpretation, its numbers of queries, and that hid is not
read, under `HidFree`.

The step leads from a family S of typed oracles, the first family, to the second, `stSpec S lam C`.
There a chain oracle returns only a state: the chaining value and the last block, hid, of its old
answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). (`Link`, `stSpec`: Rom/StateFirst.lean.) A mixed program (over `mixSpec`) makes typed
queries (the honest side's, to the first family) and raw queries (an adversary's, to the second).
(`mixSpec`, `real`: Rom/StateFirstMix.lean.)

  `mixBound_mixExp`   If committer and prover make at most nC and nP queries at chain oracles and
                      the adversary at most t queries (hC, hP, hV), then with N batches: at most nC
                      + N * nP typed queries at chain oracles (`wCh`: weight 1 there, 0 at unchanged
                      oracles) and t raw queries.
  `hidFreeM_mixExp`   Every typed query's continuation does not depend on the hid of a chain answer
                      (its last block), if the scheme's algorithms do not (`HidFree`).

Limits: nothing on the reduction's interpretation of the mixed experiment
(Rom/StateFirstPrivIdeal.lean). No probability, no bound on a distance.
-/
import Rom.StateFirstPrivReplay
import Rom.StateFirstKit2

set_option autoImplicit false

namespace Rom
open ZKCP

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o))
  {I X W PP IVK ISK Pf : Type} {α β : Type}

/-! ## The experiment as a mixed program -/

/-- steps 3 and 4 of the real experiment (`Gen.realLoop`, ZKCP/Gen.lean; numbered as in
ZKCP/Defs.lean, realLoop): P makes typed queries, the adversary raw ones -/
def mixLoop (A : Gen.Arg S I X W IVK ISK Pf)
    (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf) (isk : ISK) :
    Gen.AdvVerifier (stSpec S lam C) X Pf → ℕ → Gen.View (stSpec S lam C) IVK X Pf →
    OComp (mixSpec C) (Gen.View (stSpec S lam C) IVK X Pf)
  | .halt, _, v => .pure v
  | .query x q k, n, v =>
    .query (S := mixSpec C) (.inr x) q fun r =>
      mixLoop A Z isk (k r) n { v with trace := v.trace ++ [⟨x, q, r⟩] }
  | .sample m k, n, v =>
    .sample m fun r => mixLoop A Z isk (k r) n { v with coins := v.coins ++ [r.val] }
  | .request _, 0, v => .pure v
  | .request k, n + 1, v =>
      match Z v with
      | none => .pure v
      | some b =>
        (liftT C (A.P isk b.pairs)).bind fun πs =>
          mixLoop A Z isk (k (b.released πs.val)) n
            { v with sessions := v.sessions ++ [b.released πs.val] }

def mixExp (A : Gen.Arg S I X W IVK ISK Pf) (Vt : IVK → Gen.AdvVerifier (stSpec S lam C) X Pf)
    (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf) (i : I) (N : ℕ) :
    OComp (mixSpec C) (Gen.View (stSpec S lam C) IVK X Pf) :=
  (liftT C (A.C i)).bind fun key => mixLoop C A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩

/-! ## The real interpretation -/

theorem real_mixLoop (A : Gen.Arg S I X W IVK ISK Pf) (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf)
    (isk : ISK) (V : Gen.AdvVerifier (stSpec S lam C) X Pf) :
    ∀ (n : ℕ) (v : Gen.View (stSpec S lam C) IVK X Pf),
      real C (mixLoop C A Z isk V n v) = Gen.realLoop (stateFirstArg C A) Z isk V n v := by
  induction V with
  | halt => intro n v; rfl
  | query x q k ih => intro n v; simp only [mixLoop, real, Gen.realLoop, ih]
  | sample m k ih => intro n v; simp only [mixLoop, real, Gen.realLoop, ih]
  | request k ih =>
    intro n v
    cases n with
    | zero => rfl
    | succ n =>
      cases hz : Z v with
      | none => simp only [mixLoop, Gen.realLoop, hz]; rfl
      | some b => simp only [mixLoop, Gen.realLoop, hz, real_bind, real_liftT, ih]; rfl

/-- The real interpretation of the mixed experiment is the real experiment on the scheme over the
second family (an equality of programs). -/
theorem real_mixExp (A : Gen.Arg S I X W IVK ISK Pf)
    (Vt : IVK → Gen.AdvVerifier (stSpec S lam C) X Pf)
    (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf) (i : I) (N : ℕ) :
    real C (mixExp C A Vt Z i N) = Gen.realExp (stateFirstArg C A) Vt Z i N := by
  simp only [mixExp, real_bind, real_liftT, real_mixLoop]
  rfl

/-! ## The numbers of queries -/

/-- A typed program with at most n queries at chain oracles, followed by mixed programs with the
bounds (m, t), has the bounds (n + m, t). -/
theorem mixBound_liftT_bind (c : OComp S α) (g : α → OComp (mixSpec C) β) (m t : ℕ)
    (hg : ∀ a, MixBound C (g a) m t) (n : ℕ) (h : c.CostBoundAt (wCh C) n) :
    MixBound C ((liftT C c).bind g) (n + m) t := by
  have h' := MixBound.bind hg (mixBound_liftT c n h)
  rwa [Nat.zero_add] at h'

theorem mixBound_mixLoop (A : Gen.Arg S I X W IVK ISK Pf)
    (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf) (isk : ISK) (nP : ℕ)
    (hP : ∀ v b, Z v = some b → (A.P isk b.pairs).CostBoundAt (wCh C) nP)
    (V : Gen.AdvVerifier (stSpec S lam C) X Pf) :
    ∀ (n : ℕ) (v : Gen.View (stSpec S lam C) IVK X Pf) (t : ℕ),
      V.QueryBound t → MixBound C (mixLoop C A Z isk V n v) (n * nP) t := by
  induction V with
  | halt => intro _ _ _ _; trivial
  | sample m k ih => exact fun n v t h r => ih r n _ t (h r)
  | query x q k ih =>
    intro n v t h
    cases t with
    | zero => exact h.elim
    | succ t => exact fun r => ih r n _ t (h r)
  | request k ih =>
    intro n v t h
    cases n with
    | zero => trivial
    | succ n =>
      cases hz : Z v with
      | none => simp only [mixLoop, hz]; trivial
      | some b =>
        simp only [mixLoop, hz]
        rw [Nat.succ_mul, Nat.add_comm]
        exact mixBound_liftT_bind C _ _ (n * nP) t (fun πs => ih _ n _ t (h _)) nP (hP v b hz)

theorem mixBound_mixExp (A : Gen.Arg S I X W IVK ISK Pf)
    (Vt : IVK → Gen.AdvVerifier (stSpec S lam C) X Pf) (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf)
    (i : I) (N nC nP t : ℕ) (hC : (A.C i).CostBoundAt (wCh C) nC)
    (hP : ∀ isk v b, Z v = some b → (A.P isk b.pairs).CostBoundAt (wCh C) nP)
    (hV : ∀ ivk, (Vt ivk).QueryBound t) :
    MixBound C (mixExp C A Vt Z i N) (nC + N * nP) t := by
  unfold mixExp
  exact mixBound_liftT_bind C _ _ (N * nP) t
    (fun key => mixBound_mixLoop C A Z key.2 nP (hP key.2) (Vt key.1) N _ t (hV key.1)) nC hC

/-! ## Under the hypotheses below, hid is not read -/

theorem hidFreeM_liftT_bind (c : OComp S α)
    (g : α → OComp (mixSpec C) β) (hg : ∀ a, HidFreeM C (g a)) :
    c.FactorsBy (fun o _ r r' => (C o).agH r r') → HidFreeM C ((liftT C c).bind g) := by
  induction c with
  | pure a => intro _; exact hg a
  | sample n k ih => exact fun h x => ih x (h x)
  | query o q k ih =>
    intro h
    refine ⟨fun r r' hr => ?_, fun r => ih r (h.2 r)⟩
    show (liftT C (k r)).bind g = (liftT C (k r')).bind g
    rw [h.1 r r' hr]

theorem hidFreeM_mixLoop (A : Gen.Arg S I X W IVK ISK Pf) (hH : HidFree C A)
    (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf) (isk : ISK)
    (V : Gen.AdvVerifier (stSpec S lam C) X Pf) :
    ∀ (n : ℕ) (v : Gen.View (stSpec S lam C) IVK X Pf), HidFreeM C (mixLoop C A Z isk V n v) := by
  induction V with
  | halt => intro _ _; trivial
  | sample m k ih => exact fun n v r => ih r n _
  | query x q k ih => exact fun n v r => ih r n _
  | request k ih =>
    intro n v
    cases n with
    | zero => trivial
    | succ n =>
      cases hz : Z v with
      | none => simp only [mixLoop, hz]; trivial
      | some b =>
        simp only [mixLoop, hz]
        exact hidFreeM_liftT_bind C _ _ (fun πs => ih _ n _) (hH.P isk b.pairs)

theorem hidFreeM_mixExp (A : Gen.Arg S I X W IVK ISK Pf) (hH : HidFree C A)
    (Vt : IVK → Gen.AdvVerifier (stSpec S lam C) X Pf)
    (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf) (i : I) (N : ℕ) :
    HidFreeM C (mixExp C A Vt Z i N) := by
  unfold mixExp
  exact hidFreeM_liftT_bind C _ _
    (fun key => hidFreeM_mixLoop C A hH Z key.2 (Vt key.1) N _) (hH.C i)

end Rom
