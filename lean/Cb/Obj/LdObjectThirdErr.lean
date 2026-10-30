-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectThirdErr.lean: the errors of the link and of the offline linear test within a third
of the distance, written out in the order of the rounds.

In standard terms: book-keeping of soundness errors. For two sub-protocols, the sub-protocol for the
claim that two encoded indices hold the same index (the link) and the proximity test with claims
that follows weights-formedness, it writes out the list of errors, round by round, at the numbers of
Cb/Obj/LdObjectThirdTests.lean: all list bounds 1, the folds' errors `εThird`. These errors are
numbers that the link lists and the test lists (the data field `err` of `K.nums ..`, a `LinkNums`,
Hiop/ListNums.lean; of `O.numsF ..`, a `LinNumsR`, Hiop/RecSubs.lean): that a sub-protocol is sound
at the numbers that are listed for it is no statement of this file; that tie is `Spec.ldT3_link`,
`Spec.ldT3_lin` (Cb/Obj/LdObjectThirdTests.lean), each under the hypotheses of its statement, among
them that each whole test on a group (`Kc.T`; `T.T₁`, `T.T₂`) is a tail (`LdEnd.OK`) and `T.Q'.OK`:
premises, which have these parts' own `know` (that condition itself asks soundness of some of the
parts one level down: for these the tie carries soundness, it does not found it).

Statements and proofs (unfolding: Cb/Obj/LdObjectErr.lean has the lists in the blocks' notation;
here the numbers of Cb/Obj/LdObjectThirdTests.lean are put in).
All errors are counts of values of one verifier message. q = |E|; v = number of row variables of the
index; n = number of positions of an index.

Main names:
  `Spec.ldT3e_send`: a sending costs nothing: with lists of one member no two members can collide:
    the error of the seed's round is 0.
  `D.Base3 t d`: the whole test of D is the base case alone on the complex, drawing t positions,
    with e + 1 exceptional coefficients and a list of 1.
  `Spec.ldT3e_base`, `Spec.ldT3e_run`: the base case of `Base3` on a complex read at the positions
    P, at the radius e, drawing t positions: (e + 1) + 1, then (|P| - e - 1)^t.
  `Spec.ldT3e_link`: the link with its closing, any whole test T, all list bounds 1 (`S.L`, `Kc.L`),
    `Fin Cf.C₀.n` non-empty:
      γ: εThird e₀ + εThird e₁ + v q^(v-1); the joint seed: 0; the answers: 0; the locations: the
      larger of (n - e₀ - 1)^t₀ · n^t₁ and n^t₀ · (n - e₁ - 1)^t₁; φ: l q^(l-1); the bridge: the
      evader's number; then T's errors.
  `Spec.ldT3e_link_base`: as above, with `Kc.run.Base3 t dG`: .. then (e + 1) + 1, (|P| - e - 1)^t,
    e the group's joint radius.
  `Spec.ldT3e_lin`: the test at one instance with the plan without a splitting, any whole tests T₁,
    T₂, all list bounds 1 (`Sn.LW`, `Sn.LU`, `Sn.LO`, `T.L₁`, `T.L₂`), `Fin O.Cf.C₀.n` non-empty:
      seed of W: 0; answers: 0; the shared point: errPt (εThird e'); seed of G_u: 0; 0; the
      locations: (n - e' - 1)^t; seed of Ω: 0; 0; ζ: errZeta; first bridge: its evader's number;
      T₁'s errors; second bridge; T₂'s errors; then the errors of what closes the rest of the plan.
  `Spec.ldT3e_lin_base`: as above, with `T.D₁.Base3 t₁ d₁`, `T.D₂.Base3 t₂ d₂`.
  `Spec.ldT3e_names`: what the names say (by definition), for `Fin Cf.C₀.n` non-empty.

Notation: `e₀`, `e₁` (the link): natural numbers (`LdLkP`, Cb/Ld/LdLink.lean: the radii at which the
two folds are tested); `t₀`, `t₁` (the link): natural numbers (`LdLkP`: the numbers of locations);
`e'`, `t` (the test): natural numbers (`LdLinP`, Cb/Ld/LdLin.lean: the radius at which the fold is
tested, the number of locations); `l`: a natural number (`LdLkW`, Cb/Ld/LdLinkWords.lean: the number
of coordinates of φ, and `LdLinW`, Cb/Ld/LdLinWords.lean: of ζ); `klo`: a natural number (`LdLinW`:
the number of column variables inside a code row); `d` (in `Base3 t d`): a natural number (the head
of Cb/Ld/LdBase.lean, on the extractor: the corrector of erasures with the threshold d).

Limits: this file does not say what the numbers mean: the blocks' own files. It does not say the
numbers of values of the verifier messages (Cb/Obj/LdObjectErr.lean has them for the link's core and
for a test on a group (`ldOErr_run`, `ldOErr_cons`); not for the test at one instance). The folds'
errors are upper bounds (Cb/Obj/LdObjectThirdTests.lean, Declared (2), (3)).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectThirdTests
import Cb.Obj.LdObjectErr

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the whole test of D is the base case alone on the complex, with the numbers of "within a third"
-/
def LdRunD.Base3 {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) (t d : ℕ) : Prop :=
  ∃ cov : (D.G.joint D.Sb D.sl D.Z).C.NP → (D.G.joint D.Sb D.sl D.Z).P,
    D.T = ldBaseEnd (D.G.joint D.Sb D.sl D.Z) t cov d (D.G.e + 1) 1

namespace Spec

/-- States, for list bounds 1: a sending costs nothing. -/
def ldT3e_send : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (Sd : N.Seeds) (L : N.O → ℕ),
    (∀ a, L a = 1) → ldSendFamErr N Sd L = 0

def ldT3e_base : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d : ℕ),
    (ldBaseEnd a t cov d (a.e + 1) 1).N.err.toList =
      [(a.e + 1) + 1, (Fintype.card a.P - a.e - 1) ^ t]

def ldT3e_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (t d : ℕ),
    D.Base3 t d → D.T.N.err.toList = [(D.G.e + 1) + 1, (Fintype.card D.G.P - D.G.e - 1) ^ t]

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The link. -/
def ldT3e_link : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (Kc : K.P.Cl)
      (d₂ : K.P.W2) (d : K.P.W0),
    (∀ a, S.L a = 1) → Kc.L = 1 →
    (K.nums (K.full S (Cf.εThird K.e₀) (Cf.εThird K.e₁) Kc d₂ d)).err.toList =
      [K.P.errGam (Cf.εThird K.e₀) (Cf.εThird K.e₁), 0, 0, K.P.errLoc, K.P.errPhi, Kc.Z.err] ++
        Kc.T.N.err.toList

def ldT3e_link_base : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (Kc : K.P.Cl)
      (d₂ : K.P.W2) (d : K.P.W0) (t dG : ℕ),
    (∀ a, S.L a = 1) → Kc.L = 1 → Kc.run.Base3 t dG →
    (K.nums (K.full S (Cf.εThird K.e₀) (Cf.εThird K.e₁) Kc d₂ d)).err.toList =
      [K.P.errGam (Cf.εThird K.e₀) (Cf.εThird K.e₁), 0, 0, K.P.errLoc, K.P.errPhi, Kc.Z.err,
        (Kc.G.e + 1) + 1, (Fintype.card Kc.G.P - Kc.G.e - 1) ^ t]

/-- The test at one instance. -/
def ldT3e_lin : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPl O.toC) (T : LdLinPlT p)
      (Sn : O.toC.P.Snd) (d : O.toC.P.W0),
    (∀ a, Sn.LW a = 1) → (∀ a, Sn.LU a = 1) → (∀ a, Sn.LO a = 1) → T.L₁ = 1 → T.L₂ = 1 →
    (O.numsF Sn (O.Cf.εThird O.e') T.Q T.fq d).err.toList =
      [0, 0, O.toC.P.errPt (O.Cf.εThird O.e'), 0, 0, O.toC.P.errLoc, 0, 0, O.toC.P.errZeta] ++
        (T.Z₁.err :: T.T₁.N.err.toList ++ (T.Z₂.err :: T.T₂.N.err.toList ++ T.Q'.c.errs))

def ldT3e_lin_base : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPl O.toC) (T : LdLinPlT p)
      (Sn : O.toC.P.Snd) (d : O.toC.P.W0) (t₁ t₂ d₁ d₂ : ℕ),
    (∀ a, Sn.LW a = 1) → (∀ a, Sn.LU a = 1) → (∀ a, Sn.LO a = 1) →
    T.L₁ = 1 → T.L₂ = 1 → T.D₁.Base3 t₁ d₁ → T.D₂.Base3 t₂ d₂ →
    (O.numsF Sn (O.Cf.εThird O.e') T.Q T.fq d).err.toList =
      [0, 0, O.toC.P.errPt (O.Cf.εThird O.e'), 0, 0, O.toC.P.errLoc, 0, 0, O.toC.P.errZeta,
          T.Z₁.err, (p.G₁.e + 1) + 1, (Fintype.card p.G₁.P - p.G₁.e - 1) ^ t₁, T.Z₂.err,
          (p.G₂.e + 1) + 1, (Fintype.card p.G₂.P - p.G₂.e - 1) ^ t₂] ++ T.Q'.c.errs

/-- What the names say. -/
def ldT3e_names : Prop :=
  (∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (a b : ℕ),
    K.P.errGam a b = a + b + Cf.X.v * Fintype.card E ^ (Cf.X.v - 1) ∧
    K.P.errLoc =
      max ((Cf.C₀.n - K.e₀ - 1) ^ K.t₀ * Cf.C₀.n ^ K.t₁)
        (Cf.C₀.n ^ K.t₀ * (Cf.C₀.n - K.e₁ - 1) ^ K.t₁) ∧
    K.P.errPhi = K.l * Fintype.card E ^ (K.l - 1)) ∧
  (∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (ε : ℕ),
    O.toC.P.errPt ε =
      ε * Fintype.card E ^ O.klo + (O.Cf.X.v + O.klo) * Fintype.card E ^ (O.Cf.X.v + O.klo - 1) ∧
    O.toC.P.errLoc = (O.Cf.C₀.n - O.e' - 1) ^ O.t ∧
    O.toC.P.errZeta = O.l * Fintype.card E ^ (O.l - 1)) ∧
  ∀ (Cf : LdCf F E) (e : ℕ), Cf.εThird e =
    Cf.v * (e + 1) * Fintype.card E ^ (Cf.v - 1) + 1 * (Cf.X.v * Fintype.card E ^ (Cf.X.v - 1))

end
end Spec

theorem ldT3e_send : Spec.ldT3e_send := by
  intro E _ N Sd L h
  unfold ldSendFamErr
  exact Finset.sum_eq_zero fun a _ => by rw [h a]; simp

theorem ldT3e_base : Spec.ldT3e_base := fun _ _ _ _ _ _ _ => rfl

theorem ldT3e_run : Spec.ldT3e_run := by
  rintro E _ _ S D t d ⟨cov, h⟩
  exact (congrArg (fun X => X.N.err.toList) h).trans (ldT3e_base E _ t cov d)

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldT3e_link : Spec.ldT3e_link F E := by
  intro Cf _ K S Kc d₂ d hS hL
  rw [ldOErr_link F E Cf K S _ _ Kc d₂ d, ldT3e_send E K.P.N S.Sd S.L hS, hL, Nat.one_mul]

theorem ldT3e_link_base : Spec.ldT3e_link_base F E := by
  intro Cf _ K S Kc d₂ d t dG hS hL hT
  have a1 : Kc.T.N.err.toList = [(Kc.G.e + 1) + 1, (Fintype.card Kc.G.P - Kc.G.e - 1) ^ t] :=
    ldT3e_run E _ Kc.run t dG hT
  rw [ldT3e_link F E Cf K S Kc d₂ d hS hL, a1]
  rfl

theorem ldT3e_lin : Spec.ldT3e_lin F E := by
  intro O _ p T Sn d hW hU hO h1 h2
  rw [ldOErr_lin F E O _ Sn T.Q T.fq d, ldT3e_send E _ _ Sn.LW hW,
    ldT3e_send E _ _ Sn.LU hU, ldT3e_send E _ _ Sn.LO hO]
  have e1 := (ldOErr_cons E _ _ _ T.D₁ (LdTc.cons T.D₂ T.Q' T.d₂ T.d₂') T.d₁ T.d₁').1
  have e2 := (ldOErr_cons E _ _ _ T.D₂ T.Q' T.d₂ T.d₂').1
  have e3 : T.Q.c.errs =
      (T.L₁ * T.Z₁.err) :: T.T₁.N.err.toList ++
        ((T.L₂ * T.Z₂.err) :: T.T₂.N.err.toList ++ T.Q'.c.errs) :=
    e1.trans (congrArg _ e2)
  rw [e3, h1, h2, Nat.one_mul, Nat.one_mul]

theorem ldT3e_lin_base : Spec.ldT3e_lin_base F E := by
  intro O _ p T Sn d t₁ t₂ d₁ d₂ hW hU hO h1 h2 hT₁ hT₂
  have a1 : T.T₁.N.err.toList = [(p.G₁.e + 1) + 1, (Fintype.card p.G₁.P - p.G₁.e - 1) ^ t₁] :=
    ldT3e_run E _ T.D₁ t₁ d₁ hT₁
  have a2 : T.T₂.N.err.toList = [(p.G₂.e + 1) + 1, (Fintype.card p.G₂.P - p.G₂.e - 1) ^ t₂] :=
    ldT3e_run E _ T.D₂ t₂ d₂ hT₂
  rw [ldT3e_lin F E O p T Sn d hW hU hO h1 h2, a1, a2]
  rfl

omit [Fintype F] in
theorem ldT3e_names : Spec.ldT3e_names F E := by
  refine ⟨fun Cf _ K a b => ⟨rfl, ?_, rfl⟩, fun O _ ε => ⟨rfl, ?_, rfl⟩, fun _ _ => rfl⟩
  · show max ((Fintype.card (Fin Cf.C₀.n) - K.e₀ - 1) ^ K.t₀ * Fintype.card (Fin Cf.C₀.n) ^ K.t₁)
        (Fintype.card (Fin Cf.C₀.n) ^ K.t₀ * (Fintype.card (Fin Cf.C₀.n) - K.e₁ - 1) ^ K.t₁) = _
    rw [Fintype.card_fin]
  · show (Fintype.card (Fin O.Cf.C₀.n) - O.e' - 1) ^ O.t = _
    rw [Fintype.card_fin]

end
end Cb
