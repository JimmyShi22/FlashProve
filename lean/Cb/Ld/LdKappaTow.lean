-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaTow.lean: "every round's error, as a probability, is at most κ" (`Err.Below`,
Iop/InteractiveOracleProof.lean): the whole test on a code, as a concrete tower (folds, code switches, a base case):
from numbers, by recursion on the tower. The quoted words say e ≤ κ · v, with e the round's error, a
count of values of its verifier message (`Err`, Iop/Rbr.lean), and v the number of all values of
that message. These errors are numbers that a block lists (the data field `N.err` of `ldSwBlock`,
`ldBaseEnd`, `T.toEnd`): that a block is sound at the numbers that it lists is no statement of this
file.

Definitions (on numbers) and theorems: glue along the rules of composition; nothing is evaluated. A
concrete tower is an `LdTowC` or `LdTowG` (Cb/Obj/LdObjectTower.lean); `T.toEnd` is the whole test
as one block.

Main names:
  `SumPar.Kap`: `Y.Kap Lst mC mS mW κ`: the zero-knowledge sumcheck that folds, k + 1 rounds, each
    verifier message a challenge in `Y.Ch` (`ld_sum_below`, Cb/Ld/LdGroupLinkBelow.lean).
  `LdSw.Kap`: `D.Kap e L κ`: the code switch, two rounds: (pairs in the list) · (the out-of-domain
    sample's exceptional seeds) ≤ κ · (number of its seeds); (|P| - e - 1)^t · |Zb.D| +
    |P|^t · (L · Zb.err) ≤ κ · (number of (t positions, a seed of the zero-evader)).
  `LdJoint.KapB`: `a.KapB t bad L2 κ`: the base case, two rounds.
  `LdTowC.Kap`, `LdTowG.Kap`: `T.Kap κ`: by recursion.
  `ldKappa_towC`, `ldKappa_towG`: `T.Kap κ` → every round's error of `T.toEnd`, as a probability, is
    at most κ.
  `ldKappa_pre`: a test D whose whole test is the tower T (`e : D.T = T.toEnd`): bridge's number
    and `T.Kap κ` → `D.Kap κ` (Cb/Ld/LdKappaRun.lean).
  The types of positions (P, P' of a code switch; `G.P` of a group) are taken nonempty.

Limits: this file says nothing on the size of any number. It does not say that the numbers Lst, mC,
mS, mW, L, bad, L2 bound lists and agreement: asked elsewhere (the towers' own hypotheses).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaRun
import Cb.Obj.LdObjectTower
import Cb.Ld.LdGroupLinkBelow

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {E : Type} [Field E] [Fintype E]

/-- The fold's numbers: Lst 0 ≤ κ |Ch|; for i < k: mC (i + 1) + [if i + 1 ≤ h: mS (i + 1) +
mW (i + 1)] + Lst i · n ≤ κ |Ch|. -/
structure SumPar.Kap {P : Type} [Fintype P] (Y : SumPar E P) (Lst mC mS mW : ℕ → ℕ) (κ : ℝ≥0∞) :
    Prop where
  first : (Lst 0 : ℝ≥0∞) ≤ κ * (Fintype.card Y.Ch : ℝ≥0∞)
  round : ∀ i, i < Y.k →
    ((mC (i + 1) + (if i + 1 ≤ Y.h then mS (i + 1) + mW (i + 1) else 0) + Lst i * Y.n : ℕ) : ℝ≥0∞) ≤
      κ * (Fintype.card Y.Ch : ℝ≥0∞)

/-- The code switch's numbers. -/
structure LdSw.Kap {P P' St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
    (D : LdSw E P P' St) (e L : ℕ) (κ : ℝ≥0∞) : Prop where
  ood : (D.W.err1 L : ℝ≥0∞) ≤ κ * (Fintype.card D.Zo.D : ℝ≥0∞)
  loc : (D.W.err2 e L : ℝ≥0∞) ≤ κ * (Fintype.card ((Fin D.t → P) × D.Zb.D) : ℝ≥0∞)

theorem ldKappa_sw {P P' St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
    (D : LdSw E P P' St) (e e' L t' : ℕ) (κ : ℝ≥0∞) (h : D.Kap e L κ) :
    Err.Below (ldSwBlock D e e' L t').N.err κ :=
  ⟨h.ood, h.loc, trivial⟩

/-- The base case's numbers: bad + L2 ≤ κ · |E|; (|P| - e - 1)^t ≤ κ · (number of t positions). -/
structure LdJoint.KapB (a : LdJoint E) (t bad L2 : ℕ) (κ : ℝ≥0∞) : Prop where
  comb : ((bad + L2 : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞)
  loc  : (((Fintype.card a.P - a.e - 1) ^ t : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card (Fin t → a.P) : ℝ≥0∞)

theorem ldKappa_base (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d bad L2 : ℕ)
    (κ : ℝ≥0∞) (h : a.KapB t bad L2 κ) :
    Err.Below (ldBaseEnd a t cov d bad L2).N.err κ :=
  ⟨h.comb, h.loc, trivial⟩

/-- A concrete tower's numbers, by recursion: the base's; a stage's fold, its switch, the rest. -/
def LdTowC.Kap (κ : ℝ≥0∞) : {a : LdJoint E} → LdTowC a → Prop
  | _, .base a t _ _ bad L2 => a.KapB t bad L2 κ
  | _, @LdTowC.step _ _ _ _ _ _ _ _ _ _ Y sl e S _ Lst mC mS mW _ L rest =>
    (Y.reform sl).Kap Lst mC mS mW κ ∧ (S.D e).Kap e L κ ∧ rest.Kap κ

theorem ldKappa_towC (κ : ℝ≥0∞) :
    ∀ {a : LdJoint E} (T : LdTowC a), T.Kap κ → Err.Below T.toEnd.N.err κ := by
  intro a T
  induction T with
  | base a t cov d bad L2 => exact fun h => ldKappa_base a t cov d bad L2 κ h
  | step Y sl e S d Lst mC mS mW e' L rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact Err.Below.app
      (Err.Below.app
        (Err.Below.app trivial (ld_sum_below (Y.reform sl) Lst mC mS mW κ h1.first h1.round))
        (ldKappa_sw (S.D e) e e' L rest.toTower.q κ h2)) (ih h3)

section
variable {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B → Type}
  {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)}

/-- The numbers of a concrete tower on a group's complex. -/
def LdTowG.Kap (κ : ℝ≥0∞) : LdTowG G Sb sl Z → Prop
  | .plain T => T.Kap κ
  | @LdTowG.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw _ Lst mC mS mW _ L rest =>
    (Sh.fold Sb sl Z).Kap Lst mC mS mW κ ∧ (Sw.D G.e).Kap G.e L κ ∧ rest.Kap κ

theorem ldKappa_towG (κ : ℝ≥0∞) (T : LdTowG G Sb sl Z) (h : T.Kap κ) :
    Err.Below T.toEnd.N.err κ := by
  cases T with
  | plain T => exact ldKappa_towC κ T h
  | shaped Sh Sw d Lst mC mS mW e' L rest =>
    obtain ⟨h1, h2, h3⟩ := h
    exact Err.Below.app
      (Err.Below.app (ld_sum_below (Sh.fold Sb sl Z) Lst mC mS mW κ h1.first h1.round)
        (ldKappa_sw (Sw.D G.e) G.e e' L rest.toTower.q κ h2))
      (ldKappa_towC κ rest h3)

end

/-- A test whose whole test is a tower (`e`): the bridge's number (`hb`) and `T.Kap κ` (`h`) give
`D.Kap κ`. -/
theorem ldKappa_pre {S : Sig E} (D : LdRunD S) (T : LdTowG D.G D.Sb D.sl D.Z) (κ : ℝ≥0∞)
    (e : D.T = T.toEnd)
    (hb : ((D.L * D.Z.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞)) (h : T.Kap κ) : D.Kap κ :=
  ⟨hb, by rw [e]; exact ldKappa_towG κ T h⟩

end
end Cb
