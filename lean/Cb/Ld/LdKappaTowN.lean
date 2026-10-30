-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaTowN.lean: for a whole test that is a tower: its numbers as a list with one entry per
stage, and a decidable check on that list, for errors "at most 2^-x", or at most
2^w · 2^-x in a round that draws locations, which has w bits of work.

Definitions (two records of natural numbers with their checks; "the tower has these numbers").
For variable towers: no tower is built here; nothing is evaluated. "At most 2^-x" is said
of numbers that the tower's blocks list (`T.toEnd.N.err`, through `T.KapW`,
Cb/Ld/LdKappaWorkObj.lean): that a tower is sound at the numbers that it lists is no statement of
this file.

Why: `T.KapW w κ` (Cb/Ld/LdKappaWorkObj.lean) is a recursion over a tower whose clauses hold
cardinalities of types. To meet it at parameters of a protocol one needs (1) the tower's numbers as
a list of numerals, said once by equations and bounds; (2) inequalities between numerals alone.



Main names:
  `StN`: one stage's numbers: nP long positions, e radius, ts locations of its code switch; nCh
    challenges, deg (masking degree - 1: `SumPar.n`, Cb/Ld/LdSum.lean) of its fold; lst the list of
    its complex; bC, bZ, bW the agreement counts of its code and two mask codes; zoE of zoD, zbE of
    zbD: the exceptional seeds of the switch's sample and zero-evader; lNext the list of the next
    complex.
  `s.Ok w x`: four inequalities between natural numbers.
  `BsN`, `B.Ok w x`: the base case: (bad + l2) · 2^x ≤ q; (nP - e - 1)^t · 2^x ≤ 2^w · nP^t.
  `LdTowC.At`, `LdTowG.At`: `T.At L B`: the tower has these numbers: by recursion: equations for
    cardinalities, radii, numbers of locations and the degree; bounds from above for lists,
    agreement counts and exceptional seeds.
  From `T.KapW` the bound on the errors of `T.toEnd`, with the bits `T.bits w`, is
  `ldKappaW_towC`, `ldKappaW_towG` (Cb/Ld/LdKappaWorkObj.lean).

  The types of positions (P, P' of a code switch; `G.P` of a group) are taken nonempty.

Towers below the Johnson radius and within a third (Cb/Obj/LdObjectTowerJohn.lean,
Cb/Obj/LdObjectTowerThird.lean) are such towers by their maps toC, toG: their lists and counts are
constants.

Limits: this file does not say that a tower with given numbers exists, or that the checks bound its
errors. It says nothing on the towers' own hypotheses
(codes, distances, samples, packing). This file says nothing on the value of any number.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaWorkObj
import Cb.Ref.GlRefNum

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

/-- One stage's numbers. -/
structure StN where
  nP : ℕ
  e : ℕ
  ts : ℕ
  nCh : ℕ
  deg : ℕ
  lst : ℕ
  bC : ℕ
  bZ : ℕ
  bW : ℕ
  zoE : ℕ
  zoD : ℕ
  zbE : ℕ
  zbD : ℕ
  lNext : ℕ

/-- The check of one stage: the fold's first round; its further rounds; the code switch's two
rounds, with 2^w at the second, which draws locations. -/
def StN.Ok (s : StN) (w x : ℕ) : Prop :=
  s.lst * 2 ^ x ≤ s.nCh ∧
  (s.bC + (s.bZ + s.bW) + s.lst * s.deg) * 2 ^ x ≤ s.nCh ∧
  s.lNext.choose 2 * s.zoE * 2 ^ x ≤ s.zoD ∧
  ((s.nP - s.e - 1) ^ s.ts * s.zbD + s.nP ^ s.ts * (s.lNext * s.zbE)) * 2 ^ x ≤
    2 ^ w * (s.nP ^ s.ts * s.zbD)

instance (s : StN) (w x : ℕ) : Decidable (s.Ok w x) := by unfold StN.Ok; infer_instance

/-- The base case's numbers; `BsN.Is` asks: nP long positions, e radius, t locations; bad, l2:
bounds from above for the numbers bad, L2 of `LdJoint.KapBW` (Cb/Ld/LdKappaWorkObj.lean); q = |E|.
-/
structure BsN where
  nP : ℕ
  e : ℕ
  t : ℕ
  bad : ℕ
  l2 : ℕ
  q : ℕ

def BsN.Ok (B : BsN) (w x : ℕ) : Prop :=
  (B.bad + B.l2) * 2 ^ x ≤ B.q ∧ (B.nP - B.e - 1) ^ B.t * 2 ^ x ≤ 2 ^ w * B.nP ^ B.t

instance (B : BsN) (w x : ℕ) : Decidable (B.Ok w x) := by unfold BsN.Ok; infer_instance

section
variable {E : Type} [Field E] [Fintype E]

/-- a fold and the code switch after it have the numbers s -/
structure StN.Is {P P' : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P'] (s : StN)
    (Y : SumPar E P) (S : LdSwD Y P') (e : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ) : Prop where
  nP    : Fintype.card P = s.nP
  e     : e = s.e
  ts    : S.ts = s.ts
  nCh   : Fintype.card Y.Ch = s.nCh
  deg   : Y.n = s.deg
  lst   : ∀ i, Lst i ≤ s.lst
  bC    : ∀ i, mC i ≤ s.bC
  bZ    : ∀ i, mS i ≤ s.bZ
  bW    : ∀ i, mW i ≤ s.bW
  zoE   : S.Zo.err ≤ s.zoE
  zoD   : Fintype.card S.Zo.D = s.zoD
  zbE   : S.Zb.err ≤ s.zbE
  zbD   : Fintype.card S.Zb.D = s.zbD
  lNext : L ≤ s.lNext

/-- the base case has the numbers B -/
structure BsN.Is (B : BsN) (a : LdJoint E) (t bad L2 : ℕ) : Prop where
  nP  : Fintype.card a.P = B.nP
  e   : a.e = B.e
  t   : t = B.t
  bad : bad ≤ B.bad
  l2  : L2 ≤ B.l2
  q   : Fintype.card E = B.q

/-- The tower has these numbers. -/
def LdTowC.At : {a : LdJoint E} → LdTowC a → List StN → BsN → Prop
  | _, .base a t _ _ bad L2, [], B => B.Is a t bad L2
  | _, @LdTowC.step _ _ _ _ _ _ _ _ _ _ Y sl e S _ Lst mC mS mW _ L rest, s :: Ls, B =>
    s.Is (Y.reform sl) S e Lst mC mS mW L ∧ rest.At Ls B
  | _, .base _ _ _ _ _ _, _ :: _, _ => False
  | _, @LdTowC.step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, [], _ => False

section
variable {B' : Type} [Fintype B'] {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B' → Type}
  {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B')}

def LdTowG.At : LdTowG G Sb sl Z → List StN → BsN → Prop
  | .plain T, Ls, B => T.At Ls B
  | @LdTowG.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw _ Lst mC mS mW _ L rest, s :: Ls, B =>
    s.Is (Sh.fold Sb sl Z) Sw G.e Lst mC mS mW L ∧ rest.At Ls B
  | @LdTowG.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, [], _ => False

end
end
end Cb
