-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NormWordsOfHear.lean: the norms' words of the file of scales, at the environment
that a run of K4's own text makes, under a table of scales that reads the public record alone.

Johnson/Road/FormsKeysIdnW.lean proves `normWords_sclOf`: the record `NormWords v D` holds under the
table `sclOf v.y.h v.sc v.g v.y.Lam`, if a layer has two norms and the group has D.nl layers. A law
on a run wants that table fixed IN FRONT of the run. OnBytes/Desc/First/K4/HearPublic.lean says what
the environment o.v of a return is: the plan's layout, the plan's scales, the group. So the table is
`sclOf P.y.h P.sc g P.y.Lam`: it reads nothing of what was heard.

  `env_of_hear`: o.v.y = P.y, o.v.sc = P.sc, o.v.g = g.
  `normWords_of_hear`: the record at o.v under that table.

Limits. An identity on data with two public premises: no draw, no soundness.
-/
import Johnson.Road.FormsKeysIdnW
import OnBytes.Desc.First.K4.HearPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (engFl hear)

theorem env_of_hear {P : Pub} {hp : Layer.HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) :
    o.v.y = P.y ∧ o.v.sc = P.sc ∧ o.v.g = g ∧ o.v.zk = fo.zk := by
  obtain ⟨_, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, _, _, ev, _⟩ :=
    Desc.First.K4.hear_public h
  rw [ev]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem normWords_of_hear {P : Pub} {hp : Layer.HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) (D : Dim)
    (hNN : P.y.NN = 2) (hL : P.y.Lam = D.nl) :
    NormWords (scl := sclOf P.y.h P.sc g P.y.Lam) o.v D := by
  obtain ⟨vy, vsc, vg, _⟩ := env_of_hear h
  have N := normWords_sclOf o.v D (by rw [vy]; exact hNN) (by rw [vy]; exact hL)
  rw [vy, vsc, vg] at N
  exact N

#print axioms normWords_of_hear

end OnBytes.Road.K4
