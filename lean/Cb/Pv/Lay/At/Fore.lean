-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Fore.lean: the stages of a layers' sub-proof's own rounds up to the terms (Fore,
Cb/Pv/Lay/OwnAll.lean) at a value: the library's description of a feed-forward segment.

Main names:
  `ForePar`: what stays free: the sizes, the tables, the group's first layer; the entries, how a
    tuple of messages is read as entries (msg), the entries as cells (rd) and as weights (rw); in
    the first statement: the lookup's point (zOf) and what the lookup's end leaves for the calls'
    joint extension, as a public part and a form in the entries (kTg, kInc); the order of the
    squares' rounds; the places of the mask entries.
  `nr`, `tp`: the letters of Cb/Pv/Lay/At/Norms.lean and Terms.lean from these.
  `kEnd`: what the lookup's end leaves. `jg`: the gap of the lookup's join as a function of the
    hidden sum S of the terms: accS + lineS + S - kEnd. `tS`: the true sum of the terms.
  `fore`: the record, at statements X' from which the first statement and the token point are read.
  `fore_pL`: what is claimed behind the token point, written out.
  `fore_atPt`: it gives that the extension at the point of each of the 17 identities' defects of
    every norm vanishes, and the join at the true sum of the terms.
  `tS_eq`, `jn_iff`: under what tm_sum asks (what the panel QK needs of the sizes; in each layer the
    shifts of queries and keys equal or both at least 16; a layer has twice the hidden units of an
    expert): the true sum is ClT, and the join at it says that the sum over the calls of weight
    times KF (Inst/Model/FF/Objects.lean) is kEnd.

Limits: that KF is the extension of a call's key vector is not shown here: see the theorem own_join
(OnBytes.Road.own_join, in a later file). That the programs' records are these is not said here;
nor that kEnd is what the programs' lookup leaves: kTg and kInc are free. For a tie with the
programs it will not be enough that the batched sumcheck's target less its incoming form has the
programs' value: the target itself, and so kTg, must be the public part of the programs' start form
as a number. Nothing is said on an honest prover or on hiding.


-/
import Cb.Pv.Lay.At.Norms
import Cb.Pv.Lay.At.Line
import Cb.Pv.Lay.At.Terms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW dJ lDd wc KF ClT)

noncomputable section

/-- The letters of the stages up to the terms that stay free. -/
structure ForePar (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type) where
  /-- the sizes, the tables, the number of the group's first layer -/
  D : Dim
  tb : Tables
  L0 : ℕ
  /-- the entries; how the messages are read as entries, the entries as cells and as weights -/
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  msg : M → J → E
  rd : (J → E) → Cell → E
  rw : (J → E) → ℕ → LW E
  two : (2 : E) ≠ 0
  /-- the lookup's point; what its end leaves for the calls' joint extension -/
  zOf : X → ℕ → E
  kTg : X → E
  kInc : X → J → E
  /-- the order in which the squares' variables are bound -/
  eS : Fin (D.lL + 1 + (lDd D + D.lT)) ≃ Fin (D.lL + 1 + (lDd D + D.lT))
  /-- the masks of the squares, of the rows, of the terms -/
  mkS : Fin D.nNu → Fin 9 → J
  wS : PIdx (ldPartFmt E (D.lL + 1 + (lDd D + D.lT)) (fun _ => 2) ++ [pDummy E 2]) → J
  cS : Bool → J
  mkP : Fin (D.nNu * 7) → J
  rP : J
  wP : PIdx (ldPartFmt E D.lT (fun _ => 2) ++ [pDummy E 2]) → J
  cP : Fin D.nNu × Fin 4 → J
  rT : J
  wT : PIdx (ldPartFmt E D.lT (fun _ => 2) ++ [pDummy E 1]) → J
  cT : ShA D → J

attribute [instance] ForePar.finJ ForePar.decJ

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace ForePar
variable (P : ForePar E M X)

/-- The norms' letters. -/
@[reducible] def nr : NormPar0 E where
  D := P.D
  J := P.J
  rd := P.rd
  two := P.two
  eS := P.eS
  mkS := P.mkS
  wS := P.wS
  cS := P.cS
  mkP := P.mkP
  rP := P.rP
  wP := P.wP
  cP := P.cP

/-- The terms' letters. -/
@[reducible] def tp : TermPar0 E where
  D := P.D
  tb := P.tb
  L0 := P.L0
  J := P.J
  rd := P.rd
  rw := P.rw
  rT := P.rT
  wT := P.wT
  cT := P.cT

/-- What the lookup's end leaves for the calls' joint extension. -/
def kEnd (x : X) (m : M) : E := P.kTg x - ∑ j, P.kInc x j * P.msg m j

/-- The gap of the lookup's join, as a function of the hidden sum of the terms. -/
def jg (x : X) (S : E) (m : M) : E :=
  accS P.D (P.rd (P.msg m)) (P.rw (P.msg m)) (P.zOf x) +
    lineS P.D (P.rd (P.msg m)) P.tb P.L0 (P.rw (P.msg m)) (P.zOf x) + S - P.kEnd x m

/-- The true sum of the terms. -/
def tS (x : X) (m : M) : E :=
  tsum P.tp.tm.toSum.T.par (P.zOf x) (P.msg m) - P.msg m P.rT

/-- The stages up to the terms, at statements X'. x0: the first statement inside one; pv: the token
point; Rd0: what else is claimed at the start and is taken up only by the last stages. -/
def fore {X' : Type} (x0 : X' → X) (pv : X' → Fin P.D.lT → E) (Rd0 : X' → M → Prop) :
    Fore E M X' where
  G := P.nr.sq
  st0 := pv
  rd0 := P.msg
  Rw := P.nr.rows
  st2 := pv
  rd2 := P.msg
  Tm := P.tp.tm
  st3 := fun x => P.zOf (x0 x)
  rd3 := P.msg
  jg := fun x S m => P.jg (x0 x) S m
  Rd0 := Rd0

variable {X' : Type} (x0 : X' → X) (pv : X' → Fin P.D.lT → E) (Rd0 : X' → M → Prop)

/-- What is claimed behind the points, written out. -/
theorem fore_pL (x : X') (m : M) :
    (P.fore x0 pv Rd0).H.pL x m ↔
      P.nr.sq.Phi (pv x) (P.msg m) ∧ P.nr.rows.Idn (pv x) (P.msg m) ∧
        P.jg (x0 x) (P.tS (x0 x) m) m = 0 ∧ Rd0 x m := Iff.rfl

/-- **What is claimed behind the token point gives that the defects' extensions vanish at it, and
the join at the true sum of the terms.** -/
theorem fore_atPt (x : X') (m : M) (h : (P.fore x0 pv Rd0).H.pL x m) :
    (∀ k : ℕ × Fin P.D.nNu,
      Blocks.ext P.D.lT (dJ P.D (P.rd (P.msg m)) k.1 k.2) (Blocks.nat (pv x)) = 0) ∧
      P.jg (x0 x) (P.tS (x0 x) m) m = 0 ∧ Rd0 x m := by
  obtain ⟨h1, h2, h3, h4⟩ := (P.fore_pL x0 pv Rd0 x m).1 h
  exact ⟨fun k => P.nr.norms_atPt (pv x) (P.msg m) h1 h2 k.1 k.2, h3, h4⟩

/-- The true sum of the terms is the library's honest hidden sum. -/
theorem tS_eq (C : P.D.ChOK)
    (hk : ∀ l, l < P.D.nl →
      (P.D.Pl l).kq = (P.D.Pl l).kk ∨ (16 ≤ (P.D.Pl l).kq ∧ 16 ≤ (P.D.Pl l).kk))
    (hf : P.D.f = 2 * P.D.fe) (x : X) (m : M) :
    P.tS x m = ClT P.D (P.rd (P.msg m)) P.tb P.L0 (P.rw (P.msg m)) (P.zOf x) := by
  unfold tS
  rw [P.tp.tm.tsum_eq, show P.tp.tm.rJ = P.rT from rfl, add_sub_cancel_right]
  exact P.tp.tm_sum C hk hf (P.zOf x) (P.msg m)

/-- **What the join at the true sum says.** -/
theorem jn_iff (C : P.D.ChOK)
    (hk : ∀ l, l < P.D.nl →
      (P.D.Pl l).kq = (P.D.Pl l).kk ∨ (16 ≤ (P.D.Pl l).kq ∧ 16 ≤ (P.D.Pl l).kk))
    (hf : P.D.f = 2 * P.D.fe) (x : X) (m : M) :
    P.jg x (P.tS x m) m = 0 ↔
      ∑ c, wc P.D (P.zOf x) c * KF P.D (P.rd (P.msg m)) P.tb P.L0 (P.rw (P.msg m)) (P.zOf x) c =
        P.kEnd x m := by
  rw [P.tS_eq C hk hf]
  have e : ∑ c, wc P.D (P.zOf x) c *
      KF P.D (P.rd (P.msg m)) P.tb P.L0 (P.rw (P.msg m)) (P.zOf x) c =
      accS P.D (P.rd (P.msg m)) (P.rw (P.msg m)) (P.zOf x) +
        lineS P.D (P.rd (P.msg m)) P.tb P.L0 (P.rw (P.msg m)) (P.zOf x) +
        ClT P.D (P.rd (P.msg m)) P.tb P.L0 (P.rw (P.msg m)) (P.zOf x) := by
    unfold accS lineS ClT KF
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    have e2 : ∀ A B : ℕ → Inst.Model.FFSeg.Fam → E, ∀ L : ℕ → List Inst.Model.FFSeg.Fam,
        ∀ g : ℕ → E, ∑ l ∈ range P.D.nl, g l * ((L l).map fun s => A l s + B l s).sum =
          ∑ l ∈ range P.D.nl, g l * ((L l).map fun s => A l s).sum +
            ∑ l ∈ range P.D.nl, g l * ((L l).map fun s => B l s).sum := by
      intro A B L g
      rw [← sum_add_distrib]
      refine sum_congr rfl fun l _ => ?_
      rw [List.sum_map_add]
      ring
    rw [e2]
    ring
  rw [e]
  unfold jg
  constructor <;> intro h <;> linear_combination h

end ForePar
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.ForePar.fore_atPt
#print axioms Cb.Pv.Lay.At.ForePar.jn_iff
