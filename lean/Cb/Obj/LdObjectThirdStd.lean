-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectThirdStd.lean: for three standard parts the conditions "within a third" follow from
the laws of their codes, a distance d with 3 e < d, and what else their records `Third` ask; the
file is meant for a guard against empty theorems on the offline phase within a third.

In standard terms: helper lemmas for example instances. For the simplest proximity tests (a base
case alone) and the simplest oracle messages, they reduce three of the conditions asked in
Cb/Obj/LdObjectThird.lean, Cb/Obj/LdObjectThirdTests.lean and Cb/Obj/LdObjectToyKit.lean (`D.In3`,
`S.Third`, `M.OK 1 t`) to facts on codes: the laws of `LdCode.Laws`, a minimum distance d, a radius
e with 3 e < d, and the further clauses of the records `Third`.

Definitions, statements and proofs. A tool for guards against empty theorems; no parameter of a
protocol.

Main names:
  `Spec.ldStd3_base`: a test whose whole test is the base case alone at the group's distance d, with
    e + 1 exceptional coefficients and a list of 1 (`D.T = ldBaseEnd _ t cov d (D.G.e + 1) 1`), on a
    group within a third (`D.G.Third d`), with the base case's number of positions (`D.t = t`), the
    bound 1 (`D.L = 1`) and an evader that evades (`D.Z.OK`), is a test within a third (`D.In3`).
  `M.Third d t`: a standard oracle message (Cb/Obj/LdObjectToyKit.lean): laws, distance d, 3 e < d,
    transparent, the encoding hides t long positions, the placement `M.plc` and the pad's
    coefficients `M.b` are injective, and no `M.b β` is 0. `Spec.ldStd3_msg`: then `M.OK 1 t`.
  `D.Third` (`StdPO`): the standard plan of three base cases over a test O
    (Cb/Obj/LdObjectPartPlan.lean): every oracle message as read at the common positions: laws,
    distance d, transparent, "er implies its own radius"; 3 er < d; the numbers bad = er + 1,
    L2 = 1, Lc = 1.
  `Spec.ldStd3_plan`: then, for P non-empty, its three tests are within a third.
  `D.Third t` (`StdLk`): the link with standard parts (Cb/Obj/LdObjectLinkStd.lean): its message
    `M.Third D.d t`; bad = e + 1, L2 = 1, Lc = 1.
  `Spec.ldStd3_link`: then, for P and `Fin Cf.C₀.n` non-empty, its sending at the bound 1 meets
    `S.Third` (Cb/Obj/LdObjectThirdTests.lean), and its closing's test is within a third.

Notation: `bad`, `L2`, `Lc` (of `StdPO`): natural numbers (`StdPO.Hyp`,
Cb/Obj/LdObjectPartPlan.lean, asks, of every `C : LdCode E P` with `C.Laws`, `C.MCAat er bad`, and
with `C.Dist d` too, `C.ListAt er L2` and `C.ListAt er Lc`).

Limits: this file does not say that such codes exist.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectThirdProofs
import Cb.Obj.LdObjectPartPlanProofs
import Cb.Obj.LdObjectLinkStd

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- A standard oracle message within a third. -/
structure StdM.Third {E P : Type} [Fintype P] [Field E] [Fintype E] (M : StdM E P) (d t : ℕ) :
    Prop where
  laws : M.Cm.Laws
  dist : M.Cm.Dist d
  lt   : 3 * M.e < d
  tr   : M.Cm.Transparent
  zk   : M.Cm.Zk t
  plc  : Function.Injective M.plc
  inj  : Function.Injective M.b
  ne0  : ∀ β, M.b β ≠ 0

/-- The standard plan within a third. -/
structure StdPO.Third {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {O : LdOL F E}
    {P : Type} [Fintype P] (D : StdPO O P) : Prop where
  laws : ∀ o, ((O.toC.S.om o).C.atPos (D.posAll o)).Laws
  dist : ∀ o, ((O.toC.S.om o).C.atPos (D.posAll o)).Dist D.d
  tr   : ∀ o, ((O.toC.S.om o).C.atPos (D.posAll o)).Transparent
  fits : ∀ o (f g : (O.toC.S.om o).C.Word),
    ((O.toC.S.om o).C.atPos (D.posAll o)).Near D.er f g → (O.toC.S.om o).C.Near (O.toC.S.om o).e f g
  lt   : 3 * D.er < D.d
  bad  : D.bad = D.er + 1
  l2   : D.L2 = 1
  lc   : D.Lc = 1

/-- The link with standard parts within a third. -/
structure StdLk.Third {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
    {P : Type} [Fintype P] (D : StdLk Cf P) (t : ℕ) : Prop where
  msg : D.M.Third D.d t
  bad : D.bad = D.M.e + 1
  l2  : D.L2 = 1
  lc  : D.Lc = 1

namespace Spec

/-- The base case alone. -/
def ldStd3_base : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (t d : ℕ)
      (cov : (D.G.joint D.Sb D.sl D.Z).C.NP → (D.G.joint D.Sb D.sl D.Z).P),
    D.T = ldBaseEnd (D.G.joint D.Sb D.sl D.Z) t cov d (D.G.e + 1) 1 → D.t = t → D.L = 1 →
    D.G.Third d → D.Z.OK → D.In3

def ldStd3_msg : Prop :=
  ∀ (E P : Type) [Fintype P] [Field E] [Fintype E] (M : StdM E P) (d t : ℕ), M.Third d t → M.OK 1 t

section
variable (F E : Type) [Field F] [Field E] [Fintype E] [Algebra F E]

/-- The three tests of the standard plan. -/
def ldStd3_plan : Prop :=
  ∀ (O : LdOL F E) (P : Type) [Fintype P] [Nonempty P] (D : StdPO O P),
    D.Third → D.T.D₁.In3 ∧ D.T.D₂.In3 ∧ D.X.run.In3

/-- The link with standard parts. -/
def ldStd3_link : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P]
      (D : StdLk Cf P) (t : ℕ),
    D.Third t → (D.S 1 t).Third (fun _ => D.d) ∧ D.Kc.run.In3

end
end Spec

theorem ldStd3_base : Spec.ldStd3_base := by
  intro E _ _ S D t d cov hT ht hL hG hZ
  refine ⟨.plain (.base _ t cov d), d, hT, ht, hL, hG, hZ, ?_⟩
  exact ⟨ld_laws_fam E D.G.P _ _ hG.laws, ld_dist_fam _ d hG.dist, hG.lt, ld_transp_fam _ hG.transp⟩

theorem ldStd3_msg : Spec.ldStd3_msg := fun E P _ _ _ M d t h =>
  ⟨h.laws, ld_list_unique E P M.Cm d M.e h.laws h.dist (by have := h.lt; omega),
    h.zk, h.plc, h.inj, h.ne0⟩

section
variable (F E : Type) [Field F] [Field E] [Fintype E] [Algebra F E]

theorem ldStd3_plan : Spec.ldStd3_plan F E := by
  intro O P _ _ D h
  refine ⟨?_, ?_, ?_⟩
  · refine ldStd3_base E _ D.T.D₁ D.tb₁ D.d (fun _ => Classical.arbitrary P) ?_ rfl h.lc
      ⟨fun a => h.laws a.1, fun a => h.dist a.1, fun a => h.tr a.1,
        h.lt, fun a f g hn => h.fits a.1 f g hn⟩ ?_
    · show ldBaseEnd _ D.tb₁ _ D.d D.bad D.L2 = ldBaseEnd _ D.tb₁ _ D.d (D.er + 1) 1
      rw [h.bad, h.l2]
    · letI : DecidableEq (D.pl.G₁.Row O.toC.B₁) := Classical.decEq _
      exact ok_indep E (D.pl.G₁.Row O.toC.B₁)
  · refine ldStd3_base E _ D.T.D₂ D.tb₂ D.d (fun _ => Classical.arbitrary P) ?_ rfl h.lc
      ⟨fun a => h.laws a.1.1, fun a => h.dist a.1.1, fun a => h.tr a.1.1,
        h.lt, fun a f g hn => h.fits a.1.1 f g hn⟩ ?_
    · show ldBaseEnd _ D.tb₂ _ D.d D.bad D.L2 = ldBaseEnd _ D.tb₂ _ D.d (D.er + 1) 1
      rw [h.bad, h.l2]
    · letI : DecidableEq (D.pl.G₂.Row LinB₂) := Classical.decEq _
      exact ok_indep E (D.pl.G₂.Row LinB₂)
  · refine ldStd3_base E _ D.X.run D.tb₃ D.d (fun _ => Classical.arbitrary P) ?_ rfl h.lc
      ⟨fun a => h.laws a.1.1.1, fun a => h.dist a.1.1.1, fun a => h.tr a.1.1.1,
        h.lt, fun a f g hn => h.fits a.1.1.1 f g hn⟩ ?_
    · show ldBaseEnd _ D.tb₃ _ D.d D.bad D.L2 = ldBaseEnd _ D.tb₃ _ D.d (D.er + 1) 1
      rw [h.bad, h.l2]
    · letI : DecidableEq (D.G₃.Row {_b : D.BM // True}) := Classical.decEq _
      exact ok_indep E (D.G₃.Row {_b : D.BM // True})

theorem ldStd3_link : Spec.ldStd3_link F E := by
  intro Cf _ P _ _ D t h
  have hM := ldStd3_msg E P D.M D.d t h.msg
  have hS := stdLk_snd D hM
  refine ⟨⟨hS.laws, fun _ => h.msg.dist, fun _ => by have := h.msg.lt; show 2 * D.M.e < D.d; omega,
      fun _ => rfl, hS.fair, hS.ev, hS.snd, hS.bl, hS.hid⟩,
    ?_⟩
  refine ldStd3_base E _ D.Kc.run D.tb D.d (fun _ => Classical.arbitrary P) ?_ rfl h.lc
    ⟨fun _ => h.msg.laws, fun _ => h.msg.dist, fun _ => h.msg.tr, h.msg.lt, fun _ _ _ hn => hn⟩ ?_
  · show ldBaseEnd _ D.tb _ D.d D.bad D.L2 = ldBaseEnd _ D.tb _ D.d (D.M.e + 1) 1
    rw [h.bad, h.l2]
  · letI : DecidableEq (D.G.Row D.K.P.RowB) := Classical.decEq _
    exact ok_indep E (D.G.Row D.K.P.RowB)

end
end Cb
