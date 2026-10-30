-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectOnBStd2Close.lean: for toys: the closing of the test for linear constraints with
standard parts, over a preamble that leaves a family, for at most N instances: all that the whole
test asks of its closing, under the hypotheses of `Spec.std2B_close`.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation; it follows a preamble (Hiop/RecSubs.lean, Hiop/RecBuild.lean).

Definitions, statements (Cb.Spec.std2B_*) and proofs. A tool for guards against empty theorems; no
parameter of a protocol.

The plan and its three whole tests are those of Cb/Obj/LdObjectLinStd2.lean, unchanged. For a
batch (W, G_u, Ω: Cb/Obj/LdObjectLinStd2.lean):
  the first test (G_u and Ω): once, by the shared part of the prover;
  the second (Ω, W, the slot's message of index masks): in every slot;
  the third (all that the preamble left to the slot, with the rows that it filed, `D.slM`, `D.xM`):
    in every slot.
  What the preamble left is a slot's own (Cb/Ld/LdLinCloseDemandV.lean: `C.isSh`: shared are the
    oracle messages sent with G_u and with Ω).

Main names:
  `D.cZV N L tW tU tO ba x₀`: the closing for a batch with its honest side
    (Cb/Ld/LdLinCloseVLin.lean: `T.cZV`).
  `D.HypB N L tW tU tO ba`: `D.Hyp` (one instance), and one more number: tb₁ + N · tb₂ ≤ tO: Ω is
    in the shared test and in the second test of each of the N slots. (All else is read in one
    slot, or once.)
  `Spec.std2B_one` (at N = 1 the one more number is `D.Hyp`'s own), `std2B_shared`, `std2B_behind`,
    `std2B_kb`, `std2B_honest`: as in Cb/Obj/LdObjectOnBStd.lean and Cb/Obj/LdObjectOnBStdV.lean,
    `std2B_behind` and `std2B_honest` at the bound ba on the oracles left.
  `Spec.std2B_close`: the index code and P have a position (`Nonempty (Fin Cf.C₀.n)`,
    `Nonempty P`), values x₀ and of `(D.C.E₀.prod D.C.S.ext).Str`, `D.HypB` ⇒ the six conditions on
    the closing of Cb/Ld/LdLinBHonTop.lean's `ldLinT_all`, said of `D.cZV`:
    its links stand behind every chain and have the budgets' halves from q5 (one instance)
    (`OkFrom`, `SidesCT`);
    its annotated links are knowledge sound from the key after the challenge ζ, `D.C.P.key6`
    (Cb/Ld/LdLinChainB.lean); it stands behind every chain of batch links that ends where the core
    ends (`OkFromV`); its annotations are coherent (`Coh`); nothing follows
    (`∀ Jn, (D.QV3 N).VT.q Jn fun _ => ∅`).

Limits: this file does not say that `D.HypB` can be met. It says nothing on the senders' and the
core's conditions. No splitting.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinStd2Proofs
import Cb.Ld.LdLinCloseVLinProofs
import Cb.Ld.LdBatchPlanLin
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace StdLn2
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] [Nonempty P] (D : StdLn2 Cf P)

/-- nothing is left -/
def nil3 : LdTcA (D.pl.S₂.sub D.D₃.kp) D.C.E₀ D.C.Wpa :=
  LdTcA.nil (D.pl.S₂.sub D.D₃.kp) D.C.E₀ D.C.Wpa (fun a => a.2.elim, ())

/-- what closes the rest of the plan (`D.T.Q'`), for a batch: the third test in every slot; then
nothing is left -/
def rest3 : LdTcA D.pl.S₂ D.C.E₀ D.C.Wpa :=
  LdTcA.consLo D.D₃ D.nil3 (fun _ => (fun _ => 0, fun _ => 0), ())
    ((fun _ => 0, fun _ => 0), (fun a => a.2.elim, ()))

/-- The plan for a batch. -/
def QA : LdTcA D.C.S D.C.E₀ D.C.Wpa := D.T.QA D.rest3.cA D.rest3.same

/-- what the rest needs of each oracle message -/
def b₃ (N : ℕ) : D.pl.S₂.O → ℕ := D.D₃.needV N (fun a => D.C.isSh a.1.1) fun _ => 0

variable [Nonempty (Fin Cf.C₀.n)]

/-- the demand on families of positions when nothing is left -/
def q4 (N : ℕ) : QFam (D.C.E₀.prod (D.pl.S₂.sub D.D₃.kp).ext) N :=
  (D.pl.S₂.sub D.D₃.kp).qV (fun a => D.C.isSh a.1.1.1) (QFam.each fun _ => True) fun _ => 0

/-- the honest side of "nothing is left" -/
def QV4 (N : ℕ) : LdTcV N D.nil3 ⟨D.C.P.Sh6, fun _ _ _ _ => True, D.q4 N⟩ :=
  LdTcV.nil (D.pl.S₂.sub D.D₃.kp) D.C.E₀ D.C.Wpa (fun a => a.2.elim, ()) _

/-- the honest side of the rest -/
def QV3 (N : ℕ) :
    LdTcV N D.rest3 ⟨D.C.P.Sh6, fun _ _ _ _ => True, D.pl.qB₂ N (fun _ => True) (D.b₃ N)⟩ :=
  LdTcV.consLo D.D₃ D.nil3 (fun _ => (fun _ => 0, fun _ => 0), ())
    ((fun _ => 0, fun _ => 0), (fun a => a.2.elim, ()))
    ⟨D.C.P.Sh6, fun _ _ _ _ => True, D.pl.qB₂ N (fun _ => True) (D.b₃ N)⟩
    (fun _ _ _ _ => True) (D.q4 N) (D.QV4 N)

/-- The closing for a batch, with its honest side. -/
def cZV (N L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) (x₀ : D.T.St₁ × D.C.S.Smp) :
    ChainV Unit N (D.C.P.V6 (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) N)
      (D.QV3 N).VT :=
  D.T.cZV N (fun _ => True) (D.b₃ N) (fun _ _ _ _ => True) D.rest3.cA D.rest3.same (D.Sn L tW tU tO)
    (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) x₀ (D.QV3 N)

omit [Nonempty P] [Nonempty (Fin Cf.C₀.n)] in
/-- The conditions for a batch. -/
structure HypB (N L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) : Prop where
  hyp  : D.Hyp L tW tU tO ba
  posO : D.tb₁ + N * D.tb₂ ≤ tO

end StdLn2

namespace Spec
section
variable (F E : Type) [Field F] [Field E] [Fintype E] [Algebra F E]

def std2B_one : Prop :=
  ∀ (Cf : LdCf F E) (P : Type) [Fintype P] (D : StdLn2 Cf P) (L tW tU tO : ℕ) (ba : D.Sa.O → ℕ),
    D.Hyp L tW tU tO ba → D.HypB 1 L tW tU tO ba

def std2B_shared : Prop := ∀ (Cf : LdCf F E) (P : Type) [Fintype P] (D : StdLn2 Cf P), D.pl.Shared

/-- States, under the hypotheses below: the closing stands behind every chain, and its budgets fit
(one instance). -/
def std2B_behind : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn2 Cf P)
      (L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) (A : Joint Unit) (c₀ : Chain Unit A D.C.j6J),
    D.Hyp L tW tU tO ba →
    (D.C.cZ D.T.Q D.T.fq).OkFrom c₀ ∧
    (D.C.cZ D.T.Q D.T.fq).SidesCT
      (D.C.P.q5 (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba))

/-- States, under the hypotheses below: the closing is knowledge sound from the key after the
challenge ζ, `D.C.P.key6`. -/
def std2B_kb : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn2 Cf P)
      (L tW tU tO N : ℕ) (ba : D.Sa.O → ℕ),
    D.Hyp L tW tU tO ba → (D.C.cZA D.QA D.T.fq).KB N D.C.P.key6 ldKeyT

/-- States, under the hypotheses below: the honest side of the rest meets its conditions
(`LdTcV.OK`, Cb/Ld/LdLinCloseVPlan.lean). -/
def std2B_rest : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn2 Cf P)
      (L tW tU tO N : ℕ) (ba : D.Sa.O → ℕ),
    D.Hyp L tW tU tO ba → (D.QV3 N).OK

/-- The honest side of a batch. -/
def std2B_honest : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P]
      (D : StdLn2 Cf P) (N L tW tU tO : ℕ) (ba : D.Sa.O → ℕ)
      (x₀ : D.T.St₁ × D.C.S.Smp) (_ : (D.C.E₀.prod D.C.S.ext).Str),
    D.HypB N L tW tU tO ba →
    (∀ (Z : Joint Unit) (VZ : JV N Z)
          (c₀ : ChainV Unit N VZ
            (D.C.P.V6 (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) N)),
        (D.cZV N L tW tU tO ba x₀).OkFromV c₀) ∧
    (D.cZV N L tW tU tO ba x₀).forget.Coh ∧
    (∀ Jn, (D.QV3 N).VT.q Jn fun _ => ∅) ∧
    (D.cZV N L tW tU tO ba x₀).forget = D.C.cZA D.QA D.T.fq ∧
    (D.cZV N L tW tU tO ba x₀).forget.forget = D.C.cZ D.T.Q D.T.fq

/-- The six conditions on the closing. -/
def std2B_close : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P]
      (D : StdLn2 Cf P) (N L tW tU tO : ℕ) (ba : D.Sa.O → ℕ)
      (x₀ : D.T.St₁ × D.C.S.Smp) (_ : (D.C.E₀.prod D.C.S.ext).Str),
    D.HypB N L tW tU tO ba →
    (∀ (A : Joint Unit) (c₀ : Chain Unit A D.C.j6J),
      (D.cZV N L tW tU tO ba x₀).forget.forget.OkFrom c₀) ∧
    (D.cZV N L tW tU tO ba x₀).forget.forget.SidesCT
      (D.C.P.q5 (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba)) ∧
    (D.cZV N L tW tU tO ba x₀).forget.KB N D.C.P.key6 ldKeyT ∧
    (∀ (Z : Joint Unit) (VZ : JV N Z)
          (c₀ : ChainV Unit N VZ
            (D.C.P.V6 (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) N)),
        (D.cZV N L tW tU tO ba x₀).OkFromV c₀) ∧
    (D.cZV N L tW tU tO ba x₀).forget.Coh ∧
    ∀ Jn, (D.QV3 N).VT.q Jn fun _ => ∅

end
end Spec

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] [Nonempty P] {D : StdLn2 Cf P}

/-- what the three tests need of each oracle message, in a batch -/
theorem std2B_needA (N : ℕ) (a : D.Sa.O) :
    D.T.D₁.need (D.T.D₂.needV N (fun a => D.C.isSh a.1) (D.b₃ N)) (D.nA a) =
      (if a = D.iM then D.tb₂ else 0) + D.tb₃ := by
  simp [LdRunD.need, LdRunD.needV, StdLn2.isA, LdLinC.isSh, StdLn2.b₃]

theorem std2B_needW (N : ℕ) :
    D.T.D₁.need (D.T.D₂.needV N (fun a => D.C.isSh a.1) (D.b₃ N)) D.C.nW = D.tb₂ := by
  simp [LdRunD.need, LdRunD.needV, StdLn2.isA, LdLinC.isSh]

theorem std2B_needU (N : ℕ) :
    D.T.D₁.need (D.T.D₂.needV N (fun a => D.C.isSh a.1) (D.b₃ N)) D.C.nU = D.tb₁ := by
  simp [LdRunD.need]

theorem std2B_needO (N : ℕ) :
    D.T.D₁.need (D.T.D₂.needV N (fun a => D.C.isSh a.1) (D.b₃ N)) D.C.nO = D.tb₁ + N * D.tb₂ := by
  simp [LdRunD.need, LdRunD.needV, StdLn2.isA, LdLinC.isSh]

end

section
variable (F E : Type) [Field F] [Field E] [Fintype E] [Algebra F E]

theorem std2B_one : Spec.std2B_one F E := fun _ _ _ _ _ _ _ _ _ h =>
  ⟨h, by rw [Nat.one_mul]; exact h.posO⟩

theorem std2B_shared : Spec.std2B_shared F E := by
  intro Cf P _ D o ho
  rcases ho with rfl | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

theorem std2B_behind : Spec.std2B_behind F E := fun _ _ _ _ _ D _ _ _ _ _ A c₀ h =>
  ldLinCl_chain E _ _ _ _ D.C D.T.Q D.T.fq _ A c₀ std2_says (std2_q h) (std2_demand h)

theorem std2B_kb : Spec.std2B_kb F E := fun _ _ _ _ _ D _ _ _ _ N _ h =>
  ldPlanLin_kb E _ _ _ _ D.C D.pl D.T D.rest3.cA D.rest3.same N (std2B_shared F E _ _ D)
    std2_rest std2_saysA (std2_d1 h) (std2_d2 h)
    (ldPlanB_cons_local E _ _ _ D.D₃ D.nil3 _ _ N (ldKeyU _) (ldKeyU _) id (std2_d3 h)
      (ldPlanB_nil E _ _ _ _ N _) fun _ _ _ _ => rfl)

theorem std2B_rest : Spec.std2B_rest F E := by
  intro Cf _ P _ _ D L tW tU tO N ba h
  refine ldPlanV_cons_local E _ _ _ N D.D₃ D.nil3 _ _
    ⟨D.C.P.Sh6, fun _ _ _ _ => True, D.pl.qB₂ N (fun _ => True) (D.b₃ N)⟩ (fun _ _ _ _ => True)
    (D.q4 N) (D.QV4 N) (std2_d3 h) ?_ (fun _ _ _ _ => trivial) ?_ ?_
  · exact ldPlanV_nil E _ _ _ _ N _ fun Jn => ldDemandV_empty E _ _ N _ _ _ (fun _ _ => trivial) Jn
  · exact ldRunV_bears_local E _ D.D₃ _ _ _ _ _ _ N _ _ (std2_d3 h)
      (ldDemandV_local E _ D.D₃ _ _ _ _ _ _ N (fun a => D.C.isSh a.1.1) (QFam.each fun _ => True)
        (fun _ => 0) _ (std2_d3 h))
  · exact ldDemandV_her E _ _ N _ _ _ ((qfam_her _ extNone N).1 _)

theorem std2B_honest : Spec.std2B_honest F E := by
  intro Cf _ P _ _ D N L tW tU tO ba x₀ y₀ h
  exact ldLinVL_all E _ _ _ _ D.C D.pl D.T N (fun _ => True) (D.b₃ N) (fun _ _ _ _ => True)
    D.rest3.cA D.rest3.same x₀ y₀ (D.QV3 N) (D.Sn L tW tU tO)
    (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) ba (std2B_shared F E _ _ D) std2_rest std2_saysA
    (std2_d1 h.hyp) (std2_d2 h.hyp) (std2B_rest F E Cf P D L tW tU tO N ba h.hyp)
    (fun _ _ _ _ => trivial) (fun _ hW => hW)
    (fun a => le_of_eq_of_le (std2B_needA N a) (h.hyp.posA a))
    (fun _ => le_of_eq_of_le (std2B_needW N) h.hyp.posW)
    (fun _ => le_of_eq_of_le (std2B_needU N) h.hyp.posU)
    (fun _ => le_of_eq_of_le (std2B_needO N) h.posO)

theorem std2B_close : Spec.std2B_close F E := by
  intro Cf _ P _ _ D N L tW tU tO ba x₀ y₀ h
  obtain ⟨h1, h2, h3, h4, h5⟩ := std2B_honest F E Cf P D N L tW tU tO ba x₀ y₀ h
  refine ⟨fun A c₀ => ?_, ?_, ?_, h1, h2, h3⟩
  · have h6 := (std2B_behind F E Cf P D L tW tU tO ba A c₀ h.hyp).1
    rw [← h5] at h6
    exact h6
  · have h6 := (std2B_behind F E Cf P D L tW tU tO ba _
      (Chain.one
        (⟨IOR.pure some (ExtMap.id _),
          IOR.Honest.pure _ _ (fun a => a),
          fun _ _ w => w,
          IOR.Nums.pure Unit _ _⟩ : Link Unit D.C.j6J D.C.j6J)) h.hyp).2
    rw [← h5] at h6
    exact h6
  · have h6 := std2B_kb F E Cf P D L tW tU tO N ba h.hyp
    rw [← h4] at h6
    exact h6

end
end Cb
