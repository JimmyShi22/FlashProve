-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectOnBStd.lean: for toys: the test for linear constraints on the encoded index with
standard parts, for at most N instances: what the batch asks beside one instance, first half.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation. In a session it runs on a batch of at most N instances that share the encoded
index.

Definitions, statements (Cb.Spec.stdLnB_*) and proofs. A tool for guards against empty theorems; no
parameter of a protocol.
It builds on Cb/Obj/LdObjectLinStd.lean (`D : StdLn Cf P`; `D.Hyp` are conditions on codes, sample
maps and numbers).

The statements on the test for a batch (Cb/Obj/LdObjectOnBTerm.lean: `Spec.ldOnT_object`,
`Spec.ldOnT_object_far`) require, beside what one instance asks:
  (1) the senders of the second and third family read the vector that they send, and nothing else
    of the witness (`Sn.Apart`);
  (2) the closing stands behind the core and its budgets fit (one instance) (`OkFrom`, `SidesCT`);
  (3) the closing is knowledge sound from the key after the challenge ζ, `D.C.P.key6`
    (Cb/Ld/LdLinChainB.lean, `ChainA.KB`: link by link, for the vectors of at most N statements with
    one key) (batch, sound);
  (4) the closing's honest side for sets of slots: behind the core, coherent annotations, nothing
    follows (`∀ Jn, VT.q Jn fun _ => ∅`) (batch, honest).
  (not all hypotheses are named here: see the two statements)
Here (1), (2), (3), for every N, from `D.Hyp`. (4) is in the second half
(Cb/Obj/LdObjectOnBStdV.lean).

Main names:
  `D.rest0`, `D.QA`: what closes the rest of the plan, `D.T.Q'` (nothing is left: one link without
    rounds), and the plan for a batch (Cb/Ld/LdBatchPlanLin.lean): the first test (G_u and Ω) once,
    by the shared part; the second (Ω and W) in every slot (W, G_u, Ω: Cb/Obj/LdObjectLinStd.lean).
  `Spec.stdLnB_apart`: (1).
  `Spec.stdLnB_shared`: every member of the first group is a shared oracle message.
  `Spec.stdLnB_behind`: (2), at the bound "anything" on the oracles left: the preamble leaves
    nothing here.
  `Spec.stdLnB_kb`: (3).
  (2) and (3) also require that the index code and P have a position (`Nonempty (Fin Cf.C₀.n)`,
    `Nonempty P`).

Limits: this file does not say that `D.Hyp` can be met (Cb/Obj/LdObjectLinToy.lean). It says
nothing on the honest side of a batch.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinStd
import Cb.Ld.LdBatchPlanLin
import Cb.Ld.LdLinChainFresh
import Cb.Ld.LdLinCloseLinProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace StdLn
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] [Nonempty P] (D : StdLn Cf P)

/-- what closes the rest of the plan (`D.T.Q'`), for a batch: nothing is left -/
def rest0 : LdTcA D.pl.S₂ D.C.E₀ D.C.Wpa := LdTcA.nil _ _ _ (fun a => a.2.elim, ())

/-- The plan for a batch. -/
def QA : LdTcA D.C.S D.C.E₀ D.C.Wpa := D.T.QA D.rest0.cA D.rest0.same

end StdLn

namespace Spec
section
variable (F E : Type) [Field F] [Field E] [Fintype E] [Algebra F E]

def stdLnB_apart : Prop :=
  ∀ (Cf : LdCf F E) (P : Type) [Fintype P] (D : StdLn Cf P) (L tW tU tO : ℕ),
    (D.Sn L tW tU tO).Apart

def stdLnB_shared : Prop := ∀ (Cf : LdCf F E) (P : Type) [Fintype P] (D : StdLn Cf P), D.pl.Shared

/-- States, under the hypotheses below: the closing stands behind every chain, and its budgets
fit. -/
def stdLnB_behind : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn Cf P)
      (L tW tU tO : ℕ) (A : Joint Unit) (c₀ : Chain Unit A D.C.j6J),
    D.Hyp L tW tU tO →
    (D.C.cZ D.T.Q D.T.fq).OkFrom c₀ ∧
    (D.C.cZ D.T.Q D.T.fq).SidesCT (D.C.P.q5 (D.Sn L tW tU tO) fun _ => True)

/-- States, under the hypotheses below: the closing is knowledge sound from the key after the
challenge ζ, `D.C.P.key6` (`ChainA.KB`, Cb/Ld/LdLinChainB.lean: link by link, for the vectors of at
most N statements with one key). -/
def stdLnB_kb : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P]
      (D : StdLn Cf P) (L tW tU tO N : ℕ),
    D.Hyp L tW tU tO → (D.C.cZA D.QA D.T.fq).KB N D.C.P.key6 ldKeyT

end
end Spec

section
variable (F E : Type) [Field F] [Field E] [Fintype E] [Algebra F E]

theorem stdLnB_apart : Spec.stdLnB_apart F E := by
  intro Cf P _ D L tW tU tO
  refine ⟨fun w w' k h => funext fun a => funext fun j => ?_,
    fun w w' k h => funext fun a => funext fun j => ?_⟩
  · show Sum.elim (D.datU w') (fun _ => k a) (D.MU.place.symm j) =
      Sum.elim (D.datU w) (fun _ => k a) (D.MU.place.symm j)
    unfold StdLn.datU
    rw [h]
  · show Sum.elim (D.datO w') (fun _ => k a) (D.MO.place.symm j) =
      Sum.elim (D.datO w) (fun _ => k a) (D.MO.place.symm j)
    unfold StdLn.datO
    rw [h]

theorem stdLnB_shared : Spec.stdLnB_shared F E := by
  intro Cf P _ D o ho
  rcases o with ((e | a) | a) | a
  · exact e.elim
  · exact absurd (by cases a; rfl) ho
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨a, rfl⟩

theorem stdLnB_behind : Spec.stdLnB_behind F E := fun _ _ _ _ _ D _ _ _ _ A c₀ h =>
  ldLinCl_chain E _ _ _ _ D.C D.T.Q D.T.fq _ A c₀ stdLn_says (stdLn_q h) (stdLn_demand h)

theorem stdLnB_kb : Spec.stdLnB_kb F E := fun _ _ _ _ _ D _ _ _ _ N h =>
  ldPlanLin_kb E _ _ _ _ D.C D.pl D.T D.rest0.cA D.rest0.same N (stdLnB_shared F E _ _ D)
    (fun _ _ => by simp [Slf.val])
    ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial, fun _ _ _ => trivial⟩ (stdLn_d1 h)
    (stdLn_d2 h) (ldPlanB_nil E _ _ _ _ N _)

end
end Cb
