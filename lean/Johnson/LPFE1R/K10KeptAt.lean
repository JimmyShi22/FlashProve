-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/K10KeptAt.lean: THE FIELD "kept" OF AtMgA.K10Left
(Johnson/P5J/K10Left.lean), TO THE LETTER, FROM THE ONE HEAD AtMg ALONE. A joining: nothing is
evaluated here.

  P5J.AtMg.kept    at each m < 25: every tenant of (At.N Zp cF).keptOf m stands in
                   (At.N Zp cF).group m: by AtMg.N_core (Johnson/P5T/CoreAtMg.lean: the numbers'
                   sent and keptOf are the written core's) and kept_full
                   (Link/Law/KeptInGroup.lean: the kernel)
  P5J.k10_kept_at  **the field kept**

Limits. IT STANDS OVER THE VERIFIER's LIST OF ENTRY TESTS OF THIRTEEN ROWS (through AtMg.N_core;
GLOSSARY.md, "entry tests"). The full size alone. No soundness statement.

-/
import Johnson.P5T.CoreAtMg
import Johnson.Desc.First.Link.Law.KeptInGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain Place KindName)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.LinkJoin (keptIn_of_B kept_full k10_link_lt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- What the next segment keeps lies in its own segment's group, at the numbers in which a kind's
law ends. -/
theorem AtMg.kept (h : AtMg o Z D r Zp Np cF) :
    ∀ m < 25, ∀ t ∈ (At.N Zp cF).keptOf m, t ∈ (At.N Zp cF).group m := by
  intro m hm t ht
  obtain ⟨e1, e2, -⟩ := h.N_core
  unfold VerifiableInference.Desc.First.Numbers.group
  rw [e1]
  rw [e2] at ht
  exact keptIn_of_B kept_full m hm t ht

/-- **K10Left's FIELD kept, TO THE LETTER.** -/
theorem k10_kept_at (h : AtMg o Z D r Zp Np cF) :
    ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
      ∀ t ∈ (At.N Zp cF).keptOf (a.link.getD 0), t ∈ (At.N Zp cF).group (a.link.getD 0) :=
  fun _ a ha hk => h.kept _ (k10_link_lt (List.mem_of_getElem? ha) hk)

end P5J

#print axioms P5J.AtMg.kept
#print axioms P5J.k10_kept_at
