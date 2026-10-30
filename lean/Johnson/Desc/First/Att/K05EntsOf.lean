-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05EntsOf.lean: kind K5: WHICH ENTRIES THE LAW's RETURNED FORMS NAME: every
entry of the two lists and of the join's form names row 0 of the plan's array of the reads: from the
law's record of returns (Returns, Johnson/Desc/First/Att/K05GatheredZero.lean, WITH ITS FIELD u3),
what the hearing's law says (Said), and three facts on the ledger's array.

IS IT EMPTY HERE? NO MEMBER IS SHOWN.

Main names:
  `U3At A Kc G`: the ledger G has the array A.iU3, as wide as Kc, at least A.nW wide, of one row.
  `ents_of_returns`: **every entry of l₁ ++ l₂ ++ [xj.1] names row 0 of the array A.iU3**, from
    Returns at S := A.S, tl := A.seam.tl, nW := A.nW and the seat's own look · A0.iU3 = A.iU3 · Said
    xr h G Ls · U3At A Kc G · the lookup's closing form names no entry (gL.cEnd.ents = #[]).
CALLED, NOT TYPED ANEW: inAt_is, firstAt_is, secondAt_is
(Johnson/Desc/First/Att/Claims/InAtIs.lean) · heardPlain_of_said, cov_parts, first_named,
second_named (Johnson/Desc/First/Att/Claims/HeardPlain.lean) · row0_of_cov
(Johnson/Desc/First/Att/Claims/CoveredApart.lean) · cov_joinW
(Johnson/Desc/First/Att/K05JoinThere.lean) · the library's keysRun_covered
(Johnson/Desc/First/Att/Claims/CoveredKeys.lean) and joinF_is
(Johnson/Desc/First/Att/Claims/PortJoin.lean). Nothing is claimed on soundness, completeness or
hiding.
-/
import Johnson.Desc.First.Att.K05GatheredZero
import Johnson.Desc.First.Att.K05JoinThere
import Johnson.Desc.First.Att.Claims.InAtIs
import Johnson.Desc.First.Att.Claims.HeardPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open K5Law (inAt_is firstAt_is secondAt_is heardPlain_of_said cov_parts first_named second_named
  row0_of_cov keysRun_covered joinF_is)

/-- The ledger has the plan's array of the reads, at the law's width, of one row. -/
def U3At (A : Attention.Plan) (Kc : ℕ) (G : Fork) : Prop :=
  ∃ T, G.trees[A.iU3]? = some T ∧ T.K = Kc ∧ A.nW ≤ T.K ∧ T.R = 1

/-- **Every entry of the returned forms names row 0 of the array A.iU3.** -/
theorem ents_of_returns {A A0 : Attention.Plan} {gL : Forest.Heard} {G Fj : Fork} {h : Heard}
    {l : Left} {i : Runs.In} {Kc : ℕ} {l₁ l₂ : List Aff} {jn : Runs.JoinsP} {k3 : Runs.PadIn}
    {kf : Array Aff} {tj : OnBytes.K.Kc.Tape} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    {xr : Params.AttentionRounds} {Ls : Lists}
    (Rt : Returns A.S gL.zx gL.zk G h l A0 gL i Kc l₁ l₂ jn k3 kf Fj tj xj A.seam.tl A.nW
      (lookOfO (parCOf A).geo.lmb gL))
    (hA : A0.iU3 = A.iU3) (hs : Said xr h G Ls) (hU : U3At A Kc G) (hc : gL.cEnd.ents = #[]) :
    ∀ f ∈ l₁ ++ l₂ ++ [xj.1], ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0 := by
  obtain ⟨T, hT, hK, hW, _⟩ := hU
  have hp := heardPlain_of_said hs
  have u3 : i.iU3 = A.iU3 := Rt.u3.trans hA
  have eIn := inAt_is A Rt.left Rt.geo Rt.zkI u3 Rt.points Rt.tables hT hK
  intro f hf y hy
  rcases List.mem_append.1 hf with hf | hf
  · rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨a, b, _⟩ := first_named (c := parCOf A)
        (firstAt_is A Rt.left Rt.geo Rt.zkI u3 Rt.points Rt.tables hT hK Rt.first) hp hT hW f hf y hy
      exact ⟨a, b⟩
    · obtain ⟨a, b, _⟩ := second_named (c := parCOf A)
        (secondAt_is A Rt.left Rt.geo Rt.zkI u3 Rt.points Rt.tables hT hK Rt.second) hp hT hW f hf y
        hy
      exact ⟨a, b⟩
  · rw [List.mem_singleton.1 hf, (joinF_is Rt.join).1] at hy
    obtain ⟨hL, hR⟩ := cov_parts eIn hp
    have hC := cov_joinW (g := gL) (keysRun_covered hL hR Rt.first Rt.keys) hc
    obtain ⟨a, b, _⟩ := row0_of_cov (hK ▸ hW) (hC y hy)
    exact ⟨a.trans u3, b⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.ents_of_returns
