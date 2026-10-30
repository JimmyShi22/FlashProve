-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Proof.lean: the law of Statement.lean, beside this file, holds.

  `law`: at every list of callers, every caller of the proved block `kBatFoldRide`, every three
    written rounds and six readings: `Law`.

How. `closing_inv` (Inv.lean) reads the yes backwards. From there the steps are those of the
library's proofs at this place (`batFold_tied`, `batFold_tied_rows`), which behind their first lines
speak of rounds of a view and of typed transcripts alone: `Rd.carK_some`, `batFoldRide_out`,
`Rd.Scal.sumOf`, `Rd.Scal.carK_reads`, `batX_horner`, `combine_target`, `first_claim`,
`sClaim_reads`.
No run of the program `verify-on-bytes` takes part: neither the statement nor the proof names its
monad, its context or channel, batVerify or foldVerify. Its pure functions that `closing` calls by
name do (Bat.combine, foldOutput, foldClaimRound; the library's runRows, begun; what these call),
with the library's laws on two of them (`combine_target`; the claim's step in `StepOK`).

Limits: those of
Statement.lean.
-/
import Johnson.Desc.First.Close.Law.Statement
import Johnson.Desc.First.Close.Law.Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Model.Road OnBytes.Tie.Pv.Fold Iop OnBytes.Flat KObj KObj.RowCar
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv
open OnBytes.PscRun (sentOf drawnOf)

/-- **The law of K10 holds**, at every list of callers, caller, written rounds and readings. -/
theorem law (L : List (BatFoldCaller GE)) (c : BatFoldCaller GE) (rB rE rR : Round)
    (ρ : Rd c rB rE rR) : Law L c rB rE rR ρ := by
  intro hS hst hfx P S S' g mask out a τ hk ht h hO hR
  obtain ⟨G, x, row, lay, m, F, vB, v₀, rs, sum, eps, qs, gs, S2, e0, hG, p3, hrow, f2, f3, f4, f5,
    f6⟩ := closing_inv h
  have eV : ρ.V τ = ρ.viewB τ.1 τ.2.1 :: ρ.viewE τ.2.2.1 τ.2.2.2.1 ::
      ρ.vK (Yc c).k τ.2.2.2.2 := rfl
  rw [eV] at e0
  obtain ⟨e1, e0⟩ := List.cons.inj e0
  obtain ⟨e2, e3⟩ := List.cons.inj e0
  have hlen : (ρ.vK (Yc c).k τ.2.2.2.2).length = (Yc c).k := Rd.vK_length ρ _ _
  have hmem : ∀ r ∈ ρ.viewE τ.2.2.1 τ.2.2.2.1 :: ρ.vK (Yc c).k τ.2.2.2.2,
      (ρ.rdCh (drawnOf r)).isSome := fun r hr => ht.2 r (by
    rw [eV]
    show r ∈ (ρ.viewE τ.2.2.1 τ.2.2.2.1 :: ρ.vK (Yc c).k τ.2.2.2.2).take ((Yc c).k + 1)
    rw [List.take_succ_cons, List.take_of_length_le (le_of_eq hlen)]
    exact hr)
  obtain ⟨z, gz⟩ := Option.isSome_iff_exists.1 (ht.1 (ρ.viewB τ.1 τ.2.1) (by
    rw [eV]
    show _ ∈ [ρ.viewB τ.1 τ.2.1]
    exact List.mem_singleton.2 rfl))
  obtain ⟨e, ge⟩ := Option.isSome_iff_exists.1 (hmem _ List.mem_cons_self)
  obtain ⟨τk, hτk⟩ := ρ.carK_some (Yc c).k τ.2.2.2.2 fun rv hrv =>
    hmem rv (List.mem_cons_of_mem _ hrv)
  have himg : ρ.carS.tr τ = some (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk) := by
    obtain ⟨m1, c1, m2, c2, t⟩ := τ
    show (ρ.rdZ (drawnOf (ρ.viewB m1 c1))).bind (fun z' =>
      ((ρ.rdCh (drawnOf (ρ.viewE m2 c2))).bind fun e' =>
        ((ρ.carK (Yc c).k).tr t).map fun τ' => (((), ρ.sumOf m2), e', τ')).map fun τ' =>
          (((), ()), z', τ')) = _
    rw [gz, ge, hτk]
    rfl
  obtain ⟨xo, hxo, htg⟩ := batFoldRide_out c hfx a.1 a.2 z (ρ.sumOf τ.2.2.1) e τk
  refine ⟨_, (xo, (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).imp a.2
    (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk)), himg, ?_, ?_⟩
  · exact congrArg (Option.map fun xo' => (xo', (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).imp a.2
      (((), ()), z, ((), ρ.sumOf τ.2.2.1), e, τk))) hxo
  · show xo.1.1 = readE out.target
    have hsum : ρ.sumOf τ.2.2.1 = readE sum := hS.sumOf (ch := τ.2.2.2.1) (by rw [e2]; exact f2)
    have hval : (Yc c).val e = readE eps := hS.val eps e (by
      rw [← drawnOf_one f3, ← e2]
      exact ge)
    have hrd : Reads (Yc c).val (Yc c).n (rd2 c) (Yc c).k τk qs gs :=
      hS.carK_reads (Yc c).k τ.2.2.2.2 qs gs τk (by rw [e3]; exact f4) hτk
    have hx : (batX c a.1 z).1.1 = readE row.target := by
      rw [batX_horner c (hO G x z hG (by rw [e1]; exact p3) gz)]
      have h1 := combine_target rdE (begun S g G) g ⟨lay, runRows S G⟩ x row hrow (hR G hG)
      simp only [rdE_val] at h1
      exact h1.symm
    rw [htg, hx, hsum, hval, ← first_claim, sClaim_reads hst _ _ _ _ _ hrd, f6]
    rfl

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.law
