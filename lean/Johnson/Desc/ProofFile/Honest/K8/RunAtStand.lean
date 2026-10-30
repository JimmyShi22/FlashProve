-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/RunAtStand.lean: THE SMALLNESS TEST: AT A STAND OF THE BATCHING
(`BatStand`, Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean, another house's file) THE RUN
"K8.equations" HAS SAID YES INSIDE THE GATHERER: FETCHED, WITH WHATEVER SENTENCE THE DRAW LAYS AND
EACH RUN OF THE ORDER HANDS ON. General in the thread and in that sentence. A lemma; none of the
library's goals.

  **`run_at_stand`**   K8At Lk k pW → at a stand, for every sentence I on states: (the draw's yes
                   from s lays I) → (each run that the order names hands I on) → ∃ e front q tl' F1
                   cls, I e ∧ partOf e = some q ∧ equations front q.tl q.funs q.F = .ok (tl', F1,
                   cls)
  `run_at_stand_num`   at I e := K9L.numOf u e = K9L.numOf u s: so the run's data, blanked, and its
                   list of tables are those of the state in front of the batching
By the other house's `gather_ran` and `ran_inv` (Johnson/Desc/ProofFile/Honest/K9/GatherFold.lean)
and the library's `sits_equations` (Johnson/Desc/First/TailClaims/K8Sits.lean): the road of
`counts_front` (Johnson/Desc/ProofFile/Honest/K8/CountsFrontK8.lean), cut free of the counts.
Limits. WHICH state e is, beyond I, is not said: it lies behind the draw and the runs that stand in
front of the kind's entry in the order. `K8At` and the two premises on I are premises.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.CountsFrontK8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (K8Part equations)
open VerifiableInference.Desc.First.TailClaims.Law (blank partOf sits_equations)
open VerifiableInference.Desc.First.K8.Honest (parts_of)
open ProofFile.Honest.K9 (BatStand gathered gather_ran ran_inv k8Entry drawnOne)

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts} {Lk : Link S Claim} {p : Desc.K9.Where}
  {T : Thread Bk S Claim V W X Pb} {b : Nat}

/-- **The run's yes, fetched out of the gatherer's.** -/
theorem run_at_stand {k : Desc.K9.SegSort} {pW : K8.ParW} (hK : K8At Lk k pW)
    {κ : Coins Bk} {s : S} {m : Mid W X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List Desc.OpenedColumn} {s' : S} {x : E}
    {z : S × Desc.K9.Part × List Claim} {G : Fork}
    (hS : BatStand Lk p T b κ s m En ds y cols s' x z G) (I : S → Prop)
    (hD : ∀ t₁,
      (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
        I t₁)
    (hR : ∀ o ∈ Lk.order, ∀ run, LinkJoin.At Lk o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      I e → I e₁) :
    ∃ (e : S) (front : Nat) (q : K8Part) (tl' : HTailF2) (F1 : Fork) (cls : List Claim),
      I e ∧ partOf e = some q ∧ equations front q.tl q.funs q.F = .ok (tl', F1, cls) := by
  have hg := hS.bat.gathered
  cases hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] with
  | error e => simp [gathered, hd] at hg
  | ok t₁ =>
    cases hy : claimsInBy Lk.each Lk.hear Lk.order t₁ with
    | error e => simp [gathered, hd, hy] at hg
    | ok yy =>
      obtain ⟨ls, -, hRan⟩ := gather_ran Lk.each Lk.hear Lk.order t₁ yy hy
      obtain ⟨hAll, -⟩ := ran_inv Lk.hear I Lk.order 0 t₁ ls yy.2
        (fun o ho run hr n t zz hI hz => hR o ho run hr n t zz.1 zz.2 hz hI) (hD t₁ hd) hRan
      obtain ⟨l, run, n, e, zz, hr, hI, hz, -⟩ := forall₂_left hAll (k8Entry k) hK.1
      obtain ⟨runK, h8, hu⟩ := hK.2 run hr
      obtain ⟨q, tl', F1, hq, he, -⟩ :=
        (sits_equations pW runK h8 n e zz.2 zz.1).1 (hu n e zz hz)
      exact ⟨e, _, q, tl', F1, zz.1, hI, hq, he⟩

/-- At the three numbers: the run's data, blanked, and its tables are those in front. -/
theorem run_at_stand_num (u : HTailF2) {k : Desc.K9.SegSort} {pW : K8.ParW} (hN : NumRun Lk u)
    (hDn : NumDraw p u) (hK : K8At Lk k pW)
    {κ : Coins Bk} {s : S} {m : Mid W X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List Desc.OpenedColumn} {s' : S} {x : E}
    {z : S × Desc.K9.Part × List Claim} {G : Fork}
    (hS : BatStand Lk p T b κ s m En ds y cols s' x z G) :
    ∃ (front : Nat) (q : K8Part) (tl' : HTailF2) (F1 : Fork) (cls : List Claim),
      s.tl?.map (blank u) = some (blank u q.tl) ∧ S.funs? s = some q.funs ∧
        equations front q.tl q.funs q.F = .ok (tl', F1, cls) := by
  obtain ⟨e, front, q, tl', F1, cls, hI, hq, he⟩ := run_at_stand hK hS
    (fun e => K9L.numOf u e = K9L.numOf u s) (fun t₁ h => hDn s x t₁ h)
    fun o ho run hr n e c e₁ hz hI => (hN o ho run hr n e c e₁ hz).trans hI
  obtain ⟨ht, hf, -⟩ := parts_of hq
  have hI' : K9L.numOf u e = K9L.numOf u s := hI
  have e1 : e.tl?.map (blank u) = s.tl?.map (blank u) := congrArg (·.1) hI'
  have e2 : e.funs? = s.funs? := congrArg (·.2.1) hI'
  refine ⟨front, q, tl', F1, cls, ?_, e2.symm.trans hf, he⟩
  rw [← e1, ht]
  rfl

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.run_at_stand
#print axioms ProofFile.Honest.K8.run_at_stand_num
