-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Terms.lean: THE LAYERS' OWN ROUNDS (K4): hearTerms RETURNS
(OnBytes/Desc/First/K4/Hear.lean: the second token sumcheck). A general law: nothing is evaluated.

  rowsTerms, slotsTerms   the rows of K4's table that it hears; the slots that it takes.
  TermsLeft       what it leaves: the sumcheck's slots by number, which are filled, the number of
                  challenges; every slot of the form KT has been shown; every slot that it takes is
                  filled.
  **hearTerms_returns**   room, a tape of its rows' shape, the point has its coordinates, there is
                  an end value, and ONE TEST ON A SAMPLED VALUE, "coin-zero": the element drawn in
                  the sumcheck's first round is not 0: it returns, with TermsLeft.

Limits. A conditional law. Nothing on values beyond the named test. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.K4.Returns.Norms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc D6.Ret
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc.First.Shape (affSh AffSh)

/-- The rows of K4's table that hearTerms hears: the first part of its number 4. -/
def rowsTerms (P : Pub) : List Rd := masked P.y.h.lt 2 1 (nEndT P.y)

/-- The slots that hearTerms takes. -/
def slotsTerms (P : Pub) : Nat := 1 + (1 + (2 * P.y.h.lt + (1 + nEndT P.y)))

/-- What hearTerms leaves. F: the ledger in front; G: behind. -/
structure TermsLeft (P : Pub) (F G : Fork) (H H' : Heard) (tT : Tsc) : Prop where
  some : H'.tT = some tT
  rest : H' = { H with tT := H'.tT, KT := H'.KT }
  cl : tT.sCl = F.next
  clF : Filled G tT.sCl
  sEnd : tT.sEnd = F.next + (1 + (1 + (2 * P.y.h.lt + 1)))
  ends : ∀ i, i < nEndT P.y → Filled G (tT.sEnd + i)
  r : tT.r.size = P.y.h.lt
  kt : Shown G H'.KT
  /-- every slot that it takes is filled -/
  marks : ∀ j, F.next ≤ j → j < G.next → Filled G j

/-- **hearTerms returns.** -/
theorem hearTerms_returns (P : Pub) (H : Heard) {F : Fork} {k : Nat}
    (hR : Room F (slotsTerms P + k)) {t : Tape} (hT : TapeOf (rowsTerms P) t) (u : Tape)
    (hzt : P.y.h.lt ≤ H.ztF.size) (hn : 1 ≤ nEndT P.y)
    -- the test on a sampled value: "coin-zero": the element drawn in the sumcheck's
    -- first round
    (vE : ∀ s0 eps t', t = ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t' →
      isZeroE eps = false) :
    ∃ H' G tT, hearTerms engFl P H F (t ++ u) = some (H', G, u) ∧ Room G k ∧ Below F G ∧
      G.next = F.next + slotsTerms P ∧ TermsLeft P F G H H' tT := by
  unfold rowsTerms at hT
  unfold slotsTerms at hR
  obtain ⟨tT, G1, eps, e1, ⟨s0, t', ht⟩, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14,
      e15⟩ :=
    tscIn_tape (F := F) (k := k) H.ztF hzt hn (Nat.le_refl 1) (by refine hR.mono ?_; omega) hT u
  have hz := vE s0 eps t' ht
  have hcl : Shown G1 tT.p.start := by
    rw [e13]
    exact shown_slot (by omega) e7
  obtain ⟨G2, f1, f2, f3, f4, f5, f6, f7, f8⟩ := row_tape e2 e4 e3 zeroE (kept := {}) hcl
    (fun _ hj => by cases hj)
    (fun j hj => by
      rw [e13] at hj
      have hj' : j ∈ [F.next] ++ ([] : List Nat) := hj
      have : j = F.next := by simpa using hj'
      omega) u
  refine ⟨{ H with tT := some { tT with p := { tT.p with rowMade := true } },
                   KT := (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps)) }, G2,
    { tT with p := { tT.p with rowMade := true } }, ?_, f2, ?_, ?_, ?_⟩
  · unfold hearTerms
    refine bindR e1 ?_
    refine bindR (mustR (by rw [e12, hz]; rfl) _ _) ?_
    refine bindR f1 ?_
    rfl
  · exact ⟨f4.trans e5.ns, fun _ => f5, by omega, fun j hj =>
      (f7 j (Or.inl (by omega))).trans (e5.same j hj)⟩
  · unfold slotsTerms
    omega
  · exact
      { some := rfl, rest := rfl, cl := e6
        clF := (f7 _ (Or.inl (by show tT.sCl < _; omega))).2 (by rw [e6]; exact e7)
        sEnd := e9
        ends := fun i hi => (f7 _ (Or.inr (by show _ ≤ tT.sEnd + i; omega))).2 (e11 i hi)
        r := e14, kt := f8.scale _
        marks := fun j h1 h2 => by
          by_cases q : tT.p.first ≤ j ∧ j < tT.sEnd
          · exact f6 j q.1 (by omega)
          · exact (f7 j (by omega)).2
              ((tsc_marks e2 e7 e8 e10 e11 e15 j h1 (by omega)).2 q) }

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.hearTerms_returns
