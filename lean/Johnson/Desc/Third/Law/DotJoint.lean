-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/DotJoint.lean: THE (Dot) JOINT, ITS CORE, ON WORDS IN A FIELD: what the row
that the last chain's first block ("K14, second part") has laid SAYS. Theorems; no definition.

WHOSE. THE TEXT COMES FROM A FILE OF THIS PROJECT THAT IS NOT IN THIS REPOSITORY,
carried here to the library's own imports: not a
token of a statement or a proof is turned; the structure AtDot stands in its own file
(Johnson/Desc/Third/Law/AtDot.lean).

Two laws are joined: the last chain's (Johnson/Desc/Third/Law/Says.lean: Says p s s': WHICH row lies
WHERE, exactly) and K14's (Johnson/Desc/K14/Law/MeansDotOk.lean: dotMeansOk: WHAT the
constraint (Dot) says of words, for well-formed row weights; Johnson/Desc/K14/Law/PlacedDot.lean:
placedDot_of_seated).

  seated_of_says   behind a yes the two messages of (Dot) are seated: SeatedDot at Omega's number
                   and at loc.w.
  dot_means        **THE CORE**: behind a yes there is a row dot such that (i) the own group's open
                   rows behind are those in front with dot pushed as the last, and (ii) OF ALL WORDS
                   m: dot says what it says IF AND ONLY IF the sum over y below matrixRows of
                   g(y) · Omega(y) is the sum over c below 2 ^ kCol of eq(psi, c) · W(c) (DotEq):
                   g and psi the border's, Omega and W read off m at Omega's number and at loc.w
                   through the plan's two layouts.
  dot_gives        the half that a relation behind the block spends: if all the own group's open
                   rows behind the block hold of m, DotEq holds.

OBJECT   Says (so (batchLinearConstraintsSecondPart p).decide, through law_k14Second).   USER   row0_back
(Johnson/Desc/Third/Law/Row0.lean).   LETTERS   ρ, a reading into a field; m, any words.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

What it is not. It is on WORDS IN A FIELD K under a reading ρ of the program's elements. It does
not say what ties words to what a prover has sent; that Omega is the table applied to eq(psi); that
W was fixed before psi was drawn; nothing is counted.
At silly members. A block that lays the row without a coefficient, or (Dot) at another point, on
another group or not at all, does not meet Says: so dot_means says nothing of it. Without AtDot's
"omega" the layout of (Dot) and the table of the message part: SeatedDot fails, and the iff is not
claimed. Without "weights" K14's law (dotMeansOk) is not claimed either.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.Third.Law.Says
import Johnson.Desc.Third.Law.AtDot
import Johnson.Desc.K14.Law.MeansDotOk
import Johnson.Desc.K14.Law.PlacedDot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open _root_.Desc.K14.Law (SeatedDot DotEq dotMeansOk placedDot_of_seated)

variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- Behind a yes the two messages of (Dot) are seated. -/
theorem seated_of_says (p : P₁₄) (s s' : S₃) (h : Says p s s') (a : AtDot p s) :
    SeatedDot s'.st s.st.codes p.S s.st.oracles.size s.loc.w := by
  obtain ⟨b, y, G, dot, hb, _, hy, _, _, hO, _, _, _, _, _, hc, fo, _, _⟩ := h
  obtain ⟨x, hx, sx⟩ := a.w
  have lt : s.loc.w < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  refine ⟨hc, fun e => absurd lt (by rw [← e]; exact Nat.lt_irrefl _), ⟨_, hO, a.omega b y hb hy⟩,
    ⟨x, ?_, sx⟩⟩
  rw [fo _ lt]
  exact hx

/-- **THE CORE.** -/
theorem dot_means (p : P₁₄) (s s' : S₃) (h : Says p s s') (a : AtDot p s) :
    ∃ (b : Border) (G G' : OnBytes.Group) (dot : OnBytes.Row),
      s.loc.border = some b ∧ s.st.groups[s.loc.own]? = some G ∧
      s'.st.groups[s.loc.own]? = some G' ∧ G'.rows = G.rows.push dot ∧
      ∀ m : Words K, Means.Says ρ s'.st dot m ↔
        DotEq p.S.matrixRows p.S.kCol (fun y => (b.g.map fun g => ρ.val (g.entry y)).sum)
          (fun y => m s.st.oracles.size .main ((linLayOmega s.st.codes p.S).index y))
          (b.shared.psi.map ρ.val)
          (fun c => m s.loc.w .main ((linLayW s.st.codes p.S).index c)) := by
  have hS := seated_of_says p s s' h a
  obtain ⟨b, y, G, dot, hb, _, _, _, _, _, hG, _, hd, _, hG', _, _, _, _⟩ := h
  exact ⟨b, G, _, dot, hb, hG, hG', rfl, fun m =>
    dotMeansOk ρ s'.st p.S b.g b.shared.psi s.st.oracles.size _ s.loc.w _ dot hd (a.weights b hb)
      (placedDot_of_seated hS a.lin) m⟩

/-- **What a relation behind the block spends**: if all the own group's open rows behind hold of m,
(Dot)'s equation holds. -/
theorem dot_gives (p : P₁₄) (s s' : S₃) (h : Says p s s') (a : AtDot p s) (m : Words K)
    (hs : ∀ G', s'.st.groups[s.loc.own]? = some G' → Means.AllSay ρ s'.st G'.rows.toList m) :
    ∃ b, s.loc.border = some b ∧
      DotEq p.S.matrixRows p.S.kCol (fun y => (b.g.map fun g => ρ.val (g.entry y)).sum)
        (fun y => m s.st.oracles.size .main ((linLayOmega s.st.codes p.S).index y))
        (b.shared.psi.map ρ.val)
        (fun c => m s.loc.w .main ((linLayW s.st.codes p.S).index c)) := by
  obtain ⟨b, G, G', dot, hb, _, hG', hr, hm⟩ := dot_means ρ p s s' h a
  refine ⟨b, hb, (hm m).1 (hs G' hG' dot ?_)⟩
  rw [hr]
  simp

end VerifiableInference.Desc.Third.Law
