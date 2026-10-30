-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0.lean: THE LAST CHAIN's FIRST BLOCK ("K14, second part") IN THE FORM THAT
THE RULE OF COMPOSITION FOR ONE CHAIN ASKS OF EACH BLOCK (Piece.GoodIn,
Johnson/Desc/Sound/GoodIn.lean), AT ANY ERRORS: it has no round, no chance and no extractor.
BEHIND: every open row of the request's own group, as it lies in the record behind, holds of the
witness' words. IN FRONT: every open row of the own group as it lies in the record in front holds of
them (the row (Eval) is among these, where the promise in front says so), AND (Dot)'s equation
holds. AN ASSEMBLY: nothing on what the block lays is typed here. Spent, as they stand, are the last
chain's own laws: law_k14Second (a yes drops nothing, writes no mark, and lays what Says says),
old_rows_back (a row that names older messages alone says the same behind as in front), dot_gives
(the row (Dot) says (Dot)'s equation: by dotMeansOk of the linear claim's law). Theorems.

  RowsHold ρ s m       every open row of the own group, as it lies in the record s, holds of m.
  DotHolds ρ p s m     (Dot)'s equation at the record in front: the weights and the point of the two
                       ends at hand; Omega's words under the next number of the statement; W's
                       words.
  Names s              the own group's open rows name messages of the statement alone.
  own_same             the block leaves the own group's number.
  row0_back            behind a yes: RowsHold behind gives RowsHold and DotHolds in front.
  row0_goodIn          **the row.** Rc: whatever else rides (the pins): it goes back by a premise.
  eval_of_rows         so a row that lies among the own group's open rows in front holds.
OBJECT   (batchLinearConstraintsSecondPart p).decide, through law_k14Second.
USER     row0_back: row0_backW (Johnson/Desc/Third/Law/Row0Words.lean), so rowZero
         (Johnson/Desc/Third/Law/Row0AtTable.lean). row0_goodIn IS A FORERUNNER: nobody calls it:
         its promise behind is "what a yes gives", no table's.
LETTERS  ρ · m, any words.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.
What is not claimed. That the row (Eval) lies among the own group's open rows in front, and that the
numbers in the rows go to the witness' components: the promise's matter. AtDot and Names in front
are parts of the promise: not shown here of a real record. rw, Prm, Rc are letters. A block that
refuses all has GoodIn too. No soundness of a verifier.

-/
import Johnson.Desc.Third.Law.RowsOfEarlierMessages
import Johnson.Desc.ChainEndGoodIn
import Johnson.Desc.Third.Law.DotJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open VerifiableInference.Desc.Sound (Frame Piece goodIn_of_sure)
open _root_.Desc.K14.Law (DotEq)
open _root_.Run.PQ (CK)

variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- Every open row of the own group, as it lies in the record, holds of the words. -/
def RowsHold (s : S₃) (m : Words K) : Prop :=
  ∀ G, s.st.groups[s.loc.own]? = some G → Means.AllSay ρ s.st G.rows.toList m

/-- (Dot)'s equation at the record in front of the block. -/
def DotHolds (p : P₁₄) (s : S₃) (m : Words K) : Prop :=
  ∃ b, s.loc.border = some b ∧
    DotEq p.S.matrixRows p.S.kCol (fun y => (b.g.map fun g => ρ.val (g.entry y)).sum)
      (fun y => m s.st.oracles.size .main ((linLayOmega s.st.codes p.S).index y))
      (b.shared.psi.map ρ.val)
      (fun c => m s.loc.w .main ((linLayW s.st.codes p.S).index c))

/-- The own group's open rows name messages of the statement alone. -/
def Names (s : S₃) : Prop :=
  ∀ G, s.st.groups[s.loc.own]? = some G → ∀ r ∈ G.rows.toList, ∀ o ∈ r.oracles,
    o < s.st.oracles.size

/-- The block leaves the own group's number. -/
theorem own_same (p : P₁₄) (s s' : S₃) (h : Says p s s') : s'.loc.own = s.loc.own := by
  obtain ⟨_, _, _, _, _, hl, _⟩ := h
  rw [hl]

/-- **Behind a yes.** -/
theorem row0_back (p : P₁₄) (s s' : S₃) (h : Says p s s') (hk : Later.Carries s.st s'.st)
    (a : AtDot p s) (n : Names s) (m : Words K) (hs : RowsHold ρ s' m) :
    RowsHold ρ s m ∧ DotHolds ρ p s m := by
  have hs' : ∀ G', s'.st.groups[s.loc.own]? = some G' → Means.AllSay ρ s'.st G'.rows.toList m := by
    intro G' hG'
    rw [← own_same p s s' h] at hG'
    exact hs G' hG'
  exact ⟨old_rows_back ρ p s s' h hk m n hs', dot_gives ρ p s s' h a m hs'⟩

variable {Cl W : Type} {C : CK} {F : Frame}

/-- **The row.** -/
theorem row0_goodIn (p : P₁₄) (pc : Piece C F S₃ Cl W) (hb : pc.b = batchLinearConstraintsSecondPart p)
    (hext : ∀ a τ w, pc.ext a τ w = w) (rw : W → Words K) (Prm : S₃ × F.E.Str → Prop)
    (hkeep : ∀ a τ b, AtDot p a.1 → Names a.1 → pc.ior.red.out a τ = some b → Prm a → Prm b)
    (Rc : S₃ × F.E.Str → W → Prop)
    (hback : ∀ a τ b w, AtDot p a.1 → Names a.1 → Prm a → pc.ior.red.out a τ = some b → Rc b w →
      Rc a w) :
    pc.GoodIn (fun a => AtDot p a.1 ∧ Names a.1 ∧ Prm a)
      (fun b => (∃ s, AtDot p s ∧ Says p s b.1) ∧ Prm b)
      (fun a w => RowsHold ρ a.1 (rw w) ∧ DotHolds ρ p a.1 (rw w) ∧ Rc a w)
      (fun b w => RowsHold ρ b.1 (rw w) ∧ Rc b w) := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha hout => ?_
  obtain ⟨_, rs, gs, hd⟩ := pc.out_of_decide a τ b hout
  rw [hb] at hd
  have hk := (law_k14Second (Cl := Cl) p).1 _ _ _ _ hd
  have hs := (law_k14Second (Cl := Cl) p).2 _ _ _ _ hd
  refine ⟨⟨⟨a.1, ha.1, hs⟩, hkeep a τ b ha.1 ha.2.1 hout ha.2.2⟩, fun w hw => ?_⟩
  rw [hext]
  obtain ⟨r1, r2⟩ := row0_back ρ p a.1 b.1 hs hk ha.1 ha.2.1 (rw w) hw.1
  exact ⟨r1, r2, hback a τ b w ha.1 ha.2.1 ha.2.2 hout hw.2⟩

/-- A row that lies among the own group's open rows holds. -/
theorem eval_of_rows (s : S₃) (m : Words K) (h : RowsHold ρ s m) (G : OnBytes.Group)
    (hG : s.st.groups[s.loc.own]? = some G) (r : OnBytes.Row) (hr : r ∈ G.rows.toList) :
    Means.Says ρ s.st r m := h G hG r hr

end VerifiableInference.Desc.Third.Law
