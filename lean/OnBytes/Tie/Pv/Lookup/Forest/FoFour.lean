-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoFour.lean: the lookup of a sub-proof as one typed block, with three
facts on that one term (four in the names: the term and the three); general in the forest's public
numbers.

The block is forB E h L V VC: the draw of the shift if the forest has several calls, then the whole
chain of the lookup, at the letters that forA reads off the verifier's record h
(OnBytes.Model.Forest.Shape) and the caller's layout L.
forB_four states of this one term, for every setting s and scope sc and every plan P that the
verifier's own planner makes of the forest's sizes, finish s sc (planForest (forestSize h)) = .ok P:
 1. knowledge soundness (KnowAt, all four fields) from «each call's keys lie in that call's table»
    to the lookup's end claims, with the block's own errors;
 2. the block's rounds are the plan's rounds: ShapeIs E shape (P.rounds.map (·.entry)). Of an
    entry's twelve fields a typed round bears three: the bytes of the message, the elements drawn,
    how many of them are not 0;
 3. the block's errors against the plan's: there is a list Q of (c, n, (a, kind)), one for each
    round, in which the c are the block's numbers of bad challenges, the n are the sizes of the
    rounds' challenge sets, errOf s sc (a, kind) is the round's error in the plan, and
    c * b = a * n, where b is the size of the field, that less 1 where the element drawn is not 0,
    and 1 where nothing is drawn. So c / n = a / b exactly. errOf
    (OnBytes/Tie/Pv/Lookup/Port/TwPlanLaw.lean) is the planner's Bound.ratio a b, times the number
    of instances in the scope request, cut to a Binary. That this Binary is at least a / b as a
    number is not stated here.
Premises: FoNums.ok h = true and 2 ^ h.d * (2 ^ 32 - 1) < p, both on public numbers; the setting's
field has as many elements as E; the planner does not refuse. Where it refuses the statement is
empty; that it does not refuse is stated nowhere here.

Main definitions: forQuad. Main theorems: plan_forest, forB_plan, forB_four.
Not claimed: anything on the name and the other eight numbers of an entry beyond the equality of the
two lists of data (plan_forest); the hashed form; the end claims in the verifier's own forms; that
forB's reduction is the function Forest.pad (OnBytes/Model/Look.lean).
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoVal
import OnBytes.Tie.Pv.Lookup.Port.TwFour

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwRound TwPlan TwErr TwLaw OnBytes.G4
open OnBytes.Params (Setting Scope Planned finish planForest)

/-- What the verifier's planner lays for the forest h: the entries are forEnts, in all twelve
fields; the errors are the planner's quotients of the shift's pair and ratN's. -/
theorem plan_forest {h : Sh} (H : FoNums.ok h = true) {s : Setting} {sc : Scope} {P : Planned}
    (hf : finish s sc (planForest (OnBytes.Model.forestSize h)) = .ok P) :
    P.rounds.map (·.entry) = forEnts (s.workOf .field sc) h ∧
    P.rounds.map (·.error) =
        (shHead (FoNums.several h) (2 ^ h.d, 1) ++ ratN (FoNums.v' h) h.d FoNums.w FoNums.n).map
        (errOf s sc) := by
  have e : OnBytes.Model.forestSize h = ⟨FoNums.v' h + 1, h.d, FoNums.several h⟩ := by
    rw [← ok_v H]
    rfl
  rw [e] at hf
  exact finish_forest (FoNums.v' h) h.d (FoNums.several h) hf

/-- (c, n, (a, kind)), one for each round -/
def forQuad (q : Nat) (h : Sh) : List Quad :=
  shHead (FoNums.several h) (2 ^ h.d, q, (2 ^ h.d, 1)) ++ quadN (FoNums.v' h) h.d FoNums.w FoNums.n
      q

theorem map_shHead {α β : Type} (f : α → β) (b : Bool) (x : α) :
    (shHead b x).map f = shHead b (f x) := by
  cases b <;> rfl

theorem forQuad_c (q : Nat) (h : Sh) : (forQuad q h).map (·.1) = forEps q h := by
  rw [forQuad, forEps, List.map_append, map_shHead, quad_c]
theorem forQuad_r (q : Nat) (h : Sh) :
    (forQuad q h).map (·.2.2) = shHead (FoNums.several h) (2 ^ h.d, 1) ++ ratN (FoNums.v' h) h.d
        FoNums.w FoNums.n := by
  rw [forQuad, List.map_append, map_shHead, quad_r]
theorem forQuad_n (q wk : Nat) (h : Sh) :
    (forQuad q h).map (·.2.1) = (forEnts wk h).map (TwRound.sizeOf q) := by
  rw [forQuad, forEnts, List.map_append, List.map_append, map_shHead, map_shHead, quad_n,
      entN_sizes]
  congr 2
  exact ((size_rd0 q wk "LKP shift" 0 1).trans (Nat.pow_one q)).symm
theorem forQuad_rule (q : Nat) (h : Sh) :
    ∀ x ∈ forQuad q h, x.1 * bOf q x.2.2.2 = x.2.2.1 * x.2.1 := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · unfold shHead at hx
    split at hx
    · rw [List.mem_singleton.1 hx]
      exact ok_same q _
    · cases hx
  · exact rule_all _ _ _ _ _ x hx

section
variable (E : Type) [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  (h : Sh) (L : Lay E St₀ J₀) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
      (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Ex : ExtSpec)

/-- The block's rounds and errors are the plan's. -/
theorem forB_plan (H : FoNums.ok h = true) (s : Setting) (sc : Scope)
    (hq : s.cardE = Fintype.card E) (P : Planned)
    (hf : finish s sc (planForest (OnBytes.Model.forestSize h)) = .ok P) :
    ShapeIs E (forB E h L V VC (Ex := Ex)).R.shape (P.rounds.map (·.entry)) ∧
    ∃ Q : List Quad,
      Q.map (·.1) = errList (forB E h L V VC (Ex := Ex)).e ∧
      Q.map (·.2.1) = (forB E h L V VC (Ex := Ex)).R.shape.map (fun r => Nat.card r.Chal) ∧
      Q.map (fun x => errOf s sc x.2.2) = P.rounds.map (·.error) ∧
      ∀ x ∈ Q, x.1 * bOf s.cardE x.2.2.2 = x.2.2.1 * x.2.1 := by
  obtain ⟨f1, f2⟩ := plan_forest H hf
  refine ⟨?_, forQuad s.cardE h, ?_, ?_, ?_, forQuad_rule _ h⟩
  · rw [f1]
    exact forB_shape E h L V VC Ex _
  · rw [forQuad_c, hq]
    exact (forB_eps E h L V VC Ex).symm
  · rw [forQuad_n s.cardE 0 h, hq, ← Nat.card_eq_fintype_card]
    exact (shapeIs_sizes (forB_shape E h L V VC Ex 0)).symm
  · rw [f2, ← forQuad_r s.cardE h, List.map_map]
    rfl

/-- Knowledge soundness, rounds and errors of the one term forB. This is said under the hypotheses
that stand in the statement itself, which this comment does not list; it is no claim that they hold.
-/
theorem forB_four (p : ℕ) [CharP E p] (Kc M Wp : Type) (R0 : Rels Kc St₀ Ex (M × Wp))
    (msg₀ : M → J₀ → E)
    (H : FoNums.ok h = true) (hp : 2 ^ h.d * (2 ^ 32 - 1) < p)
    (s : Setting) (sc : Scope) (hq : s.cardE = Fintype.card E) (P : Planned)
    (hf : finish s sc (planForest (OnBytes.Model.forestSize h)) = .ok P) :
    KnowAt (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
        (fun _ _ _ wp => wp)
      (forB E h L V VC (Ex := Ex)).e ∧
    ShapeIs E (forB E h L V VC (Ex := Ex)).R.shape (P.rounds.map (·.entry)) ∧
    ∃ Q : List Quad,
      Q.map (·.1) = errList (forB E h L V VC (Ex := Ex)).e ∧
      Q.map (·.2.1) = (forB E h L V VC (Ex := Ex)).R.shape.map (fun r => Nat.card r.Chal) ∧
      Q.map (fun x => errOf s sc x.2.2) = P.rounds.map (·.error) ∧
      ∀ x ∈ Q, x.1 * bOf s.cardE x.2.2.2 = x.2.2.1 * x.2.1 :=
  ⟨holeC E p St₀ J₀ h L V VC Ex Kc M Wp R0 msg₀ H hp, forB_plan E h L V VC Ex H s sc hq P hf⟩

end
end Cb.Fo
