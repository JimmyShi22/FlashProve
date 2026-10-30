-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastBehind.lean: ROW 2 OF THE LAST CHAIN's TABLE: THE PROMISE BEHIND THE
PROXIMITY TEST's PIECE (the field `behind` of the row's debt), at the filling of the
book-keeping (`fillAt p R hand ended`, Johnson/Desc/Last/ShapeAtTable.lean).
  `OwnYesLays p R π`: WHAT IS OWED OF THE KIND's FILES: where the book-keeping's test at border 2
    says yes of the record in front and the seated block says yes: the own group's test has begun,
    the codes are as they were, the statement is tidy.
  `own_loc`: the seated block's yes leaves the chain's named values (`loc`): by the text of
    `leaveOwn`.
  `behind_fill`: **the promise at border 3 behind any piece that holds the seated block as the maker
    lays it**: from `PromReadsBelow` at the piece's base and `OwnYesLays`: by `held_yes`
    (LastYes.lean), `onQ₃_next` (Johnson/Desc/Last/ShapeRows.lean) and `step_two`
    (ShapeGives.lean), whose four debts are `own_loc` and the three of `OwnYesLays`.
Limits. OwnYesLays is shown nowhere. Nothing on soundness.
-/
import Johnson.LLT25R.LastYes
import Johnson.Desc.Last.ShapeRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Maker
open _root_.Run
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (onOwn enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut)

/-- **What is owed of the kind's files on what its yes lays.** -/
def OwnYesLays {Cl' : Type} (p : P₁₄) (R : List Fmt.DeclaredRound) (π : P12) : Prop :=
  ∀ (f : Handed) (o : SharedOut) (s s' : S₃) rs gs, shapeAt p R 2 f o s = true →
    (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Cl')).decide s rs gs = .ok s' →
    (∃ G, s'.st.groups[s.loc.own]? = some G ∧ G.inRun = true) ∧ s'.st.codes = s.st.codes ∧
      Means.Tidy s'.st

/-- The seated block's yes leaves the chain's named values. -/
theorem own_loc {Cl' : Type} (b : Block T12 Cl') (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (onOwn b).decide s rs gs = .ok s') :
    s'.loc = s.loc := by
  have h' : ((enterOwn s).bind fun t => (b.decide t rs gs).bind (leaveOwn s)) = .ok s' := h
  obtain ⟨t, -, h2⟩ := bindOk h'
  obtain ⟨t', -, h3⟩ := bindOk h2
  have e : ({ s with st := t'.st, book := t'.book, roots := t'.roots } : S₃) = s' :=
    Except.ok.inj h3
  rw [← e]

section
variable {P S₁ S₂ Cl' Wt : Type} {C : CK} {Fr : Frame} (Nn : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) Wt) (Pm : PromMeaning S₂) (Oc : P × S₁ → Strs → Prop) (p : P₁₄)
  (R : List Fmt.DeclaredRound) (hand : P × S₁ → Option Handed) (ended : S₂ → Option SharedOut)
  (π : P12)

/-- **The promise behind the proximity test's piece.** -/
theorem behind_fill (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl' Wt)
    (hx : x.b = held (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Cl')))
    (hr : PromReadsBelow Nn Pm Oc x.base) (hY : OwnYesLays (Cl' := Cl') p R π) :
    ∀ a τ e, onQ₃ Nn Mg Pm (fillAt p R hand ended) Oc 2 a → x.ior.red.out a τ = some e →
      onQ₃ Nn Mg Pm (fillAt p R hand ended) Oc 3 e := by
  intro a τ e h ho
  obtain ⟨h1, rs, gs, hd⟩ := held_yes _ x hx a τ e ho
  refine onQ₃_next Nn Mg Pm Oc p R hand ended x hr a e τ ho h1 h (fun f o _ _ hk => ?_)
    (fun hl => absurd hl (by decide))
  obtain ⟨run, codes, tidy⟩ := hY f o _ _ rs gs hk hd
  exact step_two hk (own_loc _ _ _ rs gs hd) run codes tidy

end

end LLT25

#print axioms LLT25.own_loc
#print axioms LLT25.behind_fill
