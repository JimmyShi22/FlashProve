-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/HandsAtK10R.lean: «HandsR» (what one sub-protocol owes, AT THE FENCED STATES, so that each sub-protocol's yes hands on the half of the table's promise that reads the verifier's state) AT K10, AS A TERM: HandsAtK10.lean's three theorems IN THE FORM THAT COUNTS. Statements and proofs.
  hands_k10R        as hands_k10, at every fence Fk : ℕ → S → Prop: THE ONE BINDER THAT RANGES OVER STATES, hE («more»), NOW HAS Fk k s IN HAND: ∀ s s', Fk k s → K10Step s s' → s.failed = none → XK N links ps E k s = true → E (k + 1) s' = true. THEN IM.HandsR Fk N links ps E ft k b.
  hands_k10R_lot    at the lot's own sub-protocol (K9.closing Q).retype.
  hands_k10R_under  at every sub-protocol that stands under it (b.UnderR …): by IM.HandsR.under.
THE OTHER BINDERS RANGE OVER NO STATE: H (the decision's yes is the frame's closing's: paid by closing_writes in the second and third theorem) · hF, hX, hB: three tests with code on the table's lists · hk, hK, hn: what stands at number k of two lists. THE FIVE FIELDS mark · shape · rows · members · book SPEND NO FENCE: they hold at every s with the step's yes and XK.
LIMITS. hE is a premise: E is a letter. The three tests' yes are premises here. Nothing on soundness.

-/
import Johnson.IMR.HandsFence
import Johnson.Desc.First.Close.Law.CountsAtK10

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Place Oracle)
open VerifiableInference.Desc.First (S ModelPart Numbers start closersFit closersNext bookFit)
open VerifiableInference.Desc.First.Close (Par K10Step closeFrame entries k10_step_of_yes
  k10_step_mark k10_step_shape k10_step_rows k10_step_members k10_step_book_told closing_writes)
open VerifiableInference.Desc.K9 (recOf putRec)
open ProofFile (Cl)

/-- **«HandsR» at a sub-protocol whose decision's yes is the frame's closing's.** -/
theorem hands_k10R (Fk : Nat → S → Prop) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (E : Nat → S → Bool) (ft k : Nat) (p : Place) (Pr : Par) (b : Block S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (recOf s).owed (recOf s).frame
      (recOf s).st (entries Pr) rs = .ok x ∧ s' = putRec s ⟨none, x.1, x.2⟩)
    (hF : closersFit links ps (start links) = true) (hX : closersNext links ps = true)
    (hk : ps[k]? = some p) (hK : p.kind = .K10) (told : List (List Oracle))
    (hB : bookFit N ps told = true) (hn : told[k]? = some [])
    (hE : ∀ s s', Fk k s → K10Step s s' → s.failed = none → IM.XK N links ps E k s = true →
      E (k + 1) s' = true) : IM.HandsR Fk N links ps E ft k b := by
  have hs : ∀ s s', IM.Yes ft b s s' → K10Step s s' := fun s s' hy => by
    obtain ⟨rs, cols, n, e⟩ := hy
    exact k10_step_of_yes Pr b H s s' ⟨ft, rs, cols, n, e⟩
  have hlt : k < ps.length := (List.getElem?_eq_some_iff.1 hk).1
  refine ⟨fun s s' _ hy h => ?_, fun s s' _ hy _ _ hx => ?_, fun s s' _ _ _ _ _ => ?_,
    fun s s' _ _ _ _ _ => ?_, fun s s' _ hy _ _ hx => ?_,
    fun s s' hf hy h0 _ hx => hE s s' hf (hs s s' hy) h0 hx⟩
  · rw [k10_step_mark (hs s s' hy)]
    exact h
  · exact k10_step_shape links ps k p hX hk hK (hs s s' hy) (IM.xk_parts hx).1
  · exact k10_step_rows links ps k p hF hk hK N s'
  · exact k10_step_members links ps k p hF hk hK N s'
  · exact k10_step_book_told N ps told hB k hlt hn (hs s s' hy) (IM.xk_parts hx).2.2.2.1

/-- **At the lot's own sub-protocol.** -/
theorem hands_k10R_lot (Fk : Nat → S → Prop) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (E : Nat → S → Bool) (ft k : Nat) (p : Place) (Q : Par)
    (hF : closersFit links ps (start links) = true) (hX : closersNext links ps = true)
    (hk : ps[k]? = some p) (hK : p.kind = .K10) (told : List (List Oracle))
    (hB : bookFit N ps told = true) (hn : told[k]? = some [])
    (hE : ∀ s s', Fk k s → K10Step s s' → s.failed = none → IM.XK N links ps E k s = true →
      E (k + 1) s' = true) :
    IM.HandsR Fk N links ps E ft k
      (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype :=
  hands_k10R Fk N links ps E ft k p Q _
    (fun s rs gs s' h => closing_writes (Cl := Unit) Q s s' rs gs h) hF hX hk hK told hB hn hE

/-- **At every sub-protocol that stands under it.** -/
theorem hands_k10R_under (Fk : Nat → S → Prop) (N : Numbers) (links : List ModelPart)
    (ps : List Place) (E : Nat → S → Bool) (ft k : Nat) (p : Place) (Q : Par) (b : Block S Cl)
    (hU : b.UnderR (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype)
    (hF : closersFit links ps (start links) = true) (hX : closersNext links ps = true)
    (hk : ps[k]? = some p) (hK : p.kind = .K10) (told : List (List Oracle))
    (hB : bookFit N ps told = true) (hn : told[k]? = some [])
    (hE : ∀ s s', Fk k s → K10Step s s' → s.failed = none → IM.XK N links ps E k s = true →
      E (k + 1) s' = true) : IM.HandsR Fk N links ps E ft k b :=
  IM.HandsR.under (hands_k10R_lot Fk N links ps E ft k p Q hF hX hk hK told hB hn hE) hU

end LPFK10

#print axioms LPFK10.hands_k10R
#print axioms LPFK10.hands_k10R_lot
#print axioms LPFK10.hands_k10R_under
