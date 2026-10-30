-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/HandsAtK10.lean: «Hands» (Johnson/IMR/HandsDef.lean: what one block owes so that each block's yes hands the growth on) AT K10's BLOCK, AS A TERM. Statements and
proofs.
  hands_k10        b a block over the first chain's state whose decision's yes is the frame's closing's (H); ps[k]? = some p of the kind K10; the two tests on the table say yes (closersFit · closersNext: PromiseBehind.lean · ShapeBehind.lean); the
                   table's test on its numbers says yes and block k tells nothing (bookFit · told[k]? = some []: CountsAtK10.lean); «more» along a K10Step (hE): THEN IM.Hands N links ps E ft k b.
  hands_k10_lot    at the lot's own block (K9.closing Q).retype: H is paid by closing_writes (Leaves.lean).
  hands_k10_under  at every block b that stands under it (b.UnderR …: IM's alone_underR at a seated block): by IM.Hands.under.
LIMITS. hE («more»: E (k + 1) s' from XK … k s along a K10Step) is a premise: E is a letter of that form. The three tests' yes are premises here (by the kernel at two rows of segments; free at the filled numbers: other files). Nothing on
soundness.

-/
import Johnson.IMR.HandsDef
import Johnson.Desc.First.Close.Law.CountsAtK10

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Place Oracle)
open VerifiableInference.Desc.First (S ModelPart Numbers start closersFit closersNext bookFit)
open VerifiableInference.Desc.First.Close (Par K10Step closeFrame entries k10_step_of_yes
  k10_step_mark k10_step_shape k10_step_rows k10_step_members k10_step_book_told closing_writes)
open VerifiableInference.Desc.K9 (recOf putRec)
open ProofFile (Cl)

/-- **«Hands» at a block whose decision's yes is the frame's closing's.** -/
theorem hands_k10 (N : Numbers) (links : List ModelPart) (ps : List Place) (E : Nat → S → Bool)
    (ft k : Nat) (p : Place) (Pr : Par) (b : Block S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (recOf s).owed (recOf s).frame
      (recOf s).st (entries Pr) rs = .ok x ∧ s' = putRec s ⟨none, x.1, x.2⟩)
    (hF : closersFit links ps (start links) = true) (hX : closersNext links ps = true)
    (hk : ps[k]? = some p) (hK : p.kind = .K10) (told : List (List Oracle))
    (hB : bookFit N ps told = true) (hn : told[k]? = some [])
    (hE : ∀ s s', K10Step s s' → s.failed = none → IM.XK N links ps E k s = true →
      E (k + 1) s' = true) : IM.Hands N links ps E ft k b := by
  have hs : ∀ s s', IM.Yes ft b s s' → K10Step s s' := fun s s' hy => by
    obtain ⟨rs, cols, n, e⟩ := hy
    exact k10_step_of_yes Pr b H s s' ⟨ft, rs, cols, n, e⟩
  have hlt : k < ps.length := (List.getElem?_eq_some_iff.1 hk).1
  refine ⟨fun s s' hy h => ?_, fun s s' hy _ _ hx => ?_, fun s s' _ _ _ _ => ?_,
    fun s s' _ _ _ _ => ?_, fun s s' hy _ _ hx => ?_, fun s s' hy h0 _ hx => hE s s' (hs s s' hy) h0 hx⟩
  · rw [k10_step_mark (hs s s' hy)]
    exact h
  · exact k10_step_shape links ps k p hX hk hK (hs s s' hy) (IM.xk_parts hx).1
  · exact k10_step_rows links ps k p hF hk hK N s'
  · exact k10_step_members links ps k p hF hk hK N s'
  · exact k10_step_book_told N ps told hB k hlt hn (hs s s' hy) (IM.xk_parts hx).2.2.2.1

/-- **At the lot's own block.** -/
theorem hands_k10_lot (N : Numbers) (links : List ModelPart) (ps : List Place) (E : Nat → S → Bool)
    (ft k : Nat) (p : Place) (Q : Par)
    (hF : closersFit links ps (start links) = true) (hX : closersNext links ps = true)
    (hk : ps[k]? = some p) (hK : p.kind = .K10) (told : List (List Oracle))
    (hB : bookFit N ps told = true) (hn : told[k]? = some [])
    (hE : ∀ s s', K10Step s s' → s.failed = none → IM.XK N links ps E k s = true →
      E (k + 1) s' = true) :
    IM.Hands N links ps E ft k
      (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype :=
  hands_k10 N links ps E ft k p Q _
    (fun s rs gs s' h => closing_writes (Cl := Unit) Q s s' rs gs h) hF hX hk hK told hB hn hE

/-- **At every block that stands under it.** -/
theorem hands_k10_under (N : Numbers) (links : List ModelPart) (ps : List Place) (E : Nat → S → Bool)
    (ft k : Nat) (p : Place) (Q : Par) (b : Block S Cl)
    (hU : b.UnderR (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype)
    (hF : closersFit links ps (start links) = true) (hX : closersNext links ps = true)
    (hk : ps[k]? = some p) (hK : p.kind = .K10) (told : List (List Oracle))
    (hB : bookFit N ps told = true) (hn : told[k]? = some [])
    (hE : ∀ s s', K10Step s s' → s.failed = none → IM.XK N links ps E k s = true →
      E (k + 1) s' = true) : IM.Hands N links ps E ft k b :=
  IM.Hands.under hU (hands_k10_lot N links ps E ft k p Q hF hX hk hK told hB hn hE)

end LPFK10

#print axioms LPFK10.hands_k10
#print axioms LPFK10.hands_k10_lot
#print axioms LPFK10.hands_k10_under
