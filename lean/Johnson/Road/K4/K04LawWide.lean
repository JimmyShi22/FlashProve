-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04LawWide.lean: THE KIND K4's SHARE OF THE CHAIN OF PROMISES, CARRIED FROM A WIDER
MEANING DOWN TO A NARROWER ONE, IN THE CHAIN's SECOND FORM. It ends in `KindTiedR` by
name, and asks the facts along the run AT K4's OWN TWENTY-FOUR BORDERS ALONE. One statement with its
proof: a call, at each of the twelve numbers, of the bridge, by its three parts
(`tiedAtR_of_widen`, `onQ_down_A`, `onQ_up_A`): the bridge as one call (`tiedAtR_of_classA`) asks
the facts at every border and spends them at two. No new argument. IT PAYS NOTHING.

WHY. The composed meaning's reference form has a small door: thirteen names that only carried a fact
on the verifier's state across many sub-protocols have left it for facts along the verifier's run (a
condition Rch beside the table's promise). K4's laws are typed at a meaning whose door holds
these names. The bridge (`tiedAtR_of_classA`, Johnson/Desc/Sound/PlusDoorA.lean) carries one tie at
the wider meaning `widen Mg M pub' io'` to a tie of the second form (`TiedAtR`,
Johnson/Desc/Sound/ChainOfPromisesR.lean) at Mg. `KindTied` is, by its text, `TiedAt` at each number
of the kind: so the bridge serves point by point.

  `k04_tiedR_of_wide`: from `KindTied N (widen Mg M pub' io') linksFull (flatPlacesOf linksFull
    true) E l KindName.K4` (what `k04_law_of` ends in, called at the wider meaning): `KindTiedR N Mg
    linksFull (flatPlacesOf linksFull true) Rch E l KindName.K4` (Johnson/Desc/Sound/TiedR.lean): at
    every number at which the written list names the kind K4, the piece there is tied in the second
    form at Mg. Under the bridge's own premises: outside a class cA of names the wider tests are
    Mg's (hhand); the wider "in order" gives Mg's (hio); the test on the two doors accepts at the
    borders 28 g + 4 and 28 g + 5 (hD); at the borders 28 g + 4 and 28 g + 5, wherever Rch holds,
    the facts of the class hold (hF); an accepting run of the piece hands Rch on (hs).

Limits. EVERY PREMISE STAYS A PREMISE: hD IS A TEST WITH CODE, RUN NOWHERE IN THIS FILE: at the
lists `moreAll`, `moreWideAll` and the class `classA` the kernel decides it (`k4_doorsFit_wide`,
with `doors_of_fit`: Johnson/Road/K4/Rec/DoorsFitWide.lean); hF ASKS, AT THESE TWENTY-FOUR BORDERS,
EVERY NAME OF THE CLASS THAT IS OPEN AT THE WIDER DOOR THERE, NOT ONLY
WHAT K4 SPENDS, AND THE WIDER "IN ORDER" WHOLE; hs has a lemma general in the kind (`handsOn_map`,
Johnson/Top/H0/Walk/ReachHands.lean: its statement read; not called here). Rch is a letter: at
«never» every tie is free. That `k04_law_of`'s binders can be met at a wider meaning is shown by
nobody. Nothing on soundness.
-/
import Johnson.Road.K4.K04Places
import Johnson.Desc.Sound.TiedPlaces
import Johnson.Desc.Sound.PlusDoorA
import Johnson.Desc.Sound.TiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.First (S Pub More Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound

/-- **K4's share, from the wider meaning to the narrower, in the second form.** -/
theorem k04_tiedR_of_wide {Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (M : More) (pub' : Pub → P × S → Bool) (io' : P × S → Bool) (cA : Pub → Bool)
    (Rch : ℕ → (P × S) × Fr.E.Str → Prop)
    (E : ℕ → (P × S) × Fr.E.Str → (P × S) × Fr.E.Str → W → W)
    (l : List (Piece C Fr (P × S) Cl W))
    (H : KindTied N (widen Mg M pub' io') linksFull (flatPlacesOf linksFull true) E l KindName.K4)
    (hhand : ∀ i, cA i = false → ∀ x, pub' i x = Mg.pub i x)
    (hio : ∀ x, io' x = true → Mg.inOrder x = true)
    (hD : ∀ g, g < 12 →
      doorsFitB Mg.more M cA linksFull (flatPlacesOf linksFull true) (28 * g + 4) = true ∧
        doorsFitB Mg.more M cA linksFull (flatPlacesOf linksFull true) (28 * g + 4 + 1) = true)
    (hF : ∀ g, g < 12 →
      (∀ a, Rch (28 * g + 4) a →
        FactsAt Mg M pub' io' cA linksFull (flatPlacesOf linksFull true) (fun a => a) (28 * g + 4)
          a) ∧
        ∀ b, Rch (28 * g + 4 + 1) b →
          FactsAt Mg M pub' io' cA linksFull (flatPlacesOf linksFull true) (fun a => a)
            (28 * g + 4 + 1) b)
    (hs : ∀ g, g < 12 → ∀ q, l[28 * g + 4]? = some q →
      HandsOn Rch (28 * g + 4) (q.withMap (E (28 * g + 4)))) :
    KindTiedR N Mg linksFull (flatPlacesOf linksFull true) Rch E l KindName.K4 := by
  intro i q a hq ha hk
  obtain ⟨g, hg, rfl, -⟩ := k04_places_full i a ha hk
  exact tiedAtR_of_widen N Mg M pub' io' linksFull (flatPlacesOf linksFull true) (fun a => a) Rch
    (28 * g + 4) (q.withMap (E (28 * g + 4)))
    (fun b => onQ_down_A N Mg M pub' io' cA linksFull (flatPlacesOf linksFull true) (fun a => a)
      (28 * g + 4 + 1) b hhand hio (hD g hg).2)
    (fun a hr => onQ_up_A N Mg M pub' io' cA linksFull (flatPlacesOf linksFull true) (fun a => a)
      (28 * g + 4) a hhand (hD g hg).1 ((hF g hg).1 a hr))
    (fun b hr => onQ_up_A N Mg M pub' io' cA linksFull (flatPlacesOf linksFull true) (fun a => a)
      (28 * g + 4 + 1) b hhand (hD g hg).2 ((hF g hg).2 b hr))
    (hs g hg q hq) (H (28 * g + 4) q a hq ha hk)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04_tiedR_of_wide
