-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/MadeMorePlus.lean: kind K5: K5AtMg's FIELD madeMore
(Johnson/Desc/First/Att/K05AtMg.lean: what the list of extra public tests says the sub-protocol
makes holds behind the lay) AT ANY FILLING Mg WITH Mg.pub = pubAll D base AND Mg.more = morePlus M0
(Johnson/Desc/First/Att/Door/Plus.lean). After MadeMoreAt.lean (at another form of the
composed filling): one call turns: k5_makes ↦ k5_makes_plus
(Johnson/Desc/First/Att/Door/Law/K5MakesPlus.lean); the rest is taken over line for line, by
program. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Att.Door.Law.K5MakesPlus

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Att.P (behind hear Heard K5Place geoOf)

theorem madeMore_plus {Pp W : Type} (D : PubData) (base : Pub → Pp × S → Bool) (Mg : Meaning Pp W) (hpub : Mg.pub = pubAll D base)
    (M0 : More) (hmore : Mg.more = morePlus M0) (N : Numbers) (links : List ModelPart) {pl pl' : Place} (O : List Item) (Q : List Pub)
    (Fr : Frame) {m : Nat} (Ix : K5Place links m pl pl') (h0 : (M0.rows links pl).makes = []) (own : Params.AttentionRounds)
    (hatt : D.d5.isAtt m = true) {A : Attention.Plan} (hA : D.d5.W.A[m / 2]? = some A)
    (hPm : ∀ a : Pp × S, Mg.pubP (.more (some m) "K5.okAt") a ∧ Mg.pubP (.more (some m) "K5.plain") a)
    (hok : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear own (att.F, rs, 0) = some (hd, G, [], 0) → okThereB (geoOf A.S) (behind s att hd G) = true)
    (hplain : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear own (att.F, rs, 0) = some (hd, G, [], 0) → plainThereB A.iU3 A.nW (behind s att hd G) = true) :
    ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ x ∈ (Mg.more.rows links pl).makes, Mg.pub (moreItem x) (π, behind s att hd G) = true ∧
        Mg.pubP (moreItem x) (π, behind s att hd G) := by
  intro π s y att hd G rs hon hu e hh x hx
  rw [hmore, k5_makes_plus Ix M0 h0] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · refine ⟨?_, (hPm _).1⟩
    show Mg.pub (.more (some m) "K5.okAt") _ = true
    rw [hpub, pubAll_more_okAt D base m hatt, hA]
    exact hok π s y att hd G rs hon hu e hh
  · refine ⟨?_, (hPm _).2⟩
    show Mg.pub (.more (some m) "K5.plain") _ = true
    rw [hpub, pubAll_more_plain D base m hatt, hA]
    exact hplain π s y att hd G rs hon hu e hh

#print axioms madeMore_plus

end H2K5.Door
