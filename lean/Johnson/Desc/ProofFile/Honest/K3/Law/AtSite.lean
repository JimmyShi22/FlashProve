-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/AtSite.lean: the honest side of the kind "lookup" (K3). What
holds behind the hearing's return at a lookup of a public part, with `Lawful` shown and not assumed.
Conditional on the six hypotheses below. Two theorems, one abbreviation.

Terms. Honest/K3/GLOSSARY.md. In this file: what the lookup leaves is `Left`
(Honest/K3/Law/LookLeftOf.lean). `Lawful` and `Left` have two letters, planes and keys; here they
are given values: the planes' values of the structure's own bits (`Spec.planesOf`) and the extension
of the structure's own keys (`Spec.keysOf`, both in Honest/K3/Law/SpecLawful.lean).

What is shown.
  `siteData`: the specification's data at a site, made of the input as the half's reader of the
    input reads it, and of the challenges.
  `left_site_spec`: at the specification's summands: there are coins, stage by stage, that are those
    which the row was handed (`CoinsAre`), and at the course with them: what was heard is the run's,
    with its points; the invariant `Inv` (Honest/K3/Law/Statements.lean) holds behind the last
    stage; and `Left` holds at the two values above.
  `left_site_fast`: the same at the summands that fold tables.

Hypotheses that remain, in both theorems.
  `hS`, `hL`: `Stands` and `LedgerIn` (Honest/K3/Law/Top.lean).
  `hy`: a play of the seated row has returned.
  `hh`: `hearV` returns on the rounds played.
  `hSet`: the input no longer moves from the challenges in front of the lookup on (`Ask.Settled` at
    the site's number of rounds in front): so not at the lookup's own first challenge either.
  `hM`: the relation after the challenge at the structure's keys and bits (`Data.Mid`).
  Besides, `hs`: s is a site of the public part Z.

Imported. Both theorems rest on the theorems of Honest/SumLaw/ (through Honest/K3/Law/HBPaid.lean).

How the proof goes. The summands that fold tables are lawful because they agree, at the run, with
the specification's (`site_agree`, Honest/K3/FastLaw/Sites.lean; `agreeLawful`,
Honest/K3/Law/Agree.lean; `lawful_site`, Honest/K3/Law/SpecAtSite.lean).

Users. Honest/K3/Law/Thread/LeftThr.lean imports this file and uses `siteData`.

Limits. No instance of these hypotheses is exhibited in this file: it lays no course at a site of a
public part. The nearest thing to one is Honest/K3/Law/JoinedMember.lean [not in this library]: the
like hypotheses met together at a synthetic place, at the specification's summands (by evaluation).
What is left has its values at mask entries that are the coins spent: which coin the verifier's
world reads under which slot is not said here. The verifier's side is the kind's own texts.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.HBPaid
import Johnson.Desc.ProofFile.Honest.K3.Law.Agree
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecAtSite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork)
open VerifiableInference.Desc.K3 (HeardV hearV)

variable {W₀ Rc Xi Tr V₁ W₁ X₁ : Type}

/-- **The specification's data at a site**: the site's public numbers; the structure that the half's
reader of the input makes of the input at the challenges heard in front; the points of all
challenges by number. -/
abbrev siteData (s : Site) (w : Ask) (heard ds : List Fmt.Drawn) :=
  dataAt (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta) (w heard)
    (ptsOf s.at_.face s.at_.base (heard ++ ds))

/-- **Conditional on `Stands`, `LedgerIn`, the play's and `hearV`'s return, `Ask.Settled` and
`Data.Mid`: at a lookup of a public part, at the specification's summands: what was heard is the
run's, with its points; the invariant holds behind the last stage; and `Left` holds at the planes'
values of the structure's own bits and the extension of the structure's own keys.** It rests on the
theorems of Honest/SumLaw/. No instance of these hypotheses is exhibited in this file. -/
theorem left_site_spec (src : Sources W₀ Xi Tr) (Z : Pub) (s : Site) (hs : s ∈ lookSites Z)
    (wit : W₁ → Ask) (name : String) (v : Option V₁) (es : List Fmt.Entry) (m : Mid W₁ X₁)
    (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩
      ((specFill (Rc := Rc) src).jobs s).asked wit s.at_).parts)
    (first : Nat) (F G : Fork) (y : List Played × Mid W₁ X₁) (g : HeardV)
    (hS : Stands s.at_ es m ds) (hL : LedgerIn s.at_.face first F)
    (hy : play (seatSteps s.at_ ((specFill (Rc := Rc) src).jobs s).asked wit name v es c) ds [] m =
      .ok y)
    (hh : hearV s.at_.face F (roundsOf y.1) = some (g, G))
    (hSet : Ask.Settled s.at_.base (wit m.st.input))
    (hM : (siteData s (wit m.st.input) m.st.heard ds).Mid) :
    ∃ c' : (t : Stage) → StageCoins s.at_ t,
      CoinsAre (V := Unit)
        (courseAt s.at_ ((specFill (Rc := Rc) src).jobs s).asked first wit m ds c')
        (unlift (X := X₁) (fun (_ : V₁) => ()) wit
          (lookRow ⟨ptsOf, pointsAt⟩ ((specFill (Rc := Rc) src).jobs s).asked s.at_) c) ∧
      HeardIs (courseAt s.at_ ((specFill (Rc := Rc) src).jobs s).asked first wit m ds c') g ∧
      PointsAgree s.at_.face g s.at_.base (m.st.heard ++ ds) ∧
      Inv (courseAt s.at_ ((specFill (Rc := Rc) src).jobs s).asked first wit m ds c')
        (stages s.at_.face).length G ∧
      Left (courseAt s.at_ ((specFill (Rc := Rc) src).jobs s).asked first wit m ds c')
        (Spec.planesOf (siteData s (wit m.st.input) m.st.heard ds))
        (Spec.keysOf (siteData s (wit m.st.input) m.st.heard ds)) g G := by
  obtain ⟨h1, _⟩ := FastLaw.sites_ok Z s hs
  have hp : s.at_.face.parts = [s.shape.v] := by rw [h1]; rfl
  obtain ⟨c', hc, hH, P, hI, hLeft⟩ := leftInnerP V₁ W₁ X₁ Ask s.at_ _ wit name v es m ds c first F
    G
    s.shape.v y g hS hp hL hy hh
  exact ⟨c', hc, hH, P, hI, hLeft _ _ (Spec.lawful_site (Rc := Rc) src Z s hs
    (courseAt s.at_ ((specFill (Rc := Rc) src).jobs s).asked first wit m ds c') rfl rfl
    (fit_of_stands hS _ first wit c') hSet hM)⟩

/-- **The same at the summands that fold tables**, conditional on the same. It rests on the theorems
of Honest/SumLaw/. No instance of these hypotheses is exhibited in this file. -/
theorem left_site_fast (src : Sources W₀ Xi Tr) (Z : Pub) (s : Site) (hs : s ∈ lookSites Z)
    (wit : W₁ → Ask) (name : String) (v : Option V₁) (es : List Fmt.Entry) (m : Mid W₁ X₁)
    (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩
      ((fastFill (Rc := Rc) src).jobs s).asked wit s.at_).parts)
    (first : Nat) (F G : Fork) (y : List Played × Mid W₁ X₁) (g : HeardV)
    (hS : Stands s.at_ es m ds) (hL : LedgerIn s.at_.face first F)
    (hy : play (seatSteps s.at_ ((fastFill (Rc := Rc) src).jobs s).asked wit name v es c) ds [] m =
      .ok y)
    (hh : hearV s.at_.face F (roundsOf y.1) = some (g, G))
    (hSet : Ask.Settled s.at_.base (wit m.st.input))
    (hM : (siteData s (wit m.st.input) m.st.heard ds).Mid) :
    ∃ c' : (t : Stage) → StageCoins s.at_ t,
      CoinsAre (V := Unit)
        (courseAt s.at_ ((fastFill (Rc := Rc) src).jobs s).asked first wit m ds c')
        (unlift (X := X₁) (fun (_ : V₁) => ()) wit
          (lookRow ⟨ptsOf, pointsAt⟩ ((fastFill (Rc := Rc) src).jobs s).asked s.at_) c) ∧
      HeardIs (courseAt s.at_ ((fastFill (Rc := Rc) src).jobs s).asked first wit m ds c') g ∧
      PointsAgree s.at_.face g s.at_.base (m.st.heard ++ ds) ∧
      Inv (courseAt s.at_ ((fastFill (Rc := Rc) src).jobs s).asked first wit m ds c')
        (stages s.at_.face).length G ∧
      Left (courseAt s.at_ ((fastFill (Rc := Rc) src).jobs s).asked first wit m ds c')
        (Spec.planesOf (siteData s (wit m.st.input) m.st.heard ds))
        (Spec.keysOf (siteData s (wit m.st.input) m.st.heard ds)) g G := by
  obtain ⟨h1, _⟩ := FastLaw.sites_ok Z s hs
  have hp : s.at_.face.parts = [s.shape.v] := by rw [h1]; rfl
  obtain ⟨c', hc, hH, P, hI, hLeft⟩ := leftInnerP V₁ W₁ X₁ Ask s.at_ _ wit name v es m ds c first F
    G
    s.shape.v y g hS hp hL hy hh
  have hFs := fit_of_stands hS ((specFill (Rc := Rc) src).jobs s).asked first wit c'
  have hLs := Spec.lawful_site (Rc := Rc) src Z s hs
    (courseAt s.at_ ((specFill (Rc := Rc) src).jobs s).asked first wit m ds c') rfl rfl hFs hSet hM
  have hA := FastLaw.site_agree (Rc := Rc) src Z s hs
    (courseAt s.at_ ((specFill (Rc := Rc) src).jobs s).asked first wit m ds c') rfl rfl hFs
  exact ⟨c', hc, hH, P, hI, hLeft _ _ ((agreeLawful Ask _ _ _ _ hFs hA).2 hLs)⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.left_site_spec
#print axioms ProofFile.Honest.K3.Law.left_site_fast
