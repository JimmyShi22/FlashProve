-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TablesGlued.lean: THE THREE TABLES OF JOINTS FIT TOGETHER AT THE CHAINS' ENDS: Three.Glued (Johnson/Desc/Sound/FileRule.lean: glue₁, glue₂, ends) at ONE value of
the rule's Places: the first chain's conditions and relations from its table (placesM), the shared chain's from its own (onQ₂, relQ₂), the last chain's from
its own (onQ₃, relQ₃), with the letters tied (tiedNumbers, tiedMeaning, ocEnd: Johnson/Desc/Sound/TieEnd.lean). One statement written as def … : Prop, and its proof: three
calls (tieEnd, tieLast, endsLast). (the last chain's book-keeping is a Bool; general in the first chain's record: get; (SH) and (SH₃) are asked inside the promises alone).

FROM ELEVEN PREMISES, EACH BY NAME: three lengths (each chain is as long as its table: tests) · (END) what is open at the first chain's end · (TP) table_promise · (SH) the
shared chain's book-keeping at its border 0, inside the first chain's last promise · (PW) the cells' pin at the two records · (START) the last chain's start says yes only at a first chain's last record without
a mark · (SH₃) inside the shared chain's last promise its yes gives the last chain's book-keeping at border 0 · (PO→), (PO←) Omega's promise and pin between the acting part's value and the whole strings.
WHAT IS NOT ASKED: anything for the items that cross a joint as one term (the claim on M, W's pin, the index masks' pin, (Eval), (Dot)); anything at the file's
end: behind the last block no item is open.

Limits. A rule under letters. It says that the relations at the ends are one chain of implications; it says nothing of any block.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.Sound.BordersLastQProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start onAt openSets)

/-- **The file's conditions and relations, all three chains' from their tables.** -/
def placesAll {C : CK} {D : WholeD} {all : List LeftT} {Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type}
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
    (get : P × S₁' → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart)
    (ps : List Place) (R₀ : (P × S₁') × (EAll D all).Str → W → Prop) (Ns : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') W) (ML : MeaningL S₃' W) (Pm : PromMeaning S₂')
    (PL : PromMeaningL S₂' S₃' (P × S₁')) (split : Bool) :
    Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W :=
  placesM T.ft₁ N₁ Mg₁ links ps get R₀
    { Q with
      on₂ := onQ₂ (tiedNumbers N₁ Ns) Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂
      R₂ := relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂
      on₃ := onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) Pm PL
        (ocEnd get N₁ Mg₁ links ps)
      R₃ := relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) ML }

/-- **The three tables fit together at the chains' ends.** -/
def TablesGlued : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type) (pub : Y → P)
    (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
    (get : P × S₁' → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (links : List ModelPart)
    (ps : List Place) (R₀ : (P × S₁') × (EAll D all).Str → W → Prop) (Ns : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') W) (ML : MeaningL S₃' W) (Pm : PromMeaning S₂')
    (PL : PromMeaningL S₂' S₃' (P × S₁')) (split : Bool),
    1 + T.l₁.length = ps.length →
    1 + T.l₂.length = (sharedPlaces split).length →
    1 + T.l₃.length = lastPlaces.length →
    (∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) ps.length i → i ∈ endFirst) →
    (∀ b : (P × S₁') × (EAll D all).Str,
      Mg₁.decodes (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      Pm.tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2)))) →
    (∀ b : (P × S₁') × (EAll D all).Str,
      (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q).on₁ (1 + T.l₁.length) b → Pm.shape 0 (start₂ b.1.1) = true) →
    (∀ (b : (P × S₁') × (EAll D all).Str) (w : W),
      Mg.pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
      Mg₁.pinW (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w) →
    (∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → (get (p, s₁)).2.failed = none) →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
      onQ₂ (tiedNumbers N₁ Ns) Pm (ocEnd get N₁ Mg₁ links ps) split T.p₂ T.l₂ (1 + T.l₂.length) b →
      start₃ b.1.1.1 b.1.1.2 b.1.2 = some s → PL.shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true) →
    (∀ b : ((P × S₁') × S₂') × (EAll D all).Str,
      (PromS.noColl .oOmega).holds (tiedNumbers N₁ Ns) Pm
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ (1 + T.l₂.length)).2 b).1
        (strsOfAct (frameAt D all D.key₂ T.ft₂)
          ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ (1 + T.l₂.length)).2 b)) →
      (PromS.noColl .oOmega).holds (tiedNumbers N₁ Ns) Pm b.1.2
        (strsOf (frameAt D all D.key₃ T.ft₃) b.2)) →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (w : W),
      (ItemS.pin .oOmega).holdsSh (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) b.1.2
        (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
      muQ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w) →
    (T.ofStarts pub start₁ start₂ start₃).Glued
      (placesAll T Q get N₁ Mg₁ links ps R₀ Ns Mg ML Pm PL split)

theorem tablesGlued : TablesGlued := by
  intro C D all Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W pub start₁ start₂ start₃ T Q get N₁ Mg₁ links ps R₀ Ns Mg ML Pm PL
    split h₁ h₂ h₃ hEnd hTP hSh hPW hStart hSh₃ hPOf hPOb
  refine ⟨?_, ?_, ?_⟩
  · exact tieEnd C D all Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W pub start₁ start₂ start₃ T
      { Q with
        on₃ := onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) Pm PL
          (ocEnd get N₁ Mg₁ links ps)
        R₃ := relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) ML }
      get N₁ Mg₁ links ps R₀ Ns Mg Pm split h₁ hEnd hTP hSh hPW
  · exact tieLast C D all Y P S₁' S₂' S₃' X₁ X₂ Cl W pub start₁ start₂ start₃ T
      (placesM T.ft₁ N₁ Mg₁ links ps get R₀ Q) (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) ML Pm PL
      (ocEnd get N₁ Mg₁ links ps) split h₂ hStart hSh₃ hPOf hPOb
  · exact endsLast C D all Y P S₁' S₂' S₃' _ _ Cl W (T.ofStarts pub start₁ start₂ start₃)
      (placesAll T Q get N₁ Mg₁ links ps R₀ Ns Mg ML Pm PL split) (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ Mg) ML h₃

#check @TablesGlued

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tablesGlued
