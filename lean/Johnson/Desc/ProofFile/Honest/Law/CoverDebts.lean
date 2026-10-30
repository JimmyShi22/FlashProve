-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverDebts.lean: the first chain's bounds, from statements about
single falls and marks. It applies `localDebts_own` (Honest/Law/CoverOwn.lean) at a description's
first chain. The chain's data are a letter `Xc`, named by the hypothesis `hXc`, as in
Honest/Law/CoverLetter.lean. The conclusion has the form of the hypothesis `d₁` of `falls_letter`
there; `falls_asks` (Honest/Law/CoverAsks.lean) applies the one to the other. It is general in the
file's description. No sub-protocol of the protocol is named here.

  1  `debts_letter`   the bounds of all gated sub-protocols of the first chain

Limits.
  * The marks of the first chain are the owners' marks `hm` followed by `fitMarks` of the gated
    sub-protocols.
  * Every statement about a fall or a mark (`hM`, `hPM`, `hF`, `hin`, `hP'`), the places at which
    they may stand (`hfs`, `hseat`, `he`), which sub-protocol has a round (`Hs`, `hlast`, `hend`,
    `hmr`) and the numbers (`hq0`, `hp₁`, `hp₂`) are hypotheses. None is proved here of any
    description.
  * `hC` (what the kit of challenges shows fits its round) and `hz` are hypotheses, and so are four
    on the description: `cut` (the first chain is `pre₁ ++ [e₁]`), `hdata` (`FileDescription.data`
    returns), `he₁` (`e₁` has one round) and `hpl` (`FileDescription.placesOk`, the library's executable
    test).
  * No number follows from the theorem.
  * The theorem proves no property of a prover or a protocol.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverOwn
import Johnson.Desc.ProofFile.Honest.Law.CoverLetter
import Johnson.Desc.ProofFile.Honest.Law.CoverData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X TF TJ T3 : Type}

set_option maxHeartbeats 2000000 in
/-- The first chain's bounds. `Xc`: the chain's data, named by `hXc`. `fs`: the chain's falls. `hm`:
the owners' marks. `hP'`: whoever proves it may use that the verifier's state just before a
sub-protocol that has a round is reached by the steps of the sub-protocols under `below`. -/
theorem debts_letter (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (D : WholeD) {F : FileDescription Xi} (Pr : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) (fs : List (Fall F.S₁)) (hm : List Mark) (p₁ : Nat → ℝ≥0∞)
    {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl} (cut : F.first.blocksInOrder = pre₁ ++ [e₁])
    {file : String} (hdata : F.data file = .ok D) {z₁ : Fmt.DeclaredRound} (he₁ : e₁.rounds = [z₁])
    (hpl : F.placesOk = true)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (hXc : Xc = fun _ => at₁ F Pr w₀ rc x R)
    (hz : ∀ b ∈ pre₁, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (seatF seatM : Place → Bool) (hfs : ∀ f ∈ fs, seatF f.place = true)
    (hseat : ∀ mk ∈ hm, seatM mk.place = true)
    (Hs : ∀ (P : List (Block F.S₁ F.Cl)) (c d : Block F.S₁ F.Cl) (Q : List (Block F.S₁ F.Cl)),
      F.first.blocksInOrder = P ++ c :: d :: Q → seatF d.place = true → d.rounds = [] →
      c.rounds ≠ [] ∧ seatF c.place = true)
    (he : seatF e₁.place = false) (hlast : ∀ A b, pre₁ = A ++ [b] → b.rounds ≠ [])
    (hend : ∀ A b, pre₁ = A ++ [b] →
      ¬ (seatM b.place = true ∨ (seatF b.place = true ∧ b.rounds ≠ [])))
    (hmr : ∀ b ∈ pre₁, seatM b.place = true → b.rounds ≠ [])
    (PM : Block F.S₁ F.Cl → List Fmt.Drawn → Prop) (qM : Block F.S₁ F.Cl → Mark → ℝ≥0∞)
    (hq0 : ∀ b ∈ pre₁, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    (hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk))
    (hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy F.first.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (P : Block F.S₁ F.Cl → List Fmt.Drawn → F.S₁ → Prop)
    (qF : Block F.S₁ F.Cl → Fall F.S₁ → ℝ≥0∞) (reps : Block F.S₁ F.Cl → List (Fall F.S₁))
    (hF : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ g ∈ reps b, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt C g 0 b (b' :: B ++ [e₁]) dsb [] (P b) (qF b g))
    (hin : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ [e₁]), f.place = d.place) →
      ∃ g ∈ reps b, ∀ fr s' own, P b fr s' →
        localFall [f] 0 (b :: (b' :: B ++ [e₁])) s' own →
        localFall [g] 0 (b :: (b' :: B ++ [e₁])) s' own)
    (hP' : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy F.first.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (F.first.blocksInOrder.map below) F.start₁ A.length (F.pub x, s')) →
      P b fr s')
    (hp₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
        p₁ (0 + A.length))
    (hp₂ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = false →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum ≤ p₁ (0 + A.length)) :
    LocalDebts C F.first.blocksInOrder fs (hm ++ fitMarks pre₁) 0 Xc p₁ [noDraw]
      (silentQ (hm ++ fitMarks pre₁) 0 pre₁) pre₁ 0 0 D.ds₁ :=
  localDebts_own (S := F.S₁) (Cl := F.Cl) (W := Local W₀ Rc Xi Tr) (Y := X) C hC F.first.blocksInOrder pre₁
    [e₁] fs hm 0 Xc p₁ [noDraw] (Pb := F.XiPub) F.start₁ (fun _ => F.pub x)
    (fun base a h =>
      let ⟨m₀, h1, h2⟩ := letter_starts F Pr w₀ rc x R Xc hXc base a h
      ⟨m₀, [], h1, h2⟩)
    (letter_stored F Pr w₀ rc x R Xc hXc) cut D.ds₁
    (kindFits_first hdata cut he₁) hz (pre_nodup hpl cut) seatF seatM hfs hseat Hs
    (fun _ hd => (List.mem_singleton.1 hd) ▸ he) (fun A b e hb => absurd hb (hlast A b e)) hend hmr
    (ft := 0) (letter_tree F Pr w₀ rc x R Xc hXc) PM qM hq0 hM hPM P qF reps hF hin hP' hp₁ hp₂

end ProofFile.Honest

#print axioms ProofFile.Honest.debts_letter
