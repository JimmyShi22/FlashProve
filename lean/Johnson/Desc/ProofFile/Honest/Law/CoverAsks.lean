-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverAsks.lean: one theorem from statements about single falls and
marks to the bound on the chance that a run meets a fall, with the statements bundled in one
structure. `debts_letter` (Honest/Law/CoverDebts.lean) gives the first chain's bounds from sixteen
hypotheses on falls, marks, places, rounds and numbers, and `falls_letter`
(Honest/Law/CoverLetter.lean) gives the bound on the chance from the first chain's bounds. A theorem
that wrote the sixteen hypotheses and the bound into one statement was too slow for Lean to check,
twice. Here the sixteen are the fields of a structure, `FirstAsks`, so the statement that composes
the two lemmas is short. It is general in the file's description. No sub-protocol of the protocol is
named here.

  1  `FirstAsks`   the sixteen hypotheses of `debts_letter` on falls, marks, places, rounds and
     numbers
  2  `debts_asks`   `debts_letter` from the structure
  3  `falls_asks`   the bound, from the structure: `falls_letter` at `debts_asks`

Limits.
  * `FirstAsks` is a list of hypotheses. No member of it is shown here, at any description.
  * The marks of the first chain are the owners' marks `hm` followed by `fitMarks` of the gated
    sub-protocols.
  * `hC` (what the kit of challenges shows fits its round) is a hypothesis.
  * Beside these `falls_asks` takes: `hR` (`ready` returns at these coins), `Sf`, `hne` (there are
    gated sub-protocols), `s₁` (no fall is met before the chain's first round), `hdata`
    (`FileDescription.data` returns), `he₁` (the last sub-protocol has one round) and `hpl`
    (`FileDescription.placesOk`). `debts_asks` takes `hdata`, `he₁` and `hpl` too.
  * The shared and the second chain have empty lists of falls, and their marks are silent at typed
    messages.
  * No number follows from the theorems.
  * The theorems prove no property of a prover or a protocol.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverDebts

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

/-! ## 1 The hypotheses as one structure -/

set_option maxHeartbeats 2000000 in
/-- A list of hypotheses: what `debts_letter` asks about falls, marks, places, rounds and numbers at
a description's first chain. This file shows no member of it. A member of it is what
`debts_asks` and `falls_asks` ask beside their hypotheses on the file, on the kit of challenges
and on the other two chains. The four fields on falls (`hF`, `hin`, `hP'`, `hp₁`) speak only of
a sub-protocol that has a round: one without a round at a fall's seat is covered by the one
before it (`Hs`). `fs`: the chain's falls. `hm`: the owners' marks. `pre₁`, `e₁`: the gated
sub-protocols and the last one. `Xc`: the chain's data. `seatF`, `seatM`: where a fall and a
mark may stand. `PM`, `qM`, `P`, `qF`, `reps`: the conditions, the numbers and the counted falls
of the owners' bounds. -/
structure FirstAsks (C : CK) {F : FileDescription Xi} (fs : List (Fall F.S₁)) (hm : List Mark)
    (p₁ : Nat → ℝ≥0∞) (pre₁ : List (Block F.S₁ F.Cl)) (e₁ : Block F.S₁ F.Cl) (x : Xi)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X) (seatF seatM : Place → Bool)
    (PM : Block F.S₁ F.Cl → List Fmt.Drawn → Prop) (qM : Block F.S₁ F.Cl → Mark → ℝ≥0∞)
    (P : Block F.S₁ F.Cl → List Fmt.Drawn → F.S₁ → Prop)
    (qF : Block F.S₁ F.Cl → Fall F.S₁ → ℝ≥0∞) (reps : Block F.S₁ F.Cl → List (Fall F.S₁)) :
    Prop where
  /-- of each gated round's entry: the elements that must not be 0 are among those drawn -/
  hz : ∀ b ∈ pre₁, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE
  /-- every fall stands at a fall's seat -/
  hfs : ∀ f ∈ fs, seatF f.place = true
  /-- every owner's mark stands at a mark's seat -/
  hseat : ∀ mk ∈ hm, seatM mk.place = true
  /-- right before a sub-protocol without a round at a fall's seat stands one with a round at such
  a seat -/
  Hs : ∀ (P : List (Block F.S₁ F.Cl)) (c d : Block F.S₁ F.Cl) (Q : List (Block F.S₁ F.Cl)),
    F.first.blocksInOrder = P ++ c :: d :: Q → seatF d.place = true → d.rounds = [] →
    c.rounds ≠ [] ∧ seatF c.place = true
  /-- the chain's last sub-protocol stands at no fall's seat -/
  he : seatF e₁.place = false
  /-- the last gated sub-protocol has a round -/
  hlast : ∀ A b, pre₁ = A ++ [b] → b.rounds ≠ []
  /-- the last gated sub-protocol stands at no mark's seat, and not with a round at a fall's seat -/
  hend : ∀ A b, pre₁ = A ++ [b] →
    ¬ (seatM b.place = true ∨ (seatF b.place = true ∧ b.rounds ≠ []))
  /-- a sub-protocol at a mark's seat has a round -/
  hmr : ∀ b ∈ pre₁, seatM b.place = true → b.rounds ≠ []
  /-- the number laid for a mark of `fitMarks` is 0 -/
  hq0 : ∀ b ∈ pre₁, qM b ⟨b.place,
    fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
    ⟨0, 1⟩⟩ = 0
  /-- the owners' bounds for their marks -/
  hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
    ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
    List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk)
  /-- the condition `PM` of the marks' bounds holds where no fall has been met and the marks before
  have been silent -/
  hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
    ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
    fellBy F.first.blocksInOrder fs (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
      (fr.drop 0) = false →
    silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr
  /-- the owners' bounds for the counted falls -/
  hF : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
    ∀ g ∈ reps b, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
    FallDebt C g 0 b (b' :: B ++ [e₁]) dsb [] (P b) (qF b g)
  /-- every fall near a sub-protocol lies inside a counted one -/
  hin : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
    ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ [e₁]), f.place = d.place) →
    ∃ g ∈ reps b, ∀ fr s' own, P b fr s' →
      localFall [f] 0 (b :: (b' :: B ++ [e₁])) s' own →
      localFall [g] 0 (b :: (b' :: B ++ [e₁])) s' own
  /-- the condition `P` of the falls' bounds holds at the walk's state; the last premise hands over
  the reached state -/
  hP' : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
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
    P b fr s'
  /-- the numbers add up, at a sub-protocol with a round at a fall's seat -/
  hp₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
    ((hm.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
      p₁ (0 + A.length)
  /-- the marks' numbers add up, at a place that is no fall's seat -/
  hp₂ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = false →
    ((hm.filter fun m => m.place == b.place).map (qM b)).sum ≤ p₁ (0 + A.length)

/-! ## 2 The two lemmas, composed -/

/-- The first chain's bounds, from the structure. -/
theorem debts_asks (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (D : WholeD) {F : FileDescription Xi} (Pr : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) (fs : List (Fall F.S₁)) (hm : List Mark) (p₁ : Nat → ℝ≥0∞)
    {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl} (cut : F.first.blocksInOrder = pre₁ ++ [e₁])
    {file : String} (hdata : F.data file = .ok D) {z₁ : Fmt.DeclaredRound} (he₁ : e₁.rounds = [z₁])
    (hpl : F.placesOk = true)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (hXc : Xc = fun _ => at₁ F Pr w₀ rc x R) {seatF seatM : Place → Bool}
    {PM : Block F.S₁ F.Cl → List Fmt.Drawn → Prop} {qM : Block F.S₁ F.Cl → Mark → ℝ≥0∞}
    {P : Block F.S₁ F.Cl → List Fmt.Drawn → F.S₁ → Prop}
    {qF : Block F.S₁ F.Cl → Fall F.S₁ → ℝ≥0∞} {reps : Block F.S₁ F.Cl → List (Fall F.S₁)}
    (St : FirstAsks C fs hm p₁ pre₁ e₁ x Xc seatF seatM PM qM P qF reps) :
    LocalDebts C F.first.blocksInOrder fs (hm ++ fitMarks pre₁) 0 Xc p₁ [noDraw]
      (silentQ (hm ++ fitMarks pre₁) 0 pre₁) pre₁ 0 0 D.ds₁ :=
  debts_letter C hC D Pr w₀ rc x R fs hm p₁ cut hdata he₁ hpl Xc hXc St.hz seatF seatM St.hfs
    St.hseat St.Hs St.he St.hlast St.hend St.hmr PM qM St.hq0 St.hM St.hPM P qF reps St.hF St.hin
    St.hP' St.hp₁ St.hp₂

/-- The bound on the chance that a run meets a fall, from the structure. `Xc` is named by `hXc`. -/
theorem falls_asks (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) (hm ms₂ ms₃ : List Mark)
    (p₁ p₂ p₃ : Nat → ℝ≥0∞) {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (Sf : StopsFit F (G.prover H) D pre₁ e₁) (hne : pre₁ ≠ [])
    (hf₂ : G.falls₂ = []) (hf₃ : G.falls₃ = [])
    (s₁ : fellBy F.first.blocksInOrder G.falls₁ (at₁ F (G.prover H) w₀ rc x R) 0 [] = false)
    {file : String} (hdata : F.data file = .ok D) {z₁ : Fmt.DeclaredRound} (he₁ : e₁.rounds = [z₁])
    (hpl : F.placesOk = true)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (hXc : Xc = fun _ => at₁ F (G.prover H) w₀ rc x R) {seatF seatM : Place → Bool}
    {PM : Block F.S₁ F.Cl → List Fmt.Drawn → Prop} {qM : Block F.S₁ F.Cl → Mark → ℝ≥0∞}
    {P : Block F.S₁ F.Cl → List Fmt.Drawn → F.S₁ → Prop}
    {qF : Block F.S₁ F.Cl → Fall F.S₁ → ℝ≥0∞} {reps : Block F.S₁ F.Cl → List (Fall F.S₁)}
    (St : FirstAsks C G.falls₁ hm p₁ pre₁ e₁ x Xc seatF seatM PM qM P qF reps)
    (hmk₂ : ∀ A b B, F.shared.blocksInOrder = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C
        ((D.ds₂.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms₂ b.place fr (drawnT C _ ρ) = none)
    (hmk₃ : ∀ A b B, F.second.blocksInOrder = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C
        ((D.ds₃.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms₃ b.place fr (drawnT C _ ρ) = none) :
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R (hm ++ fitMarks pre₁) p₁ pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R ms₂ p₂).map (·.p)).sum +
          ((gates₃ D G H w₀ rc x R ms₃ p₃).map (·.p)).sum) :=
  falls_letter C D tF tJ t3 G H w₀ rc x k R (hm ++ fitMarks pre₁) ms₂ ms₃ p₁ p₂ p₃ hR Sf hne hf₂
    hf₃ s₁ Xc hXc
    (debts_asks C hC D (G.prover H) w₀ rc x R G.falls₁ hm p₁ Sf.cut hdata he₁ hpl Xc hXc St) hmk₂
    hmk₃

end ProofFile.Honest

#print axioms ProofFile.Honest.debts_asks
#print axioms ProofFile.Honest.falls_asks
