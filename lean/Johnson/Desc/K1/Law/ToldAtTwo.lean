-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ToldAtTwo.lean: PlanAt's FIELD told AT W's SENDING (the flat list's number 356)
AND AT THE OPENING (2), IN THE BINDERS' OWN TYPES; and at every number k beside. A payment in a file
of its own.

  told_at_flat     IN THE JOIN's LETTERS: the data dataOf aN R₁ R₂ R₃, any G: where the first
                   chain's list of the data is writtenPFull's (eD) and G declares osC (hO): told
                   at the two rounds in front of which inFront c k rounds stand: at every k.
  told_W, told_G   the same at 356 and at 2, with the binders' two idle antecedents.
  data_atAll       AT THE CONSTANT: under the head the laid data's list is the written.
  declares_atAll   there, under the test on the cut, the constant's G declares osC.
  htold_atAll      so told at every k.
  htoldW_atAll, htoldG_atAll   W_HP_atAll's and G_HP_atAll's last binders
                   (Johnson/Desc/K1/Law/RadiiAtTwo.lean), to the letter: FROM hA AND hP2 ALONE.

All by told_written (Johnson/Desc/AtSeats/ToldAnywhere.lean).
What is not claimed. The head hA; the cut's test hP2; eD; hO. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RadiiAtTwo
import Johnson.Desc.AtSeats.ToldAnywhere
import Johnson.Desc.AtSeats.FromTheCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain FileDescription oraclesOf osC)
open VerifiableInference.Desc.Sound (nTrees)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.PlanWritten (cutIs cutIs_eq)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile (Cl)

/-- **In the join's letters, at every number of the flat list.** -/
theorem told_at_flat {Xi : Type} (G : FileDescription Xi) (hO : oraclesOf G.first.blocksInOrder = osC) {aN : ℕ}
    {R₁ R₂ R₃ : Rounds} (eD : (Sound.dataOf aN R₁ R₂ R₃).ds₁ = writtenPFull.ds₁) (c : Chain S Cl)
    (k : ℕ) : ∀ d₁ d₂ : RDT,
      ((Sound.dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c k)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      G.oracleAt (nTrees ((Sound.dataOf aN R₁ R₂ R₃).ds₁.take (inFront c k)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W := by
  rw [eD]
  exact HashBuild.told_written G hO (inFront c k)

theorem told_W {Xi : Type} (G : FileDescription Xi) (hO : oraclesOf G.first.blocksInOrder = osC) {aN : ℕ}
    {R₁ R₂ R₃ : Rounds} (eD : (Sound.dataOf aN R₁ R₂ R₃).ds₁ = writtenPFull.ds₁) (c : Chain S Cl)
    (P : Par) : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry P → d₁.kind = .seeds →
      ((Sound.dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      G.oracleAt (nTrees ((Sound.dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W :=
  fun d₁ d₂ _ _ => told_at_flat G hO eD c 356 d₁ d₂

theorem told_G {Xi : Type} (G : FileDescription Xi) (hO : oraclesOf G.first.blocksInOrder = osC) {aN : ℕ}
    {R₁ R₂ R₃ : Rounds} (eD : (Sound.dataOf aN R₁ R₂ R₃).ds₁ = writtenPFull.ds₁) (c : Chain S Cl)
    (P : Par) : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry P → d₁.kind = .seeds →
      ((Sound.dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      G.oracleAt (nTrees ((Sound.dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W :=
  fun d₁ d₂ _ _ => told_at_flat G hO eD c 2 d₁ d₂

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)

include hA in
/-- Under the head the laid data's list is the written data's. -/
theorem data_atAll (a : ℕ) : (D.at a).ds₁ = writtenPFull.ds₁ := by
  have hD : D = writtenPFull := Except.ok.inj (hA.laid.data.symm.trans
    (VerifiableInference.PlanWritten.seat_in_scope _ _ Zl hA.scope
      (LPFD.asks_written hA.laid.asks)).2.2)
  show D.ds₁ = _
  rw [hD]

include hP2 in
/-- Under the test on the cut the constant's G declares the written list. -/
theorem declares_atAll : oraclesOf hA.𝔇.G.first.blocksInOrder = osC :=
  oracles_of_cut (cutIs_eq hP2).1

include hP2 in
/-- **At the constant, at every number of the flat list.** -/
theorem htold_atAll (k : ℕ) : ∀ d₁ d₂ : RDT,
      ((D.at frS.P.T.a).ds₁.drop (inFront cF k)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      hA.𝔇.G.oracleAt (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF k)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W := by
  rw [data_atAll hA]
  exact HashBuild.told_written hA.𝔇.G (declares_atAll hA hP2) (inFront cF k)

include hP2 in
/-- **W_HP_atAll's binder htold.** -/
theorem htoldW_atAll : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Zp wMsgFull) →
      d₁.kind = .seeds → ((D.at frS.P.T.a).ds₁.drop (inFront cF 356)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      hA.𝔇.G.oracleAt (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W :=
  fun d₁ d₂ _ _ => htold_atAll hA hP2 356 d₁ d₂

include hP2 in
/-- **G_HP_atAll's binder htold.** -/
theorem htoldG_atAll : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Zp)) →
      d₁.kind = .seeds → ((D.at frS.P.T.a).ds₁.drop (inFront cF 2)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      hA.𝔇.G.oracleAt (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W :=
  fun d₁ d₂ _ _ => htold_atAll hA hP2 2 d₁ d₂

end

end VerifiableInference.Desc.K1
