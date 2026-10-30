-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontAtSeat.lean: the test frontFiveB on entry to the last
chain's own test, at the seated place's parameters.

  opens_one        at the written place every tree taken from the shared chain bears the number 1
  omegaIs_of_tied  Omega's tree bears the number 1, from the yes of the block on the taken sources
  sameCore_at_seat the shape on entry agrees with the closed shape
  frontFive_at_seat   the statement

The head is AtMgA at the older hash. alike_head_W is in AtFullSide/K12/RestTiesAtHeadW.lean.

Premises beside the two folds, the start, the block and the way in: the block own's rounds are the
seated block's (rfl at the file's own block), and the yes of the block on the taken sources (Tied).

Limits.
- alike_head_W's file stands over a file not yet in the library, and imports from Johnson/ to the side
  library: at landing this file and what stands over it belong in the side library, or the law moves.
- The full size alone, at the files in the head's scope.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontIndexTree
import AtFullSide.K12.RestTiesAtHeadW
import Johnson.IMR.OneOmegaAtHead
import Johnson.Desc.Third.Law.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ batchLinearConstraintsSecondPart sharedOfEnd opensTaken)
open VerifiableInference.Desc.Ground.Sh (coreSh)
open ProofFile.Honest.Sh (testSh)
open ProofFile.Honest.K12.AtProof (fourOf)
open H2K.Member (piWFull codesFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- **At a place whose openings from the chain 1 all name 1, a tree so taken bears the number 1.** -/
theorem opens_one {π : VerifiableInference.Desc.K12.P12} (ho : ToldDesc.oneOmegaB π 1 = true)
    {rounds : List Fmt.DeclaredRound} (hr : rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds) {n : ℕ}
    (h : opensTaken rounds 1 n = true) : n = 1 := by
  unfold opensTaken at h
  obtain ⟨r, hr₁, h⟩ := List.any_eq_true.1 h
  obtain ⟨o, ho₁, h⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hall := List.all_eq_true.1 ho o (List.mem_flatMap.2 ⟨r, hr ▸ hr₁, ho₁⟩)
  rw [h.1] at hall
  simpa using hall

/-- **Omega's tree bears the number 1**, from the yes of the block on the taken sources. -/
theorem omegaIs_of_tied {Cl : Type} (p : VerifiableInference.Desc.Third.P₁₄)
    (own : Block S₃ Cl) {s₀ s : S₃} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s)
    (ht : VerifiableInference.Desc.Third.Law.Tied own s) {E₂ : Proof.SharedEnd}
    {b : VerifiableInference.Desc.Third.Border} (hb : s₀.loc.border = some b)
    (hbs : b.shared = sharedOfEnd E₂)
    (hone : ∀ n, opensTaken own.rounds 1 n = true → n = 1) : OmegaIs (sharedOfEnd E₂) := by
  obtain ⟨x, q, t, hx, hq, hT, hop⟩ := VerifiableInference.Desc.Third.Law.omega_tied p own s₀ s rs gs h₁ ht
  obtain rfl := Option.some.inj (hx.symm.trans hb)
  rw [← hbs]
  exact ⟨q, t, hq, hT, hone _ hop⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **On entry to the last chain's own test the shape agrees with the closed shape**, from the yes of
the block on the taken sources. -/
theorem sameCore_at_seat {Cl : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (pI : ProofFile.InstPub)
    {e₁ : S} {d : Desc.K14.St} {r₁ r₀ r₂ u : List Fmt.RoundView} {c₁ c₀ c₂ v : List OpenedColumn}
    (hf₁ : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀))
    (hf₂ : foldBlocks 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₂ pI) r₂ c₂ = .ok (d, u, v)) {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12}
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ pI e₁ d = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) (H2K.JointK.p₁₄N Zp)).decide s₀ rs gs = .ok s)
    (h₂ : enterOwn s = .ok t) (own : Block S₃ Cl)
    (hr : own.rounds = (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W) : Block T12 Unit).rounds)
    (ht : VerifiableInference.Desc.Third.Law.Tied own s) :
    SameCore [4, 197, 198, 199] t.g 0 (coreSh ⟨t.st, t.book, t.roots⟩) narrowW ∧
      t.mask = some 198 ∧ t.pass = .nothing := by
  have hO : ∀ E₂, Desc.K14.ended d = some E₂ → OmegaIs (sharedOfEnd E₂) := by
    intro E₂ hE
    obtain ⟨E₃, f, hE₃, -, h0⟩ := startParts hs
    obtain rfl : E₂ = E₃ := Option.some.inj (hE.symm.trans hE₃)
    obtain ⟨g₀, hbd⟩ := VerifiableInference.Desc.Third.Law.start₃E_border _ _ _ _ _ _ _ _ _ _ _ h0
    exact omegaIs_of_tied _ own h₁ ht hbd rfl fun n hn =>
      opens_one (IM.Seats.oneOmega_at_head h.toAtMg) hr hn
  exact sameCore_at_own h pI hf₁ hf₂ hs h₁ h₂ hO (indexTree_at_end h hf₁)

/-- **The test frontFiveB says yes on entry to the last chain's own test**, at the seated place. -/
theorem frontFive_at_seat {Cl : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (pI : ProofFile.InstPub)
    {e₁ : S} {d : Desc.K14.St} {r₁ r₀ r₂ u : List Fmt.RoundView} {c₁ c₀ c₂ v : List OpenedColumn}
    (hf₁ : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) r₁ c₁ = .ok (e₁, r₀, c₀))
    (hf₂ : foldBlocks 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₂ pI) r₂ c₂ = .ok (d, u, v)) {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12}
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ pI e₁ d = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) (H2K.JointK.p₁₄N Zp)).decide s₀ rs gs = .ok s)
    (h₂ : enterOwn s = .ok t) (own : Block S₃ Cl)
    (hr : own.rounds = (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W) : Block T12 Unit).rounds)
    (ht : VerifiableInference.Desc.Third.Law.Tied own s) :
    frontFiveB (fourOf Np).W codesFull (testSh t) = true := by
  obtain ⟨hc, hm, hp⟩ := sameCore_at_seat h pI hf₁ hf₂ hs h₁ h₂ own hr ht
  have e : testSh t = ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, .nothing, some 198⟩ := by
    unfold testSh
    rw [hp, hm]
    rfl
  rw [ProofFile.Honest.K12.Light.frontFiveB_alike (ProofFile.Honest.K12.Light.alike_head_W h.toAtMg), e,
    ← frontFive_same hc piWFull codesFull early_written (id := 198) (by simp)]
  exact frontFive_narrowW

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.opens_one
#print axioms ProofFile.Honest.K12.AtFile.omegaIs_of_tied
#print axioms ProofFile.Honest.K12.AtFile.sameCore_at_seat
#print axioms ProofFile.Honest.K12.AtFile.frontFive_at_seat
