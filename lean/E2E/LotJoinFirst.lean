-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinFirst.lean: THE FIRST CHAIN's THREE FIELDS OF THE JOIN (TheLots, E2E/OfflineJoin.lean): firstOwes, firstNext,
firstYes, AT A LAID THREAD AND LETTER, in that structure's own words, so that each field is one call. This file does
not import the join: "an input is tied" stands as a letter Tied, which no proof here reads.

  (joinThread's and joinSaid's text lies in E2E/LotLetters.lean.)
  `joinThread d Q w x`: U₁: the thread Th (E2E/FirstHSeat.lean) at the description's three parts, at the offline prover's own
    senders (offlineValue) and the index's reader (matrixReader), at the input's matrix w.1 and committer's coins w.2.1.
  `joinSaid d Q w x`: S₁: the letter walkedFirst there (E2E/LotBegunFirst.lean).
  `LeftJoin d Q w x`: WHAT IS LEFT, seven fields, TEN CELLS: PlaysS and ExchangeS at 4, 10 · ExchangeS at 5, 11 · PlaysS and
    AcceptedS at 15 · ExchangeS at 16 · (Eval) at 17.
  `sourced_of_description`: the description that the public files make is sourced.
  `noFall`: the join's fall, fallsBy [] …, is none at every member, state and list.
  `leftStruck_of_join`: LeftStruck (E2E/LotFirstFromLeftStruck.lean) from it: what the two lookups' steps keep and what rides
    past them are struck, where Q.kind₁ at 4, 10 is the lookups' LookupKeeps (lotKindFirst, E2E/LotKindFirst.lean).
  **`joinFirstOwes`, `joinFirstNext`, `joinFirstYes`**: the three fields.
  `cellsJoin`, `cellsJoin_count`: the ten cells as a written list, counted by evaluation: 10 of 95.

THE LETTER Q STAYS: Q : LaterFill, with ONE premise: Q.kind₁ = kindFirst d.source d.numbers. Whoever lays Q as a value meets it
by rfl if that field is laid so.

HOW FINE THE FIELDS ARE. pile and eval ARE WIDER THAN THEIR CELLS: pile is all of ExchangeS at 16 (three items), eval is asked from Thr, not
from ThrS. fullPub = some K₀ is no premise here: K₀ is any. THE FIT TO TheLots IS BY ITS TEXT AND A COPY OF ITS WORDS until the join is built.

Limits. AN IMPLICATION. A member of LeftJoin at the laid letters, at every input: leftJoin_laid (E2E/LotJoinLaid.lean). ThrS in front, the premise inside every debt, is met by
nothing here (the stand: E2E/LotStandFirst.lean, under «ready returns»). Nothing on the fields sits and run, on the shared or
the last chain. AT NO FALL: acceptance at 15 is asked at every list that fits. In scope, where the test on the public files
says yes. The list of cells is written beside the structure: only a reading ties them. Nothing on soundness, completeness,
hiding or binding.
-/
import E2E.LotLetters
import E2E.LotFirstFromLeftStruck
import E2E.LotKindFirst
import E2E.LotFirstPublicAtValue
import E2E.LotBegunFirst
import Johnson.Desc.ProofFile.Honest.Law.FallFree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState KItem)
open AtPublicFiles.KeyFile (In1)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.Lookup.Key (LookupKeeps)
open ProofFile.Honest.K12.AtKey (RngYes)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-- The join's fall is none. -/
theorem noFall {S Cl : Type} (bs : List (Block S Cl)) (j : Nat) (s : S) (ds : List Fmt.Drawn) :
    fallsBy [] bs j s ds = none := by
  unfold fallsBy
  cases bs[j]? with
  | none => rfl
  | some b =>
    show fallOf [] b.place s ds = none
    simp [fallOf]

/-- The description that the public files make is sourced, where the test on them says yes. -/
theorem sourced_of_description {Z : PublicFiles} {d : OfflineDescription}
    (hd : offlineDescription Z = .ok d) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    KeySourced Z d.source d.numbers d.later := by
  obtain ⟨X, N, P, hs⟩ := AtPublicFiles.AtFiles.key_sourced Z live
  obtain ⟨X₀, m, h0, hm, hX, hN, hP⟩ := hs.source
  have e : offlineDescription Z = .ok ⟨X, N, P⟩ := by
    simp only [offlineDescription, h0, hm, hX, hN, hP, bind, Except.bind, pure, Except.pure]
  rw [hd] at e
  obtain rfl : d = ⟨X, N, P⟩ := Except.ok.inj e
  exact hs

section
variable {Z : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
  (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)

/-- **WHAT IS LEFT OF THE FIRST CHAIN AT THE JOIN**, at one input: ten cells. A premise's form. -/
structure LeftJoin (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) : Prop where
  playsK3 : ∀ b ∈ [4, 10], PlaysS (joinThread d Q w x) (joinSaid d Q w x) b
  exchangeK3 : ∀ b ∈ [4, 10], ExchangeS (joinThread d Q w x) (joinSaid d Q w x) b
  exchangeLayer : ∀ b ∈ [5, 11], ExchangeS (joinThread d Q w x) (joinSaid d Q w x) b
  playsRanges : PlaysS (joinThread d Q w x) (joinSaid d Q w x) 15
  acceptedRanges : AcceptedS (joinThread d Q w x) (joinSaid d Q w x)
    (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder) 15
  pile : ExchangeS (joinThread d Q w x) (joinSaid d Q w x) 16
  eval : ∀ blk, (joinThread d Q w x).bs[17]? = some blk → ∀ k s m E ds y cols s',
    Thr (joinThread d Q w x) 17 k s m E → drawsFit blk.rounds ds = true →
    (joinThread d Q w x).Stepped blk k s m E ds y cols s' →
    (joinThread d Q w x).Items [.claim 1 "Eval"] k s' y.2 (E.add y.1)

variable {d Q}

/-- What the two lookups' steps keep and what rides past them are struck. -/
theorem leftStruck_of_join (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (h4 : Q.kind₁ 4 = LookupKeeps) (h10 : Q.kind₁ 10 = LookupKeeps)
    {w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed} {x : Xi} (left : LeftJoin d Q w x) :
    LeftStruck d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x
      (joinSaid d Q w x) (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder) where
  playsK3 := left.playsK3
  keepsK3 := by
    intro b hb blk hblk k s m E ds y cols s' hA hd hS
    have h := ((lotKindFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q
      w.1 w.2.1 x hs scope h4 h10 (joinSaid d Q w x) b hb).1 blk hblk k s m E ds y cols s' hA hd
      hS).2.2
    have hb' := hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl <;> exact h
  exchangeK3 := left.exchangeK3
  ridesK3 := fun b hb =>
    (lotKindFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x
      hs scope h4 h10 (joinSaid d Q w x) b hb).2
  exchangeLayer := left.exchangeLayer
  playsRanges := left.playsRanges
  acceptedRanges := left.acceptedRanges
  pile := left.pile
  eval := left.eval

variable (Tied : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Prop)

/-- Both at once. -/
theorem joinFirst (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hQ : Q.kind₁ = kindFirst d.source d.numbers)
    {w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed} {x : Xi} (left : LeftJoin d Q w x) :
    OwesS (joinThread d Q w x) (joinSaid d Q w x) ∧
      YesS (joinThread d Q w x) (joinSaid d Q w x)
        (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder) := by
  have hs := sourced_of_description hd live
  exact firstFromStruck hs scope (firstPublic_atFiles hd scope live) (by rw [hQ]; rfl) _ _
    (leftStruck_of_join hs scope (by rw [hQ]; rfl) (by rw [hQ]; rfl) left)

/-- **The field firstOwes.** -/
theorem joinFirstOwes (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hQ : Q.kind₁ = kindFirst d.source d.numbers)
    (left : ∀ w x, Tied w x → LeftJoin d Q w x) :
    ∀ w x, Tied w x → OwesS (joinThread d Q w x) (joinSaid d Q w x) :=
  fun w x ht => (joinFirst hd scope live hQ (left w x ht)).1

/-- **The field firstNext.** -/
theorem joinFirstNext : ∀ w x, Tied w x → ∀ b, SaidNext (joinThread d Q w x) (joinSaid d Q w x) b :=
  fun w x _ => lotSaidNextFirst d.source d.numbers d.later _ matrixReader Q w.1 w.2.1 x

/-- **The field firstYes.** -/
theorem joinFirstYes (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hQ : Q.kind₁ = kindFirst d.source d.numbers)
    (left : ∀ w x, Tied w x → LeftJoin d Q w x) :
    ∀ w x, Tied w x → YesS (joinThread d Q w x) (joinSaid d Q w x)
      (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder) :=
  fun w x ht => (joinFirst hd scope live hQ (left w x ht)).2

end

/-- The unpaid cells of LeftJoin: member and debt. A written list. -/
def cellsJoin : List (Nat × String) :=
  cellsStruck.filter fun c => !((c.1 == 4 || c.1 == 10) &&
    (c.2 == "BehindS: keeps" || c.2 == "RidesPastS"))

/-- The count, by evaluation. -/
theorem cellsJoin_count : cellsJoin.length = 10 ∧ 19 * 5 - cellsJoin.length = 85 := by decide

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.noFall
#print axioms AtPublicFiles.FirstH.Lots.sourced_of_description
#print axioms AtPublicFiles.FirstH.Lots.leftStruck_of_join
#print axioms AtPublicFiles.FirstH.Lots.joinFirst
#print axioms AtPublicFiles.FirstH.Lots.joinFirstOwes
#print axioms AtPublicFiles.FirstH.Lots.joinFirstNext
#print axioms AtPublicFiles.FirstH.Lots.joinFirstYes
#print axioms AtPublicFiles.FirstH.Lots.cellsJoin_count
