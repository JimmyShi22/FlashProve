--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyQuietThird.lean: THE THREE SUB-PROTOCOLS OF THE KEY FILE's THIRD CHAIN THAT HAVE NO ROUND ARE
ACCEPTED, FROM NAMED PREMISES: the rule "structure | values" (`accepted_of_shape`,
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean; at a sub-protocol without a round:
E2E/ShapeQuiet.lean) called at the third chain's shape (`Z₃Own`, E2E/KeyShapeOwn.lean). By calls. At
ANY thread over that chain's flat list: no clause has to be laid into the thread's sentence. NOTHING
IS CLAIMED OF WHAT THE PARTS SEND.

  `ThirdShaped T₃ vOwn a₀`: the two premises that all three share: hyes and hfirst, below.
  **`accepted_third₁`** ("the taken trees' sources"), **`accepted_third₃`** (the chain's end):
    `Accepted` at numbers 1 and 3: these have no named test on values.
  **`accepted_third₀`** ("K14, second part"): `Accepted` at number 0, under `Values` there: its one
    named test on values ("no coefficient on a pad") passes on the honest side.

PAID BY CALLS, IN SCOPE: (B1) at all four sub-protocols (`carries_all_in_scope`) · (B2) at numbers
0, 1, 3 (`returns₀`, `returns₁`, `returns₃`, E2E/KeyShapeChain.lean) · `FitsAt`, and `Values` at 1
and 3 (E2E/ShapeQuiet.lean).
THE PRICE: PREMISES THAT ARE LEFT, BY NAME:
- **hyes: THE SHAPE's OWN RUN OVER ALL FOUR SUB-PROTOCOLS RETURNS, FROM THE FIRST SHAPE a₀**
  (`Shape.yes`): an evaluation on public values. IN SCOPE IT IS SHOWN NOWHERE. E2E/KeyShapeOwn.lean
  evaluates it in Lean's kernel at written values, from the shape of a synthetic state: not a run's.
- **hfirst: AT A VALID INPUT EVERY STATE AT WHICH THE CHAIN MAY BEGIN HAS THE FIRST SHAPE a₀.** The
  third chain begins at the door behind the two earlier chains: so this speaks of their ends. It is
  shown nowhere.
- a₀ itself is a letter.
- `Values` at number 0: owed by whoever lays the prover's parts.

Limits.
- CONDITIONAL THROUGHOUT. Where hyes fails the statements say nothing.
- Number 2, the own proximity test, has rounds: (B2) is not had there: it is not treated.
- The description's last test on this chain's last state needs no shape: E2E/KeyEndGives.lean.

-/
import E2E.ShapeQuiet
import E2E.KeyShapeOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open ProofFile.Honest AtPublicFiles.KeyLink
open VerifiableInference.Desc.Third (S₃)

variable {Z : VerifierAndGoals.PublicFiles} {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {V W Xh Pb : Type} {Bk : ProverCoinCounts}
  (T₃ : Thread Bk (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl V W Xh Pb)
  (vOwn : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (a₀ : Sh₃)

/-- **The two premises that all three share.** -/
structure ThirdShaped : Prop where
  /-- the shape's own run over all four sub-protocols returns -/
  yes : (Z₃Own X P vOwn).yes a₀ 4 = true
  /-- at a valid input every state at which the chain may begin has the first shape -/
  first : ∀ k w h s₀, T₃.valid w → T₃.begun k w h s₀ → (Z₃Own X P vOwn).sh s₀ = a₀

variable {T₃ vOwn a₀} (hbs : T₃.bs = (keyFileDescription X N P).second.blocksInOrder) (hs : KeySourced Z X N P)
  (scope : VerifierAndGoals.InScope Z = true) (hZ : ThirdShaped T₃ vOwn a₀)
  {fall : Nat → (keyFileDescription X N P).S₃ → List Fmt.Drawn → Option String}
include hbs hs scope hZ

/-- **"The taken trees' sources" is accepted.** -/
theorem accepted_third₁ : Accepted T₃ fall 1 := by
  obtain ⟨blk, e, hr⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[1]? = some blk ∧ blk.rounds = [] :=
    ⟨_, rfl, rfl⟩
  refine accepted_quiet_shape T₃ (Z₃Own X P vOwn) (n := 4) (a₀ := a₀)
    (by rw [hbs]; exact Nat.le_refl 4) (by decide) hZ.yes hZ.first (fun j => ?_) ?_
    (by rw [hbs]; exact e) hr fun _ _ _ => rfl
  · rw [hbs]
    exact carries_all_in_scope hs scope vOwn T₃.ft j
  · rw [hbs]
    exact returns₁ X N P _ vOwn T₃.ft

/-- **The chain's end is accepted.** -/
theorem accepted_third₃ : Accepted T₃ fall 3 := by
  obtain ⟨blk, e, hr⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[3]? = some blk ∧ blk.rounds = [] :=
    ⟨_, rfl, rfl⟩
  refine accepted_quiet_shape T₃ (Z₃Own X P vOwn) (n := 4) (a₀ := a₀)
    (by rw [hbs]; exact Nat.le_refl 4) (by decide) hZ.yes hZ.first (fun j => ?_) ?_
    (by rw [hbs]; exact e) hr fun _ _ _ => rfl
  · rw [hbs]
    exact carries_all_in_scope hs scope vOwn T₃.ft j
  · rw [hbs]
    exact returns₃ X N P _ vOwn T₃.ft

/-- **"K14, second part" is accepted**, where its named test on values passes on the honest side. -/
theorem accepted_third₀ (hV : Values T₃ (Z₃Own X P vOwn) fall 0) : Accepted T₃ fall 0 := by
  obtain ⟨blk, e, hr⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[0]? = some blk ∧ blk.rounds = [] :=
    ⟨_, rfl, rfl⟩
  refine accepted_of_shape T₃ (Z₃Own X P vOwn) (n := 4) (a₀ := a₀)
    (by rw [hbs]; exact Nat.le_refl 4) (by decide) hZ.yes hZ.first (fun j => ?_) ?_
    (fitsAt_quiet T₃ (by rw [hbs]; exact e) hr) hV
  · rw [hbs]
    exact carries_all_in_scope hs scope vOwn T₃.ft j
  · rw [hbs]
    exact returns₀ X N P _ vOwn T₃.ft

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.accepted_third₁
#print axioms AtPublicFiles.AtFiles.accepted_third₃
#print axioms AtPublicFiles.AtFiles.accepted_third₀
