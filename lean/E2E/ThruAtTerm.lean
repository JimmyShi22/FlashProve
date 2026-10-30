-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ThruAtTerm.lean: the crossing at T1's names: what the maker returns at onlineFilling against what
it returns at matrixFilling, the filling that onlineFilling reads through. The test on G_u stands
here as the worked case of the shared chain: the side that onlineFilling lays at its place is halfU
read through. Nothing here names a kind's law; the form serves every block of the three chains.

  matrixFilling        the filling that onlineFilling reads through
  named_in_range       its named member is in range
  online_shared_read        the online prover's shared chain is the filling's, read through
  online_shared_of_six where the six are made: the six, halfU and halfO, read through
  online_shared_find   a search by place: what the filling's search finds, read through
  online_plays_shared, online_says_shared   PlaysOn and SaysYes at a block of the shared chain: a
                       kind's statement at the filling's prover gives it at the online prover, at
                       the invariant read through Mid.narrow

Limits.
  * NOT IN FRONT OF A LAW OVER COINS.
  * base and made are premises.
  * That the filling's search finds halfU's side at the test's place is a premise of whoever uses
    online_shared_find.
  * Nothing on completeness, soundness or hiding.
-/
import AtFullSide.Honest.ThruIndex
import Johnson.Desc.ProofFile.Honest.ThruAtBlock

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open VerifiableInference.Desc (Block FileDescription Place)
open OnBytes (TableKey)

/-- **The filling that onlineFilling reads through.** -/
abbrev matrixFilling : OnlineProverParts FullSizeMatrix IndexCommitterCoins Cells Unit Unit :=
  onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- Its named member is in range. -/
theorem named_in_range : matrixFilling.inRange matrixInput.dummy = true :=
  matrixInput_inRange_at fullIn.dummy

section
variable {S Cl : Type} (files : VerifierAndGoals.PublicFiles) {Z : ProofFile.Pub} {Gr : ProofFile.Ground} {F : FileDescription ProofFile.Inst}
  {B : ProverCoinCounts} {H₀ : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
  {H' : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst TableKey Cells Unit Unit}
  {rds₀ : FullSizeMatrix → IndexCommitterCoins → Cells → Readers} {rds : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → Cells → Readers}
  {rws₀ rws : RowDataOf ProofFile.Inst}
  (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling =
    .ok ⟨Z, Gr, F, B, H₀, rds₀, rws₀⟩)
  (made : onlineMaker files = .ok ⟨Z, Gr, F, B, H', rds, rws⟩)
include base made

/-- **The online prover's shared chain is the filling's, read through.** -/
theorem online_shared_read :
    H'.shared = H₀.shared.map (Placed.thru id (Common.thru id (tableCoins files))) :=
  shared_made id (tableCoins files) matrixInput.dummy base made named_in_range

open K12 K12.AtProof in
/-- **Where the six are made: the six, halfU and halfO, read through.** -/
theorem online_shared_of_six {six : List (Placed Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit)}
    (h : nowSharedBy (matrixInput.weights Z) Z = .ok six) :
    H'.shared = (six ++ halfU (matrixInput.weights Z)
        (fun w => Bind.ForProver.encW Z (matrixInput.weights Z w)) Z ++
      halfO (matrixInput.weights Z) Z).map (Placed.thru id (Common.thru id (tableCoins files))) := by
  have e : H₀.shared = matrixFilling.shared Z Gr :=
    congrArg (fun A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit => A.H.shared) (eq_ofFill base)
  have e₂ : matrixFilling.shared Z Gr = six ++ halfU (matrixInput.weights Z)
      (fun w => Bind.ForProver.encW Z (matrixInput.weights Z w)) Z ++
      halfO (matrixInput.weights Z) Z := by
    show sharedWithUO matrixInput Z = _
    rw [sharedWithUO_ok matrixInput h, sharedWithU_ok matrixInput h]
  rw [online_shared_read files base made, e, e₂]

/-- **A search by place in the online prover's shared chain**: what the filling's search finds, read
through. -/
theorem online_shared_find (p : Place) :
    H'.shared.find? (fun x => x.place == p) =
      (H₀.shared.find? fun x => x.place == p).map
        (Placed.thru id (Common.thru id (tableCoins files))) :=
  shared_find_made id (tableCoins files) matrixInput.dummy base made named_in_range p

/-- **PlaysOn at a block of the shared chain**, at the online prover. -/
theorem online_plays_shared {Bk : ProverCoinCounts} {chain ft : Nat} {b : Block S Cl}
    {A C : Coins Bk → S → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Env → Prop}
    (h : PlaysOn .shared Bk chain ft H₀.shared b A C) :
    PlaysOn .shared Bk chain ft H'.shared b
      (fun k s m E => A k s (Mid.narrow (Common.thru id (tableCoins files)) m) E)
      (fun k s m E => C k s (Mid.narrow (Common.thru id (tableCoins files)) m) E) :=
  playsOn_shared_made id (tableCoins files) matrixInput.dummy base made named_in_range h

/-- **SaysYes at a block of the shared chain**, at the online prover. -/
theorem online_says_shared {Bk : ProverCoinCounts} {chain ft : Nat} {b : Block S Cl}
    {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Env → Prop}
    (h : SaysYes .shared Bk chain ft H₀.shared b fall A) :
    SaysYes .shared Bk chain ft H'.shared b fall
      (fun k s m E => A k s (Mid.narrow (Common.thru id (tableCoins files)) m) E) :=
  saysYes_shared_made id (tableCoins files) matrixInput.dummy base made named_in_range h

end

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.named_in_range
#print axioms ProofFile.Honest.Term.online_shared_read
#print axioms ProofFile.Honest.Term.online_shared_of_six
#print axioms ProofFile.Honest.Term.online_shared_find
#print axioms ProofFile.Honest.Term.online_plays_shared
#print axioms ProofFile.Honest.Term.online_says_shared
