-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/RcLastCode.lean: no soundness is claimed.
A light cut for a file of evaluations along a walk: the definitions with code alone, apart from their laws: so that the tests that ride are the tests that the theorems speak of. No theorem.
  sampleAtB cs sh St o      (out of ThreeAtW.lean, unturned): the message number o is there with the shape sh, and K12's files' test sampleL accepts it
  sampleTwoB cs V s         (out of RcLast.lean, unturned): where firstOfS s hands f: the group at f.own has two members, and sampleAtB accepts the first at V.indexShape, the second at V.wShape
  **rcLastB ft V L cs s**   (out of RcLast.lean, unturned) := bookInOrderB ft s.book s.roots && bookFitsB s.book && ownSitsB V s && sampleTwoB cs V s && seatsCarriedB L s.book
  p14At Z                   (out of LastBlocks.lean, unturned): K14's second part's parameters, as the seat lays them: for the letters (p14At Z).codes | (p14At Z).S.w at which the last table spends the test
It imports seven files (under Johnson/): Desc/Third/K14Second (p₁₄Z) · Desc/ProofFile/Pub (ProofFile.Pub) · Desc/K12/Law/SampleOk (sampleL) · Desc/Third/Border (firstOfS) · Desc/Last/OwnSits (OwnSeats · ownSitsB) · Desc/Sound/BookTests (bookFitsB) · Desc/K12/Door/DoorBools (bookInOrderB · seatsCarriedB · Laid).
ThreeAtW.lean, RcLast.lean and LastBlocks.lean (all three in this folder) import it and do not define these four.
-/
import Johnson.Desc.K12.Law.SampleOk
import Johnson.Desc.Third.Border
import Johnson.Desc.Last.OwnSits
import Johnson.Desc.Sound.BookTests
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.Third.K14BatchLinearConstraintsSecondPart
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (firstOfS)
open VerifiableInference.Desc.K12.Door (bookInOrderB seatsCarriedB)
open H2K.First (Seat1 ok)
open H2K.Pin (sampleL)

/-- K14's second part's parameters, as the seat lays them. -/
def p14At (Z : ProofFile.Pub) : VerifiableInference.Desc.Third.P₁₄ :=
  VerifiableInference.Desc.Third.p₁₄Z Z.p.chains.made.sized.proof.set
    Z.p.chains.made.sized.proof.codes Z.p.chains.made.sized.proof.batch

/-- The message number o is there with the shape sh, and the test `sampleL` accepts it. -/
def sampleAtB (cs : Codes) (sh : OracleShape) (St : Statement) (o : ℕ) : Bool :=
  match St.oracles[o]? with
  | some x => decide (x.shape = sh) && ok (sampleL cs ⟨o, sh, 0, 0, default, 0⟩ x)
  | none => false

/-- The test `sampleL` accepts the two members of the own group that is handed. -/
def sampleTwoB (cs : Codes) (V : OwnSeats) (s : First.S) : Bool :=
  match firstOfS s with
  | some f =>
    match f.st.groups[f.own]? with
    | some G =>
      match G.members.toList with
      | [i₁, i₂] => sampleAtB cs V.indexShape f.st i₁ && sampleAtB cs V.wShape f.st i₂
      | _ => false
    | none => false
  | none => true

/-- **All that the last chain's ledger spends of the first chain's last state.** -/
def rcLastB (ft : ℕ) (V : OwnSeats) (L : K12.Door.Laid) (cs : Codes) (s : First.S) : Bool :=
  bookInOrderB ft s.book s.roots && bookFitsB s.book && ownSitsB V s && sampleTwoB cs V s &&
    seatsCarriedB L s.book

end ToldDesc
