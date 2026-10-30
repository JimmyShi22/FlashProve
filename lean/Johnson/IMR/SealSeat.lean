-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SealSeat.lean: A LAW ABOUT THE PROOF FILE's SEAT, NO PART OF IT:
THE CHAIN's LAST BLOCK (THE SEAL) SITS, WITH NO PREMISE (seal_seated): Johnson/IMR/BackSeat.lean's seal_of with its premise SealLast brought down to one closed sentence on a literal, ProofFile.headOf "seal.behind" = "seal", WHICH IS PROVED IN ANOTHER FILE
(ProofFile.head_seal: lean/Johnson/Desc/ProofFile/Law/HeadSeal.lean: the simplifier walks String.splitOnAux step by step; its axioms, as asked in a build of these files: propext · Classical.choice · Quot.sound).
OBJECT. c.last of onlineDescription's first chain: K13's third lot's own block (K13.lotEnd, Johnson/Desc/ProofFile/Lot/K13End.lean: ChainEnd.chainEnd 1 5 true (K13.inFrontOf Z) endAsks).retype, ALONE.
USER. «K13_sits» at the seal (Johnson/Desc/AtSeats/K13SitsJoin.lean) · other files of this folder.
LETTERS. As in Johnson/IMR/BackSeat.lean.
IT CALLS, AND TYPES NONE OF: cutOf_end (lean/Johnson/Desc/First/Driver/CutEnd.lean: how the table of steps ends) · spotsOf_cutOf_of (lean/Johnson/Desc/ProofFile/Law/LastSpot.lean:
the last place is of the kind «frame», in no link) and pubBy_fields (Law/PlainMade.lean: Z.cuts is cutOf's value).

  HeadSeal          the closed sentence ProofFile.headOf "seal.behind" = "seal", as a name: seal_last | seal_sits take it as a premise and keep their statements for who calls them (seal_sits ProofFile.head_seal O).
                    A try by decide +kernel stuck at «"seal.behind".splitOn "."»; the way that goes through lies in the library (OnBytes/K/ServedFreeItem.lean:196-205).
  seal_seated       NO PREMISE: AT EVERY o, OFF AN OPENING ALONE: c.last IS seatedAs sameReply (chainEnd …).retype c.last.name (1, none, 5, frame): ALONE.
  seal_last         under HeadSeal: SealLast Bs.spots, off an opening: at every o, with no premise on scope.
  seal_sits         under HeadSeal: c.last IS seatedAs sameReply (chainEnd …).retype c.last.name (1, none, 5, frame): ALONE.

What is not claimed. What the chain's end decides. Its number in the flat list stands in
Johnson/IMR/BackSeat.lean (back_numbers: 357, in scope). The name. No soundness.
-/
import Johnson.IMR.BackSeat
import Johnson.Desc.ProofFile.Law.LastSpot
import Johnson.Desc.ProofFile.Law.PlainMade
import Johnson.Desc.ProofFile.Law.HeadSeal

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- The one premise left: a closed sentence on a literal. -/
def HeadSeal : Prop := ProofFile.headOf "seal.behind" = "seal"

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The plan's last spot is of the kind «frame» and stands behind the links.** -/
theorem seal_last (hh : HeadSeal) (O : Open o pol lay KL F Z Bs base c A B) : SealLast Bs.spots := by
  intro sp hsp
  obtain ⟨hs, -, -, -⟩ := base_made O.made
  have hc := (ProofFile.Law.pubBy_fields
    (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from O.pub)).2.2.2.1
  obtain ⟨l0, sp', e, hk, hl⟩ := ProofFile.Law.spotsOf_cutOf_of hh hc hs
  rw [e, List.getLast?_concat] at hsp
  obtain rfl := Option.some.inj hsp
  exact ⟨hk, hl⟩

/-- **THE SEAL, UNDER HeadSeal: THE CHAIN's LAST BLOCK IS K13's THIRD LOT's OWN, ALONE.** At every o; no premise on scope. -/
theorem seal_sits (hh : HeadSeal) (O : Open o pol lay KL F Z Bs base c A B) :
    ∃ b', b' ∈ (VerifiableInference.Desc.K13.lotEnd Z).blocks Bs.G₀ ∧
      b' = (VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true (VerifiableInference.Desc.K13.inFrontOf Z)
        VerifiableInference.Desc.First.endAsks : Block S Unit).retype ∧
      LaidAlone ProofFile.sameReply c.last b' c.last.name
        { chain := 1, link := none, piece := 5, kind := .frame } :=
  seal_of O (seal_last hh O)

/-- **THE SEAL SITS, WITH NO PREMISE**: at every o, off an opening alone. (HeadSeal is ProofFile.head_seal.) -/
theorem seal_seated (O : Open o pol lay KL F Z Bs base c A B) :
    ∃ b', b' ∈ (VerifiableInference.Desc.K13.lotEnd Z).blocks Bs.G₀ ∧
      b' = (VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true (VerifiableInference.Desc.K13.inFrontOf Z)
        VerifiableInference.Desc.First.endAsks : Block S Unit).retype ∧
      LaidAlone ProofFile.sameReply c.last b' c.last.name
        { chain := 1, link := none, piece := 5, kind := .frame } :=
  seal_sits ProofFile.head_seal O

end

end IM

#print axioms IM.seal_seated
#print axioms IM.seal_last
#print axioms IM.seal_sits
