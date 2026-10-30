-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/Told338N.lean.
WHAT IT DOES NOT SHOW. No soundness. One small fact on the list of what the first chain's
sub-protocols tell; nothing on any state of the verifier. In scope and under the opening O alone.
WORDS. "Tells" (Desc/Sound/PieceFence.lean: toldOf): for each sub-protocol, in order, the oracle
messages beneath the roots that it sends, all rounds together.
LETTERS. No "there is".
OBJECT. In the goals' scope, at the opened value of the IOP as written in Lean: the flat list of its
first chain's sub-protocols, at the number 338: the next token's place.
USER. The next token's law's bill: its field told (Law/K7Seated.lean: K7Rest; Law/K07AtConst.lean:
hall), at told := toldOf c.blocksInOrder, which is what the table's closed structure lays.
WHAT IT IS. THE NEXT TOKEN's PLACE TELLS NO ORACLE MESSAGE.
told_338: by IM.k7_sits (what stands at 338: the entry, the next token's own, and
the link's "opened" joined behind): none of the three declares one.

-/
import Johnson.IMR.FirstSeats
import Johnson.IMR.FlatScope
import Johnson.Desc.Sound.PieceFence

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (toldOf)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- **The next token's place tells no oracle message.** -/
theorem told_338 {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (toldOf c.blocksInOrder)[338]? = some [] := by
  obtain ⟨Lk, b, e1, e2, hj, -⟩ := IM.k7_sits hS hR O
  have f1 : c.blocksInOrder[338]? = some b := by
    have q := IM.hear_at_flat e1 e2
    rwa [IM.flatIx_scope hS hR O (by decide) 0] at q
  obtain ⟨fs, f, -, -, hb⟩ := hj
  unfold toldOf
  rw [List.getElem?_map, f1]
  show some (b.oracles.flatMap id) = some []
  rw [hb]
  rfl

end P4

#print axioms P4.told_338
