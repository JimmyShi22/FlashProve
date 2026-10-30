-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorAhead.lean: SH₃ AT THE SEATED START, WITH "THE MASKS GO AHEAD" PAID:
wherever the proof file's description's public part Z is computed, the last chain's parameters at
the seat (`ProofFile.pAt Z`) send the masks ahead. Statements and proofs; no definition.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`ahead_at_seat`**: `ProofFile.pureRoad.pub o pol lay KL = .ok Z` gives `(ProofFile.pAt Z).S.masksAhead =
    true`: two laws of other files in a row: `ProofFile.Law.pub_chainsOf`
    (Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean: `Verify.chainsOf` itself returns `Z.p.chains`)
    and `OnBytes.Model.Verify.p₁₄Z_masksAhead` (Johnson/Desc/Third/Law/MasksAhead.lean, which rests
    on `masksAhead_of_linSized`, Johnson/Desc/Last/ShapeMask.lean).
  **`sh₃_at_pub`**: `sh₃_at_seat_filled` (Johnson/Desc/Last/ShapeDoorAtSeat.lean) with that: LEFT AS
    PREMISES: hZ (Z is the computed public part: `descPure_cut` gives it from `onlineDescription`'s return) ·
    hg (the reader's second half is the record) · h1, h2, h3 (the list of places has a place of kind
    K1 behind the links of chain 1) · hd (no later row of what lay in the filling drops
    "K13.doorFirst").

Every "there is": none.
Limits. Those of ShapeDoorAtSeat.lean: the two texts in the promises in front are still to be
earned; N, Pm₀, Mg₀, N₁, links, split, T, R, g are letters. NO MEMBER. Nothing on soundness or on
hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorAtSeat
import Johnson.Desc.Third.Law.MasksAhead
import Johnson.Desc.ProofFile.Law.PlainIsPlanned

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.First (Meaning Numbers ModelPart nDoor fillDoor)
open _root_.Desc.K14 (St)

/-- **Where the public part is computed, the seat's parameters send the masks ahead.** -/
theorem ahead_at_seat {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) : (ProofFile.pAt Z).S.masksAhead = true :=
  OnBytes.Model.Verify.p₁₄Z_masksAhead (ProofFile.Law.pub_chainsOf hZ)

/-- **SH₃ AT THE SEATED START, THE DOOR's LAYER, AND A COMPUTED PUBLIC PART.** -/
theorem sh₃_at_pub {C : CK} {D : WholeD} {all : List LeftT} {Y P₀ X₁ X₂ Cl Wt W₁ : Type}
    (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (Np : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (R : List Fmt.DeclaredRound)
    (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (T : Three C D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm₀ : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (Mg₀ : Meaning P₀ W₁) (links : List ModelPart)
    (a : List Place) (p : Place) (l : List Place) (h1 : p.chain = 1) (h2 : p.link = none)
    (h3 : p.kind = .K1) (hd : ∀ p' ∈ l, nDoor ∉ (Mg₀.more.rows links p').drops)
    (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N (besideP Pm₀ (doorX (ProofFile.pAt Z) (1 + T.l₂.length)))
      (ocEnd g N₁ (fillDoor Mg₀) links (a ++ p :: l)) split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s) :
    (fillZ (ProofFile.pAt Z) R fun q => (g q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true :=
  sh₃_at_seat_filled o Z Np c R g hg T N Pm₀ split N₁ Mg₀ links a p l h1 h2 h3 hd
    (ahead_at_seat hZ) b s hb hs

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.ahead_at_seat
#print axioms VerifiableInference.Desc.Last.sh₃_at_pub
