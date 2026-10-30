-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorWithX.lean: THE DOOR OF THE LAST CHAIN CARRIES A FURTHER TEST X ON THE
SHARED CHAIN'S LAST RECORD: SH₃'s conclusion AND X, where X is laid beside `doorX` in the shared
table's `shape` at the last border. For the last chain's row 0
(their layer over `fillZ` asks `shape k q e s && X e`). Statements and proofs; no definition.

Main names (namespace `VerifiableInference.Desc.Last`).
  `x_at_last`: inside `onQ₂ N (besideP Pm₀ fun k d => doorX p K k d && (k != K || X d)) Oc split f l
    K` the test X holds of the record: general in every letter.
  **`sh₃_at_pub_X`**: at the seated start, the door's layer and a computed public part (the letters
    and premises of `sh₃_at_pub`, Johnson/Desc/Last/ShapeDoorAhead.lean), with that promise in
    front: `(fillZ (ProofFile.pAt Z) R fun q => (g q).2).shape 0 … = true` AND `X b.1.2 = true`.

HOW. `beside_beside` (Johnson/Desc/Sound/LedgerBeside.lean): two tests laid one after the other are
one: so the promise is `besideP (besideP Pm₀ fun k d => k != K || X d) (doorX p K)`, and
`sh₃_at_pub` is called at that Pm₀.
Limits. X is a letter: whoever lays it owes it at the shared chain's last block's yes; at every
other border it asks nothing. Those of ShapeDoorAhead.lean. NO MEMBER. Nothing on soundness or on
hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorAhead

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

/-- **Inside the promise at the border K the further test holds of the record.** -/
theorem x_at_last {P₁ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Pm₀ : PromMeaning St)
    (Oc : P₁ → Strs → Prop) (split : Bool) (f : Piece C Fr (P₁ × St) Cl Wt)
    (l : List (Piece C Fr (P₁ × St) Cl Wt)) (p : P₁₄) (K : ℕ) (X : St → Bool)
    (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (besideP Pm₀ fun k d => doorX p K k d && (k != K || X d)) Oc split f l K a) :
    X a.1.2 = true := by
  have h := ((promQ_beside N Pm₀ split f l _ K _).1 ha.1).2
  have h' : (K != K || X a.1.2) = true := (Bool.and_eq_true_iff.1 h).2
  simpa using h'

/-- **SH₃'s CONCLUSION AND X.** -/
theorem sh₃_at_pub_X {C : CK} {D : WholeD} {all : List LeftT} {Y P₀ X₁ X₂ Cl Wt W₁ : Type}
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
    (X : St → Bool)
    (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N (besideP Pm₀ fun k d => doorX (ProofFile.pAt Z) (1 + T.l₂.length) k d &&
        (k != 1 + T.l₂.length || X d))
      (ocEnd g N₁ (fillDoor Mg₀) links (a ++ p :: l)) split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s) :
    (fillZ (ProofFile.pAt Z) R fun q => (g q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true ∧
      X b.1.2 = true := by
  refine ⟨?_, x_at_last N Pm₀ _ split T.p₂ T.l₂ (ProofFile.pAt Z) (1 + T.l₂.length) X b hb⟩
  have hb' := hb
  rw [← beside_beside Pm₀ (fun k d => k != 1 + T.l₂.length || X d)
    (doorX (ProofFile.pAt Z) (1 + T.l₂.length))] at hb'
  exact sh₃_at_pub o pol lay KL Z hZ Np c R g hg T N _ split N₁ Mg₀ links a p l h1 h2 h3 hd b s
    hb' hs

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.x_at_last
#print axioms VerifiableInference.Desc.Last.sh₃_at_pub_X
