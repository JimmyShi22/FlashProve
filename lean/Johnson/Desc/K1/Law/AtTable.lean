-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/AtTable.lean: A SENDING AT ITS ROW OF THE TABLE OF JOINTS: the law of a sending
(`send_goodIn_entry`, Johnson/Desc/K1/Law/GoodSend4.lean) with its five ties to the table's promise
and items (`TiedAt`, Johnson/Desc/Sound/ChainOfPromises.lean). Statements with their proofs.

OBJECT. Any block b with `IsSend P stOf b` (Johnson/Desc/K1/Law/GoodSend3.lean: shown there and in
GoodSendAtS.lean and GoodSendPlaces.lean of W's sending, a later moment's, the first segment's
opening, and of these with a quiet step laid behind), at its two written rounds: `sendPiece`.
USER. `EachTied` | `chainOfPromises` (ChainOfPromises.lean): `send_tied` ends in
`TiedAt N Mg links ps get k (sendPiece …)`, to the letter.
LETTERS. The table's own: N, Mg, links, ps, get, k. The kind's: P, rad, fOf, fIn, e. One more: new:
what the seal is worth in the table's letters.

Main names:
  `isSend_under`: a block that says yes only where a sending does, with the same record
    (`Block.Under`, Johnson/Desc/Sound/HearsOnce.lean), is a sending: so a sending behind a guard.
  `send_tied`: **the five ties.** WHAT OF A SENDING's TIE HANGS ON THE CHALLENGE IS PAID BY THE LAW:
    that behind the block each sampled message is sealed (the record holds its seed and answer; no
    two members of the word's list answer alike). WHAT IS LEFT ARE FACTS AT EVERY YES, none on a
    count of challenges: hseal (at a yes from inside the promise the seal gives `new`) · hkeep
    (the promise in front, a yes and `new` give the promise behind) · hback (what the row opens
    goes back to what it closes) · hride (what rides, rides) · a mark stays · "decodes" rides.

What is not claimed. NO MEMBER IS SHOWN HERE: the six premises are met at no block in this file
(W's sending: Johnson/Desc/K13/Law/AtTableW.lean). `condPort` is a test on the plan and the radii;
that a written round has the place's entry is a premise. Nothing on the size of e. Nothing on
soundness, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.GoodSend4
import Johnson.Desc.Sound.ChainOfPromises
import Johnson.Desc.Sound.HearsOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ meansQ relQ insQ outsQ TiedAt relAt
  openAfter)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers)

/-- A block that says yes only where a sending does, with the same record, is a sending. -/
theorem isSend_under {T Cl : Type} (P : Par) (stOf : T → Statement) {c b : Block T Cl}
    (h : c.Under b) (hb : IsSend P stOf b) : IsSend P stOf c :=
  fun s s' r₁ r₂ gs hc => hb s s' r₁ r₂ gs (h _ _ _ _ hc)

variable {A Pp Cl W : Type} {F : Frame}

/-- **THE FIVE TIES AT A SENDING's ROW.** -/
theorem send_tied (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true)
    (b : Block A Cl) (hS : IsSend P (fun a => (get a).2.st) b) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.imp y τ) =
      fIn y τ.1)
    (new : A × F.E.Str → Prop)
    (hseal : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      (∀ j, sampledAt P j →
        Sealed P.codes (shapeAt P j) (rad j.val) (fOf x.2 j) (get x.1).2.st
          ((get x.1).2.st.oracles.size - (shapesOf P).length + j.val)) → new x)
    (hkeep : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      new x → onQ N Mg links ps get (k + 1) x)
    (hback : ∀ a τ x w, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      relAt (meansQ N Mg get) (outsQ links ps k) x w →
      relAt (meansQ N Mg get) (insQ links ps k) a w)
    (hride : ∀ a τ x w i, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      onQ N Mg links ps get (k + 1) x → relQ N Mg links ps get (k + 1) x w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i →
      ¬ insQ links ps k i → meansQ N Mg get i a w)
    (hMark : ∀ a τ x,
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      (get a.1).2.failed ≠ none → (get x.1).2.failed ≠ none)
    (hDec : ∀ a τ x,
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      Mg.decodes (get a.1) (strsOf F a.2) → Mg.decodes (get x.1) (strsOf F x.2)) :
    TiedAt N Mg links ps get k (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e) :=
  ⟨_, _, _, _,
    send_goodIn_entry P rad hC b (fun a => (get a).2.st) hS base d₁ d₂ he₁ hk₁ e he fOf fIn hf
      (fun a => onQ N Mg links ps get k a ∧ (get a.1).2.failed = none)
      (fun x => new x → onQ N Mg links ps get (k + 1) x)
      (relAt (meansQ N Mg get) (insQ links ps k)) (relAt (meansQ N Mg get) (outsQ links ps k))
      (fun a τ x ha hx hn => hkeep a τ x ha.1 ha.2 hx hn)
      (fun a τ x w ha hx hw => hback a τ x w ha.1 ha.2 hx hw),
    fun _ ha hm => ⟨ha, not_not.1 hm⟩,
    fun a τ x ha hm hx ho' => ho'.1 (hseal a τ x ha (not_not.1 hm) hx ho'.2),
    fun _ _ _ _ _ _ _ _ hO => hO,
    fun _ _ _ _ _ _ _ _ _ hR => hR,
    fun a τ x w i ha hm hx hon hall hi hin => hride a τ x w i ha (not_not.1 hm) hx hon hall hi hin,
    hMark, hDec⟩

end VerifiableInference.Desc.K1
