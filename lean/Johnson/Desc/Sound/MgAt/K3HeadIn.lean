-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3HeadIn.lean: in front of the output head's lookup on the calls, inside the
promise at the composed meaning (mgAll), at a state of the verifier without a mark: a next token has
been heard, as the state's own reader gives it (S.replyTok?). Statements and proofs.

How. The public item tokenSmall is open at that border (MgAt.k3_open_token, by the kernel); the
promise asks its test; at mgAll that test is tokenHeardB: an element has been heard, and its first
coordinate is below the vocabulary's size.
THE TEST READS THE FIRST COORDINATE ALONE (Reply.token: through tokOf). The state's own reader gives
a token only where the heard element IS the natural number of its first coordinate (ofNat). So one
premise stands beside the promise:
  hNat : ∀ g, a.1.out.reply = some g → Model.ofNat g.c0.toNat = g.
It is meant as a fact along the run: the one sub-protocol that lays out.reply lays an element only
where isToken V holds (second and third coordinate 0, the first below V), and every other leaves it;
ofNat gives the element back where V is at most the field's prime. None of this is shown here.

  token_is          the seat's reader of the token is the first coordinate of out.reply
  replyTok_of_nat   where the heard element is the natural number of its first coordinate, the
                    state's own reader gives that number
  heard_of_test     what tokenHeardB's accept says
  headMg_tokenHeard the test's accept, from the promise at the border
  headMg_tokIn      a.1.replyTok?.isSome = true

The border is written MgAt.borderOf 24 false (= 340). k3K 24 false
(Johnson/Desc/First/Look/K3Base.lean) has the same text (14 * l + the lookup's index + 2); that file
is not imported here.
Can the premises be met? hM holds at the composed meaning's own base by its make. Whatever meets the
promise at that border meets ha and hu. hNat holds wherever nothing is heard, and at ofNat's values.
That all hold together at a state of a run is not shown.
Limits. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAt.K3Open
import Johnson.Desc.Sound.OnParts
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.First (S)
open OnBytes

/-- The seat's reader of the token is the first coordinate of what was heard. -/
theorem token_is (h : Model.Head.Shape) (iU3 : Nat) (s : S) :
    Reply.token (seatAt h iU3).toSeat s = s.out.reply.map fun g => g.c0.toNat := rfl

/-- Where the heard element is the natural number of its first coordinate. -/
theorem replyTok_of_nat (s : S) (g : E) (hr : s.out.reply = some g)
    (hg : Model.ofNat g.c0.toNat = g) : s.replyTok? = some g.c0.toNat := by
  unfold S.replyTok?
  rw [hr]
  simp only [Option.bind_some, hg, beq_self_eq_true, if_true]

/-- What the test's accept says. -/
theorem heard_of_test (h : Model.Head.Shape) (iU3 : Nat) (s : S)
    (ht : tokenHeardB h iU3 s = true) : ∃ g, s.out.reply = some g ∧ g.c0.toNat < h.V := by
  unfold tokenHeardB at ht
  rw [token_is] at ht
  cases hr : s.out.reply with
  | none =>
    rw [hr] at ht
    cases ht
  | some g =>
    rw [hr] at ht
    exact ⟨g, rfl, of_decide_eq_true ht⟩

end VerifiableInference.Desc.Kinds.Head

namespace VerifiableInference.Desc.Sound.MgAt
open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open VerifiableInference.Desc.First (Meaning Pub flatPlacesOf)
open VerifiableInference.Desc.Kinds.Head (tokenHeardB heard_of_test replyTok_of_nat)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The test's accept, from the promise at the border. -/
theorem headMg_tokenHeard {Fr : Frame} (hM : Mg.more = {}) (z : P) (a : First.S × Fr.E.Str)
    (ha : onQ 𝔇.N (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
      (borderOf 24 false) a)
    (hu : a.1.failed = none) : tokenHeardB 𝔇.pubD.hShape 𝔇.pubD.iU3 a.1 = true := by
  have hmem : Pub.tokenSmall ∈ pubQ (mgAll 𝔇 Mg).more linksFull (flatPlacesOf linksFull true)
      (borderOf 24 false) := by
    rw [mgAll_more_closed 𝔇 Mg hM]
    exact k3_open_token
  have hp := (onParts_of_on 𝔇.N (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true)
    (fun s => (z, s)) (borderOf 24 false) a ha hu).pub Pub.tokenSmall
      (List.mem_append_left _ hmem)
  rw [mgAll_pub, First.pubAll_tokenSmall] at hp
  exact hp

/-- **A next token has been heard, as the state's own reader gives it.** -/
theorem headMg_tokIn {Fr : Frame} (hM : Mg.more = {}) (z : P) (a : First.S × Fr.E.Str)
    (ha : onQ 𝔇.N (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
      (borderOf 24 false) a)
    (hu : a.1.failed = none)
    (hNat : ∀ g, a.1.out.reply = some g → Model.ofNat g.c0.toNat = g) :
    a.1.replyTok?.isSome = true := by
  obtain ⟨g, hr, -⟩ := heard_of_test _ _ a.1 (headMg_tokenHeard 𝔇 Mg hM z a ha hu)
  rw [replyTok_of_nat a.1 g hr (hNat g hr)]
  rfl

end VerifiableInference.Desc.Sound.MgAt

#print axioms VerifiableInference.Desc.Kinds.Head.token_is
#print axioms VerifiableInference.Desc.Kinds.Head.replyTok_of_nat
#print axioms VerifiableInference.Desc.Kinds.Head.heard_of_test
#print axioms VerifiableInference.Desc.Sound.MgAt.headMg_tokenHeard
#print axioms VerifiableInference.Desc.Sound.MgAt.headMg_tokIn
