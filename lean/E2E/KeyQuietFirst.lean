--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyQuietFirst.lean: EVERY SUB-PROTOCOL OF THE KEY FILE's FIRST CHAIN THAT HAS NO ROUND IS
ACCEPTED, FROM NAMED PREMISES: the rule "structure | values" at such a sub-protocol
(`accepted_quiet_shape`, E2E/ShapeQuiet.lean) called at the first chain's shape with code at every
sub-protocol (`Z₁W`, E2E/KeyShapeFirstWhole.lean). By calls. No sub-protocol's number stands here.
NOTHING IS CLAIMED OF WHAT THE PARTS SEND.

  `PublicFirst X N`: four conditions on public values: the sending of W is there · the ranges'
    proximity test's place is early and has one answer · that test has rounds.
  `firstShape X cs`: the shape of the state at which the description starts the first chain.
  **`accepted_quiet₁`**: at every thread over `(keyFileDescription X N P).first.blocksInOrder`, every fall, every number
    b < n whose sub-protocol has no round: `Accepted`.
  `accepted_first_of_rounds`: so `Accepted` at all numbers below n follows from `Accepted` at those
    whose sub-protocol HAS rounds.

PAID BY CALLS: (B1) at every sub-protocol of the chain (`carries_whole₁`) · (B2) at every one
without a round (`returns_whole₁`) · the first shape (`start₁_shape`) · `FitsAt` and `Values`
(E2E/ShapeQuiet.lean). PREMISES THAT ARE LEFT, BY NAME:
- **hyes: THE SHAPE's OWN RUN OVER THE FIRST n SUB-PROTOCOLS RETURNS** (`Shape.yes`): an evaluation
  on public values. IT IS SHOWN NOWHERE IN LEAN: neither in scope nor at written sizes.
- `PublicFirst X N`: shown nowhere here.
- hbeg: the thread's letter `begun` holds, at a valid input, only of a state at which the
  description starts the chain.
- hv: the letter v (the named tests on values) is constantly true at the sub-protocols without a
  round.

Limits.
- CONDITIONAL THROUGHOUT. Where hyes fails the statement says nothing.
- On the first chain alone: at the shared chain (B1) is not had at all sub-protocols.

-/
import E2E.ShapeQuiet
import E2E.KeyShapeFirstWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest AtPublicFiles.KeyLink
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (FirstState Claim rangesParams)

variable (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (cs : Codes)

/-- **Four conditions on public values.** -/
def PublicFirst : Prop :=
  ∃ bw : Block FirstState Claim, sendWAt (pubOf X) X.Y.D.1 X.Y.told.1 = some bw ∧
    (rangesParams N).early = true ∧ (rangesParams N).answers = 1 ∧
    (H2K.JointK.rngEntry (pubOf X).one N).rounds ≠ []

/-- The shape of the state at which the description starts the first chain. -/
abbrev firstShape : Sh₁B :=
  a₀ X.Y.k.oneTime.codes (backOf X.Y.k.oneTime.lin cs ([], #[], #[], none))

variable {V W Xh Pb : Type} {Bk : ProverCoinCounts}
  (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
  (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)

/-- **Every sub-protocol of the first chain that has no round is accepted**, from named premises. -/
theorem accepted_quiet₁ (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder) (hp : PublicFirst X N) {n : Nat}
    (hn : n ≤ (keyFileDescription X N P).first.blocksInOrder.length)
    (hyes : (Z₁W (pubOf X) cs X.Y.D.1 X.Y.told.1 N v).yes (firstShape X cs) n = true)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    (hv : ∀ b blk, (keyFileDescription X N P).first.blocksInOrder[b]? = some blk → blk.rounds = [] →
      ∀ s rs gs, v b s rs gs = true)
    {fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String} (b : Nat) (hb : b < n)
    (blk : Block (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl)
    (hblk : (keyFileDescription X N P).first.blocksInOrder[b]? = some blk) (hr : blk.rounds = []) :
    Accepted T₁ fall b := by
  obtain ⟨bw, hw, he, ha, hR⟩ := hp
  refine accepted_quiet_shape T₁ (Z₁W (pubOf X) cs X.Y.D.1 X.Y.told.1 N v) (n := n)
    (a₀ := firstShape X cs) (by rw [hbs]; exact hn) hb hyes ?_ ?_ ?_ (by rw [hbs]; exact hblk) hr
    (hv b blk hblk hr)
  · intro k w h s₀ h1 h2
    obtain ⟨x, rfl⟩ := hbeg k w h s₀ h1 h2
    exact start₁_shape (cs := cs) (N := N) (X := X) (P := P) v x
  · intro j
    rw [hbs]
    exact carries_whole₁ (pubOf X) cs X.Y.D.1 X.Y.told.1 N T₁.ft v bw hw he ha j
  · rw [hbs]
    exact returns_whole₁ (pubOf X) cs X.Y.D.1 X.Y.told.1 N T₁.ft v bw hw hR b blk hblk hr

/-- So `Accepted` below n follows from `Accepted` at the sub-protocols that have rounds. -/
theorem accepted_first_of_rounds (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder) (hp : PublicFirst X N)
    {n : Nat} (hn : n ≤ (keyFileDescription X N P).first.blocksInOrder.length)
    (hyes : (Z₁W (pubOf X) cs X.Y.D.1 X.Y.told.1 N v).yes (firstShape X cs) n = true)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    (hv : ∀ b blk, (keyFileDescription X N P).first.blocksInOrder[b]? = some blk → blk.rounds = [] →
      ∀ s rs gs, v b s rs gs = true)
    {fall : Nat → (keyFileDescription X N P).S₁ → List Fmt.Drawn → Option String}
    (h : ∀ b blk, b < n → (keyFileDescription X N P).first.blocksInOrder[b]? = some blk → blk.rounds ≠ [] →
      Accepted T₁ fall b) (b : Nat) (hb : b < n) : Accepted T₁ fall b := by
  have hlt : b < (keyFileDescription X N P).first.blocksInOrder.length := Nat.lt_of_lt_of_le hb hn
  have hblk : (keyFileDescription X N P).first.blocksInOrder[b]? = some (keyFileDescription X N P).first.blocksInOrder[b] :=
    List.getElem?_eq_getElem hlt
  by_cases hr : ((keyFileDescription X N P).first.blocksInOrder[b]).rounds = []
  · exact accepted_quiet₁ X N P cs v T₁ hbs hp hn hyes hbeg hv b hb _ hblk hr
  · exact h b _ hb hblk hr

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.accepted_quiet₁
#print axioms AtPublicFiles.AtFiles.accepted_first_of_rounds
