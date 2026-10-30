-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PinsPaid.lean: BENEATH THE ONE LIST OF WHAT IS LEFT OF A LINK's LAW
(LinkList.lean): ITS FIELDS pinB AND pinQ, TO THE LETTER, AND THE LIKE OVER THE ONE EQUATION's PIECE
(pinE: the premise of letters_at_list, LettersAtList.lean, that stands in no field of that list):
EACH FROM TESTS ON THE PLAN AND FACTS ON THE LETTERS: NO PREMISE ON A STATE IS LEFT. Three theorems:
calls.

`PinAsks` (PinsBack.lean) says two things of the states in front of and behind a piece's yes: the
segment's tenants sit in commitment trees below the piece's first tree; the reader of the
out-of-domain (OOD) samples answers alike at the two states.

What is said.
  `pinB_of`: **the field pinB**: over the batching's piece: the statement stays (the runs' share's
    TwoBlocks). `pinQ_of`: **the field pinQ**: over the piece of the frame's sub-protocol behind it:
    the like. `pinE_of`: **pinE**: over the one equation's piece: THERE THE STATEMENT TURNS (a row
    is laid on the group; a mask's ledger moves): what stays is every message but for its ledger
    (`bare`; eq_both at bare, DoorBlind.lean).

PREMISES, none on a state: hfen (fenceFit: the table's test on its numbers) · hpins (pinsFit: the
segment's three pins are open at the three borders: the kernel's yes at the full list lies) · the
place at the border: its link and its piece (closed) · hb (the plan's count of trees at the place is
no more than the piece's first tree) · the runs' share | "a yes of b₃ is the one equation's" · which
sub-protocol the piece holds · hs | hs3 (the letter 𝔇.smp answers alike at two states with one
statement | whose messages agree but for their ledgers: AT THE NAMED READER THE SECOND IS
smpNamed_bare, FifthTieEq.lean).

Limits. General in 𝔇. The promise in front is not spent. The closed premises are evaluated by nobody
here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.PinAsksOf
import Johnson.Desc.First.Link.Law.FifthTieEq
import Johnson.Desc.First.Link.Law.RidesAtMg
import Johnson.Desc.First.Link.Law.LinkTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers fenceFit)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place) (z : P)
  (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- **THE FIELD pinB.** -/
theorem pinB_of (hfen : fenceFit 𝔇.N links pl = true) (hpins : pinsFit links pl = true)
    (pc : Place) (hk : pl[k]? = some pc) (hl : pc.link = some m)
    (hpc : pc.piece = hearN links m + 1) (L : Link S Claim) (p : Where) (share : LinkShare L p)
    (pb : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (hpb : pb.b = below L.batchB)
    (hb : 𝔇.N.treesAt pl[k]? ≤ pb.base)
    (hs : ∀ s s' : S, s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s)) :
    ∀ a τ b, onK k a → pb.ior.red.out a τ = some b →
      PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pb.base a.1 b.1 := by
  intro a τ b _ hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact pinAsks_of 𝔇.cs 𝔇.smp 𝔇.N links pl hfen hpins z k m 1 pb.base pc hk hl hpc (Or.inl rfl) hb
    a.1 b.1 (hs a.1 b.1 (share.two.1 _ _ _ _ _ j hstep).1.st)

/-- **THE FIELD pinQ.** -/
theorem pinQ_of (hfen : fenceFit 𝔇.N links pl = true) (hpins : pinsFit links pl = true)
    (pc : Place) (hk : pl[k + 1]? = some pc) (hl : pc.link = some m)
    (hpc : pc.piece = hearN links m + 2) (L : Link S Claim) (p : Where) (share : LinkShare L p)
    (pq : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (hpq : pq.b = below L.behindB)
    (hb : 𝔇.N.treesAt pl[k + 1]? ≤ pq.base)
    (hs : ∀ s s' : S, s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s)) :
    ∀ a τ b, onK (k + 1) a → pq.ior.red.out a τ = some b →
      PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pq.base a.1 b.1 := by
  intro a τ b _ hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpq hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact pinAsks_of 𝔇.cs 𝔇.smp 𝔇.N links pl hfen hpins z (k + 1) m 2 pq.base pc hk hl hpc
    (Or.inr (Or.inl rfl)) hb a.1 b.1 (hs a.1 b.1 (share.two.2 _ _ _ _ _ j hstep).1.st)

/-- **pinE: OVER THE ONE EQUATION's PIECE, WHERE THE STATEMENT TURNS.** -/
theorem pinE_of (hfen : fenceFit 𝔇.N links pl = true) (hpins : pinsFit links pl = true)
    (pc : Place) (hk : pl[k + 1 + 1]? = some pc) (hl : pc.link = some m)
    (hpc : pc.piece = hearN links m + 3) (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (hpe : pe.b = below b₃)
    (hb : 𝔇.N.treesAt pl[k + 1 + 1]? ≤ pe.base)
    (hs3 : ∀ s s' : S, (∀ i : ℕ, (s'.st.oracles[i]?).map bare = (s.st.oracles[i]?).map bare) →
      𝔇.smp (z, s') = 𝔇.smp (z, s)) :
    ∀ a τ b, onK (k + 1 + 1) a → pe.ior.red.out a τ = some b →
      PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pe.base a.1 b.1 := by
  intro a τ b _ hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  obtain ⟨_, _, e, _⟩ := eq_both pw b₃ hb₃ bare_blind _ _ _ _ _ j hstep
  exact pinAsks_of 𝔇.cs 𝔇.smp 𝔇.N links pl hfen hpins z (k + 1 + 1) m 3 pe.base pc hk hl hpc
    (Or.inr (Or.inr rfl)) hb a.1 b.1 (hs3 a.1 b.1 e.2)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pinB_of
#print axioms VerifiableInference.Desc.LinkJoin.pinQ_of
#print axioms VerifiableInference.Desc.LinkJoin.pinE_of
