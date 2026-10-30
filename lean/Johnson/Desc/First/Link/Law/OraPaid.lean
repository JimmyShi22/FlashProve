-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/OraPaid.lean: BENEATH THE LINK's TWO NAMED LISTS (`LinkList.oraB`,
`ShutList.oraS`: what the four riders on the oracles take over the batching's and over the
shutting's piece): BOTH FIELDS, TO THE LETTER, FROM A TEST ON THE PLAN AND FACTS ON THE LETTERS: no
premise on a state is left. Theorems.

What is said.
  `oraB_of`: **the field oraB** from: the fence's test on the plan (`fenceFit`); the border lies
    inside the list; the runs' share of the link; the piece holds the batching; the plan's number of
    trees at the place is no more than the piece's first tree; the committed table's decoder answers
    alike at any two states; the reader of the OOD samples answers alike at two states with one
    statement. `oraS_of`: **the field oraS**, the like, from «a yes of b₅ is the shutting's».

Limits. Calls of `oracleAsks_of` (FenceAt.lean) with «the statement and the book stay» drawn off the
piece's yes (`TwoBlocks`; `rb_shutB`). The promise in front is not spent. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.ShutList
import Johnson.Desc.First.Link.Law.FenceAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Numbers fenceFit)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (links : List ModelPart) (pl : List Place) (z : P)
  (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ)

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz

/-- **THE FIELD oraB.** -/
theorem oraB_of (hfen : fenceFit 𝔇.N links pl = true) (hk : k ≤ pl.length) (L : Link S Claim)
    (p : Where) (share : LinkShare L p) (pb : Piece C F S Claim WT) (hpb : pb.b = below L.batchB)
    (hb : 𝔇.N.treesAt pl[k]? ≤ pb.base)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (hs : ∀ s s' : S, s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s)) :
    ∀ a τ b, onK k a → pb.ior.red.out a τ = some b →
      OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N links pl z k pb.base a.1 b.1 := by
  intro a τ b _ hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact oracleAsks_of 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N links pl z k pb.base hfen hk hb
    (fun c s s' _ _ => hd c s s') (fun s s' e _ => hs s s' e) a.1 b.1
    (share.two.1 _ _ _ _ _ j hstep).1

/-- **THE FIELD oraS.** -/
theorem oraS_of (hfen : fenceFit 𝔇.N links pl = true) (hk : k ≤ pl.length) (pw : Where)
    (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Claim WT) (hps : ps.b = below b₅) (hb : 𝔇.N.treesAt pl[k]? ≤ ps.base)
    (hd : ∀ c (s s' : S), 𝔇.decT c (z, s') = 𝔇.decT c (z, s))
    (hs : ∀ s s' : S, s'.st = s.st → 𝔇.smp (z, s') = 𝔇.smp (z, s)) :
    ∀ a τ b, onK k a → ps.ior.red.out a τ = some b →
      OracleAsks 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N links pl z k ps.base a.1 b.1 := by
  intro a τ b _ hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hps hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact oracleAsks_of 𝔇.cs 𝔇.decT 𝔇.smp 𝔇.N links pl z k ps.base hfen hk hb
    (fun c s s' _ _ => hd c s s') (fun s s' e _ => hs s s' e) a.1 b.1
    (rb_shutB pw piece b₅ hb₅ _ _ _ _ _ j hstep).1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.oraB_of
#print axioms VerifiableInference.Desc.LinkJoin.oraS_of
