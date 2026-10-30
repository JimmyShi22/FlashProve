-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/Ground.lean: THE GUARD ON THE REPLY: the common ground of the files of this folder.
Definitions, and a few small laws.

Why. After every step of the proof file's first chain, except the decision at the one place that
hears the reply, the verifier rejects if the step has changed its stored copy of the reply. The test
(Johnson/Desc/SeatGuard.lean) is laid at three places of the text: `Chain.guarded H.same hearsReply`
over the whole chain (Johnson/Desc/First/Driver/Chain.lean), and `Block.guarded … fun _ => false`
around what is joined behind a block (Johnson/Desc/ProofFile/Frames1.lean) and around the first half
of the block at "H:1" (Johnson/Desc/ProofFile/Lots/H1.lean). The soundness theorem's proof takes
from this test that only one step changes the reply (Driver/Chain.lean).
This folder pays the lemmas (each step but the one that hears the reply, where it returns a state,
leaves the reply as it was), joins them, and shows that what is laid for the proof file is the same
with the test and without it.

Main names.
* `hR`: the reading: the reply that the state has heard. `ReplyR s s'`: the reply is behind the step
  as it was in front: s'.out.reply = s.out.reply. `replyR_of_out`: whoever leaves the whole field
  "out" leaves it.
* `SeatBut R`: WHAT IS ASKED OF A RELATION R: every maker of the proof file's seat BUT K7's keeps
  it. One field a maker. The fields are those of `Meaning.K2.SeatKeeps` and `SeatBack`
  (Johnson/IMR/SeatKeeps.lean), with four differences. There is no field k7: it asks that K7's block
  leave the reply, which that block is there to write (that it breaks `ReplyR` is not proved here).
  There is no refl or trans: they are stated beside. There is no side premise (on the links built,
  the head's letters, the first tree's number, K12's test on the plan): at `ReplyR` no maker needs
  one. K12's field is at all numbers, not at the seat's own alone. So each field is that file's or
  stronger.
* `Runs R b`: b's runs of claims and its runs behind the batching keep R.
* `LotsBut R lots G`: what is asked of a seat's lots: every block stands at a place of the kind K7,
  or its decision keeps R; every block's runs keep R; every batching keeps R at a gatherer that
  does. The first alternative looks only at the place that the block bears, so it exempts all that
  is joined into that block: the block at "H:1" is K2's step that enters the head's segment, joined
  with K7's block, and both go free.
* `leaves_of_decides`, `runsLeave_of_runs`, `runsLeave_of_whole`: from the relation's form (`Whole`,
  `Decides`, Johnson/Desc/FoldKeeps.lean) to the guard's laws' form (`Block.Leaves`,
  `Block.RunsLeave`).
* `sameReply_sameBy`: the seat's test is `sameBy` of the reading; the sides of == are swapped, so it
  is no unfolding.

What it leans on. Johnson/IMR/SeatKeeps.lean (the two structures that `SeatBut` follows);
Johnson/Desc/FoldKeeps.lean (`Whole`, `Decides`, `Fn`, `FnCl`); Johnson/Desc/Sound/FoldHeard.lean
(`Block.Leaves`), StillOfLeaves.lean (`Block.RunsLeave`); Johnson/Desc/SeatGuard.lean (`sameBy`).

Limits. Definitions and rules. Nothing is shown here of any maker. Nothing on soundness.


-/
import Johnson.IMR.SeatKeeps
import Johnson.Desc.Sound.GuardAtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Lot Ground Pub)

/-- The reading: the reply that the verifier's state has heard. -/
abbrev hR (s : S) := s.out.reply

/-- The reply is behind the step as it was in front. -/
def ReplyR (s s' : S) : Prop := s'.out.reply = s.out.reply

theorem replyR_refl (s : S) : ReplyR s s := rfl

theorem replyR_trans (a b c : S) (h₁ : ReplyR a b) (h₂ : ReplyR b c) : ReplyR a c :=
  h₂.trans h₁

/-- Whoever leaves the whole field out leaves the reply. -/
theorem replyR_of_out {s s' : S} (h : s'.out = s.out) : ReplyR s s' := by
  unfold ReplyR
  rw [h]

open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame) in
/-- **WHAT IS ASKED OF A RELATION: EVERY MAKER OF THE SEAT BUT K7's KEEPS IT.** -/
structure SeatBut (R : S → S → Prop) : Prop where
  frames : ∀ {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame}, framesOf built first W = .ok fs → ∀ f ∈ fs,
    Fn R f.lay ∧ Fn R f.opened ∧ Fn R f.clear
  k1First : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar),
    Whole R (K1.firstSegmentOpening (Cl := Unit) q gp)
  k1Later : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)), Whole R (K1.laterAt (Cl := Unit) q gp link piece moment arrays)
  reads : ∀ {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat} {b : Block S Unit},
    ProofFile.readsQuietAt G l X piece = some b → Whole R b
  k3 : ∀ (claim : Aff → ProofFile.Cl) (readers : Nat → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S ProofFile.Cl},
    K3.theStated claim readers X codes shape a = some b → Whole R b
  k4 : ∀ p : OnBytes.Desc.First.K4.Par, Whole R (OnBytes.Desc.First.K4.blockAtC p)
  k5 : ∀ (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) {b : Block S Claim},
    Att.P.k5AtN W l g before = some b → Whole R b
  k6 : ∀ {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)} {b : Block S Claim},
    Kinds.Head.seatedClaims W l before = some b → Whole R b
  k8 : ∀ p : K8.ParW, Whole R (K8.whole p)
  k11 : ∀ P : Johnson.Desc.First.ForkMerge.HeadMergeP,
    Whole R (Johnson.Desc.First.ForkMerge.headClaimMergeKind P)
  closeOf : ∀ (p : K9.Where) (P : Close.Par), ∀ b ∈ K9.closeOf (Cl := Unit) p P, Whole R b
  batch : ∀ (p : K9.Where) {claims : S → Except String (List Claim × S)}, FnCl R claims →
    Whole R (K9.batch K9.atS p claims)
  k2 : ∀ p : K2.P2, Whole R (K2.codeSwitchKind p : Block S Unit)
  front : ∀ tl : HTailF2, Fn R (K2.headFrontQ tl)
  openQ : ∀ P : K2.HeadPar, Fn R (K2.headOpenQ P)
  finFront : Fn R K2.finishFrontQ
  finBehind : Fn R K2.finishBehindQ
  k12 : ∀ p, Whole R (K12.atFinish p)
  k13M3 : ∀ p : K13.Where, Whole R (K13.atM3 (Cl := Unit) p)
  k13M4 : ∀ (p : K13.Where) (P : K1.Par), Whole R (K13.atM4 (Cl := Unit) p (K1.sendAtS P))

/-- A block's runs of claims and its runs behind the batching keep R. -/
def Runs {Cl : Type} (R : S → S → Prop) (b : Block S Cl) : Prop :=
  (∀ c ∈ b.claims, ∀ n, FnCl R (c.2 n)) ∧ ∀ c ∈ b.after, Fn R c.2

/-- **What is asked of a seat's lots**, at the letters G. -/
structure LotsBut (R : S → S → Prop) (lots : List Lot) (G : Ground) : Prop where
  blocks : ∀ L ∈ lots, ∀ b ∈ L.blocks G, b.place.kind = KindName.K7 ∨ Decides R b
  runs : ∀ L ∈ lots, ∀ b ∈ L.blocks G, Runs R b
  batch : ∀ L ∈ lots, ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f)

/-! ## From the relation's form to the guard's laws' form -/

theorem leaves_of_decides {Cl : Type} {b : Block S Cl} (W : Decides ReplyR b) : b.Leaves hR :=
  fun s rs gs s' h => W s rs gs s' h

theorem runsLeave_of_runs {Cl : Type} {b : Block S Cl} (W : Runs ReplyR b) : b.RunsLeave hR :=
  ⟨fun c m n s y h => W.1 c m n s y h, fun c m s s' h => W.2 c m s s' h⟩

theorem runsLeave_of_whole {Cl : Type} {b : Block S Cl} (W : Whole ReplyR b) : b.RunsLeave hR :=
  runsLeave_of_runs W.2

/-- The seat's test is `sameBy` of the reading. -/
theorem sameReply_sameBy : (ProofFile.sameReply : S → S → Bool) = sameBy hR := by
  funext t s
  show (t.out.reply == s.out.reply) = (s.out.reply == t.out.reply)
  exact Bool.eq_iff_iff.2 ⟨fun h => by rw [eq_of_beq h]; exact beq_self_eq_true _,
    fun h => by rw [eq_of_beq h]; exact beq_self_eq_true _⟩

end LPFGuard

#print axioms LPFGuard.replyR_refl
#print axioms LPFGuard.replyR_trans
#print axioms LPFGuard.replyR_of_out
#print axioms LPFGuard.leaves_of_decides
#print axioms LPFGuard.runsLeave_of_runs
#print axioms LPFGuard.runsLeave_of_whole
#print axioms LPFGuard.sameReply_sameBy
