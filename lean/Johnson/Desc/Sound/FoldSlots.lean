-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldSlots.lean: the rule of composition FOR THE N SLOTS OF ONE SESSION BEHIND ONE
KEY, stated of the verifier's own fold: the row `fold_slots` of the list of laws owed
(not in this library: "the rule of composition for N slots behind one key"). A SHEET OF STATEMENTS:
definitions, and propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE (the proofs:
Johnson/Desc/Sound/FoldSlotsProofs.lean; members with teeth: Johnson/Desc/Sound/FoldSlotsToy.lean [not in this library]).

The setting. A proof file has three hash chains. The first and the third are each request's own: in
a batch every slot has its own challenges there, and a block's law holds slot by slot, at the
block's own errors. The second chain is shared: it is run once for all N slots, under one
transcript. A shared round's error counts the challenges that are bad for SOME slot.
Johnson/Desc/Sound/SharedRule.lean has the rule for blocks whose bad challenges are a function of
what the slots share (a key): these are paid ONCE (`Piece.LostBy`, `PaidOnce`); and the library has
the union bound: N TIMES (`knowB_joining`, Ior/BatchSeq.lean). THE PROTOCOL's SHARED POINT IS
NEITHER: one draw is held against one object that all slots share (the folded table: once) AND
against each slot's own polynomial identity (once for each slot). The library counts that round by
hand (`errPtB`, Cb/Ld/LdLinB.lean: εf · q^klo + N · (v + klo) · q^(v + klo - 1); `knowB_peek`: one
round without a prover message, from a joint count). No rule of the library or of SharedRule.lean
gives "the shared part once, a slot's own part N times" for a block of several rounds.

What is said.
(1) `Spec.knowB_of_lost_both` (general: any interactive oracle reduction, run once by the shared
part): if the prover has lost, at the errors εK, towards a property that is a function of a key,
and, at the errors εO, towards a property that may read the whole statement of a slot, and where
both hold a witness behind gives one in front, then the reduction is knowledge sound for the vectors
of at most N statements with one key, AT THE ERRORS εK + N · εO, round by round.
(2) `Piece.LostBoth`: that law for a block of the description at its stretch; `PaidBoth`: such a
block is a link of the batch (`BK.LinkSh`) at its own errors, from the key made backwards
(`Piece.keyBack`) to any key behind it: so it goes into `Keyed`, `ChainLink`, `SeamLink` and
`FileKnowsJOfKeyed` as they stand. `LostBothOfLostBy` (nothing of a slot's own: εO = 0: it is
`LostBy`), `LostBothOfOwn` (nothing shared: εK = 0: the union bound), `LostBothBeside` (a claim that
is only carried). `ChainLinkBoth`: the shared chain's own decision is a link with keys from the
first acting part to the last, at the blocks' errors in a row.
(3) `FoldSlots`: THE ROW. At a description F of a proof file whose instances are pairs (request,
record), at the library's row of F's three folds, RECORD BY RECORD: the list `Links.KnowsJ` that the
top theorem for a proof file asks (`proofSound_top_links`), at the NAMED key "the shared chain's
first record, with the stored table".

Who reads each letter (FoldSlots).
  F: the description: the verifier. T: the pieces: F's blocks with their stretches, extractors and
  errors: the blocks are F's (two premises); stretches, extractors, errors are the provers' of the
  laws. Q: conditions and relations at the boundaries: read by no verifier. okF, okJ, ok3: the
  tests on the three silent rounds: the verifier's. N: the number of slots. s₂: the shared chain's
  first record as a function of the record alone: A NAMED FUNCTION, read by no verifier: it says
  what the premise "one key" means.

Every "there is", walked. `Piece.LostBoth`: the split of the block's errors (εK, εO) and the two
properties towards which the prover has lost: objects of the proof: no verifier reads them, and they
stand in no conclusion; what a reader must see, the block's error, is the piece's own field `err`,
which bounds εK + N · εO. `LostBothAt` is the same with the split as letters. `EachHands`,
`Keyed`: SharedRule.lean's. `FoldSlots`: none of its own.

Limits. (1) A RULE: no block of the protocol meets a premise here. (2) Those of SharedRule.lean,
SharedSeam.lean, FileRule.lean and FileBatch.lean: nothing on acceptance; nothing bounds the errors;
the degenerate cases (N = 0; errors as large as the number of challenges; conditions that hold of
nothing; blocks that refuse all: at a description that refuses all every premise on the blocks
holds for nothing, and the conclusion speaks of a verifier that never says yes). (3) THE PREMISE
"ONE KEY" IS A PREMISE: that F's shared chain starts from the record alone is owed where F is laid
(at the stand-in seat of the harness of record the start reads the table's key alone; a lot's own
shared chain could read the request: nothing forbids it by type). (4) What is paid N times is what
the block's files lay into εO: the rule does not say which terms these are. By a
reading of the planner (the C++ and the paper's text), not machine-checked, the shared point's
Schwartz-Zippel term is the only one, and it needs the factor. (5) A request's own rounds (the first
and the third chain) are charged for each slot by itself: whoever asks "is SOME slot of the batch
fooled" in the interactive protocol adds these over the slots (Cb/Ld/LdBatchBlocksPlan.lean's head).

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DescThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-! ## 1 The general rule: the shared part once, a slot's own part N times -/

namespace Iop

/-- Two families of bad sets as one: a challenge is bad if it is bad in either. -/
def BadFam.both : {s : Shape} → BadFam s → BadFam s → BadFam s
  | [], _, _ => ()
  | _ :: _, B, B' =>
    (fun m => {c | c ∈ B.1 m ∨ c ∈ B'.1 m}, fun m c => BadFam.both (B.2 m c) (B'.2 m c))

namespace Spec
open IOR

/-- **Shared rounds in which only the shared part speaks: what hangs on a key is paid once, what
hangs on a slot's own statement once for each slot.** `lostK`: a property of the transcript that is
a function of a key of the statement; the prover has lost towards it at the errors εK. `lostO`: a
property that may read the whole statement; the prover has lost towards it at the errors εO. Where
both hold and the verifier puts out, a witness behind gives one in front. Then: knowledge sound for
the vectors of at most N statements with one key, at εK + N · εO in each round. At εO = 0 and
`lostO` true it is `knowB_of_lost`; at εK = 0 and `lostK` true, `knowB_joining`'s count. -/
def knowB_of_lost_both : Prop :=
  ∀ (Xi Xo κ : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (N : ℕ)
      (key : Xi × Ei.Str → κ) (lostK : κ → Tr R.shape → Prop)
      (lostO : Xi × Ei.Str → Tr R.shape → Prop) (on : Xi × Ei.Str → Prop)
      (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (εK εO : Err R.shape),
    (∀ a, on a → Doomed R.shape εK (lostK (key a))) →
    (∀ a, on a → Doomed R.shape εO (lostO a)) →
    (∀ a τ b w, on a → lostK (key a) τ → lostO a τ → R.red.out a τ = some b → RB b w →
      RA a (ext a τ w)) →
    R.KnowB (RoundSplits.const (RAnn.ofShared .sh) R.shape) N (SameKey key) on RA RB ext
      (Err.add εK (Err.times N εO))

end Spec
end Iop

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ Links shA)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-! ## 2 A block's law for N slots, in two parts -/

/-- **A block's law for N slots, in two parts, with the split of its errors as letters.** εK: what
is paid once. εO: what is paid once for each slot. At εK the prover has lost towards a property
`lostK k` of the transcript that is a function of the acting part k alone (slots with one acting
part have the same bad challenges there). At εO it has lost towards a property `lostO a` that may
read the whole statement a of a slot (its own record, its own trees). Where both hold and the block
says yes, the statement behind has `on'` (the promise is kept), and every witness of it gives, by
the block's extractor, a witness of the statement in front. -/
def Piece.LostBothAt (p : Piece C F S Cl W) (εK εO : Err (uLT C p.ds))
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (act : BKey F S) : Prop :=
  ∃ (lostK : act.1 → Iop.Tr (uLT C p.ds) → Prop)
    (lostO : S × F.E.Str → Iop.Tr (uLT C p.ds) → Prop),
    (∀ a, on a → Doomed (uLT C p.ds) εK (lostK (act.2 a))) ∧
    (∀ a, on a → Doomed (uLT C p.ds) εO (lostO a)) ∧
      ∀ a τ b, on a → lostK (act.2 a) τ → lostO a τ → p.ior.red.out a τ = some b →
        on' b ∧ ∀ w, R' b w → R a (p.ext a τ w)

/-- The same, with the block's own errors bearing the split: in each round the block's error is at
least εK + N · εO. -/
def Piece.LostBoth (p : Piece C F S Cl W) (N : ℕ) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act : BKey F S) : Prop :=
  ∃ εK εO : Err (uLT C p.ds), Err.le (Err.add εK (Err.times N εO)) p.err ∧
    p.LostBothAt εK εO on on' R R' act

/-- **A block with that law is a link of the batch, at its own errors**, from the key made backwards
to any key behind it. -/
def PaidBoth : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act kB : BKey F S) (N : ℕ),
    p.LostBoth N on on' R R' act →
    (p.bk on on' R R').LinkSh N (kkAt (p.keyBack act kB)) (kkAt kB)

/-- Nothing of a slot's own: the law of SharedRule.lean is the case εO = 0. -/
def LostBothOfLostBy : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act : BKey F S) (N : ℕ),
    p.LostBy on on' R R' act → p.LostBoth N on on' R R' act

/-- Nothing shared: a block that has the law for one statement at errors εO (`Piece.GoodIn`'s
property, at εO in the place of the block's own errors), and whose own errors bear N · εO, has the
law at every acting part: the union bound. -/
def LostBothOfOwn : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act : BKey F S) (N : ℕ) (εO : Err (uLT C p.ds)),
    Err.le (Err.times N εO) p.err →
    (∀ a, on a → Doomed (uLT C p.ds) εO fun τ =>
      ∀ b, p.ior.red.out a τ = some b → on' b ∧ ∀ w, R' b w → R a (p.ext a τ w)) →
    p.LostBoth N on on' R R' act

/-- A claim that is only carried may be laid beside both relations (as `LostBeside`). -/
def LostBothBeside : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' Rc : S × F.E.Str → W → Prop) (act : BKey F S) (N : ℕ),
    p.LostBoth N on on' R R' act →
    (∀ a τ b w, on a → p.ior.red.out a τ = some b → on' b → Rc b w → Rc a (p.ext a τ w)) →
    p.LostBoth N on on' (fun a w => R a w ∧ Rc a w) (fun b w => R' b w ∧ Rc b w) act

/-- Every block of a row has the law in two parts, at the acting part of the place in front of it.
-/
def EachLostBoth (N : ℕ) (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (act : ℕ → BKey F S) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.LostBoth N (on i) (on (i + 1)) (R i) (R (i + 1)) (act i) ∧ EachLostBoth N on R act (i + 1) l

/-- **The rule for the shared chain, of the chain's own decision**: if the stretches tile the chain,
every block has its law in two parts and hands its acting part on, then the chain's decision is a
link with keys for a batch of at most N statements, from the first acting part to the last, at the
blocks' own errors in a row. -/
def ChainLinkBoth : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (N : ℕ) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (act : ℕ → BKey F S),
    Tiled p l → EachLostBoth N on R act 0 (p :: l) → EachHands act 0 (p :: l) →
    LinkJ (foldRed name ((p :: l).map (·.b)) p l h) (shA _) N (act 0).2 (act (1 + l.length)).2
      (on 0) (R 0) (Reduction.orOff (on (1 + l.length)) (R (1 + l.length))) (rowExt d p l)
      (rowErr p l)

/-! ## 3 The row: at a description, record by record -/

/-- **THE RULE OF COMPOSITION FOR N SLOTS BEHIND ONE KEY, stated of the very fold.** F: a proof
file's description, at instances that are pairs of a request and the key file's record. T: F's own
blocks with their stretches (`OfDesc`), in the filling that is meant (`atDesc`,
Johnson/Desc/Sound/DescThree.lean): by `RunsAtDesc` the three runs of the row are F's own three
folds. THE PREMISES, COUNTED: eight.
  1 `OfDesc`: the pieces hold F's own blocks. 2 `Fits`: the stretches are the file's three chains.
  3, 5 THE FIRST AND THE THIRD CHAIN (each slot's own rounds): every block is good for one
    statement, at its own errors (`EachGood`): no N.
  4 THE SHARED CHAIN: every block has its law for N slots in two parts (`EachLostBoth`), at the
    acting parts that are meant (`actsOf`: the chain's own part of the record, the stored table, the
    chain's own trees): its own error bears "what hangs on the acting part, once, and what hangs on
    a slot's own statement, N times".
  6 `Glued`: the relations at the chains' ends fit together.
  7 a test on the data: the shared chain opens no tree of the first chain.
  8 ONE KEY: the shared chain's first record is a function s₂ of the record alone.
THE CONCLUSION, for each record: the list that the top theorem for a proof file asks of the three
chains for a batch of N requests (`Links.KnowsJ`, behind `Links.comap`), at the key "the shared
chain's first record, with the stored table", at the errors of `Three.snd`: the blocks' own errors
in a row, each once, behind an error 0 for each silent round. -/
def FoldSlots : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ W TF TJ T3 : Type) (tF : TF) (tJ : TJ)
    (t3 : T3) (F : FileDescription (X × Rec)) (T : ThreeAt C D all F X₁ X₂ W) (Q : PlacesAt D all F W)
    (okF : X × Rec → TF → Bool) (okJ : F.XiPub × F.S₁ → TJ → Bool)
    (ok3 : F.XiPub × F.S₁ × F.S₂ → T3 → Bool)
    (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT C D.ds₃) (N : ℕ)
    (s₂ : Rec → F.S₂),
    OfDesc F T → (atDesc F T).Fits →
    EachGood Q.on₁ Q.R₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁) →
    EachLostBoth N Q.on₂ Q.R₂ (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂) 0
      ((atDesc F T).p₂ :: (atDesc F T).l₂) →
    EachGood Q.on₃ Q.R₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃) →
    (atDesc F T).Glued Q →
    (∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) →
    (∀ x rec, F.start₂ (F.pub (x, rec)) = s₂ rec) →
    ∀ rec : Rec,
      ((((atDesc F T).row tF tJ t3 okF okJ ok3).links
        ((atDesc F T).snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).comap fun x : X => (x, rec)).KnowsJ N
        (fun a : (F.XiPub × F.S₁) × (EAll D all).Str => (F.start₂ a.1.1, a.2.1)) (fun _ => ())

#check @Iop.Spec.knowB_of_lost_both
#check @PaidBoth
#check @LostBothOfLostBy
#check @LostBothOfOwn
#check @LostBothBeside
#check @ChainLinkBoth
#check @FoldSlots

end VerifiableInference.Desc.Sound
