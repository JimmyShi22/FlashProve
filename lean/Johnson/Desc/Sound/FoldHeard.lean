-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldHeard.lean: what a chain's fold over blocks (`foldBlocks`, `chainAt`,
Johnson/Desc/Block.lean) says, at the chain's end, of ONE READING h OF THE CARRIED RECORD: if one
block lays h from its own rounds, and no later block turns h, then at the end h is what that block's
rounds show. A SHEET OF STATEMENTS: definitions, and propositions written as `def … : Prop`. NOTHING
IS PROVED IN THIS FILE (the proofs: Johnson/Desc/Sound/FoldHeardProofs.lean).

Why. A file's description compares what was heard with what is asked in its last test alone
(`FileDescription.fin`). The proof file's hypothesis on soundness wants from that test: the token that the
TRANSCRIPT names is the instance's own (`TieFins`, Johnson/Flat/TiesSheet.lean). Between the two lie
two properties of the first chain's fold, which TiesSheet.lean's limits name and do not state: the
reply's block lays what it hears in the record; no later block turns it. Here they are stated, for
any description, and the way from them to the views is stated.

Main names.
  `Block.Leaves h`: where the block's decision goes on, h of the record is as it was.
  `Block.Lays h rd`: where it goes on, h of the record is rd of the rounds that it was shown.
  `shownAt pre b rs`: of a chain's rounds rs, those that the block b behind the blocks pre is shown.
  `FoldLeaves`, `FoldLays`, `ChainLays`: the fold's laws.
  `LeavesLift`, `LeavesLiftPart`, `LeavesLiftIn`, `LaysLiftIn`, `LeavesAndThen`, `LeavesInside`,
    `LeavesQuiet`, `LeavesAfterIn`, `LeavesLink`, `LeavesChain`: how `Leaves` is had of a block that
    is made by Block.lean's own makers.
  `FileDescription.Hears F asked rd`: A RECORD OF DATA AND LAWS: the reading, the cut of the first chain's
    flat list at the reply's block, the two properties, and what the last test's yes gives.
  `FileDescription.Hears.said`: the token that a first view names: rd of the rounds shown to that block.
  `SaidOfEnds`: where the first chain's fold ends at e₁ and the last test says yes at x and e₁, the
    token that the first view names is the one asked at x.

Every "there is", walked. None of the statements has one. `FileDescription.Hears` is a structure with data:
the reading, the three lists' parts and the block stand in it BY NAME, and `said` is a function of
them.

Limits. NO DESCRIPTION OF THE PROTOCOL IS NAMED: the one member of `FileDescription.Hears` that is laid is
a toy's (Johnson/Desc/Sound/HearsToy.lean, with controls). A description whose last test never says
yes has `fins` for nothing. At rd := fun _ => none the record can be met only by a last test that
never says yes. THAT rd READS THE REPLY's MESSAGE, and not a constant, is seen at rd's text alone:
nothing here asks it. `Leaves` and `Lays` run over ALL records, rounds and columns, also those that
no run reaches. A block's claims and its runs behind the batching are run by other blocks' decisions
(the batching's; the frame's): `LeavesLink` asks the batching's block outright, at the link's own
claims. Nothing on soundness, on acceptance, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-! ## 1 Two laws on a block -/

section
variable {S Cl α : Type}

/-- Where the block's decision goes on, the reading h of the record is as it was. -/
def Block.Leaves (h : S → α) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → h s' = h s

/-- Where the block's decision goes on, the reading h of the record is rd of the rounds that the
decision was shown. -/
def Block.Lays (h : S → α) (rd : List Fmt.RoundView → α) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → h s' = rd rs

/-- Of a chain's rounds: those that the block b, behind the blocks pre, is shown: its own stretch,
each round without the sealed digest. -/
def shownAt (pre : List (Block S Cl)) (b : Block S Cl) (rs : List Fmt.RoundView) : List Fmt.RoundView :=
  ((rs.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).map noDigest

end

/-! ## 2 The fold's laws -/

/-- A fold over blocks that all leave h leaves h. -/
def FoldLeaves : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (ft : Nat) (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
    (∀ b ∈ bs, b.Leaves h) → foldBlocks ft bs s rs cols = .ok out → h out.1 = h s

/-- **If b lays h and no block behind it turns h, then at the fold's end h is rd of the rounds that
b was shown.** Nothing is asked of the blocks in front of b. -/
def FoldLays : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (rd : List Fmt.RoundView → α) (ft : Nat) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn),
    b.Lays h rd → (∀ c ∈ post, c.Leaves h) →
    foldBlocks ft (pre ++ b :: post) s rs cols = .ok out → h out.1 = rd (shownAt pre b rs)

/-- The same of a chain's fold with nothing left over. -/
def ChainLays : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (rd : List Fmt.RoundView → α) (name : String) (ft : Nat)
    (pre : List (Block S Cl)) (b : Block S Cl) (post : List (Block S Cl)) (s e : S) (v : Fmt.View),
    b.Lays h rd → (∀ c ∈ post, c.Leaves h) →
    chainAt name ft (pre ++ b :: post) s v = .ok e → h e = rd (shownAt pre b v.rounds)

/-! ## 3 `Leaves` of blocks that Block.lean's makers make -/

/-- A block at a part, laid at a wider record: it leaves every reading that `set` leaves. -/
def LeavesLift : Prop :=
  ∀ (S T Cl α : Type) (h : T → α) (get : T → S) (set : T → S → T) (b : Block S Cl),
    (∀ t s, h (set t s) = h t) → (b.lift get set).Leaves h

/-- The like for a part that is there only at times. -/
def LeavesLiftPart : Prop :=
  ∀ (S T Cl α : Type) (h : T → α) (get? : T → Option S) (set : T → S → T) (b : Block S Cl),
    (∀ t s, h (set t s) = h t) → (b.liftPart get? set).Leaves h

/-- A block at a part, laid at a wider record, and a reading OF THE PART: the two laws go over,
where `get` reads back what `set` lays. -/
def LeavesLiftIn : Prop :=
  ∀ (S T Cl α : Type) (h : S → α) (get : T → S) (set : T → S → T) (b : Block S Cl),
    (∀ t s, get (set t s) = s) → b.Leaves h → (b.lift get set).Leaves fun t => h (get t)

def LaysLiftIn : Prop :=
  ∀ (S T Cl α : Type) (h : S → α) (rd : List Fmt.RoundView → α) (get : T → S) (set : T → S → T)
    (b : Block S Cl),
    (∀ t s, get (set t s) = s) → b.Lays h rd → (b.lift get set).Lays (fun t => h (get t)) rd

/-- Two blocks as one. -/
def LeavesAndThen : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (name : String) (p q : Block S Cl),
    p.Leaves h → q.Leaves h → (Block.andThen name p q).Leaves h

/-- A block whose own record is born and dies inside it: it leaves every reading that `leave`
leaves.
-/
def LeavesInside : Prop :=
  ∀ (S T Cl α : Type) (h : S → α) (enter : S → Except String T) (b : Block T Cl)
    (leave : S → T → Except String S),
    (∀ s t s', leave s t = .ok s' → h s' = h s) → (Block.inside enter b leave).Leaves h

/-- A block without a round. -/
def LeavesQuiet : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (name : String) (chain : Nat) (link : Option Nat) (piece : Nat)
    (f : S → Except String S),
    (∀ s s', f s = .ok s' → h s' = h s) →
      (roundlessBlock (Cl := Cl) name chain link piece f).Leaves h

/-- The runs behind the batching, in a row. -/
def LeavesAfterIn : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (bs : List (Block S Cl)) (order : List (Nat × String)),
    (∀ b ∈ bs, ∀ c ∈ b.after, ∀ s s', c.2 s = .ok s' → h s' = h s) →
    ∀ s s', afterIn bs order s = .ok s' → h s' = h s

/-- **A link's flat list**: all its blocks leave h, if its laying and clearing, the blocks in front
of the batching and behind it, the runs behind the batching, and THE BATCHING's BLOCK AT THE LINK's
OWN CLAIMS do. -/
def LeavesLink : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (L : Link S Cl),
    (∀ s s', L.lay s = .ok s' → h s' = h s) → (∀ b ∈ L.hear, b.Leaves h) →
    (L.batch (claimsInBy L.each L.hear L.order)).Leaves h →
    (∀ b ∈ L.hear, ∀ c ∈ b.after, ∀ s s', c.2 s = .ok s' → h s' = h s) →
    (∀ b ∈ L.close, b.Leaves h) → (∀ s s', L.clear s = .ok s' → h s' = h s) →
    ∀ b ∈ L.blocksInOrder, b.Leaves h

/-- **A chain's flat list**, from its first block, its front, its links' flat lists, its back and
its last block. -/
def LeavesChain : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (c : Chain S Cl),
    c.first.Leaves h → (∀ b ∈ c.front, b.Leaves h) → (∀ L ∈ c.links, ∀ b ∈ L.blocksInOrder, b.Leaves h) →
    (∀ b ∈ c.back, b.Leaves h) → c.last.Leaves h → ∀ b ∈ c.blocksInOrder, b.Leaves h

/-! ## 4 A description that hears the reply -/

/-- **What `TieFins` asks of a description**: data and laws. asked: what is asked of the proof at an
instance. rd: the token that the reply's block's rounds name. -/
structure FileDescription.Hears {Xi : Type} (F : FileDescription Xi) {Tok : Type} (asked : Xi → Tok)
    (rd : List Fmt.RoundView → Option Tok) where
  /-- the reading of the first chain's record: what was heard -/
  heard : F.S₁ → Option Tok
  /-- the first chain's blocks in front of the reply's block -/
  pre : List (Block F.S₁ F.Cl)
  /-- the reply's block -/
  blk : Block F.S₁ F.Cl
  /-- the blocks behind it -/
  post : List (Block F.S₁ F.Cl)
  cut : F.first.blocksInOrder = pre ++ blk :: post
  /-- the reply's block lays what it hears -/
  lays : blk.Lays heard rd
  /-- no later block turns it -/
  leaves : ∀ c ∈ post, c.Leaves heard
  /-- the last test's yes: what was heard is what is asked -/
  fins : ∀ x e₁ e₂ e₃, F.fin x e₁ e₂ e₃ = true → heard e₁ = some (asked x)

/-- The token that a first view, as the compiler's slot hands it, names. It reads the view's rounds
alone. -/
def FileDescription.Hears.said {Xi : Type} {F : FileDescription Xi} {Tok : Type} {asked : Xi → Tok}
    {rd : List Fmt.RoundView → Option Tok} (H : F.Hears asked rd) (v₁ : Fmt.View) : Option Tok :=
  rd (shownAt H.pre H.blk (withEmptySealRound v₁).rounds)

/-- **Where the first chain's fold, from any first state, ends at e₁ on the view v₁ with the sealing
round put back, and the last test says yes at x and e₁: the token that v₁ names is the one asked at
x.** -/
def SaidOfEnds : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (Tok : Type) (asked : Xi → Tok) (rd : List Fmt.RoundView → Option Tok)
    (H : F.Hears asked rd) (x : Xi) (s : F.S₁) (v₁ : Fmt.View) (e₁ : F.S₁) (e₂ : F.S₂) (e₃ : F.S₃),
    chainAt "the first chain" 0 F.first.blocksInOrder s (withEmptySealRound v₁) = .ok e₁ →
    F.fin x e₁ e₂ e₃ = true → H.said v₁ = some (asked x)

end VerifiableInference.Desc
