-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ExtHeard.lean: what the blocks' extractors composed (`rowExt`,
Johnson/Desc/Sound/ChainRule.lean) yield as THE TOKEN of a witness: if one block's extractor sets
the token to what the record behind the block holds as heard, the extractors of the blocks in front
of it hand the token on, and the blocks behind it leave what was heard: then, where the row puts
out, the token in the composed extractor's yield is what the LAST record holds as heard. A SHEET OF
STATEMENTS: definitions, and propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE
(the proofs: Johnson/Desc/Sound/ExtHeardProofs.lean).

Why. The proof file's hypothesis on soundness wants that the token in what the three chains'
extractors give is the one that the transcript names (`TieReads`, from `FirstReads`:
Johnson/Flat/TiesSheet.lean). At the rule of composition's value (`Three.snd`,
Johnson/Desc/Sound/FileRule.lean) the first chain's extractor is `rowExt`. This sheet cuts the law
on it into one law a block.

Main names.
  `Piece.PassesTok tok`: the block's extractor hands the witness's token on.
  `Piece.SetsTok tok heard`: where the block's reduction puts out, what the record behind it holds
    as heard is the token in its extractor's yield, WHATEVER THE WITNESS BEHIND.
  `Piece.LeavesOut h`: where the block's reduction puts out, h of the record is as it was.
  `HearsRowAt tok heard n`: block number n of the row (from 0) sets, those in front pass, those
    behind leave. `ExtRowAt tok rd n`: the extractors' side of it alone.
  THE STATEMENTS: `LeavesBelow` · `LaysBelow` · `LeavesOutOfBlock` (from `Block.Leaves`,
    Johnson/Desc/Sound/FoldHeard.lean) · `SetsOfLays` (from `Block.Lays` and a law on the
    extractor's text) · `RowLeavesOut` · `HearsRowOf` (`HearsRowAt` from the blocks' two laws and
    `ExtRowAt`) · `RowExtHeard` · `OwnOut` (the chain's decision over its own list of rounds puts
    out what the row does, along the cast of `extOwn`) · `FirstHoldsAt`: at `Three.snd`: where the
    row's first reduction puts out b₁, what b₁ holds as heard is the token in the first extractor's
    yield.

Every "there is", walked. None of the statements has one: which block sets is the number n; the last
record is read off what is handed on by a named function back₁.

Limits. NO BLOCK OF THE PROTOCOL IS NAMED. A block that never puts out meets `SetsTok` and
`LeavesOut` for nothing. THE TYPE Tok HAS TO BE CHOSEN SO THAT THE LAWS CAN BE MET: `ExtRowAt`'s
clause at the setting block runs over ALL transcripts, and `SetsTok` over all at which the block
puts out: a reading rd into a type of tokens that says nothing at some element that the round can
send meets neither: take the element as it is written, and read a token off it where the instance is
put together. `PassesTok` runs over all statements, transcripts and witnesses. Nothing here says
that an extractor with these laws has its clause of knowledge soundness: how a clause is carried to
witnesses with a token: Johnson/Flat/TiesSheet.lean (`PassesOf`, `SetsOf`). Nothing on acceptance,
on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FileRule
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-! ## 1 Three laws on a block with its stretch -/

section
variable {S Cl W Tok α : Type} {C : CK} {F : Frame}

/-- The block's extractor hands the witness's token on. -/
def Piece.PassesTok (tok : W → Tok) (p : Piece C F S Cl W) : Prop :=
  ∀ a τ w, tok (p.ext a τ w) = tok w

/-- Where the block's reduction puts out b: what b's record holds as heard is the token in the
extractor's yield, whatever the witness behind. -/
def Piece.SetsTok (tok : W → Tok) (heard : S → Option Tok) (p : Piece C F S Cl W) : Prop :=
  ∀ a τ b w, p.ior.red.out a τ = some b → heard b.1 = some (tok (p.ext a τ w))

/-- Where the block's reduction puts out, the reading h of the record is as it was. -/
def Piece.LeavesOut (h : S → α) (p : Piece C F S Cl W) : Prop :=
  ∀ a τ b, p.ior.red.out a τ = some b → h b.1 = h a.1

/-- Block number n of the row p :: l (from 0) sets the token; those in front of it pass it; those
behind it leave what was heard. -/
def HearsRowAt (tok : W → Tok) (heard : S → Option Tok) :
    ℕ → Piece C F S Cl W → List (Piece C F S Cl W) → Prop
  | 0, p, l => p.SetsTok tok heard ∧ ∀ r ∈ l, r.LeavesOut heard
  | _ + 1, _, [] => False
  | n + 1, p, q :: l => p.PassesTok tok ∧ HearsRowAt tok heard n q l

/-- THE EXTRACTORS' SIDE ALONE of `HearsRowAt`: the extractors of the blocks in front of block
number n hand the token on; the token in the yield of block number n's extractor is what rd reads of
that block's stretch's written rounds as the block is shown them. -/
def ExtRowAt (tok : W → Tok) (rd : List Fmt.RoundView → Option Tok) :
    ℕ → Piece C F S Cl W → List (Piece C F S Cl W) → Prop
  | 0, p, _ => ∀ a τ w, rd (shownAt [] p.b (rvT C p.ds τ ++ p.back)) = some (tok (p.ext a τ w))
  | _ + 1, _, [] => False
  | n + 1, p, q :: l => p.PassesTok tok ∧ ExtRowAt tok rd n q l

end

/-! ## 2 The statements -/

/-- The block with the test "every word is below the prime" in front (`below`,
Johnson/Desc/Sound/ChainRule.lean) has the two laws of Johnson/Desc/Sound/FoldHeard.lean where the
block has them. -/
def LeavesBelow : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (b : Block S Cl), b.Leaves h → (below b).Leaves h

def LaysBelow : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (rd : List Fmt.RoundView → α) (b : Block S Cl),
    b.Lays h rd → (below b).Lays h rd

/-- A block whose decision leaves h, with any stretch: its reduction leaves h. -/
def LeavesOutOfBlock : Prop :=
  ∀ (S Cl W α : Type) (C : CK) (F : Frame) (h : S → α) (p : Piece C F S Cl W),
    p.b.Leaves h → p.LeavesOut h

/-- A block whose decision lays what rd reads of its rounds: if the token in its extractor's yield
is what rd reads of the stretch's written rounds as the block is shown them, the block sets the
token.
-/
def SetsOfLays : Prop :=
  ∀ (S Cl W Tok : Type) (C : CK) (F : Frame) (tok : W → Tok) (heard : S → Option Tok)
    (rd : List Fmt.RoundView → Option Tok) (p : Piece C F S Cl W),
    p.b.Lays heard rd →
    (∀ a τ w, rd (shownAt [] p.b (rvT C p.ds τ ++ p.back)) = some (tok (p.ext a τ w))) →
    p.SetsTok tok heard

/-- A row of blocks that all leave h leaves h. -/
def RowLeavesOut : Prop :=
  ∀ (S Cl W α : Type) (C : CK) (F : Frame) (h : S → α) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)), (∀ r ∈ p :: l, r.LeavesOut h) →
    ∀ a τ b, (rowIOR p l).red.out a τ = some b → h b.1 = h a.1

/-- **`HearsRowAt` from the blocks' laws and the extractors' side.** The pieces hold the blocks
pre ++ blk :: post, each made over by g (in the use: the test below the prime in front, and the lift
to the chain's record), which carries the two laws from the reading h₀ to the reading h. -/
def HearsRowOf : Prop :=
  ∀ (S₀ S Cl W Tok : Type) (C : CK) (F : Frame) (tok : W → Tok) (h₀ : S₀ → Option Tok)
    (h : S → Option Tok) (rd : List Fmt.RoundView → Option Tok) (g : Block S₀ Cl → Block S Cl),
    (∀ b, b.Leaves h₀ → (g b).Leaves h) → (∀ b, b.Lays h₀ rd → (g b).Lays h rd) →
    ∀ (pre : List (Block S₀ Cl)) (blk : Block S₀ Cl) (post : List (Block S₀ Cl))
      (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)),
      (p :: l).map (·.b) = (pre ++ blk :: post).map g → blk.Lays h₀ rd →
      (∀ c ∈ post, c.Leaves h₀) → ExtRowAt tok rd pre.length p l →
      HearsRowAt tok h pre.length p l

/-- **Where the row puts out b, what b's record holds as heard is the token in the composed
extractor's yield, whatever the last witness.** -/
def RowExtHeard : Prop :=
  ∀ (S Cl W Tok : Type) (C : CK) (F : Frame) (tok : W → Tok) (heard : S → Option Tok) (d : W)
    (n : ℕ) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)), HearsRowAt tok heard n p l →
    ∀ a τ b w, (rowIOR p l).red.out a τ = some b → heard b.1 = some (tok (rowExt d p l a τ w))

/-- Where the stretches tile the chain: the chain's decision over its own list of rounds puts out
what the blocks' reductions composed put out at the transcript carried along h, as `extOwn` carries
it. (`FoldIsRow`, read at the chain's own list.) -/
def OwnOut : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (ds : List RDT) (_ : rowData p l = ds)
    (h : (rowIOR p l).shape = uLT C ds), Tiled p l →
    ∀ (a : S × F.E.Str) (τ : Iop.Tr (uLT C ds)),
      (chainIOR C F name ((p :: l).map (·.b)) p.base ds (rowBack p l)).red.out a τ =
        (rowIOR p l).red.out a (cast (congrArg Iop.Tr h.symm) τ)

/-- **At the rule of composition's value**: where the row's first reduction puts out b₁, what the
first chain's last record, read off b₁ by back₁, holds as heard is the token in the first chain's
extractor's yield, whatever the later chains' witness. -/
def FirstHoldsAt : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 Tok : Type) (tF : TF)
    (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W)
    (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃) (tok : W → Tok) (heard : S₁ → Option Tok)
    (n : ℕ) (back₁ : X₁ → S₁),
    T.Fits → HearsRowAt tok heard n T.p₁ T.l₁ → (∀ x s, back₁ (T.out₁ x s) = s) →
    ∀ b τ₁ w₁ b₁,
      ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₁.out b τ₁ =
        some b₁ →
      heard (back₁ b₁.1) = some (tok
        (((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).e₁ b τ₁ w₁))

end VerifiableInference.Desc.Sound
