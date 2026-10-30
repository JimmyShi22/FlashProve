-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BordersLastQ.lean: the last chain's table of joints (Johnson/Desc/Last/BordersLast.lean) AS THE CONDITIONS AND RELATIONS OF THE RULE OF
COMPOSITION AT THE THIRD CHAIN: onQ₃, relQ₃: NAMED TERMS; and the two joints that they close. Definitions, and seven statements written as def … : Prop.
NOTHING IS PROVED IN THIS FILE (Johnson/Desc/Sound/BordersLastQProofs.lean). (The joint's two halves stand apart; the book-keeping is a Bool; (SH₃) is asked inside the shared chain's last promise alone: the start's yes by itself does not give it at a silly
first record).

The third chain's record, in the filling that is meant (Three.ofStarts): ((the public part, the first chain's last record, the shared chain's last record), the
chain's own record).
  insQ₃, outsQ₃: what block number k closes | opens, with what it reads.   meansQ₃: what an item says of a statement of the chain.
  **relQ₃ k**: every item that is open at border k holds.   **onQ₃ k**: the table's promise there.
  LastJoin: if every block has its own law between the items that its row closes and opens (Piece.Own) and the items that ride past it are kept
    (Piece.Frames), the chain has EachGoodIn at onQ₃ | relQ₃.   LastJoinPlain: the like in the plain form, at the relations' shadows.
  EndLast: BEHIND THE LAST BLOCK NO ITEM IS OPEN.   EndsLast: so Three.Ends holds at relQ₃, whatever wEnd is.
  TieLast: **Three.Glue₂ WITH BOTH TABLES LAID IN** (onQ₂ | relQ₂; onQ₃ | relQ₃), FROM: the shared chain is as long as its table · (START) the
    start's yes gives "no mark" at the first chain's last record [UNFENCED, AND A FENCE WOULD NOT PAY IT: the slot's own condition holds marked records too: IT IS PAID BY THE START's OWN TEST: at the seated description: fileDescBy: start₃ begins "if !(get s₁).fin then .error …"; Johnson/Desc/First/State.lean: S.fin's first conjunct is failed.isNone; typed here at an Option: atDesc reads (F.start₃ p a b).toOption] · (SH₃) inside the shared chain's last promise (in which the first chain's rides) the start's yes gives the book-keeping at border 0 · (PO→) the shared chain's promise
    on Omega, at the acting part's value at its last border, gives it at the whole strings · (PO←) Omega's pin at the whole strings gives it at the
    acting part's value. OnZero₃OfEnd₂, RelEnd₂OfZero₃: ITS TWO HALVES, EACH BY ITSELF (the plain form's rule asks them apart): the promise goes forward; the relation goes
    back AT THE SAME WITNESS, and no promise is asked for that. THE FOUR OWN ITEMS (Eval) · (Dot) · W's pin · the index masks' pin CROSS THE JOINT AS ONE TERM: nothing is asked for them.

Limits. Those of BordersLast.lean. Every meaning is a letter: the terms are named, not closed. (START), (SH₃), (PO→), (PO←) are premises.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.BordersLast
import Johnson.Desc.Sound.GlueSecond
import Johnson.Desc.Sound.SpinePlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Last

/-- The row of block number k. A number behind the last block: the empty row. -/
def rowAtL (k : ℕ) : RowOfL := (lastPlaces[k]?.map rowL).getD {}

/-- What block number k closes, with what it reads: as a list. -/
def insL₃ (k : ℕ) : List ItemL := (rowAtL k).ins ++ (rowAtL k).ctx

/-- What it opens, with what it reads: as a list. -/
def outsL₃ (k : ℕ) : List ItemL := (rowAtL k).outs ++ (rowAtL k).ctx

def insQ₃ (k : ℕ) (i : ItemL) : Prop := i ∈ insL₃ k
def outsQ₃ (k : ℕ) (i : ItemL) : Prop := i ∈ outsL₃ k

section
variable {P S₁ S₂ S₃ Wt : Type} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ (P × S₁) Wt)
  (ML : MeaningL S₃ Wt) (Pm : PromMeaning S₂) (PL : PromMeaningL S₂ S₃ (P × S₁))
  (Oc : P × S₁ → Strs → Prop)

/-- What an item says of a statement of the chain. -/
def meansQ₃ (i : ItemL) (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) (w : Wt) : Prop :=
  i.holds N Mg ML (a.1.1.1, a.1.1.2.1) a.1.1.2.2 a.1.2 (strsOf Fr a.2) w

/-- **THE RELATION AT BORDER k OF THE LAST CHAIN: every open item holds.** -/
def relQ₃ (k : ℕ) : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Wt → Prop :=
  relAt (meansQ₃ (Fr := Fr) N Mg ML) (openAfter insQ₃ outsQ₃ (· ∈ startLast) k)

/-- **THE CONDITION AT BORDER k OF THE LAST CHAIN.** -/
def onQ₃ (k : ℕ) (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) : Prop :=
  onL N Mg Pm PL Oc k (a.1.1.1, a.1.1.2.1) a.1.1.2.2 a.1.2 (strsOf Fr a.2)

end

/-- **The last chain's joints join.** -/
def LastJoin : Prop :=
  ∀ (P S₁ S₂ S₃ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ (P × S₁) Wt)
    (ML : MeaningL S₃ Wt) (Pm : PromMeaning S₂) (PL : PromMeaningL S₂ S₃ (P × S₁))
    (Oc : P × S₁ → Strs → Prop) (l : List (Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)),
    EachOwn (onQ₃ N Mg Pm PL Oc) (meansQ₃ N Mg ML) insQ₃ outsQ₃ (· ∈ startLast) 0 l →
    EachGoodIn (onQ₃ N Mg Pm PL Oc) (relQ₃ N Mg ML) 0 l

/-- **The like in the plain form.** -/
def LastJoinPlain : Prop :=
  ∀ (P S₁ S₂ S₃ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ (P × S₁) Wt)
    (ML : MeaningL S₃ Wt) (Pm : PromMeaning S₂) (PL : PromMeaningL S₂ S₃ (P × S₁))
    (Oc : P × S₁ → Strs → Prop) (l : List (Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)),
    EachOwn (onQ₃ N Mg Pm PL Oc) (meansQ₃ N Mg ML) insQ₃ outsQ₃ (· ∈ startLast) 0 l →
    EachPlain (onQ₃ N Mg Pm PL Oc) (fun k => shadow (relQ₃ N Mg ML k)) 0 l

/-- **Behind the last block no item is open.** -/
def EndLast : Prop := ∀ i : ItemL, ¬ openAfter insQ₃ outsQ₃ (· ∈ startLast) lastPlaces.length i

/-- **Three.Ends at the last chain's table.** -/
def EndsLast : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type)
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt)
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt),
    1 + T.l₃.length = lastPlaces.length →
    T.Ends { Q with R₃ := relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML }

/-- **THE PROMISE GOES FORWARD** (the first half of the joint, by itself): the shared chain's promise at its last border gives the last chain's at its first, at
the record that the start makes. -/
def OnZero₃OfEnd₂ : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type)
    (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂')
    (PL : PromMeaningL S₂' S₃' (P × S₁')) (Oc : P × S₁' → Strs → Prop) (split : Bool),
    1 + T.l₂.length = (sharedPlaces split).length →
    (∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → Mg.unmarked1 (p, s₁)) →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
      onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b → start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
      PL.shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true) →
    (∀ b : ((P × S₁') × S₂') × (EAll D all).Str,
      (PromS.noColl .oOmega).holds N Pm ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b).1
        (strsOfAct (frameAt D all D.key₂ T.ft₂) ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b)) →
      (PromS.noColl .oOmega).holds N Pm b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2)) →
    ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
      onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b → start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
      onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)

/-- **THE RELATION GOES BACK** (the second half, by itself; NO PROMISE IS ASKED): what the last chain claims at its first border, at the record that the start
makes, gives what the shared chain claims at its last, AT THE SAME WITNESS. -/
def RelEnd₂OfZero₃ : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type)
    (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂')
    (PL : PromMeaningL S₂' S₃' (P × S₁')) (Oc : P × S₁' → Strs → Prop) (split : Bool),
    1 + T.l₂.length = (sharedPlaces split).length →
    (∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → Mg.unmarked1 (p, s₁)) →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (w : Wt),
      (ItemS.pin .oOmega).holdsSh N Mg b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
      muQ N Mg T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w) →
    ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃') (w : Wt),
      start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
      relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) w →
      relQ₂ N Mg split T.p₂ T.l₂ (1 + T.l₂.length) b w

/-- **Glue₂, with both tables laid in.** -/
def TieLast : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type) (pub : Y → P)
    (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt)
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂')
    (PL : PromMeaningL S₂' S₃' (P × S₁')) (Oc : P × S₁' → Strs → Prop) (split : Bool),
    1 + T.l₂.length = (sharedPlaces split).length →
    (∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → Mg.unmarked1 (p, s₁)) →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
      onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b → start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
      PL.shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true) →
    (∀ b : ((P × S₁') × S₂') × (EAll D all).Str,
      (PromS.noColl .oOmega).holds N Pm ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b).1
        (strsOfAct (frameAt D all D.key₂ T.ft₂) ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b)) →
      (PromS.noColl .oOmega).holds N Pm b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2)) →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (w : Wt),
      (ItemS.pin .oOmega).holdsSh N Mg b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
      muQ N Mg T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w) →
    (T.ofStarts pub start₁ start₂ start₃).Glue₂
      { Q with
        on₂ := onQ₂ N Pm Oc split T.p₂ T.l₂, R₂ := relQ₂ N Mg split T.p₂ T.l₂
        on₃ := onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc
        R₃ := relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML }

#check @LastJoin
#check @LastJoinPlain
#check @EndLast
#check @EndsLast
#check @OnZero₃OfEnd₂
#check @RelEnd₂OfZero₃
#check @TieLast

end VerifiableInference.Desc.Sound
