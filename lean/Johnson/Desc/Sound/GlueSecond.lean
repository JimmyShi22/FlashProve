-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/GlueSecond.lean: THE JOINT OF THE SHARED AND THE LAST CHAIN (`Three.Glue₂`,
Johnson/Desc/Sound/FileRule.lean), with the shared chain's conditions and relations laid as the table's own
terms (`onQ₂`, `relQ₂`): to what it comes down; and, for that, WHAT IS OPEN AT THE SHARED CHAIN's END, AS A THEOREM's
STATEMENT. Definitions, and three statements written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

  `openL ins outs s k`: the open items at border k AS A LIST, where a table's rows are lists.
  `OpenIsList`: the rule's open set (`openAfter`, Johnson/Desc/Sound/Spine.lean: a predicate) has just that list's
    members: general in the table. (It is what ties a table's computed lists, on which its tests run, to the
    relation "every open item holds".)
  `EndShared`: AT THE SHARED CHAIN's LAST BORDER THE ONE SHARED ITEM THAT IS OPEN IS o_omega's PIN, at both shapes.
  `GlueSecond`: in the filling that is meant (`Three.ofStarts`) `Glue₂` says: "the last chain has a first record,
    and what it claims there" gives what the shared chain claims at its last border. With the chain as long
    as the table: IT COMES DOWN TO: (A) THE PROMISE GOES FORWARD: from `onQ₂` at the last border, where
    `start₃` gives a record: the last chain's first condition · (B1) THE RELATION GOES BACK: o_omega's pin, at
    the shared chain's own last record and own trees · (B2) the five own items that are open at the end: no
    mark of the first chain, the index masks' pin, W's pin, (Eval), (Dot).

WHAT IT ASKS OF THE LAST CHAIN's TABLE, which is not written: its start holds these six items, read at ITS
first record. "No mark" is meant to come from `start₃`'s own yes (it refuses a first chain that does not stand
at its end; the first conjunct of that test is "no mark": Johnson/Desc/ProofFile/Frames1.lean, fileDescBy's start₃: "if !(get s₁).fin then .error …"; Johnson/Desc/First/State.lean: S.fin := s.failed.isNone && …).

Limits. Rules under letters; the last chain's first condition and relation are letters of `Places`.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersSharedQ
import Johnson.Desc.Sound.SpineList

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared

-- openL and OpenIsList (the open items at a border as a list; "the rule's open set has just that list's members") are the first table's list tools':
-- Johnson/Desc/Sound/SpineList.lean.

/-- **At the shared chain's last border one shared item is open: o_omega's pin.** -/
def EndShared : Prop :=
  ∀ (split : Bool) (i : ItemS),
    openAfter (insSh split) (outsSh split) startSh (sharedPlaces split).length i ↔
      i = .pin .oOmega

/-- **`Glue₂` at the shared chain's table's terms.** -/
def GlueSecond : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type) (pub : Y → P)
    (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt)
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (Pm : PromMeaning S₂') (Oc : P × S₁' → Strs → Prop)
    (split : Bool),
    1 + T.l₂.length = (sharedPlaces split).length →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
      onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b → start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
      Q.on₃ 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)) →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃') (w : Wt),
      onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b → start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
      Q.R₃ 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) w →
      muQ N Mg T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
          ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w ∧
        ∀ i ∈ endS.filter (·.own), i.holdsOwn N Mg b.1.1 b.1.2
          (strsOf (frameAt D all D.key₂ T.ft₂) b.2) w) →
    (T.ofStarts pub start₁ start₂ start₃).Glue₂
      { Q with on₂ := onQ₂ N Pm Oc split T.p₂ T.l₂, R₂ := relQ₂ N Mg split T.p₂ T.l₂ }

#check @OpenIsList
#check @EndShared
#check @GlueSecond

end VerifiableInference.Desc.Sound
