-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyBridges23.lean: The key
file, chains 2 and 3: at four blocks of the key file's own description the block's yes gives the
last chain's files' plain facts. Theorems; no definition.

OBJECT. Blocks number 3, 6 and 8 (from 0) of `(Key.descriptionFromSource X N P).shared.blocksInOrder` and block number 0 of
`(Key.descriptionFromSource X N P).second.blocksInOrder`: "(rec_gamma)", "joins", "SPLIT" and "K14, second part", AS THE
DESCRIPTION SEATS THEM, by their field `decide`.
USER. The tables' files' wraps of the rows 2.3, 2.6, 2.8 and 3.0 (keeps₂_67's premise hJ and
keeps₃_01's premise hL: two names that are declared nowhere in this library). Each
conclusion here is typed after that premise's form; no Lean here holds the two together:
`∀ d rs gs d', b.decide d rs gs = .ok d' → ∃ …`.
LETTERS. X N P: free. b: the block at that number in the description's own list. l: what
`K14.blocks` returns at the key file's own parameters `p14At X P`. The shape in `SplitLaid`, `RecLaid`
and `Laid` is the sized key's (`shape_one`, `shape_is`): a table that speaks at a letter S owes
S = X.chains.made.sized.key.once.shape.

CAUTION. (1) Each statement has the form "a yes gives": true, and empty, where the block never says
yes; where `K14.blocks (p14At X P)` returns nothing the three of the shared chain have no l to be
stated at. That the real key file's parameters give eight blocks, that its shape splits, and that
these four blocks say yes on an honest file is shown by no theorem here. (2) The rows that spend
these facts speak over the tables' letters: until a member of their premises together is shown
they may be true and empty at the real protocol, and count as closing nothing.
IS IT EMPTY HERE? A member was sought in prints, which are not in this repository. One (an
evaluation over other base files than these; both stored key files, MADE-UP WEIGHTS) says:
"PLAN: planOk true", "WALK chain 2: 13 states [due 13]; stopped [due none]: none", "START of the
last chain at the two honest ends …: yes". By that evaluation the shared chain's twelve blocks say
yes on the honest file at both sizes: there the three statements on the shared chain are not idle.
By inference from it: `K14.blocks` returns a list there (else the one block
that stands in fails the plan), and the shape splits (else the chain has eleven blocks). Of block 0
of the last chain no print at hand had a walk over the base files on which this file was built.
EVALUATED IS NOT PROVED.
Main names.
  `shared_3`, `shared_6`, `shared_8`: the description's blocks at these numbers are the third, sixth
    and eighth of K14's eight, seated.
  `recLaid_at_desc`, `joined_at_desc`, `splitLaid_at_desc`, `laid_at_desc`: the four.
  `shape_one`, `shape_is`: the two chains' parameters hold one shape: the sized key's.

How. `shared_at_blocks`, `second_flat` and `seat_decide` (Johnson/RunOne/KeyCut23.lean);
Johnson/Desc/Key/Laid/AtBlocks.lean; `laid_k14Second` (Johnson/Desc/Third/Law/Laid.lean).

Limits. Nothing on a piece of the compiled verifier: that the maker's piece holds `held` of such a
block is the tables'. Nothing on soundness or on hiding.
-/
import Johnson.RunOne.KeyCut23
import Johnson.Desc.Key.Laid.AtBlocks
import Johnson.Desc.Third.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- The two later chains' parameters hold one shape. -/
theorem shape_one : (p14At X P).S = (thirdPar X.chains).S := rfl

/-- It is the sized key's. -/
theorem shape_is : (p14At X P).S = X.chains.made.sized.key.once.shape := rfl

variable (b1 b2 b3 b4 b5 b6 b7 b8 : Block _root_.Desc.K14.St Unit)
  (h : _root_.Desc.K14.blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8])
include h

theorem shared_3 : (descriptionFromSource X N P).shared.blocksInOrder[3]? = some (seat b3) := by
  rw [shared_at_blocks X N P _ h]
  rfl

theorem shared_6 : (descriptionFromSource X N P).shared.blocksInOrder[6]? = some (seat b6) := by
  rw [shared_at_blocks X N P _ h]
  rfl

theorem shared_8 : (descriptionFromSource X N P).shared.blocksInOrder[8]? = some (seat b8) := by
  rw [shared_at_blocks X N P _ h]
  rfl

/-- **Row 2.3's block, as the description seats it: its yes gives RecLaid.** -/
theorem recLaid_at_desc (b : Block _root_.Desc.K14.St Claim)
    (hb : (descriptionFromSource X N P).shared.blocksInOrder[3]? = some b) :
    ∀ d rs gs d', b.decide d rs gs = .ok d' → ∃ GU rows, RecLaid (p14At X P).par d d' GU rows := by
  have e : b = seat b3 := Option.some.inj (hb.symm.trans (shared_3 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  exact recLaid_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h

/-- **Row 2.6's block: its yes gives Joined**, where the shape splits. -/
theorem joined_at_desc (hS : (p14At X P).S.sharedSplitNeeded = true)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[6]? = some b) :
    ∀ d rs gs d', b.decide d rs gs = .ok d' → ∃ GU GO, Joined d d' GU GO := by
  have e : b = seat b6 := Option.some.inj (hb.symm.trans (shared_6 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  exact joined_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h hS

/-- **Row 2.8's block: its yes gives SplitLaid**, where the shape splits. -/
theorem splitLaid_at_desc (hS : (p14At X P).S.sharedSplitNeeded = true)
    (b : Block _root_.Desc.K14.St Claim) (hb : (descriptionFromSource X N P).shared.blocksInOrder[8]? = some b) :
    ∀ d rs gs d', b.decide d rs gs = .ok d' →
      ∃ GU GO x l n row mu, SplitLaid (p14At X P).S d d' GU GO x l n row mu := by
  have e : b = seat b8 := Option.some.inj (hb.symm.trans (shared_8 X N P b1 b2 b3 b4 b5 b6 b7 b8 h))
  subst e
  exact splitLaid_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h hS

end

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- **Row 3.0's block, as the description seats it: its yes gives Laid.** -/
theorem laid_at_desc (b : Block VerifiableInference.Desc.Third.S₃ Claim)
    (hb : (descriptionFromSource X N P).second.blocksInOrder[0]? = some b) :
    ∀ s rs gs s', b.decide s rs gs = .ok s' →
      ∃ bd yO G dot, VerifiableInference.Desc.Third.Laid (thirdPar X.chains).S s s' bd yO G dot := by
  obtain ⟨f, hf, _, _, hd⟩ := second_flat X N P
  rw [hf] at hb
  have e : f = b := Option.some.inj (show some f = some b from hb)
  rw [← e]
  intro s rs gs s' hy
  rw [hd] at hy
  exact VerifiableInference.Desc.Third.Law.laid_k14Second (thirdPar X.chains) s s' rs gs hy

end

end Johnson.RunOne.KeyRows23
