-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/OrcStrs.lean: the code switch: THE READING OF THE ORACLES BY KEY AND
POSITION, OFF THE ORACLES AS PLAIN FUNCTIONS (Johnson/Desc/Msg.lean's Strs): so that the table of
joints' sentences, which are handed Strs, and the switch's law, which is handed a chain's oracles,
read one thing.
  orcY       to a key and a position: the column, at that position, of the first tree of the list
             whose key it is; the empty column where there is none
  orcS_strs  ColsAtStage.lean's orcS at a piece's stage over a frame F IS orcY F.all F.key at
             strsOf F y (Johnson/Desc/Sound/MsgAt.lean): by unfolding
LIMITS. The list of trees and the keys are the frame's: letters here. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.ColsAtStage
import Johnson.Desc.Sound.MsgAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes.Maker
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound (Frame strsOf colAt)

/-- **The reading, off the oracles as plain functions.** -/
def orcY (all : List LeftT) (key : ℕ → ℕ) (Y : Strs) (k x : ℕ) : List UInt64 :=
  match all.find? (fun L => key L.no == k) with
  | some L => Y.col L.no x
  | none => []

/-- The two readings are one. -/
theorem orcS_strs (F : Frame) (base : ℕ) (ds : List RDT) (y : F.E.Str) :
    orcS ⟨F.a, base, F.all, ds, F.key, F.all⟩ y = orcY F.all F.key (strsOf F y) := by
  funext k x
  unfold orcS orcY
  cases F.all.find? (fun L => F.key L.no == k) <;> rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.orcS_strs
