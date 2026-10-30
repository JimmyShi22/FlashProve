-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/StandsBy.lean: the kind «the code switch»: A YES TELLS AT WHICH SORT OF
PLACE THE BLOCK's NUMBERS STAND: the decision matches the numbers' field «stands» against where
the record stands, so from a yes and the record's place the field follows. NO BLOCK IMPORTS THIS
FILE.
WHY: whoever seats the lot's block at a place of the description knows where the record stands
there, not how the lot's maker spelt «stands» (it goes by the spelling of the plan's looks).
  link_of_between    a yes at a record that stands between the links: p.stands = .link
  head_of_head       a yes at a record that stands in the head's link: p.stands = .head
  finish_of_fin      a yes at a record that stands in the finish: p.stands = .finish
  between_of_link · head_of_stands · fin_of_finish   the other way: from the field to where the
                                                     record stands
A frame fact. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model

variable {snd : _root_.Tw.K2.SendFn} {p : P2} {s s' : S} {rs : List Fmt.RoundView}
  {gs : List (List (Nat × List UInt64))}

theorem link_of_between (h : decideWith snd p s rs gs = .ok s') (hb : s.here = .between) :
    p.stands = .link := by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨_, a, ha⟩ | ⟨_, a, ha⟩
  · exact hp
  · rw [hb] at ha; cases ha
  · rw [hb] at ha; cases ha

theorem head_of_head {a : HeadOwn} (h : decideWith snd p s rs gs = .ok s') (hb : s.here = .head a) :
    p.stands = .head := by
  rcases (stands _ _ _ _ _ _ h) with ⟨_, ha⟩ | ⟨hp, _⟩ | ⟨_, b, ha⟩
  · rw [hb] at ha; cases ha
  · exact hp
  · rw [hb] at ha; cases ha

theorem finish_of_fin {a : FinOwn} (h : decideWith snd p s rs gs = .ok s') (hb : s.here = .fin a) :
    p.stands = .finish := by
  rcases (stands _ _ _ _ _ _ h) with ⟨_, ha⟩ | ⟨_, b, ha⟩ | ⟨hp, _⟩
  · rw [hb] at ha; cases ha
  · rw [hb] at ha; cases ha
  · exact hp

theorem between_of_link (h : decideWith snd p s rs gs = .ok s') (hp : p.stands = .link) :
    s.here = .between := by
  rcases (stands _ _ _ _ _ _ h) with ⟨_, ha⟩ | ⟨hq, _⟩ | ⟨hq, _⟩
  · exact ha
  · rw [hp] at hq; cases hq
  · rw [hp] at hq; cases hq

theorem head_of_stands (h : decideWith snd p s rs gs = .ok s') (hp : p.stands = .head) :
    ∃ a, s.here = .head a := by
  rcases (stands _ _ _ _ _ _ h) with ⟨hq, _⟩ | ⟨_, ha⟩ | ⟨hq, _⟩
  · rw [hp] at hq; cases hq
  · exact ha
  · rw [hp] at hq; cases hq

theorem fin_of_finish (h : decideWith snd p s rs gs = .ok s') (hp : p.stands = .finish) :
    ∃ a, s.here = .fin a := by
  rcases (stands _ _ _ _ _ _ h) with ⟨hq, _⟩ | ⟨hq, _⟩ | ⟨_, ha⟩
  · rw [hp] at hq; cases hq
  · rw [hp] at hq; cases hq
  · exact ha

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.link_of_between
#print axioms VerifiableInference.Desc.First.K2.fin_of_finish
