-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/MakerJoin.lean: THE TWO HALVES OF THE MAKING OF THE PUBLIC ITEMS "frame.sentIs"
AND "ledger.treesAre" AT A LINK BEHIND LINK 0, JOINED: a yes of the code switch at the link, and
then a yes of the quiet step that opens the link: both tests say yes at the verifier's state behind
(Johnson/Desc/First/FillSent.lean). Statements and proofs: calls of
Johnson/Top/H0/Tw/K2C/SentIsMade.lean (the switch's half), Johnson/Top/H0/Tw/K2C/LinkStays.lean,
Johnson/Road/K4/Rec/MakerProofs.lean (the opening's half) and Johnson/Top/H0/Walk/FrameLaw.lean.
GLUE.

  `sentIsB_at`: the test at segment m reads the plan's data at m alone.
  **`sentIs_made_lay`**, **`sentIs_made_att`**: p.stands = .link; a yes of the switch from s to s₁;
    a yes of `openLay P` (`openAtt P`) from s₁ to s'; hg: the frame's groups in front are the
    shape's (`reqGroups`); the plan's data d has at P.l the born, own and kept of `sentDataOf` at
    the frame's shape and at the statement's number of messages in front of the switch: `sentIsB d
    P.l s'` says yes. THE FRAME's LINK NUMBER IS NO PREMISE: the opening's own test gives it, and
    the switch leaves it.
  `treesAre_made_lay`, `treesAre_made_att`: the opening's half alone, named once more for the
    caller.

OBJECT: the switch's decision (`decideWith sendByL8 p`) and the two opening steps. USER: none yet;
meant: the law of the block at a link's first place. LETTERS: p, P, s, s₁, s', d.

Limits. hg IS A PREMISE: no test of the block holds the frame's groups against the shape. That the
statement's number of messages in front is the plan's is the promise's clause on the book: not drawn
here. THAT THE SEATED BLOCK's YES IS THESE TWO YESES, ONE AFTER THE OTHER, IS NOT SAID HERE. LINK 0
(a sending, not a switch) AND THE HEAD's LINK: not here. K04_law, the law of K4's block itself, IS
NOT PROVED BY THIS. Nothing on soundness.
-/
import Johnson.Top.H0.Tw.K2C.SentIsMade
import Johnson.Road.K4.Rec.MakerProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk (LayPar AttPar openLay openAtt startFork)
open Johnson.Desc.First.Walk.Law (openLay_ok openAtt_ok)
open _root_.Tw.K2 (sendByL8)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith yes_link_stays yes_link_checkSent)
open VerifiableInference.Desc.First.FillSent (SentData TreeLook treeLook sentDataOf sentIsB
  treesAreB)

/-- The test at segment m reads the plan's data at m alone. -/
theorem sentIsB_at {d d' : SentData} {m : Nat} (hb : d.born m = d'.born m)
    (ho : d.own m = d'.own m) (hk : d.kept m = d'.kept m) (s : S) :
    sentIsB d m s = sentIsB d' m s := by
  unfold sentIsB
  rw [hb, ho, hk]

section
variable {p : P2} {s s₁ s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
  {d : SentData}

/-- **"frame.sentIs" is made at a layers' link behind link 0**, under hg. -/
theorem sentIs_made_lay {P : LayPar} (hp : p.stands = .link)
    (h1 : decideWith sendByL8 p s rs gs = .ok s₁) (h2 : openLay P s₁ = .ok s')
    (hg : s.check.frame.groups = reqGroups s.check.frame.shape)
    (hb : d.born P.l =
      (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size) d.trees).born P.l)
    (ho : d.own P.l =
      (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size) d.trees).own P.l)
    (hk : d.kept P.l =
      (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size) d.trees).kept P.l) :
    sentIsB d P.l s' = true := by
  have hl : s.check.frame.link = P.l :=
    (yes_link_stays hp h1).2.1.symm.trans (openLay_ok h2).2.2.2.1
  rw [sentIsB_at hb ho hk s']
  exact openLaySent P s₁ s' _ h2 (yes_link_checkSent hp h1 hl hg d.trees)

/-- **"frame.sentIs" is made at an attention link**, under hg. -/
theorem sentIs_made_att {P : AttPar} (hp : p.stands = .link)
    (h1 : decideWith sendByL8 p s rs gs = .ok s₁) (h2 : openAtt P s₁ = .ok s')
    (hg : s.check.frame.groups = reqGroups s.check.frame.shape)
    (hb : d.born P.l =
      (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size) d.trees).born P.l)
    (ho : d.own P.l =
      (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size) d.trees).own P.l)
    (hk : d.kept P.l =
      (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size) d.trees).kept P.l) :
    sentIsB d P.l s' = true := by
  have hl : s.check.frame.link = P.l :=
    (yes_link_stays hp h1).2.1.symm.trans (openAtt_ok h2).2.2.2.1
  rw [sentIsB_at hb ho hk s']
  exact openAttSent P s₁ s' _ h2 (yes_link_checkSent hp h1 hl hg d.trees)

/-- "ledger.treesAre" is made by the opening of a layers' link. -/
theorem treesAre_made_lay {P : LayPar} {m : Nat} (h2 : openLay P s₁ = .ok s')
    (ht : d.trees m = (startFork P.X P.ns).trees.toList.map treeLook) :
    treesAreB d m s' = true := openLayTrees P s₁ s' d m h2 ht

/-- "ledger.treesAre" is made by the opening of an attention link. -/
theorem treesAre_made_att {P : AttPar} {m : Nat} (h2 : openAtt P s₁ = .ok s')
    (ht : d.trees m = (startFork P.X P.ns).trees.toList.map treeLook) :
    treesAreB d m s' = true := openAttTrees P s₁ s' d m h2 ht

end

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.sentIs_made_lay
#print axioms OnBytes.Road.K4.Rec.sentIs_made_att
#print axioms OnBytes.Road.K4.Rec.treesAre_made_lay
#print axioms OnBytes.Road.K4.Rec.treesAre_made_att
