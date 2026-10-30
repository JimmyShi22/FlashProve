-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/MakerAtBorder.lean: THE MAKING OF THE PUBLIC TESTS "frame.sentIs" AND
"ledger.treesAre" (Johnson/Desc/First/FillSent.lean) AT A SEGMENT BEHIND SEGMENT 0, AT THE DATA AS A
TERM OFF THE PUBLIC PARAMETERS (`sentDataAt`, Johnson/Desc/First/SentTerms.lean): the three
equations on the data that Rec/MakerJoin.lean takes as premises are drawn out of two facts on the
verifier's state in front of the code switch. Statements and proofs: unfolding, then calls.

  `data_at_border`: where the frame's shape in front is the public parameters' shape, and the
    statement holds as many oracle messages as the numbers N say at the place of the segment's first
    sending: born, own and kept of `sentDataAt` at that segment are those of `sentDataOf` at the
    frame's own shape and the statement's own count.
  **`sentIs_made_lay_at`**, **`sentIs_made_att_at`**: so: the code switch accepts, then the quiet
  step that opens the segment accepts ⟹ `sentIsB (sentDataAt …) P.l` of the state behind.
  **`treesAre_made_lay_at`**, **`treesAre_made_att_at`**: the opening alone, where the segment's
  planned ledger in the list built is the opening's own.

WHO PAYS THE TWO FACTS. The count: the promise's fixed test on the book (`bookAt`: its third
clause), at the border in front of that place. The shape: "in order"'s equation on the frame's
shape, or the like fact at a reached state. hg (the frame's groups are the shape's): a fact at a
reached state.

Limits. THAT THE SEATED SUB-PROTOCOL's ACCEPT AT THAT PLACE IS THESE TWO ACCEPTS, ONE AFTER THE
OTHER, IS NOT SAID HERE. Segment 0 (a sending, not a switch) and the output head's segment: not
here. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.

-/
import Johnson.Road.K4.Rec.MakerJoin
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk (LayPar AttPar openLay openAtt startFork)
open _root_.Tw.K2 (sendByL8)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Numbers shift)
open VerifiableInference.Desc.First.K2 (P2 decideWith)
open VerifiableInference.Desc.First.FillSent (SentData treeLook sentDataOf sentDataAt baseAt treesAt
  looksOf looks_startFork sentIsB treesAreB)

variable {shape : Params.ReqShape} {N : Numbers} {links : List ModelPart} {ps : List Place}
  {built : Array Stages.LinkH} {m : ℕ} {pl : Place} {s s₁ s' : S}

/-- The data as a term, at a segment, are the data at the state's own shape and count. -/
theorem data_at_border
    (hpl : (ps.find? fun p => p.link == some m && p.piece == 1 + ((links[m]?).map shift).getD 0) =
      some pl)
    (hn : s.st.oracles.size = N.msgsAt (some pl)) (hsh : s.check.frame.shape = shape) :
    (sentDataAt shape N links ps built).born m =
        (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size)
          (sentDataAt shape N links ps built).trees).born m ∧
      (sentDataAt shape N links ps built).own m =
        (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size)
          (sentDataAt shape N links ps built).trees).own m ∧
      (sentDataAt shape N links ps built).kept m =
        (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size)
          (sentDataAt shape N links ps built).trees).kept m := by
  have hb : baseAt N links ps m = s.st.oracles.size := by
    unfold baseAt
    rw [hpl, hn]
  subst hsh
  refine ⟨rfl, ?_, ?_⟩
  · show (sentDataOf _ (baseAt N links ps) _).own m = _
    unfold sentDataOf
    simp only [hb]
  · show (sentDataOf _ (baseAt N links ps) _).kept m = _
    unfold sentDataOf
    simp only [hb]

section
variable {p : P2} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}

/-- **"frame.sentIs" is made at a feed-forward segment behind segment 0, at the term.** -/
theorem sentIs_made_lay_at {P : LayPar} (hp : p.stands = .link)
    (h1 : decideWith sendByL8 p s rs gs = .ok s₁) (h2 : openLay P s₁ = .ok s')
    (hg : s.check.frame.groups = reqGroups s.check.frame.shape)
    (hpl : (ps.find? fun q => q.link == some P.l &&
      q.piece == 1 + ((links[P.l]?).map shift).getD 0) = some pl)
    (hn : s.st.oracles.size = N.msgsAt (some pl)) (hsh : s.check.frame.shape = shape) :
    sentIsB (sentDataAt shape N links ps built) P.l s' = true := by
  obtain ⟨hb, ho, hk⟩ := data_at_border (built := built) hpl hn hsh
  exact sentIs_made_lay hp h1 h2 hg hb ho hk

/-- The like at an attention segment. -/
theorem sentIs_made_att_at {P : AttPar} (hp : p.stands = .link)
    (h1 : decideWith sendByL8 p s rs gs = .ok s₁) (h2 : openAtt P s₁ = .ok s')
    (hg : s.check.frame.groups = reqGroups s.check.frame.shape)
    (hpl : (ps.find? fun q => q.link == some P.l &&
      q.piece == 1 + ((links[P.l]?).map shift).getD 0) = some pl)
    (hn : s.st.oracles.size = N.msgsAt (some pl)) (hsh : s.check.frame.shape = shape) :
    sentIsB (sentDataAt shape N links ps built) P.l s' = true := by
  obtain ⟨hb, ho, hk⟩ := data_at_border (built := built) hpl hn hsh
  exact sentIs_made_att hp h1 h2 hg hb ho hk

end

/-- **"ledger.treesAre" is made by the opening of a feed-forward segment, at the term.** -/
theorem treesAre_made_lay_at {P : LayPar} {X : Stages.LinkH} (h2 : openLay P s₁ = .ok s')
    (hX : built[m]? = some X) (hF : X.Fp = P.X.Fp) :
    treesAreB (sentDataAt shape N links ps built) m s' = true := by
  refine treesAre_made_lay h2 ?_
  rw [looks_startFork]
  show treesAt built m = _
  unfold treesAt
  rw [hX, Option.map_some, Option.getD_some, hF]

/-- The like at an attention segment. -/
theorem treesAre_made_att_at {P : AttPar} {X : Stages.LinkH} (h2 : openAtt P s₁ = .ok s')
    (hX : built[m]? = some X) (hF : X.Fp = P.X.Fp) :
    treesAreB (sentDataAt shape N links ps built) m s' = true := by
  refine treesAre_made_att h2 ?_
  rw [looks_startFork]
  show treesAt built m = _
  unfold treesAt
  rw [hX, Option.map_some, Option.getD_some, hF]

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.data_at_border
#print axioms OnBytes.Road.K4.Rec.sentIs_made_lay_at
#print axioms OnBytes.Road.K4.Rec.sentIs_made_att_at
#print axioms OnBytes.Road.K4.Rec.treesAre_made_lay_at
#print axioms OnBytes.Road.K4.Rec.treesAre_made_att_at
