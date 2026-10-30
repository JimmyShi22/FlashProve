-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SentIsAtReads.lean: THE ROW
SI1 OF K01_law: THE MAKER's LEMMA OF THE NAMED PUBLIC ITEM (some m, "frame.sentIs1") AT A SEGMENT's
SECOND SENDING: where the test "frame.sentIs" (sentIsB, Johnson/Desc/First/FillSent.lean) accepts
the chain's state in front of an accepting run of the sub-protocol, it accepts the state behind AT
THE LIST "own" WITH THE NEW MESSAGES' NUMBERS LAID BEHIND IT. Definitions, and statements with their
proofs.
OBJECT. commitAtS (Johnson/Desc/K1/AtS.lean) at any moment, so laterAt
(Johnson/Desc/K1/Places.lean); and the reads' place's joined block `k1Reads`.
USER. The row K01_law: the item is made at piece 4 + o (here), kept at 5 + o, asked and
dropped at 6 + o.
THE QUESTION, ANSWERED: DOES AN ACCEPTING commitAtS LEAVE frame.next? YES: the open link's
frame behind IS the frame in front with its moment raised by 1 and the new numbers behind "own"
(commitAtS_frame, Johnson/Desc/K1/Law/FrameAtLater.lean: an equation on the whole frame): so next,
link, groups and keptBefore are as they were.
  ownPlus d m ids     the plan's side with ids laid behind segment m's list "own".
  sentIs_same         the test reads the open link's context alone.
  sentIs_commit       **the sending.** sentIs_laterAt: at the plan's numbers.
  sentIs_joined, sentIs_k1Reads: with a quiet block joined behind; **the reads' place's block.**
  sentIs_k1Reads_plan: **at the plan's own count**, from the promise's clause bookAt.
BENEATH. Johnson/Desc/First/FillSent.lean, which this file imports.
What is not claimed. That the test accepts any state. That the item is open at any border. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.First.FillSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model _root_.Desc.Plain
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB five_of_sentIs)
open OnBytes.Model.Stages (LinkH)

variable {Cl : Type}

/-- The plan's side with ids laid behind segment m's list "own". -/
def ownPlus (d : SentData) (m : Nat) (ids : Array Nat) : SentData :=
  { d with own := fun j => if j = m then d.own m ++ ids else d.own j }

/-- The test reads the open link's context alone. -/
theorem sentIs_same (d : SentData) (m : Nat) {s s' : S} (h : s'.link? = s.link?) :
    sentIsB d m s' = sentIsB d m s := by
  unfold sentIsB
  rw [h]

/-- **The sending.** -/
theorem sentIs_commit (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s')
    (d : SentData) (m : Nat) (h0 : sentIsB d m s = true) :
    sentIsB (ownPlus d m (idsOf P s.st.oracles.size)) m s' = true := by
  obtain ⟨L, L', hL, hL', e, _⟩ := commitAtS_frame P link moment arrays s s' r₁ r₂ gs h
  obtain ⟨a1, a2, a3, a4, a5⟩ := five_of_sentIs hL h0
  unfold sentIsB
  rw [hL']
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq]
  rw [e]
  refine ⟨⟨⟨⟨a1, a2⟩, a3⟩, ?_⟩, a5⟩
  show L.check.frame.own ++ idsOf P s.st.oracles.size =
    if m = m then d.own m ++ idsOf P s.st.oracles.size else d.own m
  rw [if_pos rfl, a4]

/-- At the plan's numbers. -/
theorem sentIs_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (laterAt q gp link piece moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s')
    (d : SentData) (m : Nat) (h0 : sentIsB d m s = true) :
    sentIsB (ownPlus d m (idsOf (parLater q gp link piece moment) s.st.oracles.size)) m s' = true :=
  sentIs_commit _ _ _ _ s s' r₁ r₂ gs h d m h0

/-- The sending with a quiet block joined behind it. -/
theorem sentIs_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.andThen nm (commitAtS P link moment arrays) q).decide s [r₁, r₂] gs = .ok s')
    (d : SentData) (m : Nat) (h0 : sentIsB d m s = true) :
    sentIsB (ownPlus d m (idsOf P s.st.oracles.size)) m s' = true := by
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  obtain ⟨_, _, _, e4, _⟩ := hq _ _ _ _ h3
  rw [sentIs_same _ m e4]
  exact sentIs_commit P link moment arrays s s₁ r₁ r₂ gs₁ h1 d m h0

/-- **The reads' place's joined block.** -/
theorem sentIs_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (IM.k1Reads Z G l X pr reads).decide s [r₁, r₂] gs = .ok s') (d : SentData) (m : Nat)
    (h0 : sentIsB d m s = true) :
    sentIsB (ownPlus d m (idsOf (parLater G.first (gpOf Z) l pr 1) s.st.oracles.size)) m s' =
      true :=
  sentIs_joined _ _ _ _ _ _ (quietP_orLoud _ _ _ G l X _) s s' r₁ r₂ gs h d m h0

/-- **At the plan's own count**: the new numbers are N.msgsAt p + 0, + 1, ... -/
theorem sentIs_k1Reads_plan (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (IM.k1Reads Z G l X pr reads).decide s [r₁, r₂] gs = .ok s') (d : SentData) (m : Nat)
    (N : Numbers) (p : Option Place) (hbk : First.bookAt N p s = true)
    (h0 : sentIsB d m s = true) :
    sentIsB (ownPlus d m (idsOf (parLater G.first (gpOf Z) l pr 1) (N.msgsAt p))) m s' = true := by
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  rw [← hbk.2]
  exact sentIs_k1Reads Z G l X pr reads s s' r₁ r₂ gs h d m h0

end VerifiableInference.Desc.K1
