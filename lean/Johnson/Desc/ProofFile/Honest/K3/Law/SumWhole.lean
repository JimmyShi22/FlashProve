-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SumWhole.lean: the masked sumcheck's honest part against the
verifier's `whole` (hearing and row at once) and against `hear` with a late row: what a caller with
a ledger can use, in one structure each. No lookup is named here. Conditional: every theorem assumes
`HB`. Three structures, two theorems.

Terms. Honest/K3/GLOSSARY.md ("ledger", "part", "sumcheck, masked sumcheck", "world, worth").

What is shown.
  `HB`: five statements of the law of the masked sumcheck's honest part, as one hypothesis.
  `WholeHon`: what holds where `whole` has heard the part's rounds at a ready ledger.
  `whole_hon`: conditional on `HB`: `whole` returns there, and `WholeHon` holds.
  `OpenHon`, `open_hon`: the like for a call without end values, whose row is made late.

Hypotheses that remain.
  `HB`: its five statements are stated in Honest/SumLaw/Statement.lean and proved in
    Honest/SumLaw/Law.lean and Honest/SumLaw/LawEnds.lean, not here; Honest/K3/Law/HBPaid.lean
    brings these proofs in. `B` is its name.
  In both theorems besides: `hs`, `hd`: the call in the run passes `shapeOk`, and the challenges
    pass `drawsOk` at it; `hx`: the part, played alone, answers; `hL`: the ledger is ready
    (`LedgerReady`); `he`: the job's shape has the end values e (in `whole_hon`), or none (in
    `open_hon`).

Imported. Honest/SumLaw/Statement.lean.

Users. This file is imported by Honest/K3/Law/StageStep.lean.

Limits. The part is played alone. `HB` is asked at all that can be shown in front of the part (every
term of the frame's `Seen`): at every list of rounds and at every value of the columns opened.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Statement
import Johnson.Desc.Part.MaskedSumFree
import Johnson.Desc.Part.MaskedSumKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part.MaskedSum
open ProofFile.Honest.SumLaw

/-- Five statements of the law of the masked sumcheck's honest part, as one hypothesis. -/
structure HB : Prop where
  answers : SumSays
  heard : SumHeard
  claim : SumClaim
  left : SumLeft
  ends : SumEnds

variable {V W X : Type} {name endName : String}

/-- **What holds where `whole` has heard the part's rounds.** k: the call as it stands in the run. e
is a letter: no field ties it to the call; `whole_hon` has he among its hypotheses. -/
structure WholeHon (J : SumJob W X) (c : SumCoins name endName J) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (C : Aff) (F : Fork) (endTerm : List E → List E → E)
      (e : Ends)
    (h : Heard) (f : Aff) (G : Fork) : Prop where
  r : h.r = varsOf (J.callAt t.input (frontOf t seen)) ds
  first : h.first = F.next
  sEnd : h.sEnd = F.next + ownSlots (J.callAt t.input (frontOf t seen)).all
  next : G.next = F.next + ownSlots (J.callAt t.input (frontOf t seen)).all + e.n
  later : Later F G
  /-- the end values' slots are filled -/
  filled : ∀ j, j < e.n → Filled G (h.sEnd + j)
  /-- nothing is filled from the new count on that was not -/
  above : ∀ j, G.next ≤ j → Filled G j → Filled F j
  /-- under the end values' slots lie the job's end values. The coin is read by a default at j <
  e.n: under he : J.shape.ends = some e the list has e.n entries (`endRun_length`,
  Honest/SumLaw/FitsAt.lean); no field here ties e to the call -/
  ends : ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H →
    ∀ j, j < e.n → mask (h.sEnd + j) = Reading.gl.val ((endRun c).getD j zeroE) →
      (H.worldOf Reading.gl mask entry).slot (h.sEnd + j) =
        Reading.gl.val ((J.ends t.input (frontOf t seen)
          ((varsOf (J.callAt t.input (frontOf t seen)) ds).take J.shape.vs.length)).getD j zeroE)
  /-- a list sh with these e.n values; that it is what the rounds show is not said here; and what
  the row is worth. The coin's factor is the last challenge heard, not the default: `wholeHon_last`,
  under he and hd (Honest/K3/Law/SumWholeDrawn.lean [not in this library]); the coin is an entry of
  its list: `endRun_length`, under he (Honest/SumLaw/FitsAt.lean). That the factor is not 0 as a
  value is the format's never-0 rule at that challenge: not shown in this file -/
  row : ∃ sh : List E,
    (∀ j, j < e.n → Reading.gl.val (sh.getD j zeroE) =
      Reading.gl.val ((J.ends t.input (frontOf t seen)
          ((varsOf (J.callAt t.input (frontOf t seen)) ds).take J.shape.vs.length)).getD j zeroE) +
        Reading.gl.val (h.r.getLastD zeroE) * Reading.gl.val ((endRun c).getD j zeroE)) ∧
    ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE) (cf : GE), Later G H →
      (∀ i, i < ownSlots (J.callAt t.input (frontOf t seen)).all →
        mask (F.next + i) = hidingCoin c i) →
      SumsTo Reading.gl (J.callAt t.input (frontOf t seen)).all
        (jobPoly J t.input (frontOf t seen) (endRun c)) [] h.r
        (C.value Reading.gl (H.worldOf Reading.gl mask entry)) cf →
      f.value Reading.gl (H.worldOf Reading.gl mask entry) =
        Reading.gl.val h.eps * (Reading.gl.val (endTerm h.r sh) - cf)

/-- **Conditional on `HB`: at a ready ledger `whole` accepts the part's rounds**, with what a caller
can use. Conditional besides on `shapeOk` of the call, on `drawsOk` of the challenges, and on the
part answering alone. -/
theorem whole_hon (B : HB) (J : SumJob W X) (c : SumCoins name endName J) (t : State W X)
    (seen : Seen) (x : List Fmt.RoundView) (ds : List Fmt.Drawn) (C : Aff) (F : Fork)
    (endTerm : List E → List E → E) (e : Ends) (he : J.shape.ends = some e)
    (hs : shapeOk (J.callAt t.input (frontOf t seen)) = true)
    (hd : drawsOk (J.callAt t.input (frontOf t seen)) ds = true)
    (hx : alone (sumPart (V := V) name endName J) c t seen ds = some x)
    (hL : LedgerReady C (J.callAt t.input (frontOf t seen)) F) :
    ∃ h f G, whole C (J.callAt t.input (frontOf t seen)) endTerm F x = some (h, f, G) ∧
      WholeHon J c t seen ds C F endTerm e h f G := by
  have hS : Sized F := hL.1
  have hke : (J.callAt t.input (frontOf t seen)).ends = some e := he
  have hen : (J.callAt t.input (frontOf t seen)).endsN = e.n := by
    unfold Call.endsN
    rw [hke]
  obtain ⟨h, G1, hh⟩ := B.heard V W X name endName J c t seen ds x C F hs hd hx hL
  have hRd := ((hear_returns_iff hL x).1 (by rw [hh]; rfl)).2
  have hw0 : (whole C (J.callAt t.input (frontOf t seen)) endTerm F x).isSome :=
    (whole_returns_iff hL endTerm x).2 ⟨hs, hRd, by rw [hke]; rfl⟩
  obtain ⟨⟨h', f, G⟩, hw⟩ := Option.isSome_iff_exists.1 hw0
  obtain ⟨e', G1', sh, he', hh', hsh, hr⟩ := whole_parts hw
  have e1 : (h', G1') = (h, G1) := by
    rw [hh] at hh'
    exact (Option.some.inj hh').symm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  obtain rfl : e' = e := by
    rw [hke] at he'
    exact (Option.some.inj he').symm
  have hS1 : Sized G1' := (hear_keeps hh).sized hS
  obtain ⟨_, hrr, _⟩ := B.claim V W X name endName J c t seen ds x C F G1' h' hd hx hh
  obtain ⟨f1, f2, f3⟩ := heard_lenK hh
  obtain ⟨_, T, Rd, _, hR, _, hG⟩ := hear_spec hh
  have hlen : Rd.values.length = e'.n := by rw [readAll_values_len hR, hen]
  have hS2 : Sized ({ F with next := F.next + ownSlots (J.callAt t.input (frontOf t seen)).all +
      Rd.values.length } : Fork) := hS
  obtain ⟨_, _, a3, _⟩ := OnBytes.PscRun.hideRun_ok _ G1' _ _ _ hS2 hG
  have hn1 := hear_next hS hh
  have hn2 := row_next hS1 hr
  -- The call with its ends written out, for the theorems on the ledger.
  have hh2 : hear C ⟨J.shape.lead, withPoints J.shape.vs (J.points t.input (frontOf t seen)),
    some e'⟩ F x
      = some (h', G1') := by
    rw [← he]
    exact hh
  have hR2 : readAll ⟨J.shape.lead, withPoints J.shape.vs (J.points t.input (frontOf t seen)),
    some e'⟩ x
      = some Rd := by
    rw [← he]
    exact hR
  have hshown : sh = Rd.values := by
    have := ledger_shownEnds hS hh2 hR2 (Later.refl G1')
    rw [hsh] at this
    exact Option.some.inj this
  have hends : ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G1' H →
      ∀ j, j < e'.n → mask (h'.sEnd + j) = Reading.gl.val ((endRun c).getD j zeroE) →
      (H.worldOf Reading.gl mask entry).slot (h'.sEnd + j) =
        Reading.gl.val ((J.ends t.input (frontOf t seen)
          ((varsOf (J.callAt t.input (frontOf t seen)) ds).take J.shape.vs.length)).getD j zeroE) :=
    fun H mask entry hl j hj hm =>
      B.ends V W X name endName J c t seen ds C F G1' H x h' e' mask entry he hS hd hx hh hl j hj hm
  refine ⟨h', f, G, hw, hrr, f1, f2, by rw [hn2, hn1, hen], whole_keeps hw, ?_, ?_, ?_, sh, ?_, ?_⟩
  · intro j hj
    have := (a3 j (by rw [List.size_toArray, hlen]; exact hj)).2.2.1
    rw [f2]
    exact ((row_keeps hr).keep _ this).1
  · intro j hj hf
    rw [hn2, hn1] at hj
    have h1 : Filled G1' j := (row_fills hS1 hr j (Or.inr (by rw [f1, f3]; omega))).1 hf
    exact (hear_fills hS hh j (Or.inr hj)).1 h1
  · intro H mask entry hl
    exact hends H mask entry ((row_keeps hr).trans hl)
  · intro j hj
    -- One world: the ledger behind the hearing, at the mask entries that are the coins.
    have k1 := ledger_ends Reading.gl
      (fun n => Reading.gl.val ((endRun c).getD (n - h'.sEnd) zeroE)) (fun _ _ _ => 0) hS hh2 hR2
      (Later.refl G1') j hj
    have k2 := hends G1' (fun n => Reading.gl.val ((endRun c).getD (n - h'.sEnd) zeroE))
      (fun _ _ _ => 0) (Later.refl G1') j hj (by simp)
    rw [k2] at k1
    have k3 : F.next + ownSlots (Call.all ⟨J.shape.lead,
        withPoints J.shape.vs (J.points t.input (frontOf t seen)), some e'⟩) + j - h'.sEnd = j := by
      have : h'.sEnd = F.next + ownSlots (Call.all ⟨J.shape.lead,
          withPoints J.shape.vs (J.points t.input (frontOf t seen)), some e'⟩) := by
        rw [f2, ← he]
        rfl
      omega
    simp only [k3] at k1
    rw [hshown, k1]
    ring
  · intro H mask entry cf hl hm hsum
    have := B.left V W X name endName J c t seen ds x C F G1' G1' G H h' (endTerm h'.r sh) {} f mask
      entry cf hd hx hh hS1 hr hl hm hsum
    rw [this, Aff.value_empty, add_zero]

/-- **What holds where `hear` has heard the rounds of a part without end values.** -/
structure OpenHon (J : SumJob W X) (c : SumCoins name endName J) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (C : Aff) (F : Fork) (h : Heard)
      (G : Fork) : Prop where
  r : h.r = varsOf (J.callAt t.input (frontOf t seen)) ds
  first : h.first = F.next
  next : G.next = F.next + ownSlots (J.callAt t.input (frontOf t seen)).all
  later : Later F G
  /-- no slot is filled by the hearing -/
  same : ∀ j, Filled G j ↔ Filled F j
  /-- what a row is worth that is made late, with no kept term -/
  row : ∀ (F' G' H : Fork) (y : Aff) (S0 : E) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE)
    (cf : GE), Sized F' → row h S0 {} F' = some (y, G') → Later G' H →
    (∀ i, i < ownSlots (J.callAt t.input (frontOf t seen)).all → mask (F.next + i) = hidingCoin c i)
      →
    SumsTo Reading.gl (J.callAt t.input (frontOf t seen)).all
      (jobPoly J t.input (frontOf t seen) (endRun c)) [] h.r
      (C.value Reading.gl (H.worldOf Reading.gl mask entry)) cf →
    y.value Reading.gl (H.worldOf Reading.gl mask entry) =
      Reading.gl.val h.eps * (Reading.gl.val S0 - cf)

/-- **Conditional on `HB`: at a ready ledger `hear` accepts the rounds of a part without end
values**, with what a caller can use. Conditional besides as `whole_hon`. -/
theorem open_hon (B : HB) (J : SumJob W X) (c : SumCoins name endName J) (t : State W X)
    (seen : Seen) (x : List Fmt.RoundView) (ds : List Fmt.Drawn) (C : Aff) (F : Fork)
    (he : J.shape.ends = none)
    (hs : shapeOk (J.callAt t.input (frontOf t seen)) = true)
    (hd : drawsOk (J.callAt t.input (frontOf t seen)) ds = true)
    (hx : alone (sumPart (V := V) name endName J) c t seen ds = some x)
    (hL : LedgerReady C (J.callAt t.input (frontOf t seen)) F) :
    ∃ h G, hear C (J.callAt t.input (frontOf t seen)) F x = some (h, G) ∧
      OpenHon J c t seen ds C F h G := by
  have hS : Sized F := hL.1
  have hke : (J.callAt t.input (frontOf t seen)).ends = none := he
  have hen : (J.callAt t.input (frontOf t seen)).endsN = 0 := by
    unfold Call.endsN
    rw [hke]
  obtain ⟨h, G, hh⟩ := B.heard V W X name endName J c t seen ds x C F hs hd hx hL
  refine ⟨h, G, hh, (B.claim V W X name endName J c t seen ds x C F G h hd hx hh).2.1,
    (heard_lenK hh).1, by rw [hear_next hS hh, hen, Nat.add_zero], hear_keeps hh,
    fun j => hear_fills hS hh j (by rw [hen]; omega), ?_⟩
  intro F' G' H y S0 mask entry cf hS' hr hl hm hsum
  rw [B.left V W X name endName J c t seen ds x C F G F' G' H h S0 {} y mask entry cf hd hx hh hS'
    hr hl hm hsum, Aff.value_empty, add_zero]

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.whole_hon
#print axioms ProofFile.Honest.K3.Law.open_hon
