-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameReadKeptAt.lean: THE THREE SENTENCES ON THE COMPOSED MEANING's PARAMETERS
(`ReadKept`, FrameFieldsBack.lean: the reader of the request, the decoder of the committed table
and the reader of the OOD samples read of the verifier's state nothing but what "cleared" keeps),
AND THE TWO PREMISES OF FramePromiseRides.lean (`DecRides`, `SeedRides`), AT THE TERMS THAT ARE
MEANT FOR THE THREE PARAMETERS. Statements and proofs.

The terms, by the composed meaning's own table of the parameters (as when this was typed): 𝔇.smp :=
`smpNamed 𝔇.cs seats` (Johnson/Desc/Sound/SmpNamed.lean: the first sample row that the statement
holds of the message, as a linear form, with its target); 𝔇.decT: a decoder that does not read the
state (`Stored.NoRec`, Johnson/Desc/First/Look/K3StoredThree.lean); 𝔇.H.req: a function of the
public part alone.

What is said.
  `formsAt_kept`, `ansAt_kept`: the form and the target that the statement holds of a message are
    the same at two states that `Kept` relates: they read its sample rows, not its ledger.
  `smpNamed_kept`: **so `smpNamed cs seats` answers alike at the two states**, at every member.
  `MeantAt 𝔇 seats r`: 𝔇's three parameters are the meant terms: three equations.
  `readKept_meant`: **`MeantAt 𝔇 seats r → ReadKept 𝔇 base`, at every base.**
  `decRides_noRec`: under `NoRec` alone `DecRides 𝔇 rel` holds at EVERY relation rel.
  `seedRides_meant`: `SeedRides 𝔇 rel base In` at every rel that gives `Kept`.
  `fieldsBack_clear_meant`, `three_clear_meant`: so `FieldsBack` and the three fields "decodes",
    "shown", "noColl" at the "cleared" of a row of `framesOf`, with no premise on these three
    parameters left but `MeantAt`.

Limits. `MeantAt` IS A PREMISE: that the closed value of 𝔇 (P5J.At.𝔇At) has these three equations is
its own file's to say: not shown here. The carried word's sentence (𝔇.cr1) and the output head's
parts' (𝔇.headPart) stay premises (`CarryBack`; `HeadBack`, FrameFieldsBackHead.lean). seats and r
are letters. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameFieldsBackHead
import Johnson.Desc.Sound.SmpNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.K1 (formsAt ansAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item Meaning Numbers)
open VerifiableInference.Desc.First.Look.Stored (NoRec)

theorem Kept.samples {s t : S} (h : Kept s t) (o : Nat) :
    (t.st.oracles[o]?).map (fun a : Oracle => a.sampleRows) =
      (s.st.oracles[o]?).map (fun a : Oracle => a.sampleRows) := by
  have h1 := congrArg (Option.map fun a : Oracle => a.sampleRows) (h.msgs o)
  rw [Option.map_map, Option.map_map] at h1
  exact h1

/-- The form that the statement holds of message number o. -/
theorem formsAt_kept {s t : S} (h : Kept s t) (cs : Codes) (sh : OracleShape) (o : Nat) :
    formsAt cs sh t.st o = formsAt cs sh s.st o := by
  have e := h.samples o
  unfold formsAt
  cases hs : s.st.oracles[o]? with
  | none =>
    rw [hs, Option.map_none, Option.map_eq_none_iff] at e
    rw [e]
  | some a =>
    rw [hs, Option.map_some] at e
    obtain ⟨b, hb, eb⟩ := Option.map_eq_some_iff.1 e
    rw [hb]
    simp only [Option.bind_some, eb]

/-- Its target. -/
theorem ansAt_kept {s t : S} (h : Kept s t) (o : Nat) : ansAt t.st o = ansAt s.st o := by
  have e := h.samples o
  unfold ansAt
  cases hs : s.st.oracles[o]? with
  | none =>
    rw [hs, Option.map_none, Option.map_eq_none_iff] at e
    rw [e]
  | some a =>
    rw [hs, Option.map_some] at e
    obtain ⟨b, hb, eb⟩ := Option.map_eq_some_iff.1 e
    rw [hb]
    simp only [Option.bind_some, eb]

/-- **The named reader of the OOD samples answers alike at two states that `Kept` relates.** -/
theorem smpNamed_kept {P : Type} (cs : Codes) (seats : List (ℕ × ℕ)) (p : P) {s t : S}
    (h : Kept s t) (x : Sending) (i : Fin x.l.length) :
    smpNamed cs seats (p, s) x i = smpNamed cs seats (p, t) x i :=
  (smpNamed_stays cs seats (p, s) (p, t) x i (formsAt_kept h cs _ _) (ansAt_kept h _)).symm

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **𝔇's three parameters are the meant terms.** -/
structure MeantAt (seats : List (ℕ × ℕ)) (r : P → P5J.TReq) : Prop where
  smp : 𝔇.smp = smpNamed 𝔇.cs seats
  dec : NoRec 𝔇.decT
  req : ∀ a, 𝔇.H.req a = r a.1

variable {𝔇}

/-- **THE THREE SENTENCES AT THE MEANT TERMS.** -/
theorem readKept_meant {seats : List (ℕ × ℕ)} {r : P → P5J.TReq} (h : MeantAt 𝔇 seats r)
    (base : Nat) : ReadKept 𝔇 base where
  req p s t _ := by rw [h.req, h.req]
  dec p s t c _ := h.dec c p s t
  smp p s t hk x _ _ := by
    rw [h.smp]
    exact smpNamed_kept 𝔇.cs seats p hk x.1 x.2

/-- Under `NoRec` the premise on the decoder holds at every relation. -/
theorem decRides_noRec (h : NoRec 𝔇.decT) (rel : S → S → Prop) : DecRides 𝔇 rel :=
  fun p s t c _ hc => by
    rw [← h c p s t]
    exact hc

theorem seedRides_meant {seats : List (ℕ × ℕ)} {r : P → P5J.TReq} (h : MeantAt 𝔇 seats r)
    {rel : S → S → Prop} (hrel : ∀ s t, rel s t → Kept s t) (base : Nat)
    (In : P × S → Strs → Prop) : SeedRides 𝔇 rel base In :=
  seedRides_of_kept 𝔇 hrel base In (readKept_meant h base)

/-- `FieldsBack` at the "cleared" of a row of the frame's own list, at the meant terms. -/
theorem fieldsBack_clear_meant {seats : List (ℕ × ℕ)} {r : P → P5J.TReq}
    (h : MeantAt 𝔇 seats r) {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List Seat.LinkFrame} {f : Seat.LinkFrame} {l : Nat}
    (hfs : Seat.framesOf built first W = .ok fs) (hf : fs[l]? = some f) (base : Nat)
    (In : P × S → Strs → Prop) (hc : CarryBack 𝔇 (Yes f.clear) base In)
    (hH : HeadBack 𝔇 (StepRel (Yes f.clear) base In)) :
    FieldsBack (mgAll 𝔇 Mg) ownDigits (fun j => j < base) (StepRel (Yes f.clear) base In) :=
  fieldsBack_clear_row_head 𝔇 Mg hfs hf base In (readKept_meant h base) hc hH

/-- The three fields "decodes", "shown", "noColl" there, at the meant terms. -/
theorem three_clear_meant {seats : List (ℕ × ℕ)} {r : P → P5J.TReq} (h : MeantAt 𝔇 seats r)
    {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List Seat.LinkFrame} {f : Seat.LinkFrame} {l : Nat}
    (hfs : Seat.framesOf built first W = .ok fs) (hf : fs[l]? = some f) (N : Numbers)
    (O : List Item) (base : Nat) (In : P × S → Strs → Prop) (hl : LowAt N O base)
    (hF : FrontGives 𝔇 Mg N O In) :
    (∀ p s t y y', Yes f.clear s t → Stays base y y' → (mgAll 𝔇 Mg).decodes (p, s) y →
        (mgAll 𝔇 Mg).decodes (p, t) y') ∧
      (∀ p s t y y' x, Yes f.clear s t → Stays base y y' → s.failed = none → In (p, s) y →
        x ∈ VerifiableInference.Desc.First.sampledIn N O → (mgAll 𝔇 Mg).shown x.1 x.2 y') ∧
      ∀ p s t y y' x, Yes f.clear s t → Stays base y y' → s.failed = none → In (p, s) y →
        x ∈ VerifiableInference.Desc.First.sampledIn N O →
        (mgAll 𝔇 Mg).noColl x.1 x.2 (p, t) y' :=
  three_clear_row 𝔇 Mg hfs hf N O base In (readKept_meant h base) hl hF

end

#print axioms smpNamed_kept
#print axioms readKept_meant
#print axioms decRides_noRec
#print axioms seedRides_meant
#print axioms fieldsBack_clear_meant
#print axioms three_clear_meant

end Johnson.Desc.First.Walk.Tied
