-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/CondRow.lean: the kind K1 (sending an encoding with an out-of-domain sample) at
a place's own numbers: one plain record of numbers, one test on it with code, and: where the test
says yes, every place with these numbers meets the kind's condition, and the library's closed caller
at these numbers meets the proved block's condition.

Johnson/Desc/K1/Law/Lit.lean has `cond_of_lit`: at a place P that is an element of the library's
written-out list the kind's one Boolean `condPort` holds. There the tests on the plan
(`planOkOwn P`) are a premise, and so is that P's sampled messages are the element's. Here a record
holds ALL messages of the sending, those without a sample too, so that the tests on the plan can be
evaluated at the record, and what is left as a premise on a place is two equations: its codes and
its messages are the record's.
  SendRow: cs: the codes · sent: the oracle messages of the prover's message, in the order of
      sending · l: the sampled ones among them, in order, each with a radius
  SendRow.par: a place with these numbers; where it stands, the number of its first tree, the
      setting's samples and the work of its round are idle
  SendRow.ok: the test: the kind's tests on the plan (every message has an admitted shape; the trees
      can be laid; some message is sampled; every sampled message's pads fit) · every code's message
      length is a power of two · the library's test on numbers `allMeet` at l · the sampled messages
      of sent, each with the radius of its rank in l, are l
  SendRow.At r P: the place P has the record's codes and messages
  planOkOwn_congr, sampledList_congr, radFrom_congr, condPort_same: the kind's tests, its list of
      sampled messages and its one Boolean read of a place its codes and its messages alone (not how
      the messages are cut into named parts)
  SendRow.Holds: at every place with the record's numbers: `condPort` at the record's radii, and the
      place's list is l; and for all letters of the library's closed caller: `SendOK`
  K01Condition, k01Condition: one closed proposition: Holds at every record at which the test says
      yes; its proof
  K01At, k01At: at a list of records: the test says yes at each, and Holds
The form follows Johnson/Top/H0/K2Caller/Row.lean (K02Condition, K02At).

What is not claimed. That a record is a plan's. That a block of a description stands at a place with
a record's numbers. Which radius a later test of proximity has: the radii are the record's. One
answer a message. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Lit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Slice Johnson.Pack Cb Iop IOR VerifiableInference.OnPublicFiles

/-! ## What the kind's tests read of a place -/

theorem shapesOf_congr (P P' : Par) (hs : P.sent = P'.sent) : shapesOf P = shapesOf P' := by
  unfold shapesOf
  rw [hs]

/-- The tests on the plan read the codes and the messages alone. -/
theorem planOkOwn_congr (P P' : Par) (hc : P.codes = P'.codes) (hs : P.sent = P'.sent) :
    planOkOwn P = planOkOwn P' := by
  simp only [planOkOwn, planOk, Par.tuple, hc, hs]

theorem sampled_aux (c c' : Codes) (s s' : List OracleShape) (hc : c = c') (hs : s = s')
    (rad : Nat → Nat) :
    (((List.finRange s.length).filter fun k => decide ((Msg.of c s[k.val]).answers ≠ 0)).map
        fun k => (s[k.val], rad k.val)) =
      (((List.finRange s'.length).filter fun k => decide ((Msg.of c' s'[k.val]).answers ≠ 0)).map
        fun k => (s'[k.val], rad k.val)) := by
  subst hc hs
  rfl

/-- So does the list of the sampled messages. -/
theorem sampledList_congr (P P' : Par) (rad : Nat → Nat) (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) : sampledList P rad = sampledList P' rad :=
  sampled_aux P.codes P'.codes (shapesOf P) (shapesOf P') hc (shapesOf_congr P P' hs) rad

/-- So do the radii that are read off a list. -/
theorem radFrom_congr (P P' : Par) (l : List (OracleShape × Nat)) (hs : P.sent = P'.sent) :
    radFrom P l = radFrom P' l := by
  funext n
  unfold radFrom
  rw [shapesOf_congr P P' hs]

/-- **So does the kind's one Boolean.** -/
theorem condPort_same (P P' : Par) (rad : Nat → Nat) (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) (h : condPort P rad = true) : condPort P' rad = true := by
  obtain ⟨h1, h2, h3⟩ := (cond_iff P rad).1 h
  refine (cond_iff P' rad).2 ⟨?_, ?_, ?_⟩
  · rw [← planOkOwn_congr P P' hc hs]
    exact h1
  · rw [← hc]
    exact h2
  · rw [← hc, ← sampledList_congr P P' rad hc hs]
    exact h3

/-! ## A record -/

/-- **The numbers of a place of the kind K1.** -/
structure SendRow where
  cs : Codes
  sent : List OracleNotice
  l : List (OracleShape × Nat)

namespace SendRow
variable (r : SendRow)

/-- A place with these numbers. -/
def par : Par :=
  { place := ⟨0, none, 0, .K1⟩, codes := r.cs, gp := ⟨0, 0⟩, work := 0
    parts := [("", r.sent.toArray)] }

theorem par_sent : r.par.sent = r.sent.toArray := by
  simp [par, Par.sent]

/-- **The test.** -/
def ok : Bool :=
  planOkOwn r.par && r.cs.lengthsOk && allMeet r.cs r.l &&
    decide (sampledList r.par (radFrom r.par r.l) = r.l)

/-- The place P has the record's codes and messages. -/
def At (P : Par) : Prop := P.codes = r.cs ∧ P.sent = r.sent.toArray

theorem at_par : r.At r.par := ⟨rfl, r.par_sent⟩

/-- **What the test's yes promises.** -/
def Holds : Prop :=
  (∀ P : Par, r.At P →
    condPort P (radFrom P r.l) = true ∧ sampledList P (radFrom P r.l) = r.l) ∧
  ∀ {Kc X W W' : Type} {E₀ : ExtSpec} (A : Rels Kc X E₀ W) (back : (sigOf r.cs r.l).Msg → W' → W),
    SendOK [sendCaller r.cs r.l A back]

end SendRow

/-- **The kind's condition, as one closed proposition.** -/
def K01Condition : Prop := ∀ r : SendRow, r.ok = true → r.Holds

theorem k01Condition : K01Condition := by
  intro r h
  unfold SendRow.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun P hP => ?_, fun A back => sendCaller_ok r.cs r.l h3 A back⟩
  have hs : r.par.sent = P.sent := r.par_sent.trans hP.2.symm
  have hc : r.par.codes = P.codes := hP.1.symm
  have hr : radFrom r.par r.l = radFrom P r.l := radFrom_congr _ _ _ hs
  have h0 : condPort r.par (radFrom r.par r.l) = true :=
    (cond_iff _ _).2 ⟨h1, h2, by rw [h4]; exact h3⟩
  refine ⟨?_, ?_⟩
  · rw [← hr]
    exact condPort_same _ _ _ hc hs h0
  · rw [← hr, ← sampledList_congr _ _ _ hc hs]
    exact h4

/-- **At a list of records**: the test says yes at each, and what it promises holds. -/
def K01At (T : List SendRow) : Prop := ∀ r ∈ T, r.ok = true ∧ r.Holds

theorem k01At (T : List SendRow) (hT : (T.all fun r => r.ok) = true) : K01At T := fun r hr =>
  have h := List.all_eq_true.1 hT r hr
  ⟨h, k01Condition r h⟩

end VerifiableInference.Desc.K1
