-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No state of the verifier is shown at which the kind's decide accepts.
Johnson/Desc/First/Look/K3CallsMade.lean: the lookup on a link's CALLS: WHAT AN ACCEPT OF THE KIND's
decide MAKES, AS THE OTHER KINDS' OWN PUBLIC TESTS ON THE STATE BEHIND, WITH NO PREMISE ON THE
ROUNDS' WORDS: the tests that the table of joints opens behind the lookup on the calls and that the
callers' files hold: look (layers, the head), callerIn (layers, attention), "K4.rowsBare",
"K4.lookLeft"; and the kind's own lookOut. Each is a short corollary of what the accept leaves
(K3Left at some rounds: Johnson/Top/H/Keep/K3LeftAnyWords.lean; PadExact: decide_exact; leftAtB:
Johnson/Desc/First/Look/K3CallsLeftAt.lean) and of the text of the state's two writers (putFork,
hearLook). Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: Desc.K3.block's decide at Desc.K3.seatCalls claim; the tests lookLayB, callerInLayB
  (Johnson/Desc/First/FillK4.lean), rowsBareB, lookLeftB (Johnson/Desc/First/FillBare.lean),
  callerIn3B (Johnson/Desc/First/Att/Door/DoorBools.lean), lookHeadB (Johnson/Stored/FillK6K7.lean),
  k3OnOut.
USER: Johnson/Desc/Sound/MgAt/K3CallsOthers.lean, K3HeadBehindAt.lean, K3CallsObjIn.lean and others.
  Meant: the kind's debt "what the sub-protocol makes" at a step on the state.
LETTERS: claim, piece, laid, before, p, guests, h, s, s', rs, cols free.

NOTE: TWO HALVES THAT THE ACCEPT DOES NOT MAKE, NAMED PREMISES: hown (a.own = none, layers) and hh5
  (a.heard5 = none, attention): the accept leaves these two fields as they were, and the kind's own
  test in front (k3OnIn) does not read them: they are facts on the state in front.

Main names: `k3_calls_made` (the whole, in one sentence) · `put_lay`, `put_att` ·
  `k3_calls_lookOut_anyWords`, `k3_calls_next_anyWords` · `look_lay_made`, `callerIn_lay_made`,
  `lookLeft_lay_made`, `rowsBare_lay_made` · `callerIn_att_made` · `look_head_made`.

Limits. look at attention stands in a file of its own (K3CallsMadeAtt.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsLeftAt
import Johnson.Desc.First.Look.K3CallsLookOut
import Johnson.Desc.First.FillK4
import Johnson.Desc.First.Att.Door.DoorBools
import Johnson.Stored.FillK6K7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open OnBytes.PscRun
open VerifiableInference.Desc.K3 (sizedB freeB heardAt k3OnIn k3OnOut)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.FillK4 (lookLayB callerInLayB filledB)
open VerifiableInference.Desc.First.FillBare (leftAtB namedB rowsBareB lookLeftB)

/-! ## The state behind the two writers -/

/-- In a layers' segment. -/
theorem put_lay {s : Desc.First.S} {a : Desc.First.LayOwn} (g : Forest.Heard) (G : Fork)
    (hh : s.here = .lay a) (hn : s.lookHeard? = none) :
    ((s.putFork G).hearLook g).here =
      .lay { a with F := G, fo := some g, lookHeard := some g } := by
  have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh] using hn
  simp [Desc.First.S.putFork, Desc.First.S.hearLook, hh, hn']

/-- In an attention segment. -/
theorem put_att {s : Desc.First.S} {a : Desc.First.AttOwn} (g : Forest.Heard) (G : Fork)
    (hh : s.here = .att a) (hn : s.lookHeard? = none) :
    ((s.putFork G).hearLook g).here =
      .att { a with F := G, g := some g, lookHeard := some g } := by
  have hn' : a.lookHeard = none := by simpa [Desc.First.S.lookHeard?, hh] using hn
  simp [Desc.First.S.putFork, Desc.First.S.hearLook, hh, hn']

/-! ## What an accept leaves, in one sentence -/

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
  {h : Forest.Shape} (s s' : Desc.First.S) (rs : List Fmt.RoundView)
  (cols : List (List (ℕ × List UInt64)))

/-- **THE WHOLE**: k3_calls_leaves (K3CallsLookOut.lean) less its premise on the words; at some
rounds; with the state behind as the two writers' value. -/
theorem k3_calls_made (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) :
    ∃ (F F' : Fork) (g : Forest.Heard) (rs' : Rounds Cb.Gl.E), s.fork? = some F ∧ Sized F ∧
      s.lookHeard? = none ∧ F.next = p.first ∧ freeB F p.first (Forest.elems h) = true ∧
      s' = (s.putFork F').hearLook g ∧ s'.fork? = some F' ∧ s'.lookHeard? = some g ∧
      K3Left Reading.gl h p.lm F F' g rs' ∧ Fo.Tp.PadExact h F F' g := by
  obtain ⟨Fk, hf, hz, hn, hfree⟩ := k3OnIn_free hs hIn
  obtain ⟨F0, x, hF0, hn0, e0, hL⟩ :=
    decide_left_some (Desc.K3.seatCalls claim) piece laid before p guests
      (Desc.K3.seatCalls_reads claim) h hs Reading.gl p.lm s s' rs cols hd
  obtain rfl : Fk = F0 := Option.some.inj (hf.symm.trans hF0)
  obtain ⟨F1, y, hF1, hn1, e1, hE⟩ :=
    decide_exact (Desc.K3.seatCalls claim) piece laid before p guests s s' rs cols hd
  obtain rfl : Fk = F1 := Option.some.inj (hf.symm.trans hF1)
  have hsome : ((Desc.K3.seatCalls claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg0 : (Desc.K3.seatCalls claim).heard s' = some x.1 := by
    rw [e0]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn0
  have hF0' : (Desc.K3.seatCalls claim).fork s' = some x.2 := by
    rw [e0]
    exact seatCalls_keeps claim _ _ _ hsome hn0
  have hg1 : (Desc.K3.seatCalls claim).heard s' = some y.1 := by
    rw [e1]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn1
  have hF1' : (Desc.K3.seatCalls claim).fork s' = some y.2 := by
    rw [e1]
    exact seatCalls_keeps claim _ _ _ hsome hn1
  have ex1 : y.1 = x.1 := Option.some.inj (hg1.symm.trans hg0)
  have ex2 : y.2 = x.2 := Option.some.inj (hF1'.symm.trans hF0')
  obtain ⟨rs', L⟩ := hL hz
  have E := (hE hz).1
  rw [ex1, ex2, L.shape] at E
  exact ⟨Fk, x.2, x.1, rs', hf, hz, hn0, hn, hfree, e0, hF0', hg0, L, E⟩

/-- **lookOut**: k3_calls_lookOut less its premise on the words. -/
theorem k3_calls_lookOut_anyWords (hs : p.shape = some h) (hdg : p.digits = false)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) : k3OnOut p s' = true := by
  obtain ⟨F, F', g, rs', -, -, -, hn, hfree, -, hF', hg, L, E⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  refine k3OnOut_of_left p s' hs ?_ hF' L E hn hfree (_root_.Fo.Pay.shapeOf_ok (shape_some p h hs))
  rw [hdg]
  exact hg

/-- **The ledger behind stands at one public number.** -/
theorem k3_calls_next_anyWords (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) :
    ∃ F', s'.fork? = some F' ∧ F'.next = p.first + Forest.elems h := by
  obtain ⟨F, F', g, rs', -, -, -, hn, -, -, hF', -, -, E⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  exact ⟨F', hF', by rw [E.next, hn]⟩

/-! ## The layers' caller's four tests -/

/-- **look, at a layers' segment.** -/
theorem look_lay_made (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) {a : Desc.First.LayOwn} (hh : s.here = .lay a) :
    lookLayB s' = true := by
  obtain ⟨F, F', g, rs', -, -, hn0, -, -, e, -, -, L, -⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  unfold lookLayB
  rw [e, put_lay g F' hh hn0]
  show (filledB F' g.cEnd && decide ((some g : Option Forest.Heard) = some g)) = true
  rw [Bool.and_eq_true]
  refine ⟨?_, decide_eq_true rfl⟩
  unfold filledB
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨h1, h2⟩ := L.cEndFilled x hx
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true h1, h2⟩

/-- **callerIn, at a layers' segment.** hown: a fact on the state in front. n: the number that the
list of rounds names. -/
theorem callerIn_lay_made (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) {a : Desc.First.LayOwn} (hh : s.here = .lay a)
    (hown : a.own = none) {n : ℕ} (hn : n = p.first + Forest.elems h) :
    callerInLayB n s' = true := by
  obtain ⟨F, F', g, rs', -, -, hn0, hf, -, e, -, -, -, E⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  unfold callerInLayB
  rw [e, put_lay g F' hh hn0]
  show (a.own.isNone && F'.next == n) = true
  rw [hown, E.next, hf, hn]
  simp

/-- **"K4.lookLeft".** hQ: the ledger in front has its sizes, the place's number of slots, and is
free from its next slot on. -/
theorem lookLeft_lay_made (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hQ : LeftQ p.ns F)
    {a' : Desc.First.LayOwn} (hh' : s'.here = .lay a') : lookLeftB s' = true := by
  obtain ⟨g, F', hg, hF', hl⟩ :=
    k3_calls_leftAt claim piece laid before p guests s s' rs cols hs hd hF hQ
  have e1 : a'.lookHeard = some g := by simpa [Desc.First.S.lookHeard?, hh'] using hg
  have e2 : a'.F = F' := by simpa [Desc.First.S.fork?, hh'] using hF'
  unfold lookLeftB
  rw [hh']
  show (a'.lookHeard.any fun g => leftAtB g a'.F) = true
  rw [e1, e2]
  exact hl

/-- **"K4.rowsBare".** -/
theorem rowsBare_lay_made (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') {F : Fork} (hF : s.fork? = some F) (hQ : LeftQ p.ns F)
    {a' : Desc.First.LayOwn} (hh' : s'.here = .lay a') : rowsBareB s' = true := by
  obtain ⟨g, F', hg, -, hl⟩ :=
    k3_calls_leftAt claim piece laid before p guests s s' rs cols hs hd hF hQ
  have e1 : a'.lookHeard = some g := by simpa [Desc.First.S.lookHeard?, hh'] using hg
  unfold rowsBareB
  rw [hh']
  show (a'.lookHeard.any fun g => g.rows.toList.all fun f => f.ents.isEmpty) = true
  rw [e1]
  show (g.rows.toList.all fun f => f.ents.isEmpty) = true
  unfold leftAtB at hl
  simp only [Bool.and_eq_true] at hl
  have hr := hl.1.1.1.1.1.1
  rw [List.all_eq_true] at hr ⊢
  intro f hf
  have h1 := hr f hf
  unfold namedB at h1
  rw [Bool.and_eq_true] at h1
  exact h1.1

/-! ## The attention caller's callerIn -/

/-- **callerIn, at an attention segment.** hh5: a fact on the state in front. -/
theorem callerIn_att_made (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) {a : Desc.First.AttOwn} (hh : s.here = .att a)
    (hh5 : a.heard5 = none) {n : ℕ} (hn : n = p.first + Forest.elems h) :
    H2K5.Door.callerIn3B n s' = true := by
  obtain ⟨F, F', g, rs', -, -, hn0, hf, -, e, -, -, -, E⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  unfold H2K5.Door.callerIn3B
  rw [e, put_att g F' hh hn0]
  show (a.heard5.isNone && (some g : Option Forest.Heard).isSome && F'.next == n) = true
  rw [hh5, E.next, hf, hn]
  simp

/-! ## The head's look -/

/-- **look, at the head's segment.** -/
theorem look_head_made (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) (hS : Head.Shape) (iU3 : ℕ) :
    Desc.Kinds.Head.lookHeadB hS iU3 s' = true := by
  obtain ⟨F, F', g, rs', -, -, -, -, -, -, hF', hg, L, -⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  unfold Desc.Kinds.Head.lookHeadB
  rw [hg]
  show (g.cEnd.slots.toList.all fun x => (s'.fork?.getD {}).gotF.getD x.1 false) = true
  rw [hF', List.all_eq_true]
  intro x hx
  exact (L.cEndFilled x hx).2

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_calls_made
#print axioms VerifiableInference.OnPublicFiles.k3_calls_lookOut_anyWords
#print axioms VerifiableInference.OnPublicFiles.k3_calls_next_anyWords
#print axioms VerifiableInference.OnPublicFiles.look_lay_made
#print axioms VerifiableInference.OnPublicFiles.callerIn_lay_made
#print axioms VerifiableInference.OnPublicFiles.lookLeft_lay_made
#print axioms VerifiableInference.OnPublicFiles.rowsBare_lay_made
#print axioms VerifiableInference.OnPublicFiles.callerIn_att_made
#print axioms VerifiableInference.OnPublicFiles.look_head_made
