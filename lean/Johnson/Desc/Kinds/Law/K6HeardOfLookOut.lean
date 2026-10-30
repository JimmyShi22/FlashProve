-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6HeardOfLookOut.lean: WHAT THE LOOKUP ON THE OUTPUT HEAD'S CALLS HEARD HAS
THE PLAN'S SHAPE AND A POINT OF THE PLAN'S SIZE, IN FRONT OF THE SUB-PROTOCOL AT THE OUTPUT HEAD:
from the public test lookOut 24 3, which the table of joints keeps open at that border.

Why. The bill for that sub-protocol took the sentence as a premise on the verifier's state.
The lookup's own test behind its sub-protocol
(Johnson/Desc/First/Look/K3Borders.lean: k3OnOut) says it, and more; the row of this
sub-protocol does not ASK that test, but the promise says every public test that is OPEN.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  sameCall_eq, zipAll_eq, sameShapeAll_eq: the lookup's test "the same shape, field by field" gives
      the equation.
  heard_of_onOut: k3OnOut's accept at headAt's place gives the two facts.
  lookOut_open: lookOut 24 3 IS OPEN AT BORDER 341 OF THE FULL CHAIN, at the closed list of extra
      public tests (Johnson/Desc/Sound/MgAllAt.lean: mgMore): by evaluation in the kernel.
  fit_closed: the table's own test pubFit accepts that closed list at the full chain: by evaluation
      in the kernel.
  heard_mgAll: SO: inside the promise at 341, at the composed meaning over a base whose list of
      extra public tests is empty.

Every letter under "there is": none.
What it does not say. Its premises: the base's list is empty (at that meaning's closed base it is,
by rfl) · the head's segment's number is 24 · headAt's place is x · the lookup on the calls stands
at piece 3 of segment 24 (k3SortAt: on the public parameters). Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6WorthAtMgAll
import Johnson.Desc.First.Look.K3HeadStated

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (Frame MsgT MgData mgAll onQ pubQ linksFull onParts_of_on)
open VerifiableInference.Desc.K3 (sameCall sameShapeAll k3OnOut)

theorem sameCall_eq (a b : OnBytes.Model.Call) (h : sameCall a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := b
  simp only [sameCall, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

theorem zipAll_eq : ∀ l l' : List OnBytes.Model.Call, l.length = l'.length →
    (l.zip l').all (fun x => sameCall x.1 x.2) = true → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: l, b :: l', h, h2 => by
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h2
    rw [sameCall_eq a b h2.1, zipAll_eq l l' (Nat.succ.inj h) h2.2]

/-- **"The same shape, field by field" gives the equation.** -/
theorem sameShapeAll_eq (a b : OnBytes.Model.Forest.Shape) (h : sameShapeAll a b = true) :
    a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := b
  simp only [sameShapeAll, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  have e : a1 = b1 := by
    apply Array.ext'
    exact zipAll_eq _ _ (by simpa using h0) h1
  rw [e]

/-- **The lookups' test behind their sub-protocol, at headAt's place.** -/
theorem heard_of_onOut {X : OnBytes.Model.Verify.Public} {x : First.Look.Place}
    (hx : headAt X = some x) (s : S)
    (h : k3OnOut (First.Look.P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x) s = true)
    (g : OnBytes.Model.Forest.Heard) (hg : s.lookHeard? = some g) :
    g.zx.size = x.fs.dT ∧ g.shape = x.fs := by
  have hsh : (First.Look.P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x).shape =
      some x.fs := by
    unfold headAt at hx
    obtain ⟨x', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', hh, hx⟩ := Option.map_eq_some_iff.1 hx
    subst hx
    exact hh
  have hh : K3.heardAt
      (First.Look.P.ofPlace (OnBytes.Params.settingOf X.P.frame) false x).digits s = some g := hg
  unfold k3OnOut at h
  rw [hsh, hh] at h
  cases hF : s.fork? with
  | none =>
    rw [hF] at h
    cases h
  | some G =>
    rw [hF] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1.1.1.1.1.1.1.1.1.2, sameShapeAll_eq _ _ h.1.1.1.1.1.1.1.1.1.1.1.1⟩

/-- **The public test lookOut 24 3 is open at border 341 of the full chain.** -/
theorem lookOut_open : First.Pub.lookOut 24 3 ∈
    pubQ Sound.mgMore linksFull (First.flatPlacesOf linksFull true) 341 := by
  decide +kernel

/-- **The table's test on the list of extra public tests accepts the closed list, at the full
chain.** -/
theorem fit_closed : First.pubFit Sound.mgMore linksFull (First.flatPlacesOf linksFull true) = true
    := by
  decide +kernel

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- **Inside the promise at 341.** -/
theorem heard_mgAll {Fr : Frame} {x : First.Look.Place} (C : CallerFits (Wp := Wp) x)
    (hMore : Mg.more = {}) (hsort : First.Look.k3SortAt Wp 24 3 = some false)
    (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N (mgAll D Mg) linksFull (First.flatPlacesOf linksFull true)
      (fun a => a) 341 a)
    (hm : a.1.2.failed = none) (g : OnBytes.Model.Forest.Heard)
    (hg : a.1.2.lookHeard? = some g) : g.zx.size = x.fs.dT ∧ g.shape = x.fs := by
  have h1 : (mgAll D Mg).pub (.lookOut 24 3) a.1 = true :=
    (onParts_of_on D.N (mgAll D Mg) linksFull _ (fun a => a) 341 a ha hm).pub _
      (List.mem_append_left _ (by
        rw [Sound.mgAll_more_closed D Mg hMore]
        exact lookOut_open))
  rw [Sound.mgAll_pub, First.pubAll_lookOut D.pubD Mg.pub 24 3 false hsort a.1] at h1
  unfold First.Look.lookOutC at h1
  have e : First.Look.placeAt Wp 24 false =
      some (First.Look.P.ofPlace (OnBytes.Params.settingOf Wp.P.frame) false x) := by
    rw [← C.seg]
    letI := (parOf Wp.hS 0).sizes
    letI := (parOf Wp.hS 0).policy
    letI : Request := ⟨fun _ => 0, 0, 0⟩
    exact VerifiableInference.OnPublicFiles.placeAt_headAt C.place
  have h2 : ((First.Look.placeAt Wp 24 false).any fun p => k3OnOut p a.1.2) = true := h1
  rw [e] at h2
  exact heard_of_onOut C.place a.1.2 h2 g hg

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.sameShapeAll_eq
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_of_onOut
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.lookOut_open
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.fit_closed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_mgAll
