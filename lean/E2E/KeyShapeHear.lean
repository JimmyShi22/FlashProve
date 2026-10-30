--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeHear.lean: A LOOKUP'S OWN SUB-PROTOCOL (`K3.lookupKind`, as Johnson/Desc/Key/Link.lean seats
it) ON THE KEY FILE'S FIRST CHAIN'S SHAPE (E2E/KeyShapeFirst.lean). Definitions, statements and
proofs, by calls. NOTHING IS SHOWN OF ANY PROVER: no completeness.

What is defined.
  `heardOf f`: what is left of what the hearing at the face f hands back from a ledger whose count
    stands at 0: the mark; the number of the forms of rows; for each claim on a part's keys its
    point's length and the slots that its form names: code on public numbers (`heardVSh`,
    Johnson/Desc/ProofFile/Honest/K3/Shape/HeardOps.lean).
  `hearBlock Q i`: lookup number i's own sub-protocol.
  `gHear Q i`: it, on the shape. It asks three public tests (the face passes its own test · the
    planner makes the place's entries · a part at least), that i lookups have written their claims
    on keys, and OF THE OPEN LEDGER'S SHAPE: the count stands at 0, there is room for just the
    face's slots, and these are free (`freeB`, Johnson/Desc/First/Shape/Parts.lean). It lays the
    ledger's shape behind the hearing (`lookUpd`) and `heardOf f`.
What is shown.
  `scopedB_of`, `leftB_of`: the ten facts `LeftG`
    (Johnson/Desc/ProofFile/Honest/K3/Parts/KeyLeft.lean) give the test `leftB`
    (E2E/KeyLookupAround.lean).
  **`hear_exact`**: where `gHear` returns at a state's shape AND THE STEP'S OWN TESTS ON ROUNDS AND
    COLUMNS PASS (`Block.Fits`), the sub-protocol's decision returns a state of the shape that
    `gHear` returns. NO TEST ON VALUES AND NO HYPOTHESIS BY NAME IS LEFT.

By what. The decision calls `hearG`; the laws on the hearing speak of `hearV`. From `Fits`: `hearV`
returns (`hearV_returns_fitsG`, over `win_of_freeB` and E2E/PlannerLookup.lean's `fit_of_planner`);
so the decision returns what `hearV` heard (E2E/KeyLookupHears.lean's `blockG_decide`); the ledger's
shape behind: `hearV_sh`; the mark: `leftG_of_hearV`, `hearV_marks`, `planesV_marks` with
`planesV_of_planesG` and `planesG_letter`; the counts and the slots: `messagesV_out`. All under
Johnson/Desc/ProofFile/Honest/K3/.

Limits.
- IT STANDS OVER FILES THAT ARE NOT KNOWN HERE TO BE REVIEWED: those that it imports under
  Johnson/Desc/ProofFile/Honest/K3/, with what they import in turn, and
  Johnson/Desc/First/Shape/Parts.lean.
- The three public tests are asked by `gHear`; that they pass at the intended sizes is shown nowhere
  here.
- `gHear` asks more of the ledger than the decision does: sufficient, not necessary.
- THE MARK SAYS NOTHING OF WHAT WAS SENT: counts, marks in the ledger and which slots a form names.
- Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyShapeFirst
import Johnson.Desc.ProofFile.Honest.K3.Shape.ReturnsStep
import Johnson.Desc.ProofFile.Honest.K3.Shape.Walk
import Johnson.Desc.ProofFile.Honest.K3.Shape.HeardWalk
import Johnson.Desc.ProofFile.Honest.K3.Parts.KeyLeft
import Johnson.Desc.ProofFile.Honest.K3.Parts.NamesMarks
import Johnson.Desc.ProofFile.Honest.K3.Law.PlanesGLetter

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyShape
open OnBytes
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (Block named need noDigest OpenedColumn step_iff)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.First.Shape (LedSh ledSh freeB free_of_B affSh)
open AtPublicFiles.KeyLookup AtPublicFiles.RowsFit
open ProofFile.Honest.K3.Shape (lookUpd hearV_sh heardVSh messagesV_out hearV_returns_fitsG win_of_freeB)
open ProofFile.Honest.K3.Parts (LeftG leftG_of_hearV Fresh hearV_marks planesV_marks)
open ProofFile.Honest.K3.Law (planesV_of_planesG planesG_letter hearV_messages)

/-! ## 1. The ten facts as the test -/

theorem scopedB_of {n : ℕ} {a : Aff} (h : a.ents.isEmpty = true ∧ ∀ t ∈ a.slots.toList, t.1 < n) :
    scopedB n a = true := by
  unfold scopedB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact h

theorem leftB_of {p : PG} {g : HeardG} {G G₂ : Fork} {cl : List PlaneClaim}
    (h : LeftG p g G cl G₂) : leftB p g G = true := by
  obtain ⟨rest, hp⟩ := h.planes
  unfold leftB
  rw [h.unpaid, hp]
  simp only [Bool.true_and, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h.three, h.room⟩, h.first⟩, h.one⟩, fun a ha => scopedB_of (h.rows a ha)⟩,
    fun c hc => scopedB_of (h.leads c hc)⟩, fun k hk => scopedB_of (h.keys k hk)⟩, h.done⟩

/-! ## 2. The lookup's own sub-protocol -/

variable (Q : Pub1) {Bk : Type} (bk : BackOf → Bk)

/-- What is left of what the hearing at the face f hands back from a ledger whose count stands at 0.
-/
def heardOf (f : Face) : HeardSh :=
  ⟨true, (heardVSh f 0).rows.length, (heardVSh f 0).keys.map fun y => (y.1, y.2.slots)⟩

/-- Lookup number i's own sub-protocol. -/
abbrev hearBlock (i : ℕ) : Block FirstState Claim :=
  lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace Q.set i (lookAt Q.one i))

/-- It, on the shape. -/
def gHear (i : ℕ) (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  let f := faceOfLkp (lookAt Q.one i)
  match a.2.look.led with
  | some (some L) =>
    if f.ok && (lookupPlace Q.set i (lookAt Q.one i)).entries.isSome &&
        decide (1 ≤ f.parts.length) && a.2.look.keys.length == i && freeB L 0 f.slots &&
        L.next == 0 && L.ns == f.slots then
      .ok (a.1, { a.2 with look := { a.2.look with
        led := some (some (lookUpd f L)), heard := some (heardOf f) } })
    else .error "the lookup: a guard on the shape"
  | _ => .error "the lookup: no ledger is open"

theorem hear_exact (i ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (gs : List (List (ℕ × List UInt64))) (s : FirstState) (t : Sh₁ Bk)
    (hg : gHear Q i (sh₁ Q bk s) = .ok t) (hfit : (hearBlock Q i).Fits ft rs cols) :
    ∃ s', (hearBlock Q i).decide s (rs.map noDigest) gs = .ok s' ∧ sh₁ Q bk s' = t := by
  unfold gHear at hg
  dsimp only at hg
  cases hF : s.base.fork with
  | none =>
    have e : (sh₁ Q bk s).2.look.led = none := by
      show (s.base.fork.map fun F => if stageOpen s then some (ledSh F) else none) = none
      rw [hF]
      rfl
    rw [e] at hg
    cases hg
  | some F =>
    cases hO : stageOpen s with
    | false =>
      have e : (sh₁ Q bk s).2.look.led = some none := by
        show (s.base.fork.map fun F => if stageOpen s then some (ledSh F) else none) = _
        rw [hF, hO]
        rfl
      rw [e] at hg
      cases hg
    | true =>
      have e : (sh₁ Q bk s).2.look.led = some (some (ledSh F)) := by
        show (s.base.fork.map fun F => if stageOpen s then some (ledSh F) else none) = _
        rw [hF, hO]
        rfl
      rw [e] at hg
      dsimp only at hg
      split at hg
      case isFalse => cases hg
      rename_i h0
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h0
      obtain ⟨⟨⟨⟨⟨⟨hok, hes⟩, hp1⟩, hk⟩, hfree⟩, hnext⟩, hns⟩ := h0
      obtain rfl := Except.ok.inj hg
      have hnext' : F.next = 0 := hnext
      have hns' : F.ns = (faceOfLkp (lookAt Q.one i)).slots := hns
      have hk' : s.base.keys.length = i := by
        have : (AtPublicFiles.AtFiles.keysSlots s.base.keys).length = i := hk
        unfold AtPublicFiles.AtFiles.keysSlots at this
        rwa [List.length_map] at this
      obtain ⟨hS, -, hfr⟩ := free_of_B hfree
      have hW := win_of_freeB (F := F) (n := (faceOfLkp (lookAt Q.one i)).slots)
        (by rw [hnext']; exact hfree)
      obtain ⟨es, hes'⟩ := Option.isSome_iff_exists.1 hes
      have hEF : entriesFit (lookupPlace Q.set i (lookAt Q.one i)).face
          ((lookupPlace Q.set i (lookAt Q.one i)).entries.getD []) = true := by
        rw [hes']
        exact AtPublicFiles.PlanLookup.fit_of_planner hok hes'
      obtain ⟨g, G, hh⟩ := hearV_returns_fitsG lookupSeat [(1, 0), (1, 1)] 0 []
        (lookupPlace Q.set i (lookAt Q.one i)) hok hW hEF hfit
      have hdec := blockG_decide lookupSeat [(1, 0), (1, 1)] 0 [] gs hes
        (show lookupSeat.fork s = some F from hF) rfl hnext' hns' hh
      refine ⟨_, hdec, ?_⟩
      have hFresh : Fresh (lookupPlace Q.set i (lookAt Q.one i)) F :=
        ⟨hS, rfl, hnext', hns', fun j hj => by simpa using hfr j hj⟩
      obtain ⟨cl, G₂, hL⟩ := leftG_of_hearV _ hFresh hh
      obtain ⟨rest, hpl⟩ := hL.planes
      obtain ⟨-, hled⟩ := hearV_sh hS hh
      obtain ⟨m1, -, -, -, -⟩ := hearV_marks hh
      obtain ⟨cl₀, hv, -, -⟩ := planesV_of_planesG _ g hpl
      have hpl₀ := planesG_letter _ hS hh [] hv
      have ecl : cl₀ = cl := by
        rw [hpl] at hpl₀
        exact (Prod.mk.inj (Option.some.inj hpl₀)).1.symm
      have m2 := planesV_marks hh hv
      rw [ecl, hnext'] at m2
      rw [hnext'] at m1
      obtain ⟨o1, -, -, -, o5, -⟩ := messagesV_out hS hp1 (hearV_messages hh).2
      rw [hnext'] at o1 o5
      subst hk'
      have hst : stageOpen (lookupSeat.put s (toHeardG g) G) = true := hL.unpaid
      have hB : heardB Q (lookupSeat.put s (toHeardG g) G) (toHeardG g) = true := by
        show (leftB (lookupPlace Q.set s.base.keys.length (lookAt Q.one s.base.keys.length))
            (toHeardG g) G &&
          (toHeardG g).rows.toList.all
            (offB
              (lookupPlace Q.set s.base.keys.length (lookAt Q.one s.base.keys.length)).face 0) &&
          match planesG
              (lookupPlace Q.set s.base.keys.length (lookAt Q.one s.base.keys.length)).face
              (toHeardG g) (G.paid (toHeardG g).owedObjects) [] with
          | none => false
          | some y => y.1.all fun c =>
            offB (lookupPlace Q.set s.base.keys.length (lookAt Q.one s.base.keys.length)).face 0
              c.lead) = true
        rw [leftB_of hL, hpl]
        simp only [Bool.true_and, Bool.and_eq_true, List.all_eq_true]
        exact ⟨fun a ha => offB_of (m1 a ha), fun c hc => offB_of (m2 c hc)⟩
      have hr : (toHeardG g).rows.size =
          (heardVSh (faceOfLkp (lookAt Q.one s.base.keys.length)) 0).rows.length := by
        rw [← o1, List.length_map, Array.length_toList]
        rfl
      have hkz : ((toHeardG g).keys.map fun k => (k.1.size, k.2.slots.toList.map (·.1))) =
          (heardVSh (faceOfLkp (lookAt Q.one s.base.keys.length)) 0).keys.map
            fun y => (y.1, y.2.slots) := by
        rw [← o5, List.map_map]
        rfl
      have hlk : lookSh Q (lookupSeat.put s (toHeardG g) G) =
          { lookSh Q s with
            led := some (some (lookUpd (faceOfLkp (lookAt Q.one s.base.keys.length)) (ledSh F)))
            heard := some (heardOf (faceOfLkp (lookAt Q.one s.base.keys.length))) } := by
        have e1 : (lookupSeat.put s (toHeardG g) G).base.heard = some (toHeardG g) := rfl
        have e2 : (lookupSeat.put s (toHeardG g) G).base.fork = some G := rfl
        unfold lookSh heardSh heardOf
        rw [hst, e1, e2]
        simp only [Option.map_some, if_true]
        rw [hB, hr, hkz, hled]
        rfl
      unfold sh₁ locSh
      rw [hlk]
      rfl

end AtPublicFiles.KeyShape

#print axioms AtPublicFiles.KeyShape.leftB_of
#print axioms AtPublicFiles.KeyShape.hear_exact
