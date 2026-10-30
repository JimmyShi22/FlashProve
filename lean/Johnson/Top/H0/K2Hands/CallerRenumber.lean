-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/CallerRenumber.lean: `CallerAt` (TiePaid.lean) feels no number of a message.
`renumber W g olds anew` (FrameRenumber.lean) lays other values at a frame's g and at each kept
member's old and anew, by its place in the frame's list, and leaves every other field.
`plRe`: the reading pl, each entry renumbered alike, by the slot's place mem κ.
`keptNo_renumber`, `nameJ_renumber`, `nameQ_renumber`: the running number of a kept row and the two
maps of names (Johnson/Top/H/SwitchMaps.lean) are the same at W and at the renumbered frame.
`fit_renumber`: so is `Fit` (Johnson/Top/H/SwitchMapsFit.lean): an ↔. `slotsAll_renumber`:
`SlotsAll` (Numbering.lean) goes over.
`callerAt_renumber`: `CallerAt` at W gives `CallerAt` at the renumbered frame, AT THE SAME iJ AND
iQ.
`callerAt_renumbered`: the three tests of FitTest.lean, run at a frame W, give `CallerAt` at W
renumbered, with the two maps of names that are made at W.
Limits. One direction for `SlotsAll` and `CallerAt`. That a frame of the programs at a real place is
a written frame renumbered is not shown here. The tests are premises. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FitTest
import Johnson.Top.H0.K2Hands.FrameRenumber

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.First.K2Caller

section
variable (W : SwitchFrame) (g : ℕ) (olds anew : Array ℕ)

/-- An entry of the frame's list, renumbered as at the place i. -/
def reAt (i : ℕ) (k : KeptPlace) : KeptPlace :=
  { k with old := olds.getD i noId, anew := anew.getD i noId }

theorem renumber_kept (i : ℕ) :
    (renumber W g olds anew).kept[i]? = (W.kept[i]?).map (reAt olds anew i) := by
  show (W.kept.mapIdx fun i k => reAt olds anew i k)[i]? = _
  rw [List.getElem?_mapIdx]

theorem renumber_rows :
    (renumber W g olds anew).kept.map (·.rows) = W.kept.map (·.rows) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map, renumber_kept]
  cases W.kept[i]? <;> rfl

/-- The running number of a kept row feels no number. -/
theorem keptNo_renumber (i b : ℕ) : keptNo (renumber W g olds anew) i b = keptNo W i b := by
  unfold keptNo
  rw [List.map_take, List.map_take, renumber_rows]

variable {K : Type} (mem row : K → ℕ) (pl : K → KeptPlace)

/-- The reading pl, each entry renumbered by its slot's place. -/
def plRe (κ : K) : KeptPlace := reAt olds anew (mem κ) (pl κ)

variable (s : Sg)

theorem nameJ_renumber :
    nameJ s (renumber W g olds anew) mem row (plRe olds anew mem pl) = nameJ s W mem row pl := rfl

theorem nameQ_renumber : nameQ s (renumber W g olds anew) mem row = nameQ s W mem row := by
  funext x
  rcases x with ⟨_ | k, j⟩ | _ | _
  · rfl
  · show restAt _ (_ + j.val) = restAt _ (_ + j.val)
    rw [keptNo_renumber]
    rfl
  · rfl
  · rfl

variable (cs : Codes) (l : List (OracleShape × ℕ))

/-- **`Fit` feels no number.** -/
theorem fit_renumber : Fit cs l s (renumber W g olds anew) mem row (plRe olds anew mem pl) ↔
    Fit cs l s W mem row pl :=
  ⟨fun F =>
    { g := F.g, mainBits := F.mainBits, mainFits := F.mainFits, mainRows := F.mainRows
      mainLen := F.mainLen, restBits := F.restBits, restFits := F.restFits
      restRows := F.restRows, room := F.room, mask := F.mask, mainTail := F.mainTail
      keptTail := fun k => by
        have t := F.keptTail k
        rw [keptNo_renumber] at t
        exact t
      maskTail := F.maskTail, oldPad := F.oldPad, keptMsg := F.keptMsg },
   fun F =>
    { g := F.g, mainBits := F.mainBits, mainFits := F.mainFits, mainRows := F.mainRows
      mainLen := F.mainLen, restBits := F.restBits, restFits := F.restFits
      restRows := F.restRows, room := F.room, mask := F.mask, mainTail := F.mainTail
      keptTail := fun k => by
        rw [keptNo_renumber]
        exact F.keptTail k
      maskTail := F.maskTail, oldPad := F.oldPad, keptMsg := F.keptMsg }⟩

variable {W mem row pl}

/-- **`SlotsAll` goes over.** -/
theorem slotsAll_renumber (A : SlotsAll K W mem row pl) :
    SlotsAll K (renumber W g olds anew) mem row (plRe olds anew mem pl) where
  member κ := by
    rw [renumber_kept, A.member κ]
    rfl
  rowIn κ := A.rowIn κ
  two := A.two
  all a k b ha hb := by
    rw [renumber_kept] at ha
    cases h0 : W.kept[a]? with
    | none =>
      rw [h0] at ha
      exact absurd ha (by simp)
    | some k0 =>
      rw [h0] at ha
      obtain rfl : reAt olds anew a k0 = k := Option.some.inj ha
      exact A.all a k0 b h0 hb

end

section
variable {S : Sig GE} (R : RowsK S) (cs : Codes) (l : List (OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  {mem row : R.Kp → ℕ} {pl : R.Kp → KeptPlace} {W₀ : SwitchFrame}
  (g : ℕ) (olds anew : Array ℕ)

/-- **`CallerAt` feels no number**: at the same two maps of names. -/
theorem callerAt_renumber (C : CallerAt R cs l iJ iQ mem row pl W₀) :
    CallerAt R cs l iJ iQ mem row (plRe olds anew mem pl) (renumber W₀ g olds anew) where
  codeC := C.codeC
  codeZ := C.codeZ
  slots := slotsAll_renumber g olds anew C.slots
  mapJ F := C.mapJ ((fit_renumber W₀ g olds anew mem row pl R.s cs l).1 F)
  mapQ F := by
    have e := C.mapQ ((fit_renumber W₀ g olds anew mem row pl R.s cs l).1 F)
    rw [e]
    unfold Johnson.Top.H.iQ
    congr 1
    exact (nameQ_renumber W₀ g olds anew mem row R.s).symm

end

variable {r : SwRow} (H : r.OK) {W : SwitchFrame} (h : r.keptAt W = true)
  (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ)

/-- **The tests are run at a frame W and spent at W renumbered.** -/
theorem callerAt_renumbered (hc : codesAt r W = true) (hf : fitAt r W = true) (g : ℕ)
    (olds anew : Array ℕ) :
    CallerAt ((rowsAt r H t₀ oM oZ).keep r.kp) r.cs r.l
      (Johnson.Top.H.iJ (stageOf r.g t₀) W (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ)
        (plAt H h t₀ oM oZ) r.cs r.l (fit_made H h t₀ oM oZ hf).nameJ)
      (Johnson.Top.H.iQ (stageOf r.g t₀) W (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ) r.cs r.l
        (fit_made H h t₀ oM oZ hf).nameQ)
      (memAt H h t₀ oM oZ) (rowAt H h t₀ oM oZ)
      (plRe olds anew (memAt H h t₀ oM oZ) (plAt H h t₀ oM oZ)) (renumber W g olds anew) :=
  callerAt_renumber _ _ _ _ _ g olds anew (callerAt_of_tests H h t₀ oM oZ hc hf)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.fit_renumber
#print axioms VerifiableInference.Desc.First.K2Hands.slotsAll_renumber
#print axioms VerifiableInference.Desc.First.K2Hands.callerAt_renumber
#print axioms VerifiableInference.Desc.First.K2Hands.callerAt_renumbered
