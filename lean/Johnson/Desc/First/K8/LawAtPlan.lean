-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawAtPlan.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LAW IN THE PLAIN FORM
AT A PLACE WHOSE NUMBERS ARE READ OFF A PUBLIC RECORD, IN A FILE WHOSE PLAN PASSES.

Johnson/Desc/First/K8/LawAtRecord.lean has the law under three premises that are facts on the plan:
the place's numbers are the typed block's at the sizes of a public record tl0 (`Fits`); every tree
off which a member's word is read is sent in front of the block's stretch (`hseat`); and tl0 itself
is a letter. Here these three are paid or filled:
  The place's numbers are READ OFF tl0 (`parOf`, Johnson/Desc/First/K8/LawAtS.lean): so `Fits`
    follows from one test on numbers: tl0's number of matrices is the length of its list
    (`fits_parOf`). `parOf` reads tl0's matrices and its number of combinations alone
    (`parOf_congr`): so these are also the numbers read off the link's PLANNED record, if tl0 has
    that record's matrices and number of combinations.
  tl0 MUST NOT BE THE PLANNED RECORD ITSELF. The caller's sizes hold the SHAPES OF THE TABLES of
    reads, off tl0's list of tables; a plan's own record has that list empty (a run fills and
    closes it). The condition in front of the draw is that the sizes of the record in the state
    are tl0's. `on_fails_at_open_list`: at a tl0 with an empty list that condition FAILS at every
    state whose list holds a table: the law would be true and say nothing at any run with a read.
    `on_of_same`: it HOLDS where the state's record has tl0's number of matrices, matrices, number
    of combinations and shapes of tables. So tl0 is: the planned record WITH THE SHAPES OF THE
    TABLES THAT THE CLOSED LIST WILL HAVE: public numbers; no weight.
  The stretch's base := the number of trees that the first chain's rounds in front of the block's
    round send: so `hseat` follows from the file's one test on the plan, if every tree that seat'
    names is named by the block (`seats_below`, Johnson/Desc/First/K8/LawSeats.lean).
  `planned_keepsW`: **the kind's law in the plain form, there.**
Statement and proof; nothing is counted anew.
Limits. tl0's list of tables is a letter HERE; since the kind's text has test (t), such a tl0 is
made of the place's numbers and a yes gives its numbers: Johnson/Desc/First/K8/LawPlace.lean. STILL
LETTERS: sym, u3 (the lay) · dig · smpOf · l, seat', arr. STILL PREMISES: that tl0's
number of matrices is the length of its list · that every tree which seat' names is named by the
block · the error e is at least the proved block's count times the sampler's own bound. THAT THE
STRETCH'S BASE IS THAT NUMBER OF TREES is the tiling's to say. That a description's block at this
place has these numbers is its maker's: the block b of the file is asked to have the kind's rounds,
decision, field `before` and tests on the plan (`Like`) at SOME seat of the file's own record: that
this seat is the one of Johnson/Desc/First/K8/AtS.lean is not asked, since the order reads none of
it. Nothing says that what stands at a boundary holds.

-/
import Johnson.Desc.First.K8.LawAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Tie.Pv.Tail KObj Johnson.Pack
  VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound

/-- The place's numbers hang on the record's matrices and number of combinations alone. -/
theorem parOf_congr (tl tl' : HTailF2) (hm : tl.mats = tl'.mats) (ht : tl.tau = tl'.tau)
    (link pc : Nat) (matsIn readsIn : List Nat) (asks : List (Nat × Nat × Nat)) :
    parOf tl link pc matsIn readsIn asks = parOf tl' link pc matsIn readsIn asks := by
  unfold parOf
  rw [hm, ht]

/-- Where the condition in front of the draw holds: the record in the state has tl0's number of
matrices, matrices, number of combinations and shapes of tables. -/
theorem on_of_same (tl0 tl : HTailF2) (s : S) (hs : s.tl? = some tl) (h1 : tl.NM = tl0.NM)
    (h2 : tl.mats = tl0.mats) (h3 : tl.tau = tl0.tau)
    (h4 : (tl.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) =
      tl0.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) :
    OnBytes.Tie.Pv.Tail.sizeOf (recOf tl0 s) = OnBytes.Tie.Pv.Tail.sizeOf tl0 := by
  unfold recOf
  rw [hs]
  show OnBytes.Tie.Pv.Tail.sizeOf tl = _
  unfold OnBytes.Tie.Pv.Tail.sizeOf
  rw [h1, h2, h3, h4]

/-- **Why tl0 must not be a plan's own record**: at a tl0 whose list of tables is empty the
condition fails at every state whose list holds a table. -/
theorem on_fails_at_open_list (tl0 tl : HTailF2) (s : S) (hs : s.tl? = some tl)
    (h0 : tl0.funs = #[]) (h1 : tl.funs ≠ #[]) :
    OnBytes.Tie.Pv.Tail.sizeOf (recOf tl0 s) ≠ OnBytes.Tie.Pv.Tail.sizeOf tl0 := by
  intro e
  unfold recOf at e
  rw [hs] at e
  have e1 : (OnBytes.Tie.Pv.Tail.sizeOf tl).tabs = (OnBytes.Tie.Pv.Tail.sizeOf tl0).tabs :=
    congrArg TSize.tabs e
  have e2 : (tl.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) =
      tl0.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab) := e1
  rw [h0] at e2
  have e3 : tl.funs.toList = [] := by simpa using e2
  exact h1 (by simpa using e3)

/-- **The kind's law in the plain form at a place whose numbers are read off a public record, in a
file whose plan passes.** -/
theorem planned_keepsW {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes)
    (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    {Cells Tok : Type} (tl0 : HTailF2)
    (sym : (sigOf cs l).Msg → ℕ → ℕ → ℕ → Cb.Gl.E) (u3 : (sigOf cs l).Msg → ℕ → Cb.Gl.E)
    (dig : Wit Cells Tok MsgT → Dig Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0).size)
    (smpOf : S → (sigOf cs l).Smp)
    (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
      smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
    (Cl : Type) (F : Frame) (link pc : Nat) (matsIn readsIn : List Nat)
    (asks : List (Nat × Nat × Nat)) (e : ℕ) (p : Par)
    (hpar : p = parOf tl0 link pc matsIn readsIn asks)
    {seatG : Seat G.S₁} {b : Block G.S₁ G.Cl} (hb : Like seatG p b)
    (pre post : List (Block G.S₁ G.Cl)) (hflat : G.first.blocksInOrder = pre ++ b :: post)
    (hG : G.planOk = true) (hnamed : ∀ i, (seat' i).1 ∈ p.matsIn ++ p.readsIn)
    (hNM : tl0.NM = tl0.mats.size)
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e).ior.red.KeepsW
      (recordReads G cs l seat' arr tl0 sym u3 dig smpOf hs Cl F p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e
        (seats_below l seat' p G hb pre post hflat hG hnamed)).onA
      (recordReads G cs l seat' arr tl0 sym u3 dig smpOf hs Cl F p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e
        (seats_below l seat' p G hb pre post hflat hG hnamed)).onB
      (recordReads G cs l seat' arr tl0 sym u3 dig smpOf hs Cl F p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e
        (seats_below l seat' p G hb pre post hflat hG hnamed)).relA
      (recordReads G cs l seat' arr tl0 sym u3 dig smpOf hs Cl F p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e
        (seats_below l seat' p G hb pre post hflat hG hnamed)).relB
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p
        (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e).err :=
  record_keepsW G cs l seat' arr tl0 sym u3 dig smpOf hs Cl F p
    (rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn pre))) e
    (seats_below l seat' p G hb pre post hflat hG hnamed)
    (hpar ▸ fits_parOf tl0 hNM link pc matsIn readsIn asks) he

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.planned_keepsW
#print axioms VerifiableInference.Desc.First.K8.on_of_same
#print axioms VerifiableInference.Desc.First.K8.on_fails_at_open_list
