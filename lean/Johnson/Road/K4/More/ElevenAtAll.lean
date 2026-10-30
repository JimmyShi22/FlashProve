--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/More/ElevenAtAll.lean: K4's AUTHORS' SHARE OF "the promise's public test is handed
on" AT THE COMPOSED MEANING's OWN PUBLIC TESTS (`pubAll Dm.pubD` over the closed base's) AND ITS OWN
SMALL DOOR (`moreAll`): behind an accept of K4's sub-protocol eleven public items' tests accept. One
structure, one statement with its proof: calls.

  `K4Fence`: WHAT IS ASKED OF THE STATE IN FRONT BESIDE THE PROMISE's PUBLIC TEST: SIX NAMED FACTS:
    the tests of "pile.room" m · "frame.liveIs" · "K12.seatsCarried" · "K12.msgShapes" accept (four
    names that have left the composed meaning's door: `hasNot_room` … in More/FrontList.lean) · the
    statement's codes are the parameters' · what the lookup heard has the public parameters' shape.
  **`eleven_at_all`**: the premises of `k4Row_wide` on the public parameters (hH · AtK4 · K4OnX ·
  K4OnD · K4NamedW · Dm.lk m = some l · the five ties) · `KeptAtS par s s'` · ePubAt … k (z, s) =
  true · the state's shape and the book's counts at k · `K4Fence` at s ⟹ ∀ q ∈ k4Eleven m, pubAll
  Dm.pubD ‹the closed base's tests› q (z, s') = true.

HOW. The wider meaning is a TOOL here, inside the proof: its 44 equations name each test; at an item
that has not left the door its test IS the composed meaning's (`pubWide_hand`). NO PROMISE AT THE
WIDER MEANING IS ASKED OR CONCLUDED: both ends speak at the composed meaning's tests.

Limits. `K4Fence`'s six are facts on reached states, owed by their authors: not shown here. Dm and E
are letters. The full size alone. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Road.K4.More.MadeEleven
import Johnson.Road.K4.More.FrontList
import Johnson.Road.K4.K4RowAtWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.More

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun)
open OnBytes.Road.K4.InT (StatesAt)
open VerifiableInference.Desc (Place Wit Claim Link K9.statesOfLink)
open VerifiableInference.Desc.First (S Pub pubAll ePubAt ePubAt_mem shapeAt bookAt pubWide_hand
  flatPlacesOf)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Look (liveIsB liveItem)
open VerifiableInference.Desc.K12.Door (atFirstSeats atFirstShapes)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT mgWide MgData WideData mgBase linksFull moreAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P)

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

/-- **What is asked of the state in front beside the promise's public test.** -/
structure K4Fence (m : ℕ) (s : S) : Prop where
  room : Johnson.Desc.First.Walk.Tied.roomIsB E.dP.free0 E.dP.fvs m s = true
  live : liveIsB Dm.sent s = true
  seats : atFirstSeats E.d12.L s = true
  shapes : atFirstShapes E.d12.M s = true
  codes : s.st.codes = Dm.cs
  heard : ∀ al fo', s.here = .lay al → al.fo = some fo' → fo'.shape = X.y.fo

variable {Dm E}

/-- **The eleven behind an accept, at the composed meaning's own public tests.** -/
theorem eleven_at_all {k m : ℕ} {pl : Place} {par : Par}
    {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
    {layout : Option ByteArray} {n : ℕ} {l : Link S Claim} {nO nG : String}
    {runO runG : ℕ → S → Except String (List Claim × S)}
    (hH : isLay Dm.links (headLink X) = false) (H : AtK4 linksFull PS k m pl)
    (Sx : K4OnX X pol KL layout m par) (Sd : K4OnD Dm m par n) (Sn : K4NamedW Dm E k m par told n)
    (hlk : Dm.lk m = some l)
    (st : ∀ u, StatesAt (K9.statesOfLink l) 2 par "front" u ∧
      StatesAt (K9.statesOfLink l) 2 par "back" u)
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO)
    (fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG))
    (gRun : GuestRun runG) {z : P} {s s' : S} (K : KeptAtS par s s')
    (hE : ePubAt (pubAll Dm.pubD (Bm).pub) moreAll linksFull PS k (z, s) = true)
    (hs : shapeAt linksFull (some pl) s = true) (hb : bookAt Dm.N PS[k]? s = true)
    (Fc : K4Fence Dm E m s) : ∀ q ∈ k4Eleven m, pubAll Dm.pubD (Bm).pub q (z, s') = true := by
  have Em := k4Means_mgWide Dm E Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have Pl := k4RowPlan_wide Dm E H Sx Sd Sn
  have hand : ∀ (q : Pub), VerifiableInference.Desc.First.classA q = false → ∀ a,
      (mgWide Dm E Bm).pub q a = pubAll Dm.pubD (Bm).pub q a := fun q hq a =>
    pubWide_hand E.d12 E.dP Dm.pubD (Bm).pub q hq a
  have fr : ∀ {f : ℕ → Pub}, hasAtK4 moreAll linksFull PS f = true →
      VerifiableInference.Desc.First.classA (f m) = false →
      (mgWide Dm E Bm).pub (f m) (z, s) = true := fun {f} hf hc => by
    rw [hand _ hc]
    exact List.all_eq_true.1 hE _ (front_mem H hf)
  have F : PubFront (mgWide Dm E Bm) (k4DataWide Dm E Bm) z linksFull PS k m pl s :=
    { asks := fun q hq => by
        simp only [frontAsks, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl
        · exact fr (f := fun m => .ledger m) has_ledger rfl
        · exact fr (f := fun m => .freeAbove m) has_freeAbove rfl
        · exact fr (f := fun m => .look m) has_look rfl
        · exact fr (f := fun m => .linkFresh m) has_linkFresh rfl
        · exact fr (f := fun m => .callerIn m) has_callerIn rfl
        · exact fr (f := fun m => .lookOut m 2) has_lookOut rfl
        · exact fr (f := fun m => .more (some m) "K4.lookLeft") has_lookLeft rfl
        · exact fr (f := fun m => .more (some m) "K4.rowsBare") has_rowsBare rfl
        · exact fr (f := fun m => .more (some m) "frame.sentIs") has_sentIs rfl
        · exact fr (f := fun m => .more (some m) "ledger.treesAre") has_treesAre rfl
        · exact fr (f := fun m => .formsInT m 2 "objects") has_objects rfl
        · rw [Em.room]
          exact Fc.room
        · rw [Em.liveIs]
          exact Fc.live
        · rw [Em.seatsCarried]
          exact Fc.seats
        · rw [Em.msgShapes]
          exact Fc.shapes
      codes := Fc.codes
      heard := Fc.heard
      shape := hs
      book := hb }
  have Se : K4Seats (k4DataWide Dm E Bm) m par
      (VerifiableInference.Desc.K9.holesAt X (headLink X) m l) l nO nG runO runG :=
    ⟨VerifiableInference.Desc.K9.readersAt_some Dm.lk X _ m l hlk, st, fO, oRun, fG, gRun⟩
  intro q hq
  have h8 := made_eleven Em H Pl Se K F q hq
  have hc : VerifiableInference.Desc.First.classA q = false := by
    simp only [k4Eleven, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [← hand q hc]
  exact h8

end OnBytes.Road.K4.More

#print axioms OnBytes.Road.K4.More.eleven_at_all
