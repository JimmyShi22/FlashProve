-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotLayerWalk.lean: A STATE OF THE KEY FILE's FIRST CHAIN THAT THE FOLD OVER ITS FIRST k SUB-PROTOCOLS RETURNS, FROM THE CHAIN's
START, HAS THE RECORD's HALF OF THE LINKS' ROWS (RecAt, Johnson/RunOne/Law/WalkAtFK.lean), for k up to the end of the lookups'
links: the library's own step fk_walk, carried along foldBlocks. (The library carries it along its history Hist₁:
rec_of_hist, RecOfHist.lean.)

  frame0, str0    a frame and a family of its oracles: fk_walk asks for one and reads nothing of it
  rec_of_fold     THE WALK
  rec_layer       so in front of the layer of lookup l (border 5 + 6 l): Inv and HeardOk: the table of homes is the letters';
                  the statement has the tables that the lookup's rows read, every home inside its mask table; l lookups have
                  written; something was heard: no shift, a point a part, each of the part's size

Limits. Steps of the verifier's: nothing on any prover. Where the fold returns. Nothing on soundness, completeness, hiding or
binding.
-/
import Johnson.RunOne.Law.WalkAtFK
import Johnson.Desc.K1.Law.AtRecord
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_cons_ok foldBlocks_append_ok)
open VerifiableInference.Desc.K3.KeyLaw (RoomFor HeardOk)
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.Key (FirstState Claim Source LaterPlaces chainStart lookupSeat
  lookupPlace)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.Law.WalkAtFK
open Johnson.RunOne.Law.SeatsKeyD (Inv)
open Johnson.RunOne.Law.LinkAtPlan (Lof)

/-- A frame. -/
def frame0 : Frame := ⟨0, [], id, 0⟩

/-- A family of its oracles. -/
def str0 : frame0.E.Str := (fun _ => (0, []), fun _ => [])

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **THE WALK.** -/
theorem rec_of_fold (ft : ℕ) (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) :
    ∀ (k : ℕ), k ≤ 2 + 6 * X.Y.k.oneTime.ranges.lookups.length →
      k ≤ (FK X N P).first.blocksInOrder.length → ∀ (seen : List Fmt.RoundView) (cols : List OpenedColumn) (s : FirstState)
        (r : List Fmt.RoundView) (c : List OpenedColumn),
        foldBlocks ft ((FK X N P).first.blocksInOrder.take k) (chainStart X.Y.k.oneTime.codes {}) seen cols =
          .ok (s, r, c) → RecAt X k s
  | 0, _, _, seen, cols, s, r, c, h => by
    have e : (chainStart X.Y.k.oneTime.codes {}, seen, cols) = (s, r, c) := Except.ok.inj h
    exact (congrArg Prod.fst e).symm
  | k + 1, hk, hl, seen, cols, s, r, c, h => by
    have hb : (FK X N P).first.blocksInOrder[k]? = some ((FK X N P).first.blocksInOrder[k]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rw [List.take_add_one, hb] at h
    obtain ⟨s1, rs1, c1, f1, f2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 h
    have f2' : foldBlocks ft [(FK X N P).first.blocksInOrder[k]'(by omega)] s1 rs1 c1 = .ok (s, r, c) := f2
    obtain ⟨-, s', kk, st, rest⟩ := foldBlocks_cons_ok.1 f2'
    obtain rfl : s' = s := congrArg Prod.fst (Except.ok.inj rest)
    obtain ⟨hfit, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ _ s1 s' _ _ _ st
    exact fk_walk (N := N) (P := P) str0 hp hR ha k (by omega) _ hb s1 s' _ gs hfit
      (rec_of_fold ft hp hR ha k (by omega) (by omega) seen cols s1 rs1 c1 f1) hdec

/-- **In front of the layer of lookup l.** -/
theorem rec_layer {l : ℕ} {s : FirstState} (h : RecAt X (2 + (6 * l + 3)) s) :
    ∃ oL kL idxN, Inv X.Y.k.oneTime l X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
        (Lof X.Y.k.oneTime l) oL kL idxN s ∧
      HeardOk lookupSeat (lookupPlace X.set l (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
        (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) s := by
  have h' := ((recAt_link X l 3 (by omega) s).1 h).1
  exact ⟨_, _, _, h'.1, h'.2⟩

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.rec_of_fold
#print axioms AtPublicFiles.FirstH.Lots.rec_layer
