-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/RidesAt.lean: «A YES HANDS THE CONDITION ON», AT THE TABLE's OWN PROMISE
(`onT`, LinkTiedAt.lean), FOR A PIECE THAT HOLDS A BLOCK WITH A QUIET ROW EACH OF WHOSE YESES LEAVES
WHAT THE PROMISE READS OF THE VERIFIER's STATE (`Rb`, RbRuns.lean). A rule, and its three uses in a
link: the batching (the law's premise h01), the frame's block behind it (h12), the shutting
(`ShutOwes.hands`). Theorems.

What is said.
  `rec_of_rb`: `RecRides` (QuietRides.lean) from `Rb`, the test on the stand in front, two
    neighbouring places of one segment with one stand, «no count of rows waits behind, or one may»,
    and the plan's two counts. `rides_of_rb`: **for a piece that holds such a block: `onT … k a` and
    the piece's yes give `onT … (k + 1) b`**, under `MgRides` at the two states. `h01_at`, `h12_at`:
    that at the batching's block and at the frame's block behind it, from `TwoBlocks`
    (LinkAtSort.lean). `hands_at`: at the shutting.

Limits. `MgRides` (seven riders on the letters of the table's meaning) IS A PREMISE AT EVERY PAIR OF
STATES: it can be paid only at a filling of these letters. The facts on the written list are
LinkPlacesFit.lean's; the plan's two counts are shown of no numbers. The one equation's piece (hon3)
is not here: its row opens a class of rows. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Desc.First.Link.Law.FromPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Where shut)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers rowOf quietRow shapeAt mayWait)
open _root_.Run.PQ (CK)

variable {P W : Type} {C : CK} {F : Frame}

/-- The share of the two states, from Rb. -/
theorem rec_of_rb (Nm : Numbers) (links : List ModelPart) (pl : List Place) (k : ℕ) (p p' : Place)
    (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p') (hn : NextIn links p p')
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (a b : S × F.E.Str) (R : Rb a.1 b.1)
    (hw : b.1.noneWaits = true ∨ mayWait links p' = true)
    (hs : shapeAt links pl[k]? a.1 = true) : RecRides Nm links pl k a b := by
  refine ⟨R.failed, R.st, R.book, ?_, ht, hm⟩
  rw [hp] at hs
  rw [hp']
  exact shape_step links p p' a.1 b.1 hs R.stand hn.stand hn.link hw R.num

/-- **A YES HANDS THE PROMISE AND «NO MARK» ON.** -/
theorem rides_of_rb (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (p p' : Place) (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p')
    (hq : quietRow (rowOf links p) = true) (hn : NextIn links p p')
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (b₀ : Block S Claim) (q : Piece C F S Claim W) (hb : q.b = below b₀)
    (hR : ∀ ft s rs cols s' j, b₀.step ft s rs cols = .ok (s', j) → Rb s s' ∧
      (shapeAt links (some p) s = true → s'.noneWaits = true ∨ mayWait links p' = true))
    (M : ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → q.ior.red.out a τ = some b →
      MgRides Nm Mg links pl z k p a b) :
    ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → q.ior.red.out a τ = some b →
      onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) b := by
  intro a τ b ha hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hb hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  obtain ⟨R, hw⟩ := hR _ _ _ _ _ j hstep
  have hs := (onT_bools Nm Mg links pl z k a ha).1
  exact onT_rides Nm Mg links pl z k p hp hq a b
    (rec_of_rb Nm links pl k p p' hp hp' hn ht hm a b R (hw (hp ▸ hs)) hs) (M a τ b ha hout) ha

/-- **h01 AT onT**: over the batching's block. -/
theorem h01_at (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (p p' : Place) (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p')
    (hq : quietRow (rowOf links p) = true) (hn : NextIn links p p')
    (hmw : mayWait links p' = true)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (L : Link S Claim) (pp : Where) (T : TwoBlocks L pp) (pb : Piece C F S Claim W)
    (hb : pb.b = below L.batchB)
    (M : ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → pb.ior.red.out a τ = some b →
      MgRides Nm Mg links pl z k p a b) :
    ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → pb.ior.red.out a τ = some b →
      onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) b :=
  rides_of_rb Nm Mg links pl z k p p' hp hp' hq hn ht hm L.batchB pb hb
    (fun ft s rs cols s' j h => ⟨(T.1 ft s rs cols s' j h).1, fun _ => Or.inr hmw⟩) M

/-- **h12 AT onT**: over the frame's block behind the batching. -/
theorem h12_at (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (p p' : Place) (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p')
    (hq : quietRow (rowOf links p) = true) (hn : NextIn links p p')
    (hmw : mayWait links p' = true)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (L : Link S Claim) (pp : Where) (T : TwoBlocks L pp) (pq : Piece C F S Claim W)
    (hb : pq.b = below L.behindB)
    (M : ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → pq.ior.red.out a τ = some b →
      MgRides Nm Mg links pl z k p a b) :
    ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → pq.ior.red.out a τ = some b →
      onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) b :=
  rides_of_rb Nm Mg links pl z k p p' hp hp' hq hn ht hm L.behindB pq hb
    (fun ft s rs cols s' j h => ⟨(T.2 ft s rs cols s' j h).1, fun _ => Or.inr hmw⟩) M

/-- **ShutOwes.hands AT onT**: over the shutting. -/
theorem hands_at (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k : ℕ) (p p' : Place) (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p')
    (hq : quietRow (rowOf links p) = true) (hn : NextIn links p p')
    (hnw : mayWait links p = false)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Claim W) (hb : ps.b = below b₅)
    (M : ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → ps.ior.red.out a τ = some b →
      MgRides Nm Mg links pl z k p a b) :
    ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → ps.ior.red.out a τ = some b →
      onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) b :=
  rides_of_rb Nm Mg links pl z k p p' hp hp' hq hn ht hm b₅ ps hb
    (fun ft s rs cols s' j h => by
      obtain ⟨R, e⟩ := rb_shutB pw piece b₅ hb₅ ft s rs cols s' j h
      refine ⟨R, fun hs => Or.inl ?_⟩
      have hs' : (First.standOf s == First.standAt links p && (s.noneWaits || mayWait links p) &&
          s.link?.all fun L => p.link == some L.link) = true := hs
      have h2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hs').1).2
      rw [hnw, Bool.or_false] at h2
      unfold S.noneWaits at h2 ⊢
      rw [e]
      exact h2) M

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rides_of_rb
#print axioms VerifiableInference.Desc.LinkJoin.h01_at
#print axioms VerifiableInference.Desc.LinkJoin.h12_at
#print axioms VerifiableInference.Desc.LinkJoin.hands_at
