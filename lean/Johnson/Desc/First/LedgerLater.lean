-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/LedgerLater.lean: "WHAT IS FILLED STAYS" along steps of a proof file's first
chain inside a segment: behind a block the sub-proof's ledger is a later state of the ledger in
front (PscRun.Later, OnBytes/Tie/Pv/Psc/PscLater.lean: no slot is taken back; every slot that is
filled stays filled, with the same shown scalar and the same factor). Here: the relation on the
chain's record, and kind K1's blocks and the two quiet blocks behind the sending of the reads.
Theorems.

  LaterS s s'          where s holds a ledger, s' holds one, and it is a later state of it.
  LaterS.refl, LaterS.trans
  fork_putFork · fork_putLink   the record's own puts.
  commitOne_later · commitFold_later · commitBehind_later · commitStep_later   a commitment's frame
                       marks arrays as received and writes nothing else of the ledger.
  commitAtS_later      **a segment's later moment (K1)** keeps LaterS.
  firstAtS_later · sendAtS_later   K1's two other blocks stand where the record holds no ledger in
                       front: they keep LaterS idly, and that is said here.
  layers_later · head_later   the two quiet blocks leave the ledger as it is.
WHAT OF `verify-on-bytes` IS USED, FOR THE COUNT: the plain record Model.Fork and its pure function
rootTaken; the relation PscRun.Later with Later.refl, Later.trans and rootTaken_later
(OnBytes/Tie/Pv/Led/LedLater.lean): theorems on plain records. No routine in a context.
What is not claimed. LaterS holds only while the chain stays inside one segment: where a segment is
left the record holds no ledger. Nothing on the virtual rows' weights. These statements name no
verifier's yes or no: they speak of what a block writes.

-/
import Johnson.Desc.K1.First
import Johnson.Desc.K1.OwnLaws
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.BlockKeeps
import OnBytes.Tie.Pv.Led.LedLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model

/-- Where s holds a ledger, s' holds one, and it is a later state of it. -/
def LaterS (s s' : S) : Prop :=
  ∀ F, s.fork? = some F → ∃ F', s'.fork? = some F' ∧ PscRun.Later F F'

/-- Nothing turns: the relation holds. -/
theorem LaterS.refl (s : S) : LaterS s s := fun F h => ⟨F, h, PscRun.Later.refl F⟩

/-- The relation goes on. -/
theorem LaterS.trans (a b c : S) (h : LaterS a b) (k : LaterS b c) : LaterS a c := by
  intro F hF
  obtain ⟨G, hG, l1⟩ := h F hF
  obtain ⟨H, hH, l2⟩ := k G hG
  exact ⟨H, hH, l1.trans l2⟩

/-- The ledger that was laid is the ledger that is read. -/
theorem fork_putFork (s : S) (F F' : Fork) (h : s.fork? = some F) :
    (s.putFork F').fork? = some F' := by
  unfold S.fork? at h
  unfold S.putFork S.fork?
  split at h
  · rfl
  · rfl
  · rename_i a ha
    split at h
    · rename_i ho
      simp only [ho, if_true]
    · cases h
  · cases h

/-- Laying the link's record leaves the ledger as it is. -/
theorem fork_putLink (s : S) (X : LinkCtx) : (s.putLink X).fork? = s.fork? := by
  obtain ⟨st, book, roots, ro, fa, ch, out, here, req⟩ := s
  cases here with
  | head a =>
    by_cases ho : a.opened = true
    · simp [S.putLink, S.fork?, ho]
    · simp [S.putLink, S.fork?, ho]
  | _ => rfl

end VerifiableInference.Desc.First

namespace VerifiableInference.Desc.First.Ledger
open OnBytes OnBytes.Model L3

/-- One array is marked as received. -/
theorem commitOne_later (L : LinkCtx) (F F' : Fork) (t : Nat) (h : commitOne L F t = .ok F') :
    PscRun.Later F F' := by
  unfold commitOne at h
  dsimp only at h
  split at h <;> split at h <;>
    first
      | (cases h; exact OnBytes.Road.Rows.rootTaken_later F t 0)
      | cases h

/-- Arrays are marked as received, one behind the other. -/
theorem commitFold_later (L : LinkCtx) (trees : List Nat) : ∀ (F F' : Fork),
    trees.foldlM (commitOne L) F = .ok F' → PscRun.Later F F' := by
  induction trees with
  | nil =>
    intro F F' h
    cases h
    exact PscRun.Later.refl F
  | cons t l ih =>
    intro F F' h
    rw [List.foldlM_cons] at h
    obtain ⟨G, h1, h2⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
    exact (commitOne_later L F G t h1).trans (ih G F' h2)

/-- Behind a commitment's sending: the arrays are marked. -/
theorem commitBehind_later (L : LinkCtx) (check : ChainCheck) (F : Fork) (trees : List Nat)
    (y : LinkCtx × Fork) (h : commitBehind L check F trees = .ok y) : PscRun.Later F y.2 := by
  unfold commitBehind at h
  obtain ⟨G, h1, h2⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  split at h2
  · cases h2
    exact commitFold_later L trees F G h1
  · cases h2

/-- A commitment's frame marks arrays as received and writes nothing else of the ledger. -/
theorem commitStep_later {W : Type} (send : Send W) (trees : List Nat) (s s' : St W)
    (rs : List Fmt.RoundView) (h : commitStep send trees s rs = .ok s') : PscRun.Later s.F s'.F := by
  unfold commitStep at h
  obtain ⟨_, _, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  obtain ⟨⟨check, w⟩, _, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨⟨L', F'⟩, h2, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  cases h
  exact commitBehind_later _ _ _ _ _ h2

end VerifiableInference.Desc.First.Ledger

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S LaterS)
open VerifiableInference.Desc.Keeps (Decides)

variable {Cl : Type}

/-- **A segment's later moment keeps "what is filled stays".** -/
theorem commitAtS_later (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides LaterS (commitAtS (Cl := Cl) P link moment arrays) := by
  intro s rs gs s' h
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF htl
    obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
    subst h2
    intro F0 hF0
    rw [hF] at hF0
    cases hF0
    refine ⟨y.held.F, First.fork_putFork _ F _ (by rw [First.fork_putLink]; exact hF), ?_⟩
    simp only [commitOwn] at h1
    split at h1
    · split at h1
      · cases h1
      · obtain ⟨x, g1, g2⟩ := Keeps.emap_ok h1
        subst g2
        exact First.Ledger.commitStep_later _ _ _ _ _ g1
    · cases h1
  · cases h

/-- The first segment's opening stands between two segments: in front the record holds no ledger. -/
theorem firstAtS_later (q : Params.First) (gp : GPar) :
    Decides LaterS (firstSegmentOpening (Cl := Cl) q gp) := by
  intro s rs _ s' h
  simp only [firstSegmentOpening] at h
  obtain ⟨_, h0, _⟩ := (bind_ok _ _ _).1 h
  have hb := (need_ok _ _ _).1 h0
  intro F hF
  unfold S.atBetween at hb
  unfold S.fork? at hF
  split at hb
  · rename_i hh
    simp [hh] at hF
  · cases hb

/-- W's sending stands at the chain's end: in front the record holds no ledger. -/
theorem sendAtS_later (P : Par) : Decides LaterS (sendAtS (Cl := Cl) P) := by
  intro s rs gs s' h
  simp only [sendAtS] at h
  split at h
  · rename_i a ha
    intro F hF
    unfold S.fork? at hF
    simp [ha] at hF
  · cases h

end VerifiableInference.Desc.K1

namespace VerifiableInference.Desc.K8.ReadsQuiet
open VerifiableInference.Desc.First (S LaterS)
open VerifiableInference.Desc.Keeps (Decides)

/-- The quiet block at a layers' link leaves the ledger as it is. -/
theorem layers_later (P : PG) : Decides LaterS (layers P) := by
  intro s rs gs s' h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := layers_ok h
  intro F hF
  refine ⟨F, ?_, OnBytes.PscRun.Later.refl F⟩
  unfold S.fork? at hF ⊢
  simp only [ha] at hF
  exact hF

/-- The quiet block at the head's link leaves the ledger as it is. -/
theorem head_later (P : PH) : Decides LaterS (head P) := by
  intro s rs gs s' h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := head_ok h
  intro F hF
  refine ⟨F, ?_, OnBytes.PscRun.Later.refl F⟩
  unfold S.fork? at hF ⊢
  simp only [ha] at hF
  exact hF

end VerifiableInference.Desc.K8.ReadsQuiet
