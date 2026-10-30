-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/CallerAtLetters.lean: the kind "lookup" (K3), for the batching kind's law (K9): THE
THREE CLAUSES OF THE CALLER's AT THE LOOKUP's RUNS "planes" AND "join" (hb · hp' · hkv: the binders
of planes_plainOk and join_plainOk, Johnson/Top/H/Keep/RunsPlain.lean) AT THE LINK's LAW's CLOSED
LETTERS: φ := phiAll u psiAll · rdAll · kapAll (Johnson/Desc/First/Link/Law/SortLetters.lean) ·
ent := entUnit (Link/Law/EntryUnit.lean), AT WHATEVER Ok AND Fu. THE CHOICE OF bv | pv | kv:
refValQ of the caller's forms READ OFF q (Johnson/P1K9R/CallerReads.lean).
Definitions, statements and proofs. A law file; no running text imports it.

PAID HERE. read, at all five families (CallerReads.lean) · filled AT "planes", BOTH CALLERS: each
form is one entry or the empty form: it names no slot (noSlots_*) · filled AT "join":
keysRun_slots under hQ (filled_keys_att).
LEFT, AS HYPOTHESES: pinned at all five families, in CallerFormsQ's own words (hPb · hPp · hPk: at
every full state that goes on from q each entry that the form names is worth entUnit q y there) ·
hQ: K5's files' promise K5OkAt at the snapshot (a clause of the named Ok at an attention link).
The clauses on the fixed part from which pinned is to come are left to other files.

  attBits · attPin · attKeys · headBits · headPin   CallerFormsQ at the five families
  bvAtt · pvAtt · kvAtt · bvHead · pvHead           THE CHOICE
  hb_att · hp_att · hkv_att · hb_head · hp_head     the clauses, to the letter of RunsPlain.lean's
                                                    binders
Limits. Implications. No state is shown to go on from any q. Nothing on soundness.

-/
import Johnson.P1K9R.CallerReads
import Johnson.Desc.First.Link.Law.SortLetters
import Johnson.Desc.First.Link.Law.EntryUnit
import Johnson.Desc.First.Att.Claims.SlotsCoveredKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (worldAt Bound Pub9 Fx9)
open VerifiableInference.Desc.PhiAll (Phi BetaAll phiAll psiAll rdAll kapAll hrd_all hkap_all)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt planeEntry PlaneRead)
open VerifiableInference.Desc.Kinds.Head.Law (Seen)
open K5Law

/-! ## 1 At "planes" the forms name no slot -/

theorem noSlots_getD {x : Option Aff} (h : ∀ f, x = some f → f.slots = #[]) :
    (x.getD {}).slots = #[] := by
  cases x with
  | none => rfl
  | some f => exact h f rfl

theorem noSlots_planeEntry {tab : List (String × ℕ × ℕ)} {iU3 cols : ℕ} {x : PlaneRead} {i : ℕ}
    {f : Aff} (h : planeEntry tab iU3 cols x i = some f) : f.slots = #[] := by
  unfold planeEntry at h
  obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
    rfl
  · cases h

theorem noSlots_u3at {x : P.Runs.In × ℕ} {place col : ℕ} {f : Aff}
    (h : (P.Runs.gather x.2 (P.Runs.u3at x.1 place col)).map (·.1) = some f) : f.slots = #[] := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold P.Runs.gather at hy
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hy
  simp only [P.Runs.u3at, P.Runs.uEnt, P.Runs.mustAs, bind, ReaderT.bind, ReaderT.run, StateT.bind,
    StateT.run, read, ReaderT.read, readThe, MonadReaderOf.read, pure, ReaderT.pure, StateT.pure,
    Option.bind] at hz
  cases c1 : decide (col < (List.lookup place x.1.t.tabLen).getD 0) with
  | false =>
    simp only [c1, Bool.false_eq_true, if_false] at hz
    exact absurd (show (none : Option (Aff × Array Aff)) = some z from hz) (by simp)
  | true =>
    cases c2 : (x.2 != 0 && decide ((place + col) / x.2 < 2 ^ 32)) with
    | false =>
      simp only [c1, c2, Bool.false_eq_true, if_false, if_true] at hz
      exact absurd (show (none : Option (Aff × Array Aff)) = some z from hz) (by simp)
    | true =>
      simp only [c1, c2, if_true] at hz
      obtain rfl : (Aff.ent x.1.iU3 ((place + col) / x.2) ((place + col) % x.2),
          (#[] : Array Aff)) = z := Option.some.inj hz
      rfl

variable {α : Type}

theorem noSlots_bits_att (rd : α → Option (Forest.Heard × P.Heard)) (c : P.ParC) (i : ℕ × ℕ)
    (q : α × Option Pub9) : (bitQ (attReadersQ rd c) i q).slots = #[] := by
  unfold bitQ
  refine noSlots_getD fun f hf => ?_
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hr
  exact noSlots_u3at hf

theorem noSlots_pin_att (rd : α → Option (Forest.Heard × P.Heard)) (c : P.ParC) (col : ℕ)
    (q : α × Option Pub9) : (pinQ (attReadersQ rd c) col q).slots = #[] := by
  unfold pinQ
  refine noSlots_getD fun f hf => ?_
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hr
  exact noSlots_u3at hf

theorem headPlanesQ_is {kap : α → Option Seen} {iU3 : ℕ} {q : α × Option Pub9}
    {at_ : PlaneRead → ℕ → Option Aff} (h : headPlanesQ kap iU3 q = some at_) :
    ∃ tab K, at_ = planeEntry tab iU3 K := by
  unfold headPlanesQ at h
  obtain ⟨z, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨u, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨tt, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨K, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · cases h
    · cases h
      exact ⟨tt.tab, K, rfl⟩
  · cases h

theorem noSlots_bits_head (kap : α → Option Seen) (iU3 : ℕ) (i : ℕ × ℕ) (q : α × Option Pub9) :
    (bitQ (headReadersQ kap iU3) i q).slots = #[] := by
  unfold bitQ
  refine noSlots_getD fun f hf => ?_
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨at_, hat, rfl⟩ := Option.map_eq_some_iff.1 hr
  obtain ⟨tab, K, rfl⟩ := headPlanesQ_is hat
  exact noSlots_planeEntry hf

theorem noSlots_pin_head (kap : α → Option Seen) (iU3 : ℕ) (col : ℕ) (q : α × Option Pub9) :
    (pinQ (headReadersQ kap iU3) col q).slots = #[] := by
  unfold pinQ
  refine noSlots_getD fun f hf => ?_
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨at_, hat, rfl⟩ := Option.map_eq_some_iff.1 hr
  obtain ⟨tab, K, rfl⟩ := headPlanesQ_is hat
  exact noSlots_planeEntry (tab := tab) (iU3 := iU3) (cols := K) (x := PlaneRead.pin) (i := col) hf

/-! ## 2 The two sentences that are left, by name -/

/-- CallerFormsQ's field pinned, as a sentence of its own. -/
def PinnedQ {ι : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (fQ : ι → α × Option Pub9 → Aff) (ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE) : Prop :=
  ∀ i q t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → ∀ x ∈ (fQ i q).ents.toList,
    (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx

/-- CallerFormsQ's field filled, as a sentence of its own. -/
def FilledQ {ι : Type} (Ok : α × Option Pub9 → Prop) (fQ : ι → α × Option Pub9 → Aff) : Prop :=
  ∀ i q u, Ok q → q.2 = some u → ∀ x ∈ (fQ i q).slots.toList, Filled u.F x.1

theorem filledQ_of_noSlots {ι : Type} (Ok : α × Option Pub9 → Prop)
    {fQ : ι → α × Option Pub9 → Aff} (h : ∀ i q, (fQ i q).slots = #[]) : FilledQ Ok fQ := by
  intro i q u _ _ x hx
  rw [h i q] at hx
  cases hx

/-- **Every slot that a key form off q names is filled in the snapshot**:
keysRun_slots (Johnson/Desc/First/Att/Claims/SlotsCoveredKeys.lean) under the promise K5OkAt, after
the pattern of firstAt_slots (Claims/InAt.lean). -/
theorem filled_keys_att (rd : α → Option (Forest.Heard × P.Heard)) (c : P.ParC)
    (Ok : α × Option Pub9 → Prop)
    (hQ : ∀ q u g h, Ok q → q.2 = some u → rd q.1 = some (g, h) → K5OkAt c g.zk h u.F) :
    FilledQ Ok (keyQ (attKeysQ rd c)) := by
  intro k q u hok hu
  unfold keyQ
  refine slotsIn_getD (Ps := Filled u.F) ?_ k
  cases hk : attKeysQ rd c q with
  | none =>
    intro f hf
    cases hf
  | some kf =>
    unfold attKeysQ at hk
    obtain ⟨xi, hxi, hk⟩ := Option.bind_eq_some_iff.1 hk
    unfold inQ at hxi
    obtain ⟨gh, hgh, hxi⟩ := Option.bind_eq_some_iff.1 hxi
    obtain ⟨u', hu', hxi⟩ := Option.bind_eq_some_iff.1 hxi
    obtain rfl : u = u' := Option.some.inj (hu.symm.trans hu')
    unfold keysOfIn at hk
    obtain ⟨k3, -, hk⟩ := Option.bind_eq_some_iff.1 hk
    obtain ⟨w, hw, hk⟩ := Option.bind_eq_some_iff.1 hk
    have Q := hQ q u gh.1 gh.2 hok hu hgh
    obtain ⟨eg, hp⟩ := inAt_pts hxi
    obtain ⟨q1, q2⟩ := Q.slots u.F _ hp
    exact keysRun_slots (l₁ := w.1) (j := w.2) (eg ▸ q1) q2 hw hk

/-! ## 3 At the closed letters -/

abbrev QAll : Type := Phi BetaAll × Option Pub9

variable (u₀ : HTailF2) (Ok : QAll → Prop) (Fu : S → Prop)

section att
variable (A : Attention.Plan)

/-- **THE CHOICE, at an attention link.** -/
def bvAtt (q : QAll) (y : Bound GE) (k col : ℕ) : GE :=
  refValQ (bitQ (attReadersQ rdAll (P.parCOf A))) entUnit (k, col) q y
def pvAtt (q : QAll) (y : Bound GE) (col : ℕ) : GE :=
  refValQ (pinQ (attReadersQ rdAll (P.parCOf A))) entUnit col q y
def kvAtt (q : QAll) (y : Bound GE) (k : ℕ) : GE :=
  refValQ (keyQ (attKeysQ rdAll (P.parCOf A))) entUnit k q y

variable (hQ : ∀ q u g h, Ok q → q.2 = some u → rdAll q.1 = some (g, h) →
    K5OkAt (P.parCOf A) g.zk h u.F)
include hQ

theorem attBits (hPb : PinnedQ (phiAll u₀ psiAll) Ok Fu
      (bitQ (attReadersQ rdAll (P.parCOf A))) entUnit) :
    CallerFormsQ (phiAll u₀ psiAll) Ok Fu
      (fun (i : ℕ × ℕ) e => bitOf (P.readersOfO A) e i.1 i.2)
      (bitQ (attReadersQ rdAll (P.parCOf A))) entUnit where
  read := att_read_bits (phiAll u₀ psiAll) Ok rdAll A (hrd_all u₀) hQ
  filled := filledQ_of_noSlots Ok (noSlots_bits_att rdAll (P.parCOf A))
  pinned := hPb

theorem attPin (hPp : PinnedQ (phiAll u₀ psiAll) Ok Fu
      (pinQ (attReadersQ rdAll (P.parCOf A))) entUnit) :
    CallerFormsQ (phiAll u₀ psiAll) Ok Fu (fun (col : ℕ) e => pinOf (P.readersOfO A) e col)
      (pinQ (attReadersQ rdAll (P.parCOf A))) entUnit where
  read := att_read_pin (phiAll u₀ psiAll) Ok rdAll A (hrd_all u₀) hQ
  filled := filledQ_of_noSlots Ok (noSlots_pin_att rdAll (P.parCOf A))
  pinned := hPp

theorem attKeys
    (hPk : PinnedQ (phiAll u₀ psiAll) Ok Fu (keyQ (attKeysQ rdAll (P.parCOf A))) entUnit) :
    CallerFormsQ (phiAll u₀ psiAll) Ok Fu
      (fun (k : ℕ) e => (keysOf (P.keysOfO A) e).getD k (Aff.ofConst zeroE))
      (keyQ (attKeysQ rdAll (P.parCOf A))) entUnit where
  read := att_read_keys (phiAll u₀ psiAll) Ok rdAll A (hrd_all u₀) hQ
  filled := filled_keys_att rdAll (P.parCOf A) Ok hQ
  pinned := hPk

/-- **hb.** -/
theorem hb_att (hPb : PinnedQ (phiAll u₀ psiAll) Ok Fu
      (bitQ (attReadersQ rdAll (P.parCOf A))) entUnit) :
    ∀ q e t b y, Fx9 (phiAll u₀ psiAll) Ok q e → Fx9 (phiAll u₀ psiAll) Ok q t → Fu t →
      atS.get? t = some b → ∀ k col,
      (bitOf (P.readersOfO A) e k col).value Reading.gl (worldAt Reading.gl b.L b.F y) =
        bvAtt A q y k col :=
  fun q e t b y he ht hfu hb k col =>
    caller_worthQ _ Ok Fu (attBits u₀ Ok Fu A hQ hPb) (k, col) q e t b y he ht hfu hb

/-- **hp'.** -/
theorem hp_att (hPp : PinnedQ (phiAll u₀ psiAll) Ok Fu
      (pinQ (attReadersQ rdAll (P.parCOf A))) entUnit) :
    ∀ q e t b y, Fx9 (phiAll u₀ psiAll) Ok q e → Fx9 (phiAll u₀ psiAll) Ok q t → Fu t →
      atS.get? t = some b → ∀ col,
      (pinOf (P.readersOfO A) e col).value Reading.gl (worldAt Reading.gl b.L b.F y) =
        pvAtt A q y col :=
  fun q e t b y he ht hfu hb col =>
    caller_worthQ _ Ok Fu (attPin u₀ Ok Fu A hQ hPp) col q e t b y he ht hfu hb

/-- **hkv.** -/
theorem hkv_att
    (hPk : PinnedQ (phiAll u₀ psiAll) Ok Fu (keyQ (attKeysQ rdAll (P.parCOf A))) entUnit) :
    ∀ q e t b y, Fx9 (phiAll u₀ psiAll) Ok q e → Fx9 (phiAll u₀ psiAll) Ok q t → Fu t →
      atS.get? t = some b → ∀ k,
      ((keysOf (P.keysOfO A) e).getD k (Aff.ofConst zeroE)).value Reading.gl
        (worldAt Reading.gl b.L b.F y) = kvAtt A q y k :=
  fun q e t b y he ht hfu hb k =>
    caller_worthQ _ Ok Fu (attKeys u₀ Ok Fu A hQ hPk) k q e t b y he ht hfu hb

end att

section head
variable (iU3 : ℕ)

theorem headBits (hPb : PinnedQ (phiAll u₀ psiAll) Ok Fu (bitQ (headReadersQ kapAll iU3)) entUnit) :
    CallerFormsQ (phiAll u₀ psiAll) Ok Fu
      (fun (i : ℕ × ℕ) e => bitOf (callerReaders (planesAt iU3)) e i.1 i.2)
      (bitQ (headReadersQ kapAll iU3)) entUnit where
  read := head_read_bits (phiAll u₀ psiAll) Ok kapAll iU3 (hkap_all u₀)
  filled := filledQ_of_noSlots Ok (noSlots_bits_head kapAll iU3)
  pinned := hPb

theorem headPin (hPp : PinnedQ (phiAll u₀ psiAll) Ok Fu (pinQ (headReadersQ kapAll iU3)) entUnit) :
    CallerFormsQ (phiAll u₀ psiAll) Ok Fu
      (fun (col : ℕ) e => pinOf (callerReaders (planesAt iU3)) e col)
      (pinQ (headReadersQ kapAll iU3)) entUnit where
  read := head_read_pin (phiAll u₀ psiAll) Ok kapAll iU3 (hkap_all u₀)
  filled := filledQ_of_noSlots Ok (noSlots_pin_head kapAll iU3)
  pinned := hPp

/-- **THE CHOICE, at the head's link.** -/
def bvHead (q : QAll) (y : Bound GE) (k col : ℕ) : GE :=
  refValQ (bitQ (headReadersQ kapAll iU3)) entUnit (k, col) q y
def pvHead (q : QAll) (y : Bound GE) (col : ℕ) : GE :=
  refValQ (pinQ (headReadersQ kapAll iU3)) entUnit col q y

/-- **hb.** -/
theorem hb_head (hPb : PinnedQ (phiAll u₀ psiAll) Ok Fu (bitQ (headReadersQ kapAll iU3)) entUnit) :
    ∀ q e t b y, Fx9 (phiAll u₀ psiAll) Ok q e → Fx9 (phiAll u₀ psiAll) Ok q t → Fu t →
      atS.get? t = some b → ∀ k col,
      (bitOf (callerReaders (planesAt iU3)) e k col).value Reading.gl
        (worldAt Reading.gl b.L b.F y) = bvHead iU3 q y k col :=
  fun q e t b y he ht hfu hb k col =>
    caller_worthQ _ Ok Fu (headBits u₀ Ok Fu iU3 hPb) (k, col) q e t b y he ht hfu hb

/-- **hp'.** -/
theorem hp_head (hPp : PinnedQ (phiAll u₀ psiAll) Ok Fu (pinQ (headReadersQ kapAll iU3)) entUnit) :
    ∀ q e t b y, Fx9 (phiAll u₀ psiAll) Ok q e → Fx9 (phiAll u₀ psiAll) Ok q t → Fu t →
      atS.get? t = some b → ∀ col,
      (pinOf (callerReaders (planesAt iU3)) e col).value Reading.gl
        (worldAt Reading.gl b.L b.F y) = pvHead iU3 q y col :=
  fun q e t b y he ht hfu hb col =>
    caller_worthQ _ Ok Fu (headPin u₀ Ok Fu iU3 hPp) col q e t b y he ht hfu hb

end head

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.noSlots_getD
#print axioms VerifiableInference.OnPublicFiles.noSlots_planeEntry
#print axioms VerifiableInference.OnPublicFiles.noSlots_u3at
#print axioms VerifiableInference.OnPublicFiles.noSlots_bits_att
#print axioms VerifiableInference.OnPublicFiles.noSlots_pin_att
#print axioms VerifiableInference.OnPublicFiles.headPlanesQ_is
#print axioms VerifiableInference.OnPublicFiles.noSlots_bits_head
#print axioms VerifiableInference.OnPublicFiles.noSlots_pin_head
#print axioms VerifiableInference.OnPublicFiles.filledQ_of_noSlots
#print axioms VerifiableInference.OnPublicFiles.filled_keys_att
#print axioms VerifiableInference.OnPublicFiles.attBits
#print axioms VerifiableInference.OnPublicFiles.attPin
#print axioms VerifiableInference.OnPublicFiles.attKeys
#print axioms VerifiableInference.OnPublicFiles.headBits
#print axioms VerifiableInference.OnPublicFiles.headPin
#print axioms VerifiableInference.OnPublicFiles.hb_att
#print axioms VerifiableInference.OnPublicFiles.hp_att
#print axioms VerifiableInference.OnPublicFiles.hkv_att
#print axioms VerifiableInference.OnPublicFiles.hb_head
#print axioms VerifiableInference.OnPublicFiles.hp_head
