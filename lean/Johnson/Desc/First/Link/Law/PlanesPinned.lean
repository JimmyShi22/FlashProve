-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlanesPinned.lean (kind K9): THE THIRD OF THE THREE SENTENCES ON THE
  CALLER's FORMS («pinned»: at every full state that goes on from q each entry that the form names
  is worth entUnit q y there: `PinnedQ`, Johnson/P1K9R/CallerAtLetters.lean) AT ALL FIVE FAMILIES OF
  THE LOOKUP's RUNS "planes" AND "join", FROM THE CLAUSES ON THE FIXED PART `PlanesAttOk` |
  `PlanesHeadOk` (OkPlanes.lean) AND THE NAMED Ok's CORE. Theorems. It changes no other file.

  THE BRIDGES: the readers off q stand in two wordings: `inOfQ_is` ·
    `readersQ_is` · `keysQ_is` · `planesQ_is` · `headQ_is`: readersOfK | keysOfK at seatCQ, and
    callerReaders at planesQ (OkPlanes.lean), ARE attReadersQ | attKeysQ | headReadersQ
    (Johnson/P1K9R/CallerReads.lean): equations.
  `pinned_of_opt`: a family «what a reader hands in, or the empty form» is pinned where each form
    handed in passes EntsOk: by `core_ents` (OkOne.lean) and `ent_full`
    (SistersFull.lean).
  `pinned_bits_att` · `pinned_pin_att` · `pinned_keys_att` · `pinned_bits_head` · `pinned_pin_head`:
    **PinnedQ (phiAll u₀ psiAll) Ok (FullAt nU) ‹the family off q› entUnit**, for whatever Ok gives
    the core and the sort's structure.
Limits. pinned_keys_att IS IDLE AT HONEST FRONTS: on one honest run at the full size the attention's
  four key forms name slots and NO ENTRY (evaluated; no theorem): there it says nothing; it stands
  because the forms' text may name entries by its type. Implications: the two structures and the
  core are premises on Ok. No state is shown to go on from any q. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OkPlanes
import Johnson.P1K9R.CallerAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC readersOfK keysOfK)
open VerifiableInference.Desc.Kinds.Head (callerReaders)
open VerifiableInference.Desc.Kinds.Head.Law (Seen)
open VerifiableInference.OnPublicFiles (inQ attReadersQ attKeysQ headPlanesQ headReadersQ readersOfIn
        keysOfIn bitQ pinQ keyQ PinnedQ)
open K5Law (inAt)

variable {β : Type}

/-! ## 1 The bridges -/

theorem inOfQ_is (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC) (q : Q β) :
    P.inOf (seatCQ rd c) c q = inQ rd c q := by
  unfold P.inOf seatCQ inQ inAt
  cases hr : rd q.1 with
  | none =>
    simp only [hr, Option.bind_eq_bind, Option.bind_none]
  | some gh =>
    cases hu : q.2 with
    | none =>
      simp only [hr, hu, Option.bind_eq_bind, Option.bind_some, Option.bind_none]
    | some u =>
      simp only [hr, hu, Option.bind_eq_bind, Option.bind_some, Option.map_some]

theorem readersQ_is (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC) (q : Q β) :
    readersOfK (seatCQ rd c) c q = attReadersQ rd c q := by
  show (P.inOf (seatCQ rd c) c q).map readersOfIn = _
  rw [inOfQ_is]
  rfl

theorem keysQ_is (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC) (q : Q β) :
    keysOfK (seatCQ rd c) c q = attKeysQ rd c q := by
  have h0 : keysOfK (seatCQ rd c) c q =
      (P.inOf (seatCQ rd c) c q).bind (keysOfIn ((seatCQ rd c).pad q)) := rfl
  rw [h0, inOfQ_is]
  rfl

theorem planesQ_is (iU3 : ℕ) (kap : Phi β → Option Seen) (q : Q β) :
    planesQ iU3 kap q = headPlanesQ kap iU3 q := by
  unfold planesQ headPlanesQ
  cases kap q.1 with
  | none => rfl
  | some z =>
    obtain ⟨zx, zs, zt, zo, zl, zr, zq⟩ := z
    cases hu : q.2 with
    | none =>
      cases zo <;> cases zt <;> simp
    | some u =>
      cases h3 : u.F.trees[iU3]? <;> cases zo <;> cases zt <;> simp [h3]

theorem headQ_is (iU3 : ℕ) (kap : Phi β → Option Seen) (q : Q β) :
    callerReaders (planesQ iU3 kap) q = headReadersQ kap iU3 q := by
  unfold callerReaders headReadersQ
  rw [planesQ_is]

/-! ## 2 Pinned -/

section
variable (u₀ : HTailF2) (Ok : Q BetaAll → Prop) (nU : Array ℕ) (tlD : HTailF2)
  (hc : ∀ q, Ok q → OkCore nU tlD q)
include hc

/-- A family «what is handed in, or the empty form». -/
theorem pinned_of_opt {ι : Type} (x : ι → Q BetaAll → Option Aff)
    (H : ∀ i q f, Ok q → x i q = some f → EntsOk nU q [f]) :
    PinnedQ (phiAll u₀ psiAll) Ok (FullAt nU) (fun i q => (x i q).getD {}) entUnit := by
  intro i q t b y hf hfu hb e he0
  have he : e ∈ ((x i q).getD {}).ents.toList := he0
  cases hx : x i q with
  | none =>
    rw [hx] at he
    cases he
  | some f =>
    rw [hx] at he
    exact ent_full u₀ psiAll Ok nU q t b y hf hfu hb e
      (core_ents hc hf.1 (H i q f hf.1 hx) f List.mem_cons_self e he)

theorem pinned_bits_att (c : ParC) (hP : ∀ q, Ok q → PlanesAttOk rdAll c nU q) :
    PinnedQ (phiAll u₀ psiAll) Ok (FullAt nU) (bitQ (attReadersQ rdAll c)) entUnit :=
  pinned_of_opt u₀ Ok nU tlD hc
    (fun (i : ℕ × ℕ) q => (attReadersQ rdAll c q).bind fun r => r.1 i.1 i.2)
    fun i q f hq hx => by
      obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.1 hx
      exact ((hP q hq).planes r (by rw [readersQ_is]; exact hr)).1 i.1 i.2 f hf

theorem pinned_pin_att (c : ParC) (hP : ∀ q, Ok q → PlanesAttOk rdAll c nU q) :
    PinnedQ (phiAll u₀ psiAll) Ok (FullAt nU) (pinQ (attReadersQ rdAll c)) entUnit :=
  pinned_of_opt u₀ Ok nU tlD hc (fun (col : ℕ) q => (attReadersQ rdAll c q).bind fun r => r.2 col)
    fun col q f hq hx => by
      obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.1 hx
      exact ((hP q hq).planes r (by rw [readersQ_is]; exact hr)).2 col f hf

theorem pinned_bits_head (iU3 : ℕ) (hP : ∀ q, Ok q → PlanesHeadOk iU3 kapAll nU q) :
    PinnedQ (phiAll u₀ psiAll) Ok (FullAt nU) (bitQ (headReadersQ kapAll iU3)) entUnit :=
  pinned_of_opt u₀ Ok nU tlD hc
    (fun (i : ℕ × ℕ) q => (headReadersQ kapAll iU3 q).bind fun r => r.1 i.1 i.2)
    fun i q f hq hx => by
      obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.1 hx
      exact ((hP q hq).planes r (by rw [headQ_is]; exact hr)).1 i.1 i.2 f hf

theorem pinned_pin_head (iU3 : ℕ) (hP : ∀ q, Ok q → PlanesHeadOk iU3 kapAll nU q) :
    PinnedQ (phiAll u₀ psiAll) Ok (FullAt nU) (pinQ (headReadersQ kapAll iU3)) entUnit :=
  pinned_of_opt u₀ Ok nU tlD hc
    (fun (col : ℕ) q => (headReadersQ kapAll iU3 q).bind fun r => r.2 col)
    fun col q f hq hx => by
      obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.1 hx
      exact ((hP q hq).planes r (by rw [headQ_is]; exact hr)).2 col f hf

theorem pinned_keys_att (c : ParC) (hP : ∀ q, Ok q → PlanesAttOk rdAll c nU q) :
    PinnedQ (phiAll u₀ psiAll) Ok (FullAt nU) (keyQ (attKeysQ rdAll c)) entUnit := by
  intro k q t b y hf hfu hb e he
  unfold keyQ at he
  cases hk : attKeysQ rdAll c q with
  | none =>
    rw [hk] at he
    cases he
  | some KF =>
    rw [hk, Option.getD_some, Array.getD_eq_getD_getElem?] at he
    cases hx : KF[k]? with
    | none =>
      rw [hx] at he
      cases he
    | some f =>
      rw [hx] at he
      have hm : f ∈ KF.toList := by
        rw [Array.mem_toList_iff]
        exact Array.mem_of_getElem? hx
      exact ent_full u₀ psiAll Ok nU q t b y hf hfu hb e
        (core_ents hc hf.1 ((hP q hf.1).keysEnts KF (by rw [keysQ_is]; exact hk)) f hm e he)

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.inOfQ_is
#print axioms VerifiableInference.Desc.LinkJoin.readersQ_is
#print axioms VerifiableInference.Desc.LinkJoin.keysQ_is
#print axioms VerifiableInference.Desc.LinkJoin.planesQ_is
#print axioms VerifiableInference.Desc.LinkJoin.headQ_is
#print axioms VerifiableInference.Desc.LinkJoin.pinned_of_opt
#print axioms VerifiableInference.Desc.LinkJoin.pinned_bits_att
#print axioms VerifiableInference.Desc.LinkJoin.pinned_pin_att
#print axioms VerifiableInference.Desc.LinkJoin.pinned_bits_head
#print axioms VerifiableInference.Desc.LinkJoin.pinned_pin_head
#print axioms VerifiableInference.Desc.LinkJoin.pinned_keys_att
