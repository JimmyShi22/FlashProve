-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/KeysEntsAt.lean (kind K9): THE CLAUSE keysEnts OF
  `PlanesAttOk` (OkPlanes.lean:
  an attention segment's key forms, which the lookup's run "join" takes from its
  caller, pass `EntsOk` at the fixed part). Statements and proofs: calls of K5's files' laws.

Why it holds. K5's files' `keysRun_covered` (Johnson/Desc/First/Att/Claims/CoveredKeys.lean):
every entry that a key form names lies in the tables' part, below the
planned length nW: from `LenIn` (paid by `len_in`) and `RowsCov` (paid by `cov_parts`,
Claims/HeardPlain.lean, from `HeardPlain` of what is held as heard). Where the array is at least nW
wide that is row 0 (`row0_of_cov`).

  `keys_make`: the make of the key forms at `inAt` (Johnson/Desc/First/Att/Claims/InAt.lean).
  `keysEnts_of`: **the clause at a fixed part q**, from hH (what rd reads at q as heard is
    HeardPlain), hW (the snapshot's array c.iU3 is at least c.nW wide), the static clause, hU and
    h0.
  `keysEnts_of_plain`: **the clause at fixed9 φ s**: hH and hW paid by `plainThereB c.iU3 c.nW s =
    true` with hrd (what rd reads back is what s has heard): JUST the premises of
    `entsFirst_of_plain` (EntsAtt.lean).
  `keysEnts_at`: **the same from the table's promise**, in the form of `entsFirst_at`
(PlainOfPromise.lean): its premises, letter for letter. AT ONE HONEST RUN OF EACH OF THE TWO SIZES
THE KEY FORMS NAMED NO ENTRY AT ALL (evaluated: 4 key forms; 37 slots at the small size, 41 at the
full size; 0 entries): THERE THE
CLAUSE HOLDS IDLY. By K5's files' own lemmas each key form is made of slots and constants.
Limits. IMPLICATIONS. hs, hU and h0 are premises here. hs hangs on a closed sentence, had from the
head and an opening of the description by `closed_at_hd` (Johnson/P5J/K09AreadyHd.lean). Nothing on
the key forms' slots. No soundness statement.
-/
import Johnson.Desc.First.Link.Law.PlanesAttAt
import Johnson.Desc.First.Att.Claims.CoveredKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Pub Meaning pubSets)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC keysOfK)
open H2K5.Door (plainThereB plain_spent)
open K5Law

variable {β : Type}

/-- The make of the key forms. -/
theorem keys_make {c : ParC} {g : Forest.Heard} {h : First.Att.P.Heard} {U : Fork}
    {x : P.Runs.In × ℕ} (e : inAt c g h U = some x) (hc : HeardPlain h) (hW : c.nW ≤ x.2)
    {y : List Aff × P.Runs.JoinsP} (h1 : P.Runs.firstRun x.1 x.2 = some y) {k3 : P.Runs.PadIn}
    {KF : Array Aff} (hk : P.Runs.keysRun x.1 k3 y.2 = some KF) : EntsMake c.iU3 KF.toList := by
  obtain ⟨_, eu, _, _, _⟩ := inAt_parts e
  obtain ⟨hL, hR⟩ := cov_parts e hc
  intro f hf z hz
  obtain ⟨a1, a2, _⟩ := row0_of_cov hW
    (keysRun_covered hL hR (l₁ := y.1) (j := y.2) h1 hk f hf z hz)
  exact ⟨a2, a1.trans eu⟩

/-- **THE CLAUSE AT A FIXED PART.** -/
theorem keysEnts_of {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC}
    {nU : Array ℕ} {q : Q β} (hH : ∀ g h, rd q.1 = some (g, h) → HeardPlain h)
    (hW : ∀ u T, q.2 = some u → u.F.trees[c.iU3]? = some T → c.nW ≤ T.K)
    (hs : ∀ tlb v, (pi8 q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (pi8 q.1).1 = some tlb → tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ KF, keysOfK (seatCQ rd c) c q = some KF → EntsOk nU q KF.toList := by
  intro KF hK
  unfold keysOfK at hK
  obtain ⟨x, hx, hK⟩ := Option.bind_eq_some_iff.1 hK
  obtain ⟨k3, _, hK⟩ := Option.bind_eq_some_iff.1 hK
  obtain ⟨y, hy, hK⟩ := Option.bind_eq_some_iff.1 hK
  cases hrd : rd q.1 with
  | none =>
    unfold P.inOf seatCQ at hx
    simp [hrd] at hx
  | some gh =>
    cases hu : q.2 with
    | none =>
      unfold P.inOf seatCQ at hx
      simp [hrd, hu] at hx
    | some u =>
      obtain ⟨g, h⟩ := gh
      rw [inOf_Q hrd hu] at hx
      obtain ⟨_, _, hk, _, _⟩ := inAt_parts hx
      obtain ⟨T, hT, eK⟩ := Option.map_eq_some_iff.1 hk
      exact ents_of_static pi8 hs hU h0
        (keys_make hx (hH g h hrd) (eK ▸ hW u T hu hT) hy hK)

/-- **THE CLAUSE AT WHAT IS FIXED AT A STATE THAT PASSES plainThereB.** -/
theorem keysEnts_of_plain {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC}
    (φ : S → Phi β) {nU : Array ℕ} {s : S} (hp : plainThereB c.iU3 c.nW s = true)
    (hrd : ∀ g h, rd (φ s) = some (g, h) → s.heard5? = some h)
    (hs : ∀ tlb v, (pi8 (fixed9 φ s).1).1 = some tlb → (fixed9 φ s).2 = some v →
      StaticOk tlb v.F)
    (hU : ∀ tlb, (pi8 (fixed9 φ s).1).1 = some tlb → tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ KF, keysOfK (seatCQ rd c) c (fixed9 φ s) = some KF →
      EntsOk nU (fixed9 φ s) KF.toList := by
  obtain ⟨U, hh, T', e1, e2, e3, e4, e5⟩ := plain_spent hp
  refine keysEnts_of (fun g h hg => ?_) (fun u T hu hT => ?_) hs hU h0
  · obtain rfl : hh = h := Option.some.inj (e2.symm.trans (hrd g h hg))
    exact e3
  · obtain rfl : U = u.F := Option.some.inj (e1.symm.trans (snap_fork φ hu))
    obtain rfl : T' = T := Option.some.inj (e4.symm.trans hT)
    exact Nat.le_of_eq e5.symm

/-- **THE CLAUSE AT WHAT IS FIXED IN FRONT OF THE BATCHING, FROM THE TABLE's PROMISE.** -/
theorem keysEnts_at {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X)
    (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
    {A : Type} {Fr : Frame} (get : A → P × S) (k m : ℕ) (a : A × Fr.E.Str)
    (hon : onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl get k a) (hu : (get a.1).2.failed = none)
    (hatt : 𝔇.pubD.d5.isAtt m = true)
    (hq : Pub.more (some m) "K5.plain" ∈ (pubSets (mgAll 𝔇 Mg₀).more links pl)[k]?.getD [])
    (c : ParC) (hc : ∀ p, 𝔇.pubD.d5.W.A[m / 2]? = some p → c.iU3 = p.iU3 ∧ c.nW = p.nW)
    (φ : S → Phi β) (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (hrd : ∀ g h, rd (φ (get a.1).2) = some (g, h) → (get a.1).2.heard5? = some h)
    {nU : Array ℕ}
    (hs : ∀ tlb v, (pi8 (fixed9 φ (get a.1).2).1).1 = some tlb →
      (fixed9 φ (get a.1).2).2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (pi8 (fixed9 φ (get a.1).2).1).1 = some tlb →
      tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ KF, keysOfK (seatCQ rd c) c (fixed9 φ (get a.1).2) = some KF →
      EntsOk nU (fixed9 φ (get a.1).2) KF.toList := by
  obtain ⟨p, hp, hok⟩ := plain_of_onQ 𝔇 Mg₀ links pl get k m a hon hu hatt hq
  exact keysEnts_of_plain φ (by rw [(hc p hp).1, (hc p hp).2]; exact hok) hrd hs hU h0

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keys_make
#print axioms VerifiableInference.Desc.LinkJoin.keysEnts_of
#print axioms VerifiableInference.Desc.LinkJoin.keysEnts_of_plain
#print axioms VerifiableInference.Desc.LinkJoin.keysEnts_at
