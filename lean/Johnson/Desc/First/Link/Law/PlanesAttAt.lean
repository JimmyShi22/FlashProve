-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlanesAttAt.lean (kind K9): THE CLAUSE planes OF
  `PlanesAttOk` (OkPlanes.lean:
  whatever form a reader of an attention segment's "planes" hands in at the fixed
    part passes `EntsOk`), AT A FIXED PART, AND AT WHAT IS FIXED AT A STATE THAT PASSES K5's FILES'
    TEST `plainThereB`. Statements and proofs: calls of K5's files' laws.

Why it holds. The attention's readers of "planes" hand in `Runs.u3at i t n`: the entry number t + n
of the reads' array, read at K columns, at n below the table's stored length
(Johnson/Desc/First/Att/RunsP.lean). Of what `tablesP` itself makes each table ends at or below the
planned length nW (`len_in`, Att/Claims/Covered.lean); so the entry's number is below
nW (`cv_u3at`); where the array is at least nW wide that is row 0 (`row0_of_cov`,
Claims/CoveredApart.lean).

  `inOf_Q`: what the runs read at the fixed part, through the seat `seatCQ rd c` (OkPlanes.lean), is
    `inAt c g h u.F` (Claims/InAt.lean) at what rd reads and the snapshot's ledger.
  `u3at_make`: a form that the reader hands in names entries at row 0 of the reads' array alone.
  `planesAtt_of`: **the clause at a fixed part q**, from hW (the snapshot's array c.iU3 is at least
    c.nW wide), the static clause, hU and h0.
  `planesAtt_of_plain`: **the clause at fixed9 φ s**, hW paid by `plainThereB c.iU3 c.nW s = true`:
    the premises of `entsFirst_of_plain` (EntsAtt.lean), LESS hrd: what was heard is not spent.
  `planesAtt_at`: **the clause at what is fixed at a state with the table's promise in front of an
    attention segment's batching**: plainThereB drawn from the promise's public item "K5.plain"
    (`plain_of_onQ`, PlainOfPromise.lean): the premises of `entsFirst_at` there, less hrd: so
      whoever pays these for entsFirst pays them for this clause.
Limits. IMPLICATIONS. hs (the static clause at what is fixed), hU and h0 are premises here. hs hangs
on a closed sentence, had from the head and an opening of the description, at a built segment where
digAt returns, by `closed_at_hd` (Johnson/P5J/K09AreadyHd.lean). plainThereB is shown of no state
here: in planesAtt_at it comes from the promise, under hatt, hq and hc. Nothing on the key forms. No
soundness statement.
-/
import Johnson.Desc.First.Link.Law.OkPlanes
import Johnson.Desc.First.Link.Law.PlainOfPromise
import Johnson.Desc.First.Att.Claims.HeardPlain

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
open VerifiableInference.Desc.First.Att.P (ParC readersOfK)
open H2K5.Door (plainThereB plain_spent)
open K5Law

variable {β : Type}

/-- What the runs read at the fixed part is inAt at what rd reads and the snapshot's ledger. -/
theorem inOf_Q {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC} {q : Q β}
    {g : Forest.Heard} {h : First.Att.P.Heard} {u : Pub9} (hrd : rd q.1 = some (g, h))
    (hu : q.2 = some u) : P.inOf (seatCQ rd c) c q = inAt c g h u.F := by
  unfold P.inOf seatCQ inAt
  simp only [hrd, hu, Option.bind_some, Option.map_some]
  rfl

/-- A form that the reader hands in names entries at row 0 of the reads' array alone. -/
theorem u3at_make {i : P.Runs.In} {K nW : ℕ} (hL : LenIn i nW) (hW : nW ≤ K) {t n : ℕ} {f : Aff}
    (h : (P.Runs.gather K (P.Runs.u3at i t n)).map (·.1) = some f) : EntsMake i.iU3 [f] := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold P.Runs.gather at hy
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hc := ((cv_u3at (K := K) hL t n) #[] z hz (by simp)).1
  intro g hg x hx
  obtain rfl := List.mem_singleton.1 hg
  obtain ⟨a1, a2, _⟩ := row0_of_cov hW (hc x hx)
  exact ⟨a2, a1⟩

/-- **THE CLAUSE AT A FIXED PART.** -/
theorem planesAtt_of {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC}
    {nU : Array ℕ} {q : Q β}
    (hW : ∀ u T, q.2 = some u → u.F.trees[c.iU3]? = some T → c.nW ≤ T.K)
    (hs : ∀ tlb v, (pi8 q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (pi8 q.1).1 = some tlb → tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ r, readersOfK (seatCQ rd c) c q = some r →
      (∀ e col f, r.1 e col = some f → EntsOk nU q [f]) ∧
        ∀ col f, r.2 col = some f → EntsOk nU q [f] := by
  intro r hr
  unfold readersOfK at hr
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hr
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
      obtain ⟨eg, eu, hk, _, ht⟩ := inAt_parts hx
      rw [← eg] at ht
      have hL : LenIn x.1 c.nW := len_in ht
      obtain ⟨T, hT, eK⟩ := Option.map_eq_some_iff.1 hk
      have hWx : c.nW ≤ x.2 := eK ▸ hW u T hu hT
      have key : ∀ t n f, (P.Runs.gather x.2 (P.Runs.u3at x.1 t n)).map (·.1) = some f →
          EntsOk nU q [f] := fun t n f hf =>
        ents_of_static pi8 hs hU h0 (eu ▸ u3at_make hL hWx hf)
      exact ⟨fun e col f hf => key _ col f hf, fun col f hf => key _ col f hf⟩

/-- **THE CLAUSE AT WHAT IS FIXED AT A STATE THAT PASSES plainThereB.** -/
theorem planesAtt_of_plain {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC}
    (φ : S → Phi β) {nU : Array ℕ} {s : S} (hp : plainThereB c.iU3 c.nW s = true)
    (hs : ∀ tlb v, (pi8 (fixed9 φ s).1).1 = some tlb → (fixed9 φ s).2 = some v →
      StaticOk tlb v.F)
    (hU : ∀ tlb, (pi8 (fixed9 φ s).1).1 = some tlb → tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ r, readersOfK (seatCQ rd c) c (fixed9 φ s) = some r →
      (∀ e col f, r.1 e col = some f → EntsOk nU (fixed9 φ s) [f]) ∧
        ∀ col f, r.2 col = some f → EntsOk nU (fixed9 φ s) [f] := by
  refine planesAtt_of (fun u T hu hT => ?_) hs hU h0
  obtain ⟨U, _, T', e1, _, _, e4, e5⟩ := plain_spent hp
  obtain rfl : U = u.F := Option.some.inj (e1.symm.trans (snap_fork φ hu))
  obtain rfl : T' = T := Option.some.inj (e4.symm.trans hT)
  exact Nat.le_of_eq e5.symm

/-- **THE CLAUSE AT WHAT IS FIXED IN FRONT OF THE BATCHING, FROM THE TABLE's PROMISE.** -/
theorem planesAtt_at {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X)
    (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
    {A : Type} {Fr : Frame} (get : A → P × S) (k m : ℕ) (a : A × Fr.E.Str)
    (hon : onQ 𝔇.N (mgAll 𝔇 Mg₀) links pl get k a) (hu : (get a.1).2.failed = none)
    (hatt : 𝔇.pubD.d5.isAtt m = true)
    (hq : Pub.more (some m) "K5.plain" ∈ (pubSets (mgAll 𝔇 Mg₀).more links pl)[k]?.getD [])
    (c : ParC) (hc : ∀ p, 𝔇.pubD.d5.W.A[m / 2]? = some p → c.iU3 = p.iU3 ∧ c.nW = p.nW)
    (φ : S → Phi β) (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) {nU : Array ℕ}
    (hs : ∀ tlb v, (pi8 (fixed9 φ (get a.1).2).1).1 = some tlb →
      (fixed9 φ (get a.1).2).2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (pi8 (fixed9 φ (get a.1).2).1).1 = some tlb →
      tlb.ix.U.getD 2 none = some c.iU3)
    (h0 : 0 < nU.getD 2 0) :
    ∀ r, readersOfK (seatCQ rd c) c (fixed9 φ (get a.1).2) = some r →
      (∀ e col f, r.1 e col = some f → EntsOk nU (fixed9 φ (get a.1).2) [f]) ∧
        ∀ col f, r.2 col = some f → EntsOk nU (fixed9 φ (get a.1).2) [f] := by
  obtain ⟨p, hp, hok⟩ := plain_of_onQ 𝔇 Mg₀ links pl get k m a hon hu hatt hq
  exact planesAtt_of_plain φ (by rw [(hc p hp).1, (hc p hp).2]; exact hok) hs hU h0

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.inOf_Q
#print axioms VerifiableInference.Desc.LinkJoin.u3at_make
#print axioms VerifiableInference.Desc.LinkJoin.planesAtt_of
#print axioms VerifiableInference.Desc.LinkJoin.planesAtt_of_plain
#print axioms VerifiableInference.Desc.LinkJoin.planesAtt_at
