-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/EqShape.lean: THE STRUCTURAL HALF OF TWO PARTS OF THE SMALLNESS TEST's
RUN OF EQUATIONS (eqKeys, eqCounts: Johnson/Desc/First/TailClaims/Equations.lean) AS ONE Bool AND
ONE UPDATE ON A SHAPE WITHOUT A FIELD ELEMENT. General laws: nothing is evaluated.

  EqSh, eqSh      the shape of what such a part reads and leaves: the smallness test's record, the
                  ledger, the list of claims so far (Johnson/Desc/First/Shape/Parts.lean).
  countsB, countsU, countsG   eqCounts' one Bool; its one update, at the heard record's shape; g: no
                  record is heard: a refusal; else the Bool, then the update. countsG_ok,
                  countsG_iff: g returns just where the Bool accepts.
  **eqCounts_shape**   where g returns at the input's shape, eqCounts returns, and the output's
                  shape is what g returned. eqCounts_carries: a yes of the run and a return of g
                  at the input's shape: then g returned the output's shape.
  keysAt, keysB, keysU, keysG, keysG_ok, keysG_iff, **eqKeys_shape**, eqKeys_carries   the same of
                  eqKeys; its update takes the number of claims that stand in front of the list,
                  which the gatherer hands in.
The two laws ask g's return alone and hold at all values: so under the Bool no test on values stands
in either part's way. Over the two laws at all values (EqCountsReturns.lean, EqKeysReturns.lean).
  countsB_no, keysB_no   without a heard record each Bool rejects.
Defaults. No update has a fallback of its own. paidB (in countsU and keysU) marks nothing at a
number outside the list of debts, in silence, as the run's Fork.paid does (Array.modify;
OnBytes/Model/Hide.lean). zkAt reads the size of a call's point with 0 outside the list, as the
run's own text reads the point with the empty point there (g.zk.getD q #[], in Equations.lean's
eqKeys): with an empty point the run's index test passes at index 0 alone, and so does the Bool: it
is as lenient as the run.

Limits. The Bools are sufficient, not necessary (Parts.lean's sizedB asks two sizes that the run
does not test). keysAt takes a whole EqSh and reads its record alone. That the shape in front of
either part passes at any public files is not said. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.EqKeysReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.PscRun VerifiableInference.Desc
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Look (laidDigits padKeyDigits)
open D6.Ret (Open taken)

/-- The shape of what a part of the run reads and leaves. -/
abbrev EqSh : Type := TlSh × LedSh × List ClaimSh

namespace EqSh
def mk (tl : TlSh) (led : LedSh) (claims : List ClaimSh) : EqSh := (tl, led, claims)
def tl (a : EqSh) : TlSh := a.1
def led (a : EqSh) : LedSh := a.2.1
def claims (a : EqSh) : List ClaimSh := a.2.2
end EqSh

def eqSh (tl : HTailF2) (s : St) : EqSh := EqSh.mk (tlSh tl) (ledSh s.1) (s.2.toList.map claimSh)

theorem heard_sh {tl : HTailF2} {g : Forest.Heard} (hg : tl.heard = some g) (s : St) :
    (eqSh tl s).tl.heard = some (heardSh g) := by
  show tl.heard.map heardSh = _
  rw [hg]
  rfl

/-! ## eqCounts -/

/-- The three claims' shapes, of the shapes. -/
def countsClaimsSh (t : TlSh) (g : HeardSh) : List ClaimSh :=
  let KB := 2 ^ (t.kT + t.cK)
  let sz := fun z : Nat => 2 ^ (min (5 + t.kT + t.cK) z - 5)
  [ClaimSh.mk none
      (rowFormSh g.leaves.first (takenSh g.leaves.degrees) g.leaves.start (AffSh.mk [] []))
      [RunSh.mk t.planes 0 0 (sz g.zb0) 0 KB],
    ClaimSh.mk none (AffSh.mk [] [g.sBit]) [RunSh.mk t.planes 1 0 (sz g.zb1) 0 KB],
    ClaimSh.mk none (AffSh.mk [] []) [RunSh.mk t.planes 2 0 KB 0 KB]]

theorem countsClaims_sh (tl : HTailF2) (g : Forest.Heard) :
    countsClaims tl g = countsClaimsSh (tlSh tl) (heardSh g) := by
  unfold countsClaims countsClaimsSh
  rw [← taken_sh]
  rfl

/-- **THE ONE Bool of eqCounts.** -/
def countsB (a : EqSh) : Bool := a.tl.heard.any fun g => openB g.leaves a.led

/-- **THE ONE UPDATE of eqCounts**, at the heard record's shape. -/
def countsU (g : HeardSh) (a : EqSh) : EqSh :=
  EqSh.mk a.tl
    ((a.led.setGot (fillB a.led.got g.leaves.first (takenSh g.leaves.degrees))).setOwed
      (paidB a.led.owed g.owedPlanes))
    (a.claims ++ countsClaimsSh a.tl g)

/-- **g for eqCounts**: the Bool, then the update. -/
def countsG (a : EqSh) : Except String EqSh :=
  match a.tl.heard with
  | none => .error "eqCounts: no record is heard"
  | some g =>
    if openB g.leaves a.led then .ok (countsU g a) else .error "eqCounts: the sumcheck is not open"

theorem countsG_ok {a t : EqSh} (h : countsG a = .ok t) :
    ∃ g, a.tl.heard = some g ∧ openB g.leaves a.led = true ∧ t = countsU g a := by
  unfold countsG at h
  cases hg : a.tl.heard with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    dsimp only at h
    by_cases hb : openB g.leaves a.led = true
    · rw [if_pos hb] at h
      exact ⟨g, rfl, hb, (Except.ok.inj h).symm⟩
    · rw [if_neg hb] at h
      cases h

theorem countsG_iff (a : EqSh) : (∃ t, countsG a = .ok t) ↔ countsB a = true := by
  unfold countsG countsB
  cases a.tl.heard with
  | none => simp
  | some g =>
    dsimp only
    by_cases hb : openB g.leaves a.led = true
    · simp [hb]
    · simp [hb]

/-- **Where g returns at the input's shape, eqCounts returns, and the output's shape is what g
returned.** -/
theorem eqCounts_shape {tl : HTailF2} {F : Fork} {cs : Array Claim} {t : EqSh} (front : Nat)
    (h : countsG (eqSh tl (F, cs)) = .ok t) :
    Ret (eqCounts tl) front (F, cs) fun tl' s' => eqSh tl' s' = t := by
  obtain ⟨gs, hgs, hb, rfl⟩ := countsG_ok h
  cases hg : tl.heard with
  | none =>
    have e : (eqSh tl (F, cs)).tl.heard = none := by
      show tl.heard.map heardSh = _
      rw [hg]
      rfl
    rw [e] at hgs
    cases hgs
  | some g =>
    rw [heard_sh hg (F, cs)] at hgs
    obtain rfl := Option.some.inj hgs
    have hO : Open g.leaves F := open_of_B hb
    refine (eqCounts_returns hg hO front cs).mono ?_
    rintro tl' s' ⟨⟨bf, rfl⟩, hL, hC⟩
    show EqSh.mk (tlSh tl) (ledSh s'.1) (s'.2.toList.map claimSh) = _
    rw [hL, hC, countsClaims_sh, ← taken_sh]
    rfl

/-- A yes of the run, and a return of g at the input's shape: then g returned the output's shape. -/
theorem eqCounts_carries {tl tl' : HTailF2} {F : Fork} {cs : Array Claim} {s' : St} {t : EqSh}
    {front : Nat} (hr : eqCounts tl front (F, cs) = .ok (tl', s'))
    (hg : countsG (eqSh tl (F, cs)) = .ok t) : t = eqSh tl' s' := by
  obtain ⟨a, s₂, e, q⟩ := eqCounts_shape front hg
  rw [hr] at e
  cases e
  exact q.symm

theorem countsB_no {tl : HTailF2} (hg : tl.heard = none) (s : St) :
    countsB (eqSh tl s) = false := by
  show (tl.heard.map heardSh).any _ = false
  rw [hg]
  rfl

/-! ## eqKeys -/

/-- The index test at a piece, of numbers: the call's number of bits, the size of its point. -/
def idxB (n zk : Nat) (p : PieceSh) : Bool :=
  decide (p.b ≤ n) &&
    (decide (min (n - p.b) zk - 0 ≤ 63) && decide (p.off / 2 ^ p.b < 2 ^ (min (n - p.b) zk - 0)))

theorem idx_sh (tl : HTailF2) (g : Forest.Heard) (q : Nat) (p : Piece) :
    idxOk tl g q p = idxB (tl.zOf q).call.n (g.zk.getD q #[]).size (pieceSh p) := by
  unfold idxOk eqIndexOK idxB
  rw [Array.size_extract]
  rfl

/-- The shape of the run that a piece lays, of numbers. -/
def keyRunB (n zk : Nat) (p : PieceSh) : RunSh :=
  RunSh.mk p.tree p.row p.c0 (2 ^ (min (n - p.b + p.a + clog2 p.colsUp) zk - (n - p.b + p.a))) 0
    p.cols

/-- The size of call q's point; outside the list 0, the empty point's: as the run's own text has it
(g.zk.getD q #[], in Equations.lean's eqKeys). -/
def zkAt (g : HeardSh) (q : Nat) : Nat := g.zk.getD q 0

theorem zk_sh (g : Forest.Heard) (q : Nat) : zkAt (heardSh g) q = (g.zk.getD q #[]).size := by
  show (g.zk.toList.map (·.size)).getD q 0 = _
  by_cases hq : q < g.zk.size
  · simp [List.getD, Array.getD, hq]
  · simp [List.getD, Array.getD, hq]

theorem call_sh (tl : HTailF2) (q : Nat) : (tlSh tl).callAt q = callSh (tl.zOf q) := by
  show (if q == 0 then callSh tl.z1 else callSh tl.z2) = callSh (if q == 0 then tl.z1 else tl.z2)
  split <;> rfl

/-- The claim's shape, of the shapes. -/
def keysClaimSh (t : TlSh) (g : HeardSh) : ClaimSh :=
  ClaimSh.mk none ((AffSh.mk [] []).append g.cEnd)
    ([0, 1].flatMap fun q => (t.callAt q).pieces.map (keyRunB (t.callAt q).n (zkAt g q)))

theorem keysClaim_sh (tl : HTailF2) (g : Forest.Heard) :
    keysClaim tl g = keysClaimSh (tlSh tl) (heardSh g) := by
  unfold keysClaim keysClaimSh
  congr 1
  show _ = ([0, 1].flatMap fun q => ((tlSh tl).callAt q).pieces.map
    (keyRunB ((tlSh tl).callAt q).n (zkAt (heardSh g) q)))
  refine List.flatMap_congr fun q hq => ?_
  rw [call_sh tl q, zk_sh]
  show _ = ((tl.zOf q).pieces.toList.map pieceSh).map _
  rw [List.map_map]
  rfl

/-- The Bool behind "a record is heard". -/
def keysAt (g : HeardSh) (a : EqSh) : Bool :=
  a.tl.padKey &&
    ([0, 1].all fun q => (a.tl.callAt q).pieces.all (idxB (a.tl.callAt q).n (zkAt g q))) &&
    a.tl.laid == some g.pub

/-- **THE ONE Bool of eqKeys.** -/
def keysB (a : EqSh) : Bool := a.tl.heard.any fun g => keysAt g a

/-- **THE ONE UPDATE of eqKeys**, at the heard record's shape. front: the number of claims in front
of the list. -/
def keysU (front : Nat) (g : HeardSh) (a : EqSh) : EqSh :=
  EqSh.mk (a.tl.setJoinObj (some (front + a.claims.length)))
    (a.led.setOwed (paidB a.led.owed g.owedJoin)) (a.claims ++ [keysClaimSh a.tl g])

/-- **g for eqKeys**: the Bool, then the update. -/
def keysG (front : Nat) (a : EqSh) : Except String EqSh :=
  match a.tl.heard with
  | none => .error "eqKeys: no record is heard"
  | some g => if keysAt g a then .ok (keysU front g a) else .error "eqKeys: the shape does not pass"

theorem keysG_ok {front : Nat} {a t : EqSh} (h : keysG front a = .ok t) :
    ∃ g, a.tl.heard = some g ∧ keysAt g a = true ∧ t = keysU front g a := by
  unfold keysG at h
  cases hg : a.tl.heard with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    dsimp only at h
    by_cases hb : keysAt g a = true
    · rw [if_pos hb] at h
      exact ⟨g, rfl, hb, (Except.ok.inj h).symm⟩
    · rw [if_neg hb] at h
      cases h

theorem keysG_iff (front : Nat) (a : EqSh) : (∃ t, keysG front a = .ok t) ↔ keysB a = true := by
  unfold keysG keysB
  cases a.tl.heard with
  | none => simp
  | some g =>
    show (∃ t, (if keysAt g a = true then Except.ok (keysU front g a) else _) = .ok t) ↔
      keysAt g a = true
    by_cases hb : keysAt g a = true
    · simp [hb]
    · simp [hb]

/-- **Where g returns at the input's shape, eqKeys returns, and the output's shape is what g
returned.** -/
theorem eqKeys_shape {tl : HTailF2} {F : Fork} {cs : Array Claim} {t : EqSh} (front : Nat)
    (h : keysG front (eqSh tl (F, cs)) = .ok t) :
    Ret (eqKeys tl) front (F, cs) fun tl' s' => eqSh tl' s' = t := by
  obtain ⟨gs, hgs, hb, rfl⟩ := keysG_ok h
  cases hg : tl.heard with
  | none =>
    have e : (eqSh tl (F, cs)).tl.heard = none := by
      show tl.heard.map heardSh = _
      rw [hg]
      rfl
    rw [e] at hgs
    cases hgs
  | some g =>
    rw [heard_sh hg (F, cs)] at hgs
    obtain rfl := Option.some.inj hgs
    have h' : ((padKeyDigits tl &&
        ([0, 1].all fun q => ((tlSh tl).callAt q).pieces.all
          (idxB ((tlSh tl).callAt q).n (zkAt (heardSh g) q)))) &&
        ((laidDigits tl).map (·.toList) == some g.shape.pub.toList)) = true := hb
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    obtain ⟨⟨hk, hi⟩, hl⟩ := h'
    have hi' : ∀ q ∈ [0, 1], ∀ p ∈ (tl.zOf q).pieces.toList, idxOk tl g q p = true := by
      intro q hq p hp
      have a := List.all_eq_true.1 hi q hq
      rw [call_sh tl q, zk_sh] at a
      rw [idx_sh]
      exact List.all_eq_true.1 a (pieceSh p) (List.mem_map.2 ⟨p, hp, rfl⟩)
    have hl' : laidDigits tl = some g.shape.pub := by
      have a := beq_iff_eq.1 hl
      cases hd : laidDigits tl with
      | none =>
        rw [hd] at a
        cases a
      | some r =>
        rw [hd] at a
        rw [Array.toList_inj.1 (Option.some.inj a)]
    refine (eqKeys_returns hg hk hi' hl' front F cs).mono ?_
    rintro tl' s' ⟨rfl, c, rfl, hc⟩
    show EqSh.mk ((tlSh tl).setJoinObj (some (front + cs.size))) (ledSh (F.paid g.owedJoin))
      ((cs.push c).toList.map claimSh) = _
    rw [ledSh_paid, claims_push, hc, keysClaim_sh]
    show _ = EqSh.mk ((tlSh tl).setJoinObj (some (front + (cs.toList.map claimSh).length))) _ _
    rw [List.length_map, Array.length_toList]
    rfl

/-- A yes of the run, and a return of g at the input's shape: then g returned the output's shape. -/
theorem eqKeys_carries {tl tl' : HTailF2} {F : Fork} {cs : Array Claim} {s' : St} {t : EqSh}
    {front : Nat} (hr : eqKeys tl front (F, cs) = .ok (tl', s'))
    (hg : keysG front (eqSh tl (F, cs)) = .ok t) : t = eqSh tl' s' := by
  obtain ⟨a, s₂, e, q⟩ := eqKeys_shape front hg
  rw [hr] at e
  cases e
  exact q.symm

theorem keysB_no {tl : HTailF2} (hg : tl.heard = none) (s : St) : keysB (eqSh tl s) = false := by
  show (tl.heard.map heardSh).any _ = false
  rw [hg]
  rfl

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.heard_sh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.countsClaims_sh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.countsG_ok
#print axioms VerifiableInference.Desc.First.TailClaims.Law.countsG_iff
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqCounts_shape
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqCounts_carries
#print axioms VerifiableInference.Desc.First.TailClaims.Law.countsB_no
#print axioms VerifiableInference.Desc.First.TailClaims.Law.idx_sh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.zk_sh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.call_sh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keysClaim_sh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keysG_ok
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keysG_iff
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqKeys_shape
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqKeys_carries
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keysB_no
#print axioms VerifiableInference.Desc.First.TailClaims.Law.EqSh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.EqSh.mk
#print axioms VerifiableInference.Desc.First.TailClaims.Law.EqSh.tl
#print axioms VerifiableInference.Desc.First.TailClaims.Law.EqSh.led
#print axioms VerifiableInference.Desc.First.TailClaims.Law.EqSh.claims
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqSh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.countsClaimsSh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.countsB
#print axioms VerifiableInference.Desc.First.TailClaims.Law.countsU
#print axioms VerifiableInference.Desc.First.TailClaims.Law.countsG
#print axioms VerifiableInference.Desc.First.TailClaims.Law.idxB
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keyRunB
#print axioms VerifiableInference.Desc.First.TailClaims.Law.zkAt
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keysClaimSh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keysAt
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keysB
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keysU
#print axioms VerifiableInference.Desc.First.TailClaims.Law.keysG
