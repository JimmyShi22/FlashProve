-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/EqKeysReturns.lean: the first part of the smallness test's run of
equations (eqKeys, Johnson/Desc/First/TailClaims/Equations.lean: the claim on the lookup's key
vectors) RETURNS wherever four conditions on the shape of its input hold, at all values. A general
law: nothing is evaluated.

The four. A record is heard; the padding key of both calls is 0 (padKeyDigits); at each piece of
both calls the piece's index fits the call's point (idxOk: three comparisons of numbers: the piece's
b is at most the call's n; then eqIndexOK's two, which read the point's length alone); the host's
count of padding places (laidDigits) returns the heard shape's own counts. padKeyDigits and
laidDigits are the library's own plain functions (Johnson/Desc/First/Look/Laid.lean): the counting
alone, in the run's order.

  rowStep, pieceStep, callStep   the count's steps, by row, piece and call.
  laid_opens      what a return of laidDigits says, in these steps.
  foldlM_cons_some   a fold in Option that returns, cut at its first step.
  idxOk           the third condition at one piece, with code.
  zcSize          the number of coordinates of the point of the columns' weights at a piece.
  keyRunSh, keysClaim   the shape of the run that a piece lays (array, row, first entry, the number
                  of weights: a power of 2, the first weight, the length), and of the claim
                  (Johnson/Desc/First/Shape/Parts.lean).
  **eqKeys_returns**   the run returns; the record behind is the record in front with the claim's
                  number laid; the ledger behind is the ledger in front with one owed mark paid; one
                  claim more lies on the list, with one run a piece, of these shapes.
  eqKeys_no_heard, eqKeys_no_key, eqKeys_bad_index   three of the four conditions are not idle:
                  without a heard record, with a padding key that is not 0, and with the first
                  piece's index out of its point's range, the run refuses, each under its own name.
                  For the fourth (the count) there is no such theorem here.
The run branches on values at one place (a table of weights is made anew where the point differs
from the last one): both arms leave a table with one entry for each value of the point's bits: that
is the loop's invariant.

Limits. What the claim's constant, coefficients and weights are is not said. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.TailClaims.EqCountsReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Look (laidDigits padKeyDigits)

/-- The count's step at one row of a piece. -/
def rowStep (tl : HTailF2) (q : Nat) (p : Piece) (read : Array Nat) (rr : Nat) :
    Option (Array Nat) :=
  HTailF2.placesRead tl.f9.dT (tl.f9.iota.getD q 0) (tl.f9.first.getD q 0)
    (2 ^ tl.f9.iota.getD q 0 + 1) read (p.off + rr * p.CP) p.Cp

/-- At one piece. -/
def pieceStep (tl : HTailF2) (q : Nat) (read : Array Nat) (p : Piece) : Option (Array Nat) :=
  (List.range p.Rp).foldlM (rowStep tl q p) read

/-- At one call. -/
def callStep (tl : HTailF2) (read : Array Nat) (q : Nat) : Option (Array Nat) :=
  (tl.zOf q).pieces.toList.foldlM (pieceStep tl q) read

/-- What a return of laidDigits says. -/
theorem laid_opens {tl : HTailF2} {pub : Array Nat} (h : laidDigits tl = some pub) :
    ∃ r, [0, 1].foldlM (callStep tl) (Forest.noPub tl.f9) = some r ∧
      (r.all fun x => decide (x ≤ 2 ^ tl.f9.dT)) = true ∧
      (r.map fun x => 2 ^ tl.f9.dT - x) = pub := by
  unfold laidDigits at h
  simp only [← Array.foldlM_toList] at h
  change (([0, 1].foldlM (callStep tl) (Forest.noPub tl.f9)).bind fun r =>
    if (r.all fun x => decide (x ≤ 2 ^ tl.f9.dT)) = true then
      some (r.map fun x => 2 ^ tl.f9.dT - x) else none) = some pub at h
  cases hr : [0, 1].foldlM (callStep tl) (Forest.noPub tl.f9) with
  | none =>
    rw [hr] at h
    cases h
  | some r =>
    rw [hr] at h
    have h' : (if (r.all fun x => decide (x ≤ 2 ^ tl.f9.dT)) = true then
      some (r.map fun x => 2 ^ tl.f9.dT - x) else none) = some pub := h
    by_cases ha : (r.all fun x => decide (x ≤ 2 ^ tl.f9.dT)) = true
    · rw [if_pos ha] at h'
      exact ⟨r, rfl, ha, Option.some.inj h'⟩
    · rw [if_neg ha] at h'
      cases h'

/-- A fold in Option that returns, cut at its first step. -/
theorem foldlM_cons_some {α β : Type} {f : β → α → Option β} {a : α} {l : List α} {b r : β}
    (h : (a :: l).foldlM f b = some r) : ∃ c, f b a = some c ∧ l.foldlM f c = some r := by
  rw [List.foldlM_cons] at h
  cases hc : f b a with
  | none =>
    rw [hc] at h
    cases h
  | some c =>
    rw [hc] at h
    exact ⟨c, rfl, h⟩

/-- The point of the columns' weights at a piece of call q: its number of coordinates. -/
def zcSize (tl : HTailF2) (g : Forest.Heard) (q : Nat) (p : Piece) : Nat :=
  min ((tl.zOf q).call.n - p.b + p.a + clog2 p.CP) (g.zk.getD q #[]).size -
    ((tl.zOf q).call.n - p.b + p.a)

/-- The shape of the run that a piece lays. -/
def keyRunSh (tl : HTailF2) (g : Forest.Heard) (q : Nat) (p : Piece) : RunSh :=
  RunSh.mk p.tree p.row p.c0 (2 ^ zcSize tl g q p) 0 p.Cp

/-- The index test at a piece. -/
def idxOk (tl : HTailF2) (g : Forest.Heard) (q : Nat) (p : Piece) : Bool :=
  decide (p.b ≤ (tl.zOf q).call.n) &&
    eqIndexOK ((g.zk.getD q #[]).extract 0 ((tl.zOf q).call.n - p.b)) (p.off / 2 ^ p.b)

/-- The shape of the claim: its form is a constant less the heard record's end value; one run a
piece. -/
def keysClaim (tl : HTailF2) (g : Forest.Heard) : ClaimSh :=
  ClaimSh.mk none ((AffSh.mk [] []).append (affSh g.cEnd))
    ([0, 1].flatMap fun q => (tl.zOf q).pieces.toList.map (keyRunSh tl g q))

/-- **The claim on the lookup's key vectors: the run returns**, at all values. -/
theorem eqKeys_returns {tl : HTailF2} {g : Forest.Heard} (hg : tl.heard = some g)
    (hk : padKeyDigits tl = true)
    (hi : ∀ q ∈ [0, 1], ∀ p ∈ (tl.zOf q).pieces.toList, idxOk tl g q p = true)
    (hl : laidDigits tl = some g.shape.pub) (front : Nat) (F : Fork) (cs : Array Claim) :
    Ret (eqKeys tl) front (F, cs) fun tl' s' =>
      tl' = { tl with joinObj9 := some (front + cs.size) } ∧
      ∃ c, s' = (F.paid g.owedJoin, cs.push c) ∧
        claimSh c = keysClaim tl g := by
  obtain ⟨rf, hfold, hall, hmap⟩ := laid_opens hl
  unfold eqKeys eqPaddingLaid eqJoinAdded
  refine Ret.bind (Ret.get _ hg (Q := fun a s' => a = g ∧ s' = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro g' _ ⟨hg', rfl⟩
  rw [hg']
  dsimp only
  refine Ret.bind (Ret.mustAs _ hk (Q := fun _ s' => s' = (F, cs)) rfl) ?_
  rintro _ _ rfl
  -- the loop over the two calls
  refine Ret.bind (Ret.forInList
    (I := fun rest (b : MProd E (MProd (Array E) (MProd (Array Nat) (MProd (Array Run2)
        (Array E))))) s' => s' = (F, cs) ∧ rest.foldlM (callStep tl) b.2.2.1 = some rf ∧
      b.2.2.2.2.size = 2 ^ b.2.1.size ∧ (∀ q ∈ rest, q ∈ [0, 1]) ∧
      b.2.2.2.1.toList.map runSh ++ (rest.flatMap fun q =>
        (tl.zOf q).pieces.toList.map (keyRunSh tl g q)) =
        [0, 1].flatMap fun q => (tl.zOf q).pieces.toList.map (keyRunSh tl g q))
    ?_ [0, 1] _ (F, cs) ⟨rfl, hfold, rfl, fun _ h => h, rfl⟩) ?_
  · -- one call
    rintro q rest ⟨constant, point, read, runs, table⟩ _ ⟨rfl, hf, hT, hq, hR⟩
    obtain ⟨rq, hrq, hrest⟩ := foldlM_cons_some hf
    dsimp only at hT hR hrq ⊢
    refine Ret.bind (Ret.forInArray
      (I := fun rest' (b : MProd (Array E) (MProd (Array Nat) (MProd (Array Run2) (Array E))))
          s' => s' = (F, cs) ∧ rest'.foldlM (pieceStep tl q) b.2.1 = some rq ∧
        b.2.2.2.size = 2 ^ b.1.size ∧ (∀ p ∈ rest', p ∈ (tl.zOf q).pieces.toList) ∧
        b.2.2.1.toList.map runSh ++ rest'.map (keyRunSh tl g q) =
          runs.toList.map runSh ++ (tl.zOf q).pieces.toList.map (keyRunSh tl g q))
      ?_ _ _ (F, cs) ⟨rfl, hrq, hT, fun _ h => h, rfl⟩) ?_
    · -- one piece
      rintro p rest' ⟨point', read', runs', table'⟩ _ ⟨rfl, hf', hT', hp, hR'⟩
      obtain ⟨rp, hrp, hrest'⟩ := foldlM_cons_some hf'
      dsimp only at hT' hR' hrp ⊢
      refine Ret.bind (Ret.mustAs _ (hi q (hq q (List.mem_cons_self ..)) p
        (hp p (List.mem_cons_self ..))) (Q := fun _ s' => s' = (F, cs)) rfl) ?_
      rintro _ _ rfl
      have hz : ((g.zk.getD q #[]).extract ((tl.zOf q).call.n - p.b + p.a)
          ((tl.zOf q).call.n - p.b + p.a + clog2 p.CP)).size = zcSize tl g q p := by
        rw [Array.size_extract]
        rfl
      have A : (eqTab ((g.zk.getD q #[]).extract ((tl.zOf q).call.n - p.b + p.a)
          ((tl.zOf q).call.n - p.b + p.a + clog2 p.CP))).size = 2 ^ zcSize tl g q p := by
        rw [OnBytes.Road.eqTab_size, hz]
      have B : ¬ (((g.zk.getD q #[]).extract ((tl.zOf q).call.n - p.b + p.a)
          ((tl.zOf q).call.n - p.b + p.a + clog2 p.CP)) != point') = true →
          table'.size = 2 ^ zcSize tl g q p := by
        intro hc
        have e : (g.zk.getD q #[]).extract ((tl.zOf q).call.n - p.b + p.a)
          ((tl.zOf q).call.n - p.b + p.a + clog2 p.CP) = point' := by simpa using hc
        rw [hT', ← e, hz]
      refine Ret.ite _ (fun hc => ?_) (fun hc => ?_) <;>
      ( refine Ret.bind (Ret.pure PUnit.unit (Q := fun _ s' => s' = (F, cs)) rfl) ?_
        rintro _ _ rfl
        refine Ret.bind (Ret.forInList
          (I := fun rest'' r s' => s' = (F, cs) ∧ rest''.foldlM (rowStep tl q p) r = some rp)
          ?_ _ _ (F, cs) ⟨rfl, hrp⟩) ?_
        · rintro rr rest'' r _ ⟨rfl, hf''⟩
          obtain ⟨r1, hr1, hrest''⟩ := foldlM_cons_some hf''
          refine Ret.bind (Ret.get _ hr1 (Q := fun a s' => a = r1 ∧ s' = (F, cs)) ⟨rfl, rfl⟩) ?_
          rintro a _ ⟨ha, rfl⟩
          rw [ha]
          refine Ret.bind (Ret.pure PUnit.unit (Q := fun _ s' => s' = (F, cs)) rfl) ?_
          rintro _ _ rfl
          exact Ret.pure _ ⟨r1, rfl, rfl, hrest''⟩
        · rintro r _ ⟨rfl, hr⟩
          have er : r = rp := by simpa using hr
          refine Ret.bind (Ret.pure PUnit.unit (Q := fun _ s' => s' = (F, cs)) rfl) ?_
          rintro _ _ rfl
          refine Ret.pure _ ⟨_, rfl, rfl, ?_, ?_, fun x hx => hp x (List.mem_cons_of_mem _ hx), ?_⟩
          · rw [er]
            exact hrest'
          · first
              | exact OnBytes.Road.eqTab_size _
              | exact hT'
          · rw [← hR']
            dsimp only
            rw [Array.toList_push, List.map_append, List.append_assoc]
            congr 1
            show [(p.tree, p.row, p.c0, _, 0, p.Cp)] ++ _ = keyRunSh tl g q p :: _
            first
              | rw [A]; rfl
              | rw [B hc]; rfl )
    · -- behind the pieces
      rintro ⟨pt, rd, rn, tb⟩ _ ⟨rfl, hrd, hT2, -, hR2⟩
      have er : rd = rq := by simpa using hrd
      dsimp only at hT2 hR2 ⊢
      refine Ret.bind (Ret.pure PUnit.unit (Q := fun _ s' => s' = (F, cs)) rfl) ?_
      rintro _ _ rfl
      refine Ret.pure _ ⟨_, rfl, rfl, ?_, hT2, fun x hx => hq x (List.mem_cons_of_mem _ hx), ?_⟩
      · rw [er]
        exact hrest
      · rw [← hR, List.flatMap_cons, ← List.append_assoc, ← hR2]
        simp
  · -- behind the calls
    rintro ⟨c0, pt, rd, rn, tb⟩ _ ⟨rfl, hrd, -, -, hR⟩
    have er : rd = rf := by simpa using hrd
    dsimp only at hR ⊢
    refine Ret.bind (Ret.forInList (I := fun _ _ s' => s' = (F, cs)) ?_ _ _ (F, cs) rfl) ?_
    · rintro y rest b _ rfl
      refine Ret.bind (Ret.pure PUnit.unit (Q := fun _ s' => s' = (F, cs)) rfl) ?_
      rintro _ _ rfl
      exact Ret.pure _ ⟨_, rfl, rfl⟩
    · rintro cst _ rfl
      refine Ret.bind (Ret.mustAs _ (by rw [er]; exact hall)
        (Q := fun _ s' => s' = (F, cs)) rfl) ?_
      rintro _ _ rfl
      refine Ret.bind (Ret.mustAs _ (by rw [er, hmap]; simp)
        (Q := fun _ s' => s' = (F, cs)) rfl) ?_
      rintro _ _ rfl
      refine Ret.bind (Ret.claims (Q := fun n s' => n = front + cs.size ∧ s' = (F, cs))
        ⟨rfl, rfl⟩) ?_
      rintro n _ ⟨hn, rfl⟩
      refine Ret.bind (Ret.emit _ (Q := fun _ s' => ∃ c, s' = (F, cs.push c) ∧
        claimSh c = keysClaim tl g) ⟨_, rfl, by
            show ClaimSh.mk none (affSh (Aff.ofConst _ - g.cEnd)) (rn.toList.map runSh) = _
            unfold keysClaim
            rw [affSh_sub, affSh_ofConst, ← hR]
            simp⟩) ?_
      rintro _ _ ⟨c, rfl, hc⟩
      refine Ret.bind (Ret.paid _ (Q := fun _ s' => s' = (F.paid g.owedJoin, cs.push c)) rfl) ?_
      rintro _ _ rfl
      exact Ret.pure _ ⟨by rw [hn], c, rfl, hc⟩

/-- Without a heard record it refuses. -/
theorem eqKeys_no_heard {tl : HTailF2} (hg : tl.heard = none) (front : Nat) (F : Fork)
    (cs : Array Claim) : eqKeys tl front (F, cs) = .error "linJoin9:829" := by
  unfold eqKeys
  rw [hg]
  rfl

/-- With a padding key that is not 0 it refuses. -/
theorem eqKeys_no_key {tl : HTailF2} {g : Forest.Heard} (hg : tl.heard = some g)
    (hk : padKeyDigits tl = false) (front : Nat) (F : Fork) (cs : Array Claim) :
    eqKeys tl front (F, cs) = .error "internal-f-padding-key" := by
  unfold eqKeys
  rw [hg, run_bind (a := g) (s' := (F, cs)) rfl]
  dsimp only
  refine run_err ?_
  show EqM.mustAs _ (padKeyDigits tl) front (F, cs) = _
  rw [hk]
  rfl

/-- With the first piece's index out of its point's range it refuses. -/
theorem eqKeys_bad_index {tl : HTailF2} {g : Forest.Heard} {p : Piece} {ps : List Piece}
    (hg : tl.heard = some g) (hk : padKeyDigits tl = true)
    (hp : (tl.zOf 0).pieces.toList = p :: ps) (hb : idxOk tl g 0 p = false) (front : Nat)
    (F : Fork) (cs : Array Claim) : eqKeys tl front (F, cs) = .error "internal-eq-index" := by
  unfold eqKeys
  rw [hg, run_bind (a := g) (s' := (F, cs)) rfl]
  dsimp only
  rw [run_bind (a := ()) (s' := (F, cs)) (by
    show EqM.mustAs _ (padKeyDigits tl) front (F, cs) = _
    rw [hk]
    rfl)]
  refine run_err ?_
  rw [List.forIn_cons]
  refine run_err ?_
  dsimp only
  refine run_err ?_
  rw [← Array.forIn_toList, hp, List.forIn_cons]
  refine run_err ?_
  dsimp only
  refine run_err ?_
  show EqM.mustAs _ (idxOk tl g 0 p) front (F, cs) = _
  rw [hb]
  rfl

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.laid_opens
#print axioms VerifiableInference.Desc.First.TailClaims.Law.foldlM_cons_some
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqKeys_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqKeys_no_heard
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqKeys_no_key
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqKeys_bad_index
