-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Door.lean
(kind K9's soundness lemma): THEOREMS: from the one equation to the row that is laid,
and the count at the row.
  T2b mk           THE STATEMENT (T2b), of any maker of rows: the row applied to the tables, less
                   its target, is the left side of the equation on the data that the tables hold;
                   and the maker returns somewhere. Tried against two silly makers: not_T2b_idle'
                   (always the empty row), not_T2b_refuse. toy_rowPremises: the public premises can
                   be met (at a ChainCheck without links: a toy). A third silly maker, which forgets
                   the terms, and a toy with a link, an array and a term: Law/ToyRow.lean.
  t2b              (T2b) holds of K9.asRow.
  door_parts       THE INVERSION of K9.door: the equation is made; the rows owed are the claims and
                   the smallness test's equations; the equation is made a row; that row is pushed
                   onto the rows of the segment's group.
  PassesRow        chi is a challenge at which all claims are added, the equation is made and made a
                   row, and THE ROW HOLDS ON THE TABLES.
  batch_sound_row  **THE COUNT AT THE ROW.** If the polynomial in chi that the claims add up to, on
                   the data that the tables hold, is not the zero polynomial, at most d elements of
                   the field are readings of a challenge at which the row holds on the tables.
  K9LawRow, k9LawRow   the lemma as one proposition, with (T2b) and the count at the row.
THE TABLES tab ARE QUANTIFIED OUTSIDE chi. New premises, by name: doorFixed (the data that the
tables hold, as the door's layout, frame and statement read them, do not hang on chi) and
RowPremises (Law/AsRow.lean: inside, sent, room: public facts). Not claimed: that the premises hold
of a segment of the protocol; that the commitments hold the prover to the tables; how chi is drawn.

-/
import Johnson.Desc.First.Batch.Law.AsRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Ans Equation equation asRow St door)

/-! ## (T2b), as a statement of any maker of rows -/

/-- **(T2b).** The second clause (the maker returns somewhere) is met at a constant equation: it
shuts out a maker that refuses everything, and nothing else. -/
def T2b (mk : ReqRows → ReqFrame → Equation → St Unit → Ans (OnBytes.Row × St Unit)) : Prop :=
  (∀ (K : Type) [CommRing K] (ρ : Reading K) (c : ChainCheck) (q : Equation) (d d' : St Unit)
      (row : OnBytes.Row) (N : Nat) (tab : Nat → OnBytes.Part → Nat → K),
    AllK9 q.terms → RowPremises c d.st N q → mk c.rows c.frame q d = .ok (row, d') →
    rowSum ρ d.st N tab row - ρ.val row.target =
      eqValue ρ (dimsOf c) (dataOf c.rows c.frame d.st tab) q) ∧
  ∀ (c : ChainCheck) (d : St Unit), ∃ q x, mk c.rows c.frame q d = .ok x

/-- (T2b) holds of K9.asRow. -/
theorem t2b : T2b asRow :=
  ⟨fun _ _ ρ c q d d' row N tab hk P h => asRow_sum ρ c q d d' row N tab hk P h,
    fun c d => ⟨constantEq zeroE, ({ target := subE zeroE zeroE }, d), by
      simp [asRow, constantEq, K9.termsRow, bind, Except.bind, pure, Except.pure]⟩⟩

theorem allK9_constant (c : E) : AllK9 (constantEq c).terms := by
  intro t ht
  simp [constantEq] at ht

/-- A maker that always returns the empty row does not meet (T2b), wherever the public premises can
be met at all. -/
theorem not_T2b_idle (c : ChainCheck) (d : St Unit) (N : Nat)
    (P : RowPremises c d.st N (constantEq oneE)) : ¬ T2b (fun _ _ _ d => .ok ({}, d)) := by
  intro h
  have h1 := h.1 Cb.Gl.E Reading.gl c (constantEq oneE) d d {} N (fun _ _ _ => 0)
    (allK9_constant oneE) P rfl
  rw [eqValue_constant] at h1
  simp [rowSum, Reading.gl.one, Reading.gl.zero] at h1

/-- A ChainCheck: no link, no array, no oracle message. -/
def toyCheck : ChainCheck := { frame := { shape := default, groups := #[] }, rows := ⟨⟨[]⟩⟩ }

/-- A carried record: no oracle message, no group, no tree. -/
def toyState : St Unit :=
  { st := default, book := { trees := #[], place := #[] }, roots := 0, opened := [], loc := () }

/-- The public premises can be met. -/
theorem toy_rowPremises (S : Statement) (N : Nat) (q : Equation) : RowPremises toyCheck S N q where
  inside := fun born name a h => by simp [toyCheck, reqArray] at h
  sent := fun t _ a o _ h => by simp [toyCheck, ReqFrame.whereIs] at h
  sentMask := fun o _ h => by
    unfold maskOracle at h
    obtain ⟨m, _, hm⟩ := Option.bind_eq_some_iff.mp h
    simp [toyCheck, ReqFrame.whereIs] at hm
  room := fun o h => by
    unfold maskOracle at h
    obtain ⟨m, _, hm⟩ := Option.bind_eq_some_iff.mp h
    simp [toyCheck, ReqFrame.whereIs] at hm

/-- So: a maker that always returns the empty row does not meet (T2b). -/
theorem not_T2b_idle' : ¬ T2b (fun _ _ _ d => .ok ({}, d)) :=
  not_T2b_idle toyCheck toyState 0 (toy_rowPremises _ _ _)

/-- A maker that refuses everything does not meet (T2b), if there is a ChainCheck at all. -/
theorem not_T2b_refuse (c : ChainCheck) (d : St Unit) : ¬ T2b (fun _ _ _ _ => .error "no") := by
  intro h
  obtain ⟨q, x, hx⟩ := h.2 c d
  simp at hx

/-! ## The door -/

/-- **The inversion of K9.door.** -/
theorem door_parts {X : Type} (owed laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (out : K9.Out X) (h : door owed laid L F d = .ok out) :
    ∃ n q G row d1, laid = some n ∧ equation L F = .ok (q, G) ∧ owed = some (G.nClaim + n) ∧
      asRow L.check.rows L.check.frame q d = .ok (row, d1) ∧
      out.d = { d1 with st := Slice.withRow d1.st L.check.group row } ∧ out.F = G ∧ out.L = L := by
  unfold door at h
  obtain ⟨n, hn, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨_, hc, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨y, hy, h⟩ := ok_bind h
  obtain ⟨d2, hd, h⟩ := ok_bind h
  have e := Except.ok.inj h
  have hd' := there_ok hd
  unfold Ground.addRowP at hd'
  split at hd'
  · have e2 := Option.some.inj hd'
    refine ⟨n, x.1, x.2, y.1, y.2, there_ok hn, hx, by simpa using need_ok hc, hy, ?_, ?_, ?_⟩
    · rw [← e, ← e2]
    · rw [← e]
    · rw [← e]
  · simp at hd'

/-! ## The count at the row -/

variable {K : Type} [Field K] (ρ : Reading K)

/-- chi is a challenge at which all claims are added, the steps behind the adding return, the
equation is made and made a row, and the row holds on the tables. dd chi: the carried record at
which the row is made. -/
def PassesRow (add : Fork → Claim → Option Fork) (eqn : LinkCtx → Fork → Ans (Equation × Fork))
    (mk : ReqRows → ReqFrame → Equation → St Unit → Ans (OnBytes.Row × St Unit))
    (tab : Nat → OnBytes.Part → Nat → K) (N : Nat) (L : E → LinkCtx) (F : E → Fork)
    (cls : E → List Claim) (after : E → Fork → Option Fork) (dd : E → St Unit) (chi : E) : Prop :=
  ∃ G H q G' row d', (cls chi).foldlM add (F chi) = some G ∧ after chi G = some H ∧
    eqn (L chi) H = .ok (q, G') ∧
    mk (L chi).check.rows (L chi).check.frame q (dd chi) = .ok (row, d') ∧
    rowSum ρ (dd chi).st N tab row = ρ.val row.target

/-- The ledgers at which the equation is made: behind the adding and the steps behind it. -/
def Reached (add : Fork → Claim → Option Fork) (F : E → Fork) (cls : E → List Claim)
    (after : E → Fork → Option Fork) (chi : E) (H : Fork) : Prop :=
  ∃ G, (cls chi).foldlM add (F chi) = some G ∧ after chi G = some H

/-- The premises at the row, by name, beside Premises. Reach chi H: the ledger H is reached if the
element drawn is chi. -/
structure DoorPremises (eqn : LinkCtx → Fork → Ans (Equation × Fork)) (Reach : E → Fork → Prop)
    (tab : Nat → OnBytes.Part → Nat → K) (N : Nat) (D : Bound K) (L : E → LinkCtx)
    (dd : E → St Unit) : Prop where
  /-- the data that the tables hold, as the door's layout, frame and statement read them, do not
  hang on chi -/
  doorFixed : ∀ chi, dataOf (L chi).check.rows (L chi).check.frame (dd chi).st tab = D
  /-- the public facts of (T2b), at every equation that is made at a ledger that is reached -/
  facts : ∀ chi H q G', Reach chi H → eqn (L chi) H = .ok (q, G') →
    RowPremises (L chi).check (dd chi).st N q

/-- The count at the row, as a statement of any three functions. -/
def T3Row (add : Fork → Claim → Option Fork) (eqn : LinkCtx → Fork → Ans (Equation × Fork))
    (mk : ReqRows → ReqFrame → Equation → St Unit → Ans (OnBytes.Row × St Unit)) : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (tab : Nat → OnBytes.Part → Nat → K) (N : Nat)
      (D : Bound K) (L : E → LinkCtx) (F : E → Fork) (cls : E → List Claim)
      (after : E → Fork → Option Fork) (dd : E → St Unit) (t : List (ℕ × K)) (d : ℕ),
    Premises add ρ D L F cls after t d →
    DoorPremises eqn (Reached add F cls after) tab N D L dd → (∃ y ∈ t, y.2 ≠ 0) →
    Prob.cnt (fun x : K =>
      ∃ chi, ρ.val chi = x ∧ PassesRow ρ add eqn mk tab N L F cls after dd chi) ≤ d

/-- A challenge at which the row holds on the tables passes. -/
theorem passes_of_row (tab : Nat → OnBytes.Part → Nat → K) (N : Nat) (D : Bound K)
    (L : E → LinkCtx) (F : E → Fork) (cls : E → List Claim) (after : E → Fork → Option Fork)
    (dd : E → St Unit)
    (Q : DoorPremises equation (Reached addClaim F cls after) tab N D L dd) (chi : E)
    (h : PassesRow ρ addClaim equation asRow tab N L F cls after dd chi) :
    Passes addClaim equation ρ D L F cls after chi := by
  obtain ⟨G, H, q, G', row, d', h1, h2, h3, h4, h5⟩ := h
  refine ⟨G, H, q, G', h1, h2, h3, ?_⟩
  have e := asRow_sum ρ (L chi).check q (dd chi) d' row N tab (equation_k9 _ _ _ _ h3)
    (Q.facts chi H q G' ⟨G, h1, h2⟩ h3) h4
  rw [Q.doorFixed chi, h5, sub_self] at e
  exact e.symm

/-- **THE COUNT AT THE ROW.** -/
theorem batch_sound_row [Fintype K] (tab : Nat → OnBytes.Part → Nat → K) (N : Nat) (D : Bound K)
    (L : E → LinkCtx) (F : E → Fork) (cls : E → List Claim) (after : E → Fork → Option Fork)
    (dd : E → St Unit) (t : List (ℕ × K)) (d : ℕ) (P : Premises addClaim ρ D L F cls after t d)
    (Q : DoorPremises equation (Reached addClaim F cls after) tab N D L dd)
    (hne : ∃ y ∈ t, y.2 ≠ 0) :
    Prob.cnt (fun x : K => ∃ chi, ρ.val chi = x ∧
      PassesRow ρ addClaim equation asRow tab N L F cls after dd chi) ≤ d :=
  le_trans
    (Prob.cnt_mono fun _ hx => by
      obtain ⟨chi, hc, hp⟩ := hx
      exact ⟨chi, hc, passes_of_row ρ tab N D L F cls after dd Q chi hp⟩)
    (batch_sound ρ D L F cls after t d P hne)

/-- **THE LEMMA WITH THE ROW, as one proposition.** -/
def K9LawRow (add : Fork → Claim → Option Fork) (eqn : LinkCtx → Fork → Ans (Equation × Fork))
    (mk : ReqRows → ReqFrame → Equation → St Unit → Ans (OnBytes.Row × St Unit)) : Prop :=
  T1 add ∧ T2 eqn ∧ T2b mk ∧ T3Row add eqn mk

/-- **K9's own functions meet it.** -/
theorem k9LawRow : K9LawRow addClaim equation asRow :=
  ⟨t1, t2, t2b, fun _ _ _ ρ tab N D L F cls after dd t d P Q hne =>
    batch_sound_row ρ tab N D L F cls after dd t d P Q hne⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.t2b
#print axioms VerifiableInference.Desc.K9L.not_T2b_idle
#print axioms VerifiableInference.Desc.K9L.not_T2b_idle'
#print axioms VerifiableInference.Desc.K9L.not_T2b_refuse
#print axioms VerifiableInference.Desc.K9L.door_parts
#print axioms VerifiableInference.Desc.K9L.batch_sound_row
#print axioms VerifiableInference.Desc.K9L.k9LawRow
