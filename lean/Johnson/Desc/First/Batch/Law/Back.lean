-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Back.lean
(kind K9's soundness lemma): THEOREMS: the equation's block, backward: no draw, no
error: IF THE ROW THAT K9.door HAS LAID HOLDS ON THE TABLES, THE LEDGER's VALUE ON THE DATA THAT THE
TABLES HOLD IS 0.
  takeN_bits, door_bits   the door changes no table's numbers of row bits and place bits: so "the
                  row applied to the tables" (rowSum) is the same at the statement in front of the
                  door and at the statement behind it.
  dataOf_bits     nor do the data that the tables hold change.
  door_back       door .. = .ok out: a row was pushed onto the rows of the segment's group; and if
                  that row holds on the tables, then Fork.total of the ledger in front, in the world
                  of dataOf, is 0: rowSum, dataOf and the premises ALL READ AT THE STATEMENT BEHIND
                  THE DOOR.
  oneEquation_back   the same of the block K9.oneEquation, through Block.step, at any state with
                  K9's lens: in the letter "one" of the segment's law (oneK, Law/ForLink.lean).
It puts (T2) and (T2b) together. The premises are RowPremises (public facts), at the equation made.

-/
import Johnson.Desc.First.Batch.Law.ForLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Ans Equation equation asRow St door takeN)

/-- Two statements give every table the same numbers of row bits and place bits. -/
def SameBits (S S' : Statement) : Prop :=
  ∀ o part, S'.rowBits o part = S.rowBits o part ∧ S'.placeBits o part = S.placeBits o part

theorem SameBits.refl (S : Statement) : SameBits S S := fun _ _ => ⟨rfl, rfl⟩

theorem SameBits.trans {S S' S'' : Statement} (h : SameBits S S') (h' : SameBits S' S'') :
    SameBits S S'' := fun o part =>
  ⟨(h' o part).1.trans (h o part).1, (h' o part).2.trans (h o part).2⟩

theorem takeMaskP_bits {X : Type} (d d' : St X) (o n : Nat)
    (h : Ground.takeMaskP d o = some (n, d')) : SameBits d.st d'.st := by
  unfold Ground.takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.mp h
    have e2 : d' = _ := (congrArg Prod.snd e).symm
    rw [e2]
    intro o' part
    simp only [Statement.rowBits, Statement.placeBits, Array.getElem?_modify]
    by_cases hoo : o = o'
    · subst hoo
      cases d.st.oracles[o]? <;> simp
    · simp [hoo]
  · simp at h

theorem takeN_bits {X : Type} (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat)
    (x : List Nat × St X), takeN o n d acc = .ok x → SameBits d.st x.2.st
  | 0, d, acc, x, h => by
    have e : (acc.reverse, d) = x := Except.ok.inj h
    rw [← e]
    exact SameBits.refl _
  | n + 1, d, acc, x, h => by
    rw [takeN] at h
    obtain ⟨y, hy, h⟩ := ok_bind h
    exact (takeMaskP_bits d y.2 o y.1 (there_ok hy)).trans (takeN_bits o n y.2 _ x h)

theorem asRow_bits {X : Type} (Rr : ReqRows) (f : ReqFrame) (q : Equation) (d d' : St X)
    (row : OnBytes.Row) (h : asRow Rr f q d = .ok (row, d')) : SameBits d.st d'.st := by
  unfold asRow at h
  obtain ⟨row0, _, h⟩ := ok_bind h
  by_cases he : q.onMasks.isEmpty = true
  · simp only [he, if_true] at h
    have e : d = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
    exact SameBits.refl _
  · simp only [he, Bool.false_eq_true, if_false] at h
    obtain ⟨m, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨o', _, h⟩ := ok_bind h
    obtain ⟨x, hx, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    have e : x.2 = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
    exact takeN_bits o' _ d [] x hx

theorem withRow_bits (S : Statement) (g : Nat) (row : OnBytes.Row) :
    SameBits S (Slice.withRow S g row) := fun _ _ => ⟨rfl, rfl⟩

variable {K : Type} [CommRing K] (ρ : Reading K)

theorem rowSum_bits (S S' : Statement) (h : SameBits S S') (N : Nat)
    (tab : Nat → OnBytes.Part → Nat → K) (row : OnBytes.Row) :
    rowSum ρ S' N tab row = rowSum ρ S N tab row := by
  unfold rowSum
  apply Finset.sum_congr rfl
  intro o _
  rw [(h o .main).1, (h o .main).2, (h o .mask).1, (h o .mask).2]

/-- The data that the tables hold are read through the tables' numbers of bits alone. -/
theorem dataOf_bits (Rr : ReqRows) (f : ReqFrame) (S S' : Statement) (h : SameBits S S')
    (tab : Nat → OnBytes.Part → Nat → K) : dataOf Rr f S' tab = dataOf Rr f S tab := by
  unfold dataOf
  congr 1
  funext born name i c
  cases reqArray Rr.layout born name with
  | none => rfl
  | some a =>
    dsimp only
    cases f.whereIs born a.message with
    | none => rfl
    | some o =>
      dsimp only
      rw [(h o .main).1, (h o .main).2]

theorem rowPremises_bits (c : ChainCheck) (S S' : Statement) (h : SameBits S S') (N : Nat)
    (q : Equation) (P : RowPremises c S' N q) : RowPremises c S N q :=
  ⟨P.inside, P.sent, P.sentMask, fun o ho => by
    have r := P.room o ho
    rw [(h o .mask).1, (h o .mask).2] at r
    exact r⟩

/-- **The equation's block, backward.** Everything is read at the statement BEHIND the door. -/
theorem door_back {X : Type} (owed laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (out : K9.Out X) (N : Nat) (tab : Nat → OnBytes.Part → Nat → K)
    (P : ∀ q G, equation L F = .ok (q, G) → RowPremises L.check out.d.st N q)
    (h : door owed laid L F d = .ok out) :
    SameBits d.st out.d.st ∧ ∃ (row : OnBytes.Row) (d1 : St X),
      out.d = { d1 with st := Slice.withRow d1.st L.check.group row } ∧
      (rowSum ρ out.d.st N tab row = ρ.val row.target →
        F.total ρ (worldAt ρ L F (dataOf L.check.rows L.check.frame out.d.st tab)) = 0) := by
  obtain ⟨n, q, G, row, d1, _, hq, _, hr, ho, _, _⟩ := door_parts owed laid L F d out h
  have hb : SameBits d.st out.d.st := by
    rw [ho]
    exact (asRow_bits _ _ _ _ _ _ hr).trans (withRow_bits _ _ _)
  refine ⟨hb, row, d1, ho, fun hh => ?_⟩
  rw [rowSum_bits ρ _ _ hb] at hh
  have e := asRow_sum ρ L.check q d d1 row N tab (equation_k9 _ _ _ _ hq)
    (rowPremises_bits _ _ _ hb N q (P q G hq)) hr
  rw [hh, sub_self] at e
  rw [dataOf_bits _ _ _ _ hb, ← equation_total ρ _ L F G q hq]
  exact e.symm

/-- **The equation's block, backward, through Block.step**, at any state T with K9's lens: where the
block says yes, a row was pushed onto the rows of the segment's group; and if that row holds on the
tables, the ledger's value in the state in front, read there, on the data that the tables hold,
is 0. -/
theorem oneEquation_back {T Cl : Type} (X : K9.Lens T) (p : K9.Where) (ft : Nat) (s : T)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat) (N : Nat)
    (tab : Nat → OnBytes.Part → Nat → K)
    (P : ∀ a q G S, X.get? s = some a → equation a.L a.F = .ok (q, G) → SameBits a.d.st S →
      RowPremises a.L.check S N q)
    (h : (K9.oneEquation (Cl := Cl) X p).step ft s rs cols = .ok (s', k)) :
    ∃ (a : K9.Part) (out : K9.Out Unit) (row : OnBytes.Row) (d1 : St Unit), X.get? s = some a ∧
      s' = X.set s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } ∧
      out.d = { d1 with st := Slice.withRow d1.st a.L.check.group row } ∧
      SameBits a.d.st out.d.st ∧
      (rowSum ρ out.d.st N tab row = ρ.val row.target →
        oneK X ρ s s (dataOf a.L.check.rows a.L.check.frame out.d.st tab) = 0) := by
  unfold Block.step at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨t', hdec, h⟩ := ok_bind h
  have e : t' = s' := congrArg Prod.fst (Except.ok.inj h)
  subst e
  simp only [K9.oneEquation] at hdec
  obtain ⟨a, ha, hdec⟩ := ok_bind hdec
  obtain ⟨out, ho, hdec⟩ := ok_bind hdec
  have ha' := there_ok ha
  have hb0 : SameBits a.d.st out.d.st := by
    obtain ⟨_, _, _, row, d1, _, _, _, hr, hd, _, _⟩ := door_parts a.owed a.laid a.L a.F a.d out ho
    rw [hd]
    exact (asRow_bits _ _ _ _ _ _ hr).trans (withRow_bits _ _ _)
  obtain ⟨hb, row, d1, hd, hback⟩ := door_back ρ a.owed a.laid a.L a.F a.d out N tab
    (fun q G hq => P a q G _ ha' hq hb0) ho
  refine ⟨a, out, row, d1, ha', (Except.ok.inj hdec).symm, hd, hb, fun hh => ?_⟩
  simp only [oneK, ha']
  exact hback hh

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.oneEquation_back
#print axioms VerifiableInference.Desc.K9L.door_back
