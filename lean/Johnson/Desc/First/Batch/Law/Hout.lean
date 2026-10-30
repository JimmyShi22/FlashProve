-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Hout.lean
(kind K9's soundness lemma): THEOREMS: the equation's block between the two relations
at its boundaries, through Block.step, at any state T with K9's lens.
  GroupHoldsAt   BEHIND: every open row of the segment's group, as the state's statement holds them,
                 holds on the tables (rowSum = target).
  dataAt         the data that the tables hold, read by the state's own layout, frame and statement.
  oneEquation_joint   where the block says yes: if GroupHoldsAt holds behind it, then IN FRONT the
                 one equation's value on dataAt is 0 (oneK .. = 0: the sentence at which the law of
                 the segment ends), and GroupHoldsAt holds in front too (the rows that were there).
Beneath: door_group (the door's own test "the group is there") and asRow_groups (making the row
turns no group).
The hypotheses: the lens's law; RowPremises (public facts) at the equation made.

-/
import Johnson.Desc.First.Batch.Law.AfterKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Ans Equation equation asRow St door takeN Lens)

theorem takeMaskP_groups {X : Type} (d d' : St X) (o n : Nat)
    (h : Ground.takeMaskP d o = some (n, d')) : d'.st.groups = d.st.groups := by
  unfold Ground.takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.mp h
    have e2 : d' = _ := (congrArg Prod.snd e).symm
    rw [e2]
  · simp at h

theorem takeN_groups {X : Type} (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat)
    (x : List Nat × St X), takeN o n d acc = .ok x → x.2.st.groups = d.st.groups
  | 0, d, acc, x, h => by
    have e : (acc.reverse, d) = x := Except.ok.inj h
    rw [← e]
  | n + 1, d, acc, x, h => by
    rw [takeN] at h
    obtain ⟨y, hy, h⟩ := ok_bind h
    rw [takeN_groups o n y.2 _ x h, takeMaskP_groups d y.2 o y.1 (there_ok hy)]

/-- Making the row turns no group. -/
theorem asRow_groups {X : Type} (Rr : ReqRows) (f : ReqFrame) (q : Equation) (d d' : St X)
    (row : OnBytes.Row) (h : asRow Rr f q d = .ok (row, d')) : d'.st.groups = d.st.groups := by
  unfold asRow at h
  obtain ⟨row0, _, h⟩ := ok_bind h
  by_cases he : q.onMasks.isEmpty = true
  · simp only [he, if_true] at h
    have e : d = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
  · simp only [he, Bool.false_eq_true, if_false] at h
    obtain ⟨m, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨o', _, h⟩ := ok_bind h
    obtain ⟨x, hx, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    have e : x.2 = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
    exact takeN_groups o' _ d [] x hx

/-- The door's own test: the segment's group is there. -/
theorem door_group {X : Type} (owed laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (out : K9.Out X) (h : door owed laid L F d = .ok out) :
    (d.st.groups[L.check.group]?).isSome = true := by
  unfold door at h
  obtain ⟨n, _, h⟩ := ok_bind h
  obtain ⟨x, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨y, hy, h⟩ := ok_bind h
  obtain ⟨d2, hd, h⟩ := ok_bind h
  have hd' := there_ok hd
  unfold Ground.addRowP at hd'
  split at hd'
  · rename_i hok
    simp only [Ground.ok, Ground.rowL, List.all_cons, Bool.and_eq_true] at hok
    rw [← asRow_groups _ _ _ _ _ _ hy]
    exact hok.1
  · simp at hd'

variable {T K : Type} [CommRing K]

/-- Every open row of the segment's group holds on the tables. -/
def GroupHoldsAt (X : Lens T) (ρ : Reading K) (N : Nat) (s : T)
    (tab : Nat → OnBytes.Part → Nat → K) : Prop :=
  ∀ a, X.get? s = some a → ∀ G, a.d.st.groups[a.L.check.group]? = some G →
    ∀ row ∈ G.rows.toList, rowSum ρ a.d.st N tab row = ρ.val row.target

/-- The data that the tables hold, read by the state's own layout, frame and statement. -/
def dataAt (X : Lens T) (s : T) (tab : Nat → OnBytes.Part → Nat → K) : Bound K :=
  match X.get? s with
  | some a => dataOf a.L.check.rows a.L.check.frame a.d.st tab
  | none => ⟨fun _ _ _ _ => 0, fun _ => 0⟩

/-- The inversion of the equation's step, as far as K9.door. -/
theorem oneEquation_inv {Cl : Type} (X : Lens T) (p : K9.Where) (ft : Nat) (s : T)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat)
    (h : (K9.oneEquation (Cl := Cl) X p).step ft s rs cols = .ok (s', k)) :
    ∃ (a : K9.Part) (out : K9.Out Unit), X.get? s = some a ∧
      door a.owed a.laid a.L a.F a.d = .ok out ∧
      s' = X.set s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } := by
  unfold Block.step at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨t', hdec, h⟩ := ok_bind h
  have e : t' = s' := congrArg Prod.fst (Except.ok.inj h)
  subst e
  simp only [K9.oneEquation] at hdec
  obtain ⟨a, ha, hdec⟩ := ok_bind hdec
  obtain ⟨out, ho, hdec⟩ := ok_bind hdec
  exact ⟨a, out, there_ok ha, ho, (Except.ok.inj hdec).symm⟩

/-- **The equation's block between its two relations.** -/
theorem oneEquation_joint {Cl : Type} (X : Lens T) (ρ : Reading K) (p : K9.Where) (ft : Nat)
    (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat) (N : Nat)
    (tab : Nat → OnBytes.Part → Nat → K)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (P : ∀ a q G, X.get? s = some a → equation a.L a.F = .ok (q, G) →
      RowPremises a.L.check a.d.st N q)
    (h : (K9.oneEquation (Cl := Cl) X p).step ft s rs cols = .ok (s', k))
    (hh : GroupHoldsAt X ρ N s' tab) :
    oneK X ρ s s (dataAt X s tab) = 0 ∧ GroupHoldsAt X ρ N s tab := by
  obtain ⟨a, out, ha, hdoor, hs'⟩ := oneEquation_inv X p ft s rs cols s' k h
  obtain ⟨n, q, G, row, d1, _, hq, _, hr, ho, _, hL⟩ := door_parts _ _ _ _ _ _ hdoor
  have hb : SameBits a.d.st out.d.st := by
    rw [ho]
    exact (asRow_bits _ _ _ _ _ _ hr).trans (withRow_bits _ _ _)
  obtain ⟨G0, hG0⟩ := Option.isSome_iff_exists.mp (door_group _ _ _ _ _ _ hdoor)
  have hg1 : d1.st.groups = a.d.st.groups := asRow_groups _ _ _ _ _ _ hr
  obtain ⟨a', ha', hL', hd'⟩ :=
    lens s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
  rw [← hs'] at ha'
  have eL : a'.L = a.L := hL'.trans hL
  have eD : a'.d.st = out.d.st := hd'
  have hGb : a'.d.st.groups[a'.L.check.group]? = some { G0 with rows := G0.rows.push row } := by
    rw [eD, eL, ho]
    show (Slice.withRow d1.st a.L.check.group row).groups[a.L.check.group]? = _
    simp only [Slice.withRow, Array.getElem?_modify, if_true, hg1, hG0, Option.map_some]
  have hall := hh a' ha' _ hGb
  constructor
  · have hrow := hall row (by simp)
    rw [eD, rowSum_bits ρ _ _ hb] at hrow
    have e := asRow_sum ρ a.L.check q a.d d1 row N tab (equation_k9 _ _ _ _ hq) (P a q G ha hq) hr
    rw [hrow, sub_self] at e
    simp only [oneK, dataAt, ha]
    rw [← equation_total ρ _ a.L a.F G q hq]
    exact e.symm
  · intro a2 ha2 G2 hG2 r hr2
    have e2 : a2 = a := Option.some.inj (ha2.symm.trans ha)
    subst e2
    have e3 : G2 = G0 := Option.some.inj (hG2.symm.trans hG0)
    subst e3
    have h1 := hall r (by simp [hr2])
    rw [eD, rowSum_bits ρ _ _ hb] at h1
    exact h1

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.door_group
#print axioms VerifiableInference.Desc.K9L.oneEquation_joint
