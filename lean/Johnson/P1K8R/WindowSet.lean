-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/WindowSet.lean: which messages the private stop set holds, in both directions.

  drawsOf, memberStop   the draws that a list of members takes; the stop at one member
  chainStop_append      a chain's stop is the first list's, or else the second's
  chainStop_iff         a chain stops with y just where some member does, with no stop in front
  row_not_hid           a list of parts without a second stop does not stop by one
  pinned_row_iff        the pinned part stops by its second stop just where a combination leaves its
                        window at the member's first drawn round
  hid_first_iff         the first stop that fires in a chain is a second stop just where, at some
                        member whose half is pinned, a combination leaves its window, with no stop
                        in front

Limits. These are statements about the list of halves. Nothing here bounds a measure.
-/
import Johnson.P1K8R.QuietLots
import Johnson.Desc.ProofFile.Honest.Law.SharesNoHid
import Johnson.FrontRoad.PinPublicSpec
import Johnson.FrontRoad.ParOwn
import Johnson.FrontRoad.SecondChainPlacesSpec
import Johnson.Desc.ProofFile.Honest.K8.QuietForm
import Johnson.Desc.ProofFile.Honest.K8.StopIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile.Honest
open ProofFile.Honest.K8 (smallFits smallHalf smallStop windowShare small_parts smallPartAt small_stop_iff
  smallHalf_parts cellsAtOf)
open ProofFile.Honest.K9 (quietStop)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (leaves)
open OnBytes.FrontRoad (PinHalvesAt parOwn)

section
variable {S Cl V W Y : Type}

/-- The draws that a list of members takes. -/
def drawsOf (A : List (Block S Cl)) : ℕ := (A.map fun b => b.rounds.length).sum

/-- The stop at one member, at the draws from its first round on. -/
def memberStop (v : Option V) (b : Block S Cl) (hs : List (Placed V W Y))
    (loc ds : List Fmt.Drawn) : Option Why :=
  (hs.find? fun h => h.place == b.place).bind fun h =>
    rowStopAt v h.parts loc (ds.take b.rounds.length)

theorem drawsOf_cons (c : Block S Cl) (A : List (Block S Cl)) :
    drawsOf (c :: A) = c.rounds.length + drawsOf A := by
  simp [drawsOf]

theorem chainStop_cons (v : Option V) (c : Block S Cl) (A : List (Block S Cl))
    (hs : List (Placed V W Y)) (loc ds : List Fmt.Drawn) :
    chainStopAt v (c :: A) hs loc ds = (memberStop v c hs loc ds).or
      (chainStopAt v A hs (loc ++ ds.take c.rounds.length) (ds.drop c.rounds.length)) := rfl

/-- Two steps of the draws are one. -/
theorem loc_step (loc ds : List Fmt.Drawn) (m n : ℕ) :
    (loc ++ ds.take m) ++ (ds.drop m).take n = loc ++ ds.take (m + n) := by
  rw [List.take_add, List.append_assoc]

theorem drop_step (ds : List Fmt.Drawn) (m n : ℕ) : (ds.drop m).drop n = ds.drop (m + n) := by
  simp [List.drop_drop, Nat.add_comm]

/-- **A chain's stop is the first list's, or else the second's.** -/
theorem chainStop_append (v : Option V) (hs : List (Placed V W Y)) (C : List (Block S Cl)) :
    ∀ (A : List (Block S Cl)) (loc ds : List Fmt.Drawn),
      chainStopAt v (A ++ C) hs loc ds = (chainStopAt v A hs loc ds).or
        (chainStopAt v C hs (loc ++ ds.take (drawsOf A)) (ds.drop (drawsOf A)))
  | [], loc, ds => by
    simp [chainStopAt, drawsOf]
  | c :: A, loc, ds => by
    rw [List.cons_append, chainStop_cons, chainStop_cons, chainStop_append v hs C A,
      Option.or_assoc, drawsOf_cons, loc_step, drop_step]

/-- **A chain stops with y just where some member does, with no stop in front.** -/
theorem chainStop_iff (v : Option V) (hs : List (Placed V W Y)) (y : Why) :
    ∀ (bs : List (Block S Cl)) (loc ds : List Fmt.Drawn),
      chainStopAt v bs hs loc ds = some y ↔
        ∃ A b B, bs = A ++ b :: B ∧ chainStopAt v A hs loc ds = none ∧
          memberStop v b hs (loc ++ ds.take (drawsOf A)) (ds.drop (drawsOf A)) = some y
  | [], loc, ds => by
    constructor
    · intro h
      cases h
    · rintro ⟨A, b, B, e, -⟩
      simp at e
  | c :: bs, loc, ds => by
    constructor
    · intro h
      rw [chainStop_cons] at h
      cases hM : memberStop v c hs loc ds with
      | some z =>
        rw [hM] at h
        refine ⟨[], c, bs, rfl, rfl, ?_⟩
        simpa [drawsOf, hM] using h
      | none =>
        rw [hM] at h
        obtain ⟨A, b, B, e, h₀, h₁⟩ :=
          (chainStop_iff v hs y bs _ _).1 (by simpa using h)
        refine ⟨c :: A, b, B, by rw [e]; rfl, ?_, ?_⟩
        · rw [chainStop_cons, hM]
          simpa using h₀
        · rw [drawsOf_cons, ← loc_step, ← drop_step]
          exact h₁
    · rintro ⟨A, b, B, e, h₀, h₁⟩
      rw [e, chainStop_append, h₀]
      show (chainStopAt v (b :: B) hs _ _) = some y
      rw [chainStop_cons, h₁]
      rfl

/-- A list of parts without a second stop does not stop by one. -/
theorem row_not_hid (v : Option V) :
    ∀ (ps : List (Part V W Y)), (∀ p ∈ ps, Quiet p) → ∀ (loc ds : List Fmt.Drawn),
      rowStopAt v ps loc ds ≠ some Why.hid
  | [], _, _, _ => by
    simp [rowStopAt]
  | p :: ps, h, loc, ds => by
    have hp := (h p List.mem_cons_self).1
    have hr := row_not_hid v ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
      (loc ++ ds.take p.moves.length) (ds.drop p.moves.length)
    have hs := stopAt_not_hid p v loc (ds.take p.moves.length) fun u j => hp u loc _
    show (p.stopAt v loc (ds.take p.moves.length)).or _ ≠ _
    cases e : p.stopAt v loc (ds.take p.moves.length) with
    | none => simpa using hr
    | some z =>
      intro h'
      have : z = Why.hid := by simpa using h'
      subst this
      exact hs e

end

section
variable {W₀ Rc Xi Tr X : Type}

/-- **The pinned part stops by its second stop just where a combination leaves its window** at the
member's first drawn round. -/
theorem pinned_row_iff (cells : Tr → Cells) (P : Par × List (ℕ × String × ℕ))
    (hf : smallFits P = true) (u : Local W₀ Rc Xi Tr) (loc : List Fmt.Drawn) (d : Fmt.Drawn) :
    rowStopAt (some u)
        [(quietStop (smallStop cells P) (windowShare P.1) :
          Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)] loc [d] = some Why.hid ↔
      (leaves P.1 (cellsAtOf (cells u.trace) P.2) d.trits.toArray).isSome = true := by
  have e : (quietStop (smallStop cells P) (windowShare P.1) :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) = smallPartAt cells P := by
    have h := small_parts W₀ Rc Xi Tr X cells P hf
    rw [smallHalf_parts] at h
    exact (List.cons.inj h).1.symm
  rw [e, ← small_stop_iff (X := X) cells P u loc d]
  show ((smallPartAt cells P).stopAt (some u) loc ([d].take 1)).or
    (rowStopAt (some u) [] (loc ++ [d].take 1) ([d].drop 1)) = _ ↔ _
  simp [rowStopAt]

/-- The pinned part does not stop by its second stop in front of its round. -/
theorem pinned_row_nil (cells : Tr → Cells) (P : Par × List (ℕ × String × ℕ))
    (hf : smallFits P = true) (u : Local W₀ Rc Xi Tr) (loc : List Fmt.Drawn) :
    rowStopAt (some u)
        [(quietStop (smallStop cells P) (windowShare P.1) :
          Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)] loc [] ≠ some Why.hid := by
  have e : (quietStop (smallStop cells P) (windowShare P.1) :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) = smallPartAt cells P := by
    have h := small_parts W₀ Rc Xi Tr X cells P hf
    rw [smallHalf_parts] at h
    exact (List.cons.inj h).1.symm
  rw [e]
  simp [rowStopAt, Part.stopAt, smallPartAt, Part.lift, ProofFile.Honest.K8.smallPart,
    ProofFile.Honest.K8.smallHid, List.range_succ]

/-- A member in front of a list that is not empty stands in the list without its last member. -/
theorem mem_dropLast_split {α : Type} (A B : List α) (b : α) (hB : B ≠ []) :
    b ∈ (A ++ b :: B).dropLast := by
  rw [List.dropLast_append_cons]
  cases B with
  | nil => exact absurd rfl hB
  | cons z B' => simp

/-- **The first stop that fires in a chain is a second stop just where, at some member whose half is
pinned, a combination leaves its window, with no stop in front.** hs: the chain's halves. bs: its
members, of which the last has no half and is not of the kind. -/
theorem hid_first_iff {Zp : ProofFile.Pub} {mats : ℕ → List (ℕ × String × ℕ)} {cells : Tr → Cells}
    {S Cl : Type} (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) (u : Local W₀ Rc Xi Tr)
    (hpin : PinHalvesAt (parOwn Zp mats) cells hs bs.dropLast)
    (hfit : ∀ b ∈ bs.dropLast, ∀ P, parOwn Zp mats b.place = some P →
      smallFits P = true ∧ b.rounds.length = 1)
    (hlast : ∀ e, bs.getLast? = some e →
      (hs.find? fun h => h.place == e.place) = none ∧ parOwn Zp mats e.place = none)
    (loc ds : List Fmt.Drawn) :
    chainStopAt (some u) bs hs loc ds = some Why.hid ↔
      ∃ A b B P d, bs = A ++ b :: B ∧ chainStopAt (some u) A hs loc ds = none ∧
        parOwn Zp mats b.place = some P ∧ (ds.drop (drawsOf A)).head? = some d ∧
        (leaves P.1 (cellsAtOf (cells u.trace) P.2) d.trits.toArray).isSome = true := by
  have hB : ∀ (A B : List (Block S Cl)) (b : Block S Cl), bs = A ++ b :: B → B = [] →
      (hs.find? fun h => h.place == b.place) = none ∧ parOwn Zp mats b.place = none := by
    intro A B b e h
    subst h
    exact hlast b (by rw [e]; simp)
  rw [chainStop_iff]
  constructor
  · rintro ⟨A, b, B, e, h₀, h₁⟩
    unfold memberStop at h₁
    cases hg : hs.find? (fun h => h.place == b.place) with
    | none =>
      rw [hg] at h₁
      cases h₁
    | some g =>
      rw [hg] at h₁
      have hne : B ≠ [] := fun h => by
        have := (hB A B b e h).1
        rw [hg] at this
        cases this
      have hb : b ∈ bs.dropLast := by
        rw [e]
        exact mem_dropLast_split A B b hne
      have hq := hpin b hb
      cases hp : parOwn Zp mats b.place with
      | none =>
        rw [hp] at hq
        exact absurd h₁ (row_not_hid _ g.parts (hq g hg) _ _)
      | some P =>
        rw [hp] at hq
        obtain ⟨g', hg', ep⟩ := hq
        obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
        obtain ⟨hf, hr⟩ := hfit b hb P hp
        have h₂ : rowStopAt (some u) g.parts _ _ = some Why.hid := h₁
        rw [ep, hr] at h₂
        cases hd : ds.drop (drawsOf A) with
        | nil =>
          rw [hd] at h₂
          exact absurd h₂ (pinned_row_nil cells P hf u _)
        | cons d t =>
          rw [hd] at h₂
          refine ⟨A, b, B, P, d, e, h₀, hp, by rw [hd]; rfl, ?_⟩
          exact (pinned_row_iff cells P hf u _ d).1 h₂
  · rintro ⟨A, b, B, P, d, e, h₀, hp, hd, hl⟩
    have hne : B ≠ [] := fun h => by
      have := (hB A B b e h).2
      rw [hp] at this
      cases this
    have hb : b ∈ bs.dropLast := by
      rw [e]
      exact mem_dropLast_split A B b hne
    obtain ⟨hf, hr⟩ := hfit b hb P hp
    have hq := hpin b hb
    rw [hp] at hq
    obtain ⟨g, hg, ep⟩ := hq
    refine ⟨A, b, B, e, h₀, ?_⟩
    unfold memberStop
    rw [hg]
    show rowStopAt (some u) g.parts _ _ = some Why.hid
    rw [ep, hr]
    cases hds : ds.drop (drawsOf A) with
    | nil =>
      rw [hds] at hd
      cases hd
    | cons d' t =>
      rw [hds] at hd
      obtain rfl : d' = d := Option.some.inj hd
      exact (pinned_row_iff cells P hf u _ d').2 hl

/-- **A chain whose halves are all silent does not stop by a second stop.** -/
theorem silent_not_hid {S Cl : Type}
    (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)) (bs : List (Block S Cl))
    (v : Option (Local W₀ Rc Xi Tr)) (h : OnBytes.FrontRoad.SilentAt hs bs)
    (loc ds : List Fmt.Drawn) : chainStopAt v bs hs loc ds ≠ some Why.hid := by
  intro hc
  obtain ⟨A, b, B, e, -, h₁⟩ := (chainStop_iff v hs Why.hid bs loc ds).1 hc
  unfold memberStop at h₁
  cases hg : hs.find? (fun x => x.place == b.place) with
  | none =>
    rw [hg] at h₁
    cases h₁
  | some g =>
    rw [hg] at h₁
    exact row_not_hid v g.parts (h b (by rw [e]; simp) g hg) _ _ h₁

end

end P1K8

#print axioms P1K8.hid_first_iff
#print axioms P1K8.silent_not_hid
#print axioms P1K8.chainStop_append
#print axioms P1K8.chainStop_iff
#print axioms P1K8.row_not_hid
#print axioms P1K8.pinned_row_iff
