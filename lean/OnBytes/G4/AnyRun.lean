-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/AnyRun.lean: a whole call of the program's lookup verifier as a function of the plain
data, at any caller that meets the laws of OnBytes/G4/AnyCaller.lean.

`Caller.Laws.verify_val`: let the caller C meet the laws, let its public inputs be `Ready` (below),
and let a stand s be given whose rounds begin with rounds that fit the lookup's entries and whose
two ledgers have enough entries left. Then

  Lkp.verify C.S C.planesAt C.masks C.group (some C.keyMasks)

applied to the context of s gives `s.course.out`, in the context of the stand `s.course.last`.
`s.course` is a record (`Caller.Course`) with each value of the run under its name. It is a function
of the stand, without a state monad and without a failure, made of the program's own pure parts:
Psc.run, lineAt, Lkp.joinPlanes, Lkp.keysOf, Lkp.byVariable, the summands, Psc.rowU, pointRow. The
lookup may have several parts, and planes that are not real. It starts at any stand, so that several
lookups on the same ledgers compose.

`Ready S` holds facts on public numbers alone: no shift; S.ok; there is a part; the length of each
part's last key level's order; the degrees at the leaves; 0 < mu + d ≤ 63. `lookupEntries` spells
the plan's entries of a lookup block by block; that they are the entries of Lkp.roundsOf is not
shown here.

Main definitions: Ready, lookupEntries, ownTotal, Caller.bitsAt, Caller.countsRow, Caller.Course,
Caller.Stand.course, Caller.Course.out.
Main theorems: Caller.Laws.run_val, Caller.Laws.verify_val.
Not claimed: as in OnBytes/G4/AnyCaller.lean. Nothing on a lookup with a shift or with tree numbers.


-/
import OnBytes.G4.AnyCourse

set_option autoImplicit false

namespace OnBytes.G4

open Blk

variable {C : Caller}

/-- What is asked of the public inputs: facts on public numbers alone. -/
structure Ready (S : Lkp.Public) : Prop where
  noShift : S.shifted = false
  ok : S.ok = true
  parts : S.parts ≠ []
  orders : ∀ v ∈ S.parts, (Lkp.orderBeginning S.lastKeyLevelOrder (v - 1)).length = v - 1
  leaves : (Lkp.defaultOrder (S.mu + S.d)).map (fun t => if t < S.mu then 2 else 3) =
    List.replicate S.d 3 ++ List.replicate S.mu 2
  some : 0 < S.mu + S.d
  small : S.mu + S.d ≤ 63

/-- The entries of a lookup without a shift, block by block, and then es'. -/
def lookupEntries (S : Lkp.Public) (work : Nat) (es' : List Fmt.Entry) : List Fmt.Entry :=
  (rDraw "LKP" work 1).entry ::
  (pscEntries work { degree := [], withY := true, degreeY := 3, values := 3 } ++
  (tieEntries work (S.planes - 2) ++
  (partEntries work (S.parts.length - 1) ++
  ((rDraw "JOIN" work S.mu).entry ::
  (treesEntries work S.parts ++
  (chainEntries work S.mu (S.d - S.d) S.d ++
  (pscEntries work (leavesSize S) ++
  ((rDraw "ZERO" work (S.mu + S.d)).entry ::
  (pscEntries work (bitsSize S) ++ es')))))))))

/-- The entries of the first ledger that a lookup takes. -/
def ownTotal (S : Lkp.Public) : Nat :=
  7 + 6 * (S.planes - 2) + 5 * (S.parts.length - 1) + treesOwn S.parts +
    chainOwn false S.mu (S.d - S.d) S.d + (1 + S.mu + 2 * S.d) + (1 + 2 * (S.mu + S.d) + 2 + 1)

theorem chainKey_false : ∀ n, chainKey false n = 0
  | 0 => rfl
  | n + 1 => by simp [chainKey, keyOf, chainKey_false n]

/-- Where the bits are read, as a map at a point. -/
def Caller.bitsAt (C : Caller) : MapAt := fun row point coeff => C.planesAt row
    (Tensor.eq point coeff)

/-- The row that says that the counts sum to the number of keys that are not padding. -/
def Caller.countsRow (C : Caller) : Row :=
  C.planesAt { target := Lkp.natE (C.S.allKeys - Lkp.paddingCount C.S) }
    { pairs := ((List.range C.S.mu).map fun t => (oneE, Lkp.natE (2 ^ 2 ^ t))) ++
        List.replicate C.S.d (oneE, oneE) }

/-- The values and stands of a whole lookup, each under its name, in the order of the run. -/
structure Caller.Course (C : Caller) where
  /-- the challenge alpha -/
  alpha : E
  /-- what the tie's first step hands on -/
  first : Psc.Out
  /-- the tie's later steps -/
  tie : List PointClaim × C.Stand
  /-- the parts' steps: the claims on the parts' roots -/
  roots : List PointClaim × C.Stand
  /-- the point at which the planes are joined -/
  join : List E
  /-- the key trees: the claims on their leaves -/
  keys : List PointClaim × C.Stand
  /-- the table's tree: the claim on its leaves -/
  table : PointClaim × C.Stand
  /-- what the sumcheck on the leaves of the table's tree hands on -/
  leaves : Psc.Out
  /-- the stand after the sumcheck on the leaves -/
  afterLeaves : C.Stand
  /-- the point of the test that the bits are bits -/
  zeta : List E
  /-- what the sumcheck on the bits hands on -/
  bits : Psc.Out
  /-- the stand at the end -/
  last : C.Stand

/-- The course of a whole lookup from a stand. -/
def Caller.Stand.course (s : C.Stand) : C.Course :=
  let S := C.S
  let alpha := s.draw
  let tieFirst := Lkp.summandTieFirst (Lkp.factorOf S zeroE alpha)
  let first := s.next.pscOut zeroSum tieFirst false id
  let tie := Caller.Stand.tieVal (S.planes - 2) (first.ends.getD 1 default)
    (s.next.afterPsc zeroSum tieFirst false [] id)
  let roots := Caller.Stand.partVal (S.parts.length - 1) (first.ends.getD 0 default) tie.2
  let join := roots.2.draws
  let keys := Caller.Stand.treesVal S.parts roots.1 roots.2.next
  let table := Caller.Stand.chainVal false S.d S.mu S.d
    (Lkp.joinPlanes S join (first.ends.getD 2 default :: tie.1)) keys.2
  let order := Lkp.defaultOrder (S.mu + S.d)
  let place := fun p => Lkp.byVariable p order
  let leaves := table.2.pscOut (leavesSum S table.1) (Lkp.summandLeaves S zeroE alpha order) false
      place
  let afterLeaves := table.2.afterPsc (leavesSum S table.1) (Lkp.summandLeaves S zeroE alpha order)
      false
    [C.bitsAt] place
  let zeta := afterLeaves.draws
  let bitsSum := levelSum ⟨zeta, [], zeroE⟩ order
  let bits := afterLeaves.next.pscOut bitsSum Lkp.summandBits false place
  let s9 := afterLeaves.next.afterPsc bitsSum Lkp.summandBits false [] place
  { alpha := alpha, first := first, tie := tie, roots := roots, join := join, keys := keys
    table := table, leaves := leaves, afterLeaves := afterLeaves, zeta := zeta, bits := bits
    last := { s9 with
      rows := (s9.rows.push (pointRow (bits.ends.getD 0 default) C.bitsAt)).push C.countsRow } }

/-- What a whole lookup returns. -/
def Caller.Course.out (x : C.Course) : Lkp.Out where
  theta := zeroE
  alpha := x.alpha
  keys := ((List.range x.keys.1.length).zip x.keys.1).map fun p =>
    Lkp.keysOf C.S zeroE x.alpha p.1 p.2

theorem PointsAt.length : ∀ {vs : List Nat} {cs : List PointClaim}, PointsAt vs cs →
    cs.length = vs.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => by simp [PointsAt.length h.2]

theorem Caller.Laws.noteKeys_val (L : C.Laws) (es cur rs last σ rows) : ∀ l : List Lkp.Keys,
    (Lkp.noteKeys l) (C.ctx es cur rs last σ rows) = .ok ((), C.ctx es cur rs last σ rows)
  | [] => rfl
  | x :: l => by
    unfold Lkp.noteKeys
    rw [bind_ok (L.note es cur rs last σ rows _ _)]
    exact Caller.Laws.noteKeys_val L es cur rs last σ rows l

/-- The claims on the planes' roots become one claim whose mask entries a row may read. -/
theorem Caller.joinPlanes_ok (C : Caller) (r : List E) (l : List PointClaim)
    (hl : ∀ x ∈ l, C.ClaimOK 0 x) : C.ClaimOK r.length (Lkp.joinPlanes C.S r l) := by
  unfold Lkp.joinPlanes
  apply foldl_inv (fun c : PointClaim => C.ClaimOK r.length c)
  · intro c j hc
    cases hj : l[j]? with
    | none =>
      simp only []
      exact ⟨hc.1, hc.2⟩
    | some p =>
      simp only []
      exact ⟨hc.1, Caller.slotsOK_append hc.2
        (Caller.slotsOK_scale _ (hl p (List.mem_of_getElem? hj)).2)⟩
  · exact ⟨rfl, by intro p hp; simp at hp⟩

/-- The map that says where the bits are keeps a row fine. -/
theorem Caller.Laws.mapsOK_bits (L : C.Laws) (h63 : C.S.mu + C.S.d ≤ 63) :
    C.MapsOK (C.S.mu + C.S.d) [C.bitsAt] := by
  intro m hm row point coeff hrow hp
  simp only [List.mem_singleton] at hm
  subst hm
  exact L.finePlanes row _ hrow (by simp [Tensor.eq, Tensor.vars, hp])
    (eq_ok point coeff (by rw [hp]; exact h63)) rfl

/-- A whole lookup at any caller, with every value named. -/
theorem Caller.Laws.run_val (L : C.Laws) (work : Nat) (h : Ready C.S) (es' : List Fmt.Entry)
    (s : C.Stand) (last0 : Option Fmt.Entry) (hq0 : NoRows last0)
    (hfit : FitsAll s.rounds (lookupEntries C.S work es'))
    (h1 : ownTotal C.S ≤ C.left s.led) (h2 : treesKey C.S.parts ≤ C.keyLeft s.led) :
    ∃ last, NoRows last ∧ FitsAll s.course.last.rounds es' ∧
      C.left s.course.last.led = C.left s.led - ownTotal C.S ∧
      C.keyLeft s.course.last.led = C.keyLeft s.led - treesKey C.S.parts ∧
      PointsAt C.S.parts s.course.keys.1 ∧
      (Lkp.run C.env) (s.ctx (lookupEntries C.S work es') last0) =
        .ok (s.course.out, s.course.last.ctx es' last) := by
  unfold lookupEntries at hfit ⊢
  unfold ownTotal at h1 ⊢
  generalize hx : s.course = x
  have hx' := hx.symm
  simp only [Caller.Stand.course] at hx'
  obtain ⟨hf1, hrun1⟩ := L.drawOne_val work "LKP" _ s last0 hq0 hfit
  obtain ⟨last2, hq2, hf2, hl2, hk2, hends2, hall2, hrun2⟩ :=
    L.value_val work zeroSum rfl (Lkp.summandTieFirst (Lkp.factorOf C.S zeroE s.draw))
      (by show 0 < 3; omega) (by show 0 < 3; omega) rfl (fun _ _ => rfl) _ s.next _
      (noRows_rDraw "LKP" work 1) hf1 (by show 1 + 3 + 3 ≤ C.left s.led; omega)
      (by intro p hp; simp [zeroSum] at hp)
  have hl2' : C.left (s.next.afterPsc zeroSum (Lkp.summandTieFirst (Lkp.factorOf C.S zeroE s.draw))
      false [] id).led = C.left s.led - 7 := hl2
  have hk2' : C.keyLeft
      (s.next.afterPsc zeroSum (Lkp.summandTieFirst (Lkp.factorOf C.S zeroE s.draw))
      false [] id).led = C.keyLeft s.led := hk2
  obtain ⟨a, b, c, he⟩ : ∃ a b c, (s.next.pscOut zeroSum
      (Lkp.summandTieFirst (Lkp.factorOf C.S zeroE s.draw)) false id).ends = [a, b, c] := by
    have h3 : (s.next.pscOut zeroSum
      (Lkp.summandTieFirst (Lkp.factorOf C.S zeroE s.draw)) false id).ends.length = 3 := hends2
    match (s.next.pscOut zeroSum
      (Lkp.summandTieFirst (Lkp.factorOf C.S zeroE s.draw)) false id).ends, h3 with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  simp only [he, List.getD_cons_zero, List.getD_cons_succ] at hx'
  obtain ⟨last3, hq3, hf3, hl3, hk3, hall3, hrun3⟩ :=
    L.tie_val work _ (C.S.planes - 2) b _ last2 (hall2 b (by simp [he])) hq2 hf2
        (by rw [hl2']; omega)
  generalize htie : Caller.Stand.tieVal (C.S.planes - 2) b
    (s.next.afterPsc zeroSum (Lkp.summandTieFirst (Lkp.factorOf C.S zeroE s.draw)) false [] id) =
        tie
    at hf3 hl3 hk3 hall3 hrun3 hx'
  obtain ⟨last4, hq4, hf4, hl4, hk4, hlen4, hall4, hrun4⟩ :=
    L.part_val work _ (C.S.parts.length - 1) a tie.2 last3 (hall2 a (by simp [he])) hq3 hf3
      (by rw [hl3, hl2']; omega)
  generalize hroots : Caller.Stand.partVal (C.S.parts.length - 1) a tie.2 = roots
    at hf4 hl4 hk4 hlen4 hall4 hrun4 hx'
  obtain ⟨hf5, hr5, hrun5⟩ := L.draws_val work C.S.mu "JOIN" _ roots.2 last4 hq4 hf4
  have hTop : C.ClaimOK (C.S.mu + (C.S.d - C.S.d))
      (Lkp.joinPlanes C.S roots.2.draws (c :: tie.1)) := by
    have := C.joinPlanes_ok roots.2.draws (c :: tie.1) (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hall2 _ (by simp [he])
      · exact hall3 q hq)
    rw [hr5] at this
    simpa using this
  have hpl : 0 < C.S.parts.length := List.length_pos_iff.2 h.parts
  obtain ⟨last6, hq6, hf6, hl6, hk6, hc6, hrun6⟩ :=
    L.trees_val work _ C.S.parts roots.1 roots.2.next _ (by rw [hlen4]; omega) hall4 h.orders
      (noRows_rDraw "JOIN" work C.S.mu) hf5
      (by show _ ≤ C.left roots.2.led; rw [hl4, hl3, hl2']; omega)
      (by show _ ≤ C.keyLeft roots.2.led; rw [hk4, hk3, hk2']; exact h2)
  have hl6' : C.left (Caller.Stand.treesVal C.S.parts roots.1 roots.2.next).2.led =
      C.left roots.2.led - treesOwn C.S.parts := hl6
  have hk6' : C.keyLeft (Caller.Stand.treesVal C.S.parts roots.1 roots.2.next).2.led =
      C.keyLeft roots.2.led - treesKey C.S.parts := hk6
  generalize hkeys : Caller.Stand.treesVal C.S.parts roots.1 roots.2.next = keys
    at hf6 hl6' hk6' hc6 hrun6 hx'
  obtain ⟨last7, hq7, hf7, hl7, hk7, hc7, hm7, hrun7⟩ :=
    L.chain_val work false C.S.d C.S.mu (orderAt_table C.S C.S.d C.S.mu) _ C.S.d
      (Lkp.joinPlanes C.S roots.2.draws (c :: tie.1)) keys.2 last6 (Nat.le_refl _) hTop.1
      (fun _ => hTop.2) hq6 hf6
      (by rw [hl6', hl4, hl3, hl2']; omega) (by rw [chainKey_false]; exact Nat.zero_le _)
  rw [chainKey_false] at hk7
  generalize htable : Caller.Stand.chainVal false C.S.d C.S.mu C.S.d
    (Lkp.joinPlanes C.S roots.2.draws (c :: tie.1)) keys.2 = table at hf7 hl7 hk7 hc7 hm7 hrun7 hx'
  -- the leaves
  have hLd := (leavesSum_d C.S table.1).trans h.leaves
  have hLlen : (leavesSum C.S table.1).vars.length = C.S.mu + C.S.d := by
    simp [leavesSum, defaultOrder_length]
  have hLsz : Psc.sizeOf (leavesSum C.S table.1)
      (Lkp.summandLeaves C.S zeroE s.draw (Lkp.defaultOrder (C.S.mu + C.S.d))) = leavesSize
          C.S := by
    simp only [Psc.sizeOf, hLd, leavesSize, Lkp.summandLeaves]
    rfl
  have hLvo : Psc.varsOf (leavesSum C.S table.1)
      (Lkp.summandLeaves C.S zeroE s.draw (Lkp.defaultOrder (C.S.mu + C.S.d))) =
      (leavesSum C.S table.1).vars := rfl
  have hLmk : Psc.masksOf (leavesSum C.S table.1)
      (Lkp.summandLeaves C.S zeroE s.draw (Lkp.defaultOrder (C.S.mu + C.S.d))) =
      1 + C.S.mu + 2 * C.S.d := by
    have e1 : (leavesSum C.S table.1).vars.map (fun w => w.d - 1) =
        (List.replicate C.S.d 3 ++ List.replicate C.S.mu 2).map (· - 1) := by
      rw [← hLd, List.map_map]
      rfl
    have e2 : Psc.masksOf (leavesSum C.S table.1)
        (Lkp.summandLeaves C.S zeroE s.draw (Lkp.defaultOrder (C.S.mu + C.S.d))) =
        1 + ((leavesSum C.S table.1).vars.map (fun w => w.d - 1)).sum + 0 := rfl
    rw [e2, e1, sum_leaves]
    omega
  have hLw : ∀ w ∈ (leavesSum C.S table.1).vars, w.fits = true ∧ 1 ≤ w.d := by
    intro w hw
    simp only [leavesSum, List.mem_map] at hw
    obtain ⟨t, _, rfl⟩ := hw
    by_cases ht : t < C.S.mu <;> simp [Psc.Weight.fits, Psc.Weight.equality, ht]
  have hLne : (leavesSum C.S table.1).vars ≠ [] := by
    intro hz
    have h3 := congrArg List.length hz
    rw [hLlen] at h3
    have h4 := h.some
    simp at h3
    omega
  obtain ⟨last8, hf8, hq8, hrun8, _, _, _, hl8, hk8⟩ :=
    L.psc_val work (leavesSum C.S table.1)
      (Lkp.summandLeaves C.S zeroE s.draw (Lkp.defaultOrder (C.S.mu + C.S.d))) false [C.bitsAt]
      (fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d))) _ table.2 last7 hq7
      (by rw [hLsz]; exact hf7)
      (by
        have ha : (leavesSum C.S table.1).vars.all Psc.Weight.fits = true :=
          List.all_eq_true.2 fun w hw => (hLw w hw).1
        have hb : (leavesSum C.S table.1).vars.isEmpty = false := by
          cases hv : (leavesSum C.S table.1).vars with
          | nil => exact absurd hv hLne
          | cons _ _ => rfl
        simp [Psc.formOK, Lkp.summandLeaves, ha, hb])
      (fun _ _ => rfl) (by rw [hLvo]; exact fun w hw => (hLw w hw).2) (by rw [hLvo]; exact hLne)
      (by rw [hLvo]; exact Nat.le_refl _)
      (by rw [hLmk]; show _ ≤ _; simp only [ownOf, Bool.false_eq_true, if_false]
          rw [hl7, hl6', hl4, hl3, hl2']; omega)
      (Nat.zero_le _) (by intro hh; cases hh) (Nat.zero_le _) (hm7 rfl) rfl
      (by rw [hLlen]; exact L.mapsOK_bits h.small) (fun p => byVariable_length p _)
  rw [hLmk] at hl8
  simp only [ownOf, keyOf, Bool.false_eq_true, if_false, Nat.sub_zero] at hl8 hk8
  have hrun8' : (Lkp.psc C.env (leavesSum C.S table.1)
      (Lkp.summandLeaves C.S zeroE s.draw (Lkp.defaultOrder (C.S.mu + C.S.d))) false [C.bitsAt]
      fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d)))
      (table.2.ctx (pscEntries work (leavesSize C.S) ++ (rDraw "ZERO" work (C.S.mu + C.S.d)).entry
          ::
        (pscEntries work (bitsSize C.S) ++ es')) last7) =
      .ok (table.2.pscOut (leavesSum C.S table.1)
          (Lkp.summandLeaves C.S zeroE s.draw (Lkp.defaultOrder (C.S.mu + C.S.d))) false
          (fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d))),
        (table.2.afterPsc (leavesSum C.S table.1)
          (Lkp.summandLeaves C.S zeroE s.draw (Lkp.defaultOrder (C.S.mu + C.S.d))) false [C.bitsAt]
          fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d))).ctx
          ((rDraw "ZERO" work (C.S.mu + C.S.d)).entry :: (pscEntries work (bitsSize C.S) ++ es'))
          last8) := by
    rw [← hLsz]
    exact hrun8
  generalize hs8 : table.2.afterPsc (leavesSum C.S table.1)
      (Lkp.summandLeaves C.S zeroE s.draw (Lkp.defaultOrder (C.S.mu + C.S.d))) false [C.bitsAt]
      (fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d))) = s8 at hf8 hl8 hk8 hx' hrun8'
  -- ZERO
  obtain ⟨hf9, hz9, hrun9⟩ := L.draws_val work (C.S.mu + C.S.d) "ZERO" _ s8 last8 hq8 hf8
  -- the bits
  have hOl := defaultOrder_length (C.S.mu + C.S.d)
  have hBsz : Psc.sizeOf (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d)))
      Lkp.summandBits = bitsSize C.S := by
    simp [Psc.sizeOf, levelSum, Lkp.summandBits, bitsSize, Psc.Weight.equality, List.map_map,
      Function.comp_def, List.map_const', hOl]
  have hBmk : Psc.masksOf (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d)))
      Lkp.summandBits = 1 + 2 * (C.S.mu + C.S.d) + 2 + 1 := by
    simp [Psc.masksOf, Psc.varsOf, Psc.hidingEntries, levelSum, Lkp.summandBits,
      Psc.Weight.equality, Psc.Weight.atZero, List.map_map, Function.comp_def, List.map_const', hOl]
    omega
  have hBlen : (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d))).vars.length =
      C.S.mu + C.S.d := by
    simp [levelSum, hOl]
  obtain ⟨last10, hf10, hq10, hrun10, hpt10, hends10, hall10, hl10, hk10⟩ :=
    L.psc_val work (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d)))
        Lkp.summandBits
      false [] (fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d))) es' s8.next _
      (noRows_rDraw "ZERO" work (C.S.mu + C.S.d))
      (by rw [hBsz]; exact hf9)
      (by simp [Psc.formOK, Lkp.summandBits, levelSum, Psc.Weight.fits, Psc.Weight.equality])
      (fun _ _ => rfl)
      (by
        intro x hx
        simp only [Psc.varsOf, Lkp.summandBits, levelSum] at hx
        simp at hx
        rcases hx with ⟨t, _, rfl⟩ | rfl <;> simp [Psc.Weight.equality, Psc.Weight.atZero])
      (by simp [Psc.varsOf, Lkp.summandBits]) (by simp [Psc.varsOf, Lkp.summandBits])
      (by
        rw [hBmk]
        simp only [ownOf, Bool.false_eq_true, if_false]
        show _ ≤ C.left s8.led
        rw [hl8, hl7, hl6', hl4, hl3, hl2']
        omega)
      (Nat.zero_le _) (by intro hh; cases hh) (Nat.zero_le _)
      (by intro p hp; simp [levelSum] at hp) rfl
      (by intro m hm; simp at hm) (fun p => byVariable_length p _)
  rw [hBmk] at hl10
  simp only [ownOf, keyOf, Bool.false_eq_true, if_false, Nat.sub_zero] at hl10 hk10
  have hrun10' : (Lkp.psc C.env (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d)))
      Lkp.summandBits false [] fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d)))
      (s8.next.ctx (pscEntries work (bitsSize C.S) ++ es')
        (some (rDraw "ZERO" work (C.S.mu + C.S.d)).entry)) =
      .ok (s8.next.pscOut (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d)))
          Lkp.summandBits false (fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d))),
        (s8.next.afterPsc (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d)))
          Lkp.summandBits false [] fun p => Lkp.byVariable p
              (Lkp.defaultOrder (C.S.mu + C.S.d))).ctx
          es' last10) := by
    rw [← hBsz]
    exact hrun10
  obtain ⟨e9, he9⟩ : ∃ a, (s8.next.pscOut
      (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d))) Lkp.summandBits false
      (fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d)))).ends = [a] := by
    have h3 : (s8.next.pscOut
      (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d))) Lkp.summandBits false
      (fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d)))).ends.length = 1 := hends10
    match (s8.next.pscOut
      (levelSum ⟨s8.draws, [], zeroE⟩ (Lkp.defaultOrder (C.S.mu + C.S.d))) Lkp.summandBits false
      (fun p => Lkp.byVariable p (Lkp.defaultOrder (C.S.mu + C.S.d)))).ends, h3 with
    | [a], _ => exact ⟨a, rfl⟩
  have h9 := hall10 e9 (by simp [he9])
  simp only [he9, List.getD_cons_zero] at hx'
  have hrowA : C.Fine (pointRow e9 C.bitsAt) := by
    unfold pointRow
    apply L.fineMasks _ _ _ (h9.2 rfl)
    exact L.mapsOK_bits h.small C.bitsAt (List.mem_singleton.2 rfl) { target := e9.value } e9.point
        oneE
      (L.fineTarget _) (by rw [h9.1, hpt10, hBlen])
  have hrowB : C.Fine C.countsRow := by
    apply L.finePlanes _ _ (L.fineTarget _)
    · simp [Tensor.vars]
    · have := h.small
      simp [Tensor.ok, Tensor.vars, distinctNats, this]
    · rfl
  subst hx'
  refine ⟨last10, hq10, hf10, ?_, ?_, hc6, ?_⟩
  · refine Eq.trans hl10 ?_
    show C.left s8.led - _ = _
    rw [hl8, hl7, hl6', hl4, hl3, hl2']
    omega
  · refine Eq.trans hk10 ?_
    show C.keyLeft s8.led = _
    simp only [hk8, hk7, hk6', hk4, hk3, hk2', Nat.sub_zero]
  unfold Lkp.run
  simp only [show C.env.S = C.S from rfl, h.noShift, Bool.false_eq_true, if_false]
  rw [bind_ok (pure_ok _ _)]
  refine (bind_ok hrun1).trans ?_
  refine (bind_ok (L.note _ _ _ _ _ _ _ _)).trans ?_
  refine (bind_ok (L.note _ _ _ _ _ _ _ _)).trans ?_
  refine (bind_ok hrun2).trans ?_
  rw [he]
  simp only []
  rw [bind_ok (pure_ok _ _)]
  refine (bind_ok hrun3).trans ?_
  refine (bind_ok hrun4).trans ?_
  refine (bind_ok hrun5).trans ?_
  refine (bind_ok (L.note _ _ _ _ _ _ _ _)).trans ?_
  refine (bind_ok hrun6).trans ?_
  refine (bind_ok hrun7).trans ?_
  refine (bind_ok hrun8').trans ?_
  refine (bind_ok (L.note _ _ _ _ _ _ _ _)).trans ?_
  refine (bind_ok hrun9).trans ?_
  refine (bind_ok hrun10').trans ?_
  rw [he9]
  refine (bind_ok (get_ok e9 _)).trans ?_
  refine (bind_ok (L.leave _ _ _ _ _ _ hrowA)).trans ?_
  refine (bind_ok (L.leave _ _ _ _ _ _ hrowB)).trans ?_
  refine (bind_ok (must_ok (by simp [hc6.length]) _)).trans ?_
  refine (bind_ok (L.noteKeys_val _ _ _ _ _ _ _)).trans ?_
  rfl

/-- THE CALL AS A FUNCTION. At any caller that meets the laws, a call of the lookup verifier from a
stand gives what the stand's course says. -/
theorem Caller.Laws.verify_val (L : C.Laws) (work : Nat) (h : Ready C.S) (es' : List Fmt.Entry)
    (s : C.Stand) (last0 : Option Fmt.Entry) (hq0 : NoRows last0)
    (hfit : FitsAll s.rounds (lookupEntries C.S work es'))
    (h1 : ownTotal C.S ≤ C.left s.led) (h2 : treesKey C.S.parts ≤ C.keyLeft s.led) :
    ∃ last, NoRows last ∧ FitsAll s.course.last.rounds es' ∧
      C.left s.course.last.led = C.left s.led - ownTotal C.S ∧
      C.keyLeft s.course.last.led = C.keyLeft s.led - treesKey C.S.parts ∧
      PointsAt C.S.parts s.course.keys.1 ∧
      (Lkp.verify C.S C.planesAt C.masks C.group (some C.keyMasks))
          (s.ctx (lookupEntries C.S work es') last0) =
        .ok (s.course.out, s.course.last.ctx es' last) := by
  obtain ⟨last, hq, hf, hl, hk, hc, hrun⟩ := L.run_val work h es' s last0 hq0 hfit h1 h2
  refine ⟨last, hq, hf, hl, hk, hc, ?_⟩
  unfold Lkp.verify
  refine (bind_ok (L.sampled _ _ _ _ _ _ (by
    intro o ho
    simp at ho
    rcases ho with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)))).trans ?_
  refine (bind_ok (must_ok h.ok _)).trans ?_
  refine (bind_ok (L.sampled _ _ _ _ _ _ (fun o ho => Or.inr (Or.inr ho)))).trans ?_
  exact hrun

end OnBytes.G4

#print axioms OnBytes.G4.Caller.Laws.verify_val
