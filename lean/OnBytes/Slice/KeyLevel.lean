-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyLevel.lean: a level of a product tree, as a step, with its soundness.

A product tree has a map on each level. On the cube, a level's map is the product of the two halves
of the next level's map in its last variable. The verifier goes down from a claim on the root
(OnBytes/Iop/Lkp.lean: levelChain). At a level it holds a claim on the level's map at a point. A
zero-knowledge sumcheck on the product of two shown maps, under equality weights at the point's
coordinates, hands on a row on mask entries, which is put aside, and a claim on each half
(OnBytes/Slice/KeyPsc.lean). Then the verifier draws one element rho, and the two claims become one
claim on the next level's map, at the sumcheck's point with rho as one more coordinate.

This file has the functions of that text over the field, with the same text (defaultOrder,
byVariable, summandProduct, levelSum, Out.placed, lineAt). The ledger of free mask entries is kept
as a list for each oracle message (fresh); that is a reading of the program's ledger, not its text.
The file makes a step of the written rounds of a level (levelStep) and proves its soundness
(level_sem): if a row that was put aside is false or the claim on the level's map is false, then,
but for the counted verifier messages, the same is true after the level of the rows and the claim on
the next level's map. A tree is so many levels in a row (treeStep, tree_sem).

The order of rounds. The sumcheck binds the variables in a stated order, a parameter here. What is
asked of the two maps is stated for the order (LevelMaps): the two halves, as functions of the point
round by round, are multilinear; the level's map at a point is the sum over the cube of the equality
polynomial times the halves; the next level's map is affine in its last variable.

The proofs are our own. The error counts: those of the sumcheck, and 1 for rho.

Main definitions: PscF.defaultOrder, byVariable, summandProduct, levelSum, Out.placed, fresh,
lineAt, LvSt, LevelMaps, levelPsc, levelNext, lineStep, levelStep, LvSt.Good, treeStep.

Main theorems: PscF.sums_level, levelPsc_sem, line_sem, level_sem, tree_sem.

Not claimed. That the program's run on a view is this step's next state. That a given tree's maps
meet LevelMaps. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyPsc
import OnBytes.Slice.KeyLevelF

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

namespace PscF

/-! ## The program's functions, over the field -/

/-- From the highest variable down. -/
def defaultOrder (n : ℕ) : List ℕ := (List.range n).reverse

/-- A point given round by round, with each coordinate put back at its variable's place. Round j
has bound variable order[j]. -/
def byVariable (byRound : List GE) (order : List ℕ) : List GE :=
  (List.range byRound.length).map fun t => ((order.zip byRound).lookup t).getD 0

/-- The product of two shown maps. -/
def summandProduct : Summand where
  shown := 2
  kept := 0
  degree := 2
  coeffs := fun _ y => [y.getD 0 0 * y.getD 1 0]

/-- The sum claim of a level: equality weights at the coordinates of the claim's point, in the
order of the rounds. -/
def levelSum (order : List ℕ) (c : PointClaim) : Claim where
  vars := order.map fun t => Weight.equality (c.point.getD t 0) 3
  masks := c.masks
  target := c.value

/-- What a run hands on, with its points put back by variable. -/
def Out.placed (place : List GE → List GE) (o : Out) : Out :=
  { o with
    point := place o.point
    ends := o.ends.map fun x => { x with point := place x.point } }

/-- Takes the next n free mask entries. free: for each oracle message its free mask entries still to
come. keys: the last two come from the message oK, the others from oM. Returns the entries and what
is still free. -/
def fresh (oM oK n : ℕ) (keys : Bool) (free : ℕ → List ℕ) : List Slot × (ℕ → List ℕ) :=
  if keys then
    let free' := Function.update free oM ((free oM).drop (n - 2))
    (((free oM).take (n - 2)).map (⟨oM, ·⟩) ++ ((free' oK).take 2).map (⟨oK, ·⟩),
      Function.update free' oK ((free' oK).drop 2))
  else (((free oM).take n).map (⟨oM, ·⟩), Function.update free oM ((free oM).drop n))

/-- (1 - rho) times the first claim plus rho times the second, at the first claim's point with
rho as one more coordinate. -/
def lineAt (rho : GE) (half0 half1 : PointClaim) : PointClaim where
  point := half0.point ++ [rho]
  masks := scaleForm (1 - rho) half0.masks ++ scaleForm rho half1.masks
  value := (1 - rho) * half0.value + rho * half1.value

/-! ## The level's summand has a tower -/

/-- The variables of a level's sumcheck. -/
theorem varsOf_level (order : List ℕ) (c : PointClaim) :
    varsOf (levelSum order c) summandProduct =
      (order.map fun t => c.point.getD t 0).map (Weight.equality · 3) ++ [Weight.atZero 3] := by
  show (order.map fun t => Weight.equality (c.point.getD t 0) 3) ++ [Weight.atZero 3] = _
  rw [List.map_map]
  rfl

/-- The tower of a level's summand, for any two multilinear halves F0, F1 (as functions of the
point round by round), any values of the mask entries and any fresh entries. -/
theorem sums_level (W : World) (F0 F1 : List GE → GE) (order : List ℕ) (h0 : ML order.length F0)
    (h1 : ML order.length F1) (c : PointClaim) (fr : List Slot) :
    Sums W (fun j => if j = 0 then F0 else F1) (fun _ _ => 0) (levelSum order c) summandProduct fr
      (prodT
        (W.mask ((fr.drop (hidingEntries (varsOf (levelSum order c) summandProduct))).getD 0
          default))
        (W.mask ((fr.drop (hidingEntries (varsOf (levelSum order c) summandProduct))).getD 1
          default))
        (order.map fun t => c.point.getD t 0) F0 F1) where
  tower := by
    rw [varsOf_level]
    exact tower_prodT _ _ _ _ _ (by rwa [List.length_map]) (by rwa [List.length_map])
  last := by
    intro γ hγ
    rw [varsOf_level, List.length_append, List.length_map, List.length_map] at hγ
    have hne : γ ≠ [] := fun h => by simp [h] at hγ
    obtain ⟨γX, β, rfl⟩ : ∃ γX β, γ = γX ++ [β] :=
      ⟨γ.dropLast, γ.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hX : γX.length = order.length := by simpa using hγ
    rw [prodT_full _ _ _ _ _ _ _ (by rw [List.length_map]; exact hX)]
    have ht : (γX ++ [β]).take (levelSum order c).vars.length = γX := by
      show (γX ++ [β]).take (order.map _).length = γX
      rw [List.length_map, ← hX, List.take_left']
      rfl
    unfold summandAt
    simp only [ht]
    simp [summandProduct, List.range_succ, dot_nil_left]

end PscF

/-! ## The level -/

/-- The state between levels: the claim on the level's map, the free mask entries of each oracle
message, and the rows that were put aside (a mask form and a target each). -/
structure LvSt where
  claim : PscF.PointClaim
  free : ℕ → List ℕ
  rows : List (PscF.MaskForm × GE)

/-- All rows hold. -/
def RowsOK (W : PscF.World) (rows : List (PscF.MaskForm × GE)) : Prop :=
  ∀ r ∈ rows, W.form r.1 = r.2

/-- All rows that were put aside hold, and the claim holds of the map A. -/
def LvSt.Good (W : PscF.World) (A : List GE → GE) (x : LvSt) : Prop :=
  RowsOK W x.rows ∧ x.claim.Holds W A

/-- What is asked of a level's map A and the next level's map A', for the order of the rounds.
Points of A and A' are by variable. -/
structure LevelMaps (order : List ℕ) (A A' : List GE → GE) : Prop where
  /-- the two halves, as functions of the point round by round, are multilinear -/
  ml0 : PscF.ML order.length fun p => A' (PscF.byVariable p order ++ [0])
  ml1 : PscF.ML order.length fun p => A' (PscF.byVariable p order ++ [1])
  /-- the level's map is the sum over the cube of the equality polynomial times the halves -/
  sum : ∀ z : List GE, z.length = order.length →
    A z = PscF.bil (order.map fun t => z.getD t 0) (fun p => A' (PscF.byVariable p order ++ [0]))
      fun p => A' (PscF.byVariable p order ++ [1])
  /-- the next level's map is affine in its last variable -/
  line : ∀ (q : List GE) (ρ : GE), A' (q ++ [ρ]) = (1 - ρ) * A' (q ++ [0]) + ρ * A' (q ++ [1])

section
variable (dEps dRound dY dVals dLine : PQ.RD) (order : List ℕ) (oM oK : ℕ) (keys : Bool)

/-- The fresh mask entries of a level's sumcheck, and what is still free after it. -/
def lvFresh (x : LvSt) : List Slot × (ℕ → List ℕ) :=
  PscF.fresh oM oK (PscF.masksOf (PscF.levelSum order x.claim) PscF.summandProduct) keys x.free

/-- The sumcheck of a level, as a step. It also tests that the claim's point has as many
coordinates as there are rounds of variables. -/
def levelPsc : Step LvSt (LvSt × PscF.Out) :=
  (pscStepY dEps (List.replicate order.length dRound) dY dVals
    (fun x => PscF.levelSum order x.claim) (fun _ => PscF.summandProduct)
    (fun x => (lvFresh order oM oK keys x).1) (List.replicate order.length 3) 2).guard
    fun x => x.claim.point.length = order.length

/-- A claim that stands for a missing one. -/
def noClaim : PscF.PointClaim := ⟨[], [], 0⟩

/-- The state after a level, from the state before it, what the sumcheck hands on, and rho. -/
def levelNext (x : LvSt) (o : PscF.Out) (ρ : GE) : LvSt where
  claim := PscF.lineAt ρ ((o.placed (PscF.byVariable · order)).ends.getD 0 noClaim)
    ((o.placed (PscF.byVariable · order)).ends.getD 1 noClaim)
  free := (lvFresh order oM oK keys x).2
  rows := x.rows ++ [((o.placed (PscF.byVariable · order)).rowMasks,
    (o.placed (PscF.byVariable · order)).rowTarget)]

/-- What the round of rho tests: two claims were handed on, and their points are equal. -/
def LineOK (o : PscF.Out) : Prop :=
  o.ends.length = 2 ∧ ((o.placed (PscF.byVariable · order)).ends.getD 0 noClaim).point =
    ((o.placed (PscF.byVariable · order)).ends.getD 1 noClaim).point

/-- The round of rho, as a step. -/
def lineStep : Step (LvSt × PscF.Out) LvSt :=
  Step.one dLine (1 * (bsRound .two dLine.entry dLine.kind).w) (fun p _ _ => LineOK order p.2)
    fun p _ c => levelNext order oM oK keys p.1 p.2 (gOne _ (valsOf dLine c))

/-- A level, as a step. -/
def levelStep : Step LvSt LvSt :=
  (levelPsc dEps dRound dY dVals order oM oK keys).seq (lineStep dLine order oM oK keys)

variable {dEps dRound dY dVals dLine order} (W : PscF.World) {A A' : List GE → GE}

/-- What stands between the sumcheck and the round of rho: the rows put aside hold, and what the
sumcheck hands on holds of the two halves. -/
def MidGood (order : List ℕ) (W : PscF.World) (A' : List GE → GE) (p : LvSt × PscF.Out) : Prop :=
  p.2.Holds W (fun j => if j = 0 then fun q => A' (PscF.byVariable q order ++ [0])
    else fun q => A' (PscF.byVariable q order ++ [1])) (fun _ _ => 0) 0 ∧ RowsOK W p.1.rows

/-- Soundness of a level's sumcheck. -/
theorem levelPsc_sem (hm : LevelMaps order A A') (hE : OneEl dEps) (hR : OneEl dRound)
    (hY : OneEl dY) :
    (levelPsc dEps dRound dY dVals order oM oK keys).Sem (LvSt.Good W A) (MidGood order W A') := by
  have h := psc_sem dEps (List.replicate order.length dRound) dY dVals
    (fun x : LvSt => PscF.levelSum order x.claim) (fun _ => PscF.summandProduct)
    (fun x => (lvFresh order oM oK keys x).1) (List.replicate order.length 3) 2 hE
    (fun d hd => by rw [List.eq_of_mem_replicate hd]; exact hR) hY
    (fun x => x.claim.point.length = order.length)
    (fun x _ =>
      { len := by
          show (order.map _).length = _
          rw [List.length_map, List.length_replicate]
        dims := by
          show (order.map _).map _ = _
          rw [List.map_map]
          exact List.map_const'
        ok := fun w hw => by
          obtain ⟨t, _, rfl⟩ := List.mem_map.1 hw
          exact PscF.equality_ok _ 3 (by decide)
        shown := by decide
        deg := rfl
        pos := by decide })
    W (fun _ j => if j = 0 then fun q => A' (PscF.byVariable q order ++ [0])
      else fun q => A' (PscF.byVariable q order ++ [1])) (fun _ _ _ => 0) _
    (fun x _ => PscF.sums_level W _ _ order hm.ml0 hm.ml1 x.claim _)
  refine Step.Sem.guard ((h.frame (R := fun x : LvSt => RowsOK W x.rows)
    (R' := fun p : LvSt × PscF.Out => RowsOK W p.1.rows) fun _ _ hr => hr).conseq
    (fun x hx hF => ?_) fun _ hp => hp)
  refine ⟨hx.2, ?_⟩
  have h1 := hx.1 hF
  rw [PscF.prodT_nil, ← hm.sum _ hF] at h1
  exact h1

/-- Soundness of the round of rho. -/
theorem line_sem (hm : LevelMaps order A A') (hL : OneEl dLine) :
    (lineStep dLine order oM oK keys).Sem (MidGood order W A') (LvSt.Good W A') := by
  intro p hp
  refine draw_cnt dLine (gOne _) hL.inj hL.logN [] () 1
    (fun _ ρ => LineOK order p.2 ∧ (levelNext order oM oK keys p.1 p.2 ρ).Good W A')
    (fun _ => ?_) _ (fun m c _ hc h => ?_) fun _ _ hB _ ho hg => hB ⟨ho, hg⟩
  · by_cases hok : LineOK order p.2
    swap
    · rw [cnt_false fun _ h => hok h.1]
      exact Nat.zero_le _
    obtain ⟨e0, e1, he⟩ := List.length_eq_two.1 hok.1
    have hpl : (p.2.placed (PscF.byVariable · order)).ends =
        [{ e0 with point := PscF.byVariable e0.point order },
          { e1 with point := PscF.byVariable e1.point order }] := by
      show p.2.ends.map _ = _
      rw [he]
      rfl
    have hq : PscF.byVariable e0.point order = PscF.byVariable e1.point order := by
      have h := hok.2
      rw [hpl] at h
      exact h
    -- what a good state after the round says
    have key : ∀ ρ, (levelNext order oM oK keys p.1 p.2 ρ).Good W A' →
        RowsOK W p.1.rows ∧ W.form p.2.rowMasks = p.2.rowTarget ∧
        (1 - ρ) * (A' (PscF.byVariable e0.point order ++ [0]) + W.form e0.masks - e0.value) +
          ρ * (A' (PscF.byVariable e1.point order ++ [1]) + W.form e1.masks - e1.value) = 0 := by
      intro ρ hg
      refine ⟨fun r hr => hg.1 r (List.mem_append_left _ hr),
        hg.1 (p.2.rowMasks, p.2.rowTarget) (List.mem_append_right _ List.mem_cons_self), ?_⟩
      have h2 : A' (PscF.byVariable e0.point order ++ [ρ]) +
          W.form (PscF.scaleForm (1 - ρ) e0.masks ++ PscF.scaleForm ρ e1.masks) =
          (1 - ρ) * e0.value + ρ * e1.value := by
        have h3 := hg.2
        unfold levelNext PscF.PointClaim.Holds at h3
        simp only [hpl] at h3
        exact h3
      rw [PscF.World.form_append, PscF.World.form_scale, PscF.World.form_scale, hm.line] at h2
      rw [← hq]
      linear_combination h2
    refine cnt_le_one fun ρ ρ' h1 h2 => ?_
    obtain ⟨hr, hrow, k1⟩ := key ρ h1.2
    obtain ⟨_, _, k2⟩ := key ρ' h2.2
    by_contra hne
    have hd : A' (PscF.byVariable e1.point order ++ [1]) + W.form e1.masks - e1.value =
        A' (PscF.byVariable e0.point order ++ [0]) + W.form e0.masks - e0.value := by
      have h3 : (ρ - ρ') * ((A' (PscF.byVariable e1.point order ++ [1]) + W.form e1.masks -
          e1.value) - (A' (PscF.byVariable e0.point order ++ [0]) + W.form e0.masks -
          e0.value)) = 0 := by linear_combination k1 - k2
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (sub_eq_zero.1 h4) hne
      · exact sub_eq_zero.1 h4
    have h0 : A' (PscF.byVariable e0.point order ++ [0]) + W.form e0.masks - e0.value = 0 := by
      rw [hd] at k1
      linear_combination k1
    refine hp ⟨⟨?_, fun j e hj => ?_⟩, hr⟩
    · show W.form p.2.rowMasks + PscF.dot p.2.rowMaps [] = p.2.rowTarget
      rw [PscF.dot_nil_right, add_zero, hrow]
    · rw [he] at hj
      match j, hj with
      | 0, hj =>
        obtain rfl := Option.some.inj hj
        exact sub_eq_zero.1 h0
      | 1, hj =>
        obtain rfl := Option.some.inj hj
        exact sub_eq_zero.1 (hd.trans h0)
      | _ + 2, hj => cases hj
  · rw [(passT_one dLine m c).1 h] at hc
    cases hc

/-- Soundness of a level. If a row that was put aside is false or the claim is false of the
level's map, then, but for the counted verifier messages, after the level a row is false or the
claim is false of the next level's map. -/
theorem level_sem (hm : LevelMaps order A A') (hE : OneEl dEps) (hR : OneEl dRound)
    (hY : OneEl dY) (hL : OneEl dLine) :
    (levelStep dEps dRound dY dVals dLine order oM oK keys).Sem (LvSt.Good W A) (LvSt.Good W A') :=
  (levelPsc_sem oM oK keys W hm hE hR hY).seq (line_sem oM oK keys W hm hL)

end

/-! ## A tree -/

/-- So many levels in a row. ord i, keys i: the order of the rounds of level i, and whether its
last two mask entries come from the second message. -/
def treeStep (dEps dRound dY dVals dLine : PQ.RD) (ord : ℕ → List ℕ) (oM oK : ℕ) (keys : ℕ → Bool)
    (k : ℕ) : Step LvSt LvSt :=
  Step.iter k (fun _ => LvSt) fun i =>
    levelStep dEps dRound dY dVals dLine (ord i) oM oK (keys i)

/-- Soundness of a tree. A i: the map of level i. -/
theorem tree_sem {dEps dRound dY dVals dLine : PQ.RD} (ord : ℕ → List ℕ) (oM oK : ℕ)
    (keys : ℕ → Bool) (k : ℕ) (W : PscF.World) (A : ℕ → List GE → GE)
    (hm : ∀ i, i < k → LevelMaps (ord i) (A i) (A (i + 1))) (hE : OneEl dEps)
    (hR : OneEl dRound) (hY : OneEl dY) (hL : OneEl dLine) :
    (treeStep dEps dRound dY dVals dLine ord oM oK keys k).Sem (LvSt.Good W (A 0))
      (LvSt.Good W (A k)) :=
  Step.Sem.iter k (fun _ => LvSt) _ (fun i => LvSt.Good W (A i)) fun i hi =>
    level_sem oM oK (keys i) W (hm i hi) hE hR hY hL

end OnBytes.Slice
