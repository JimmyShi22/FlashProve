-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/KeyLookup/PortRead.lean: the pure parts of the program's lookup that stand between
its sumchecks, read in the field: the join of two claims on a line, the join of the planes' claims,
a point put back by variable.

The program computes these on machine words (`lineAt`, OnBytes/Iop/Psc.lean; `Lkp.joinPlanes`,
`Lkp.byVariable`, OnBytes/Iop/Lkp.lean; `eqWeight`, OnBytes/Field/Mle.lean). This file has the same
texts over the field and proves that the program's functions, read (`readE`, `readPC`), are these.
Then it says what their mask forms and values are, read as functions on a type of entries
(`rdMF`, OnBytes/Tie/Pv/KeyLookup/PortSim.lean).

Main names:
  `eqW`, `lineF`, `joinOneF`, `joinF`, `byVarF`: the texts over the field.
  `read_eqW`, `read_lineF`, `read_joinF`, `read_byVarF`: the program's functions read as these.
  `rdMF_lineF`: the mask form of a join on a line is (1 - rho) times the first claim's plus rho
  times the second's.
  `joinF_point`, `rdMF_joinF`, `joinF_value`: the planes' claims as one: the point is the drawn
  one; mask form and value are the sums over the 2^mu planes of the equality weight times the
  plane's; a plane without a claim gives its weight to the value and nothing to the mask form.

Limits. No block of the program, no run on a view, no statement on soundness.

-/
import OnBytes.Tie.Pv.KeyLookup.PortSim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.PortSim

open OnBytes OnBytes.Slice

/-! ## The equality weight -/

/-- r times the product, over the coordinates x of the point, of x if the matching bit of j is 1
and of 1 - x if it is 0; the first coordinate goes with the lowest bit. -/
def eqW : List GE → ℕ → GE → GE
  | [], _, r => r
  | x :: xs, j, r => eqW xs (j / 2) (r * (if j % 2 == 1 then x else 1 - x))

/-- One step of the program's equality weight, as an equation between functions of the index and
the factor: stated of values, the kernel would open the arithmetic on words. -/
theorem eqWeight_step (x : E) (xs : List E) :
    eqWeight (x :: xs) =
      fun j r => eqWeight xs (j / 2) (mulE r (if j % 2 == 1 then x else subE oneE x)) := rfl

/-- The program's equality weight, read. -/
theorem read_eqW : ∀ (z : List E) (j : ℕ) (r : E),
    readE (eqWeight z j r) = eqW (z.map readE) j (readE r)
  | [], _, _ => rfl
  | x :: xs, j, r => by
    rw [congrFun (congrFun (eqWeight_step x xs) j) r, read_eqW xs]
    show _ = eqW (xs.map readE) (j / 2) (readE r * (if j % 2 == 1 then readE x else 1 - readE x))
    rw [readE_mul]
    split
    · rfl
    · rw [readE_sub, readE_one]

/-! ## Two claims on a line -/

/-- (1 - rho) times the first claim plus rho times the second, at the first claim's point with rho
as one more coordinate. -/
def lineF (rho : GE) (a b : PscF.PointClaim) : PscF.PointClaim where
  point := a.point ++ [rho]
  masks := PscF.scaleForm (1 - rho) a.masks ++ PscF.scaleForm rho b.masks
  value := (1 - rho) * a.value + rho * b.value

/-- The program's join on a line, read. -/
theorem read_lineF (rho : E) (a b : PointClaim) :
    readPC (lineAt rho a b) = lineF (readE rho) (readPC a) (readPC b) := by
  unfold readPC lineAt lineF
  simp only [List.map_append, List.map_cons, List.map_nil, readForm_append, read_scaleForm,
    readE_add, readE_mul, readE_sub, readE_one]

variable {J : Type} [DecidableEq J] (sl : Slot → J)

/-- The mask form of a join on a line. -/
theorem rdMF_lineF (rho : GE) (a b : PscF.PointClaim) (j : J) :
    rdMF sl (lineF rho a b).masks j =
      (1 - rho) * rdMF sl a.masks j + rho * rdMF sl b.masks j := by
  show rdMF sl (PscF.scaleForm (1 - rho) a.masks ++ PscF.scaleForm rho b.masks) j = _
  rw [rdMF_append, rdMF_scale, rdMF_scale]

/-! ## The planes' claims as one -/

/-- One step of the loop: at a weight, a plane's claim, or none, joins the claim c. -/
def joinAtF (w : GE) (o : Option PscF.PointClaim) (c : PscF.PointClaim) : PscF.PointClaim :=
  match o with
  | some p =>
    { c with masks := c.masks ++ PscF.scaleForm w p.masks, value := c.value + w * p.value }
  | none => { c with value := c.value + w }

/-- One step of the loop: plane j joins the claim c. -/
def joinOneF (r : List GE) (l : List PscF.PointClaim) (c : PscF.PointClaim) (j : ℕ) :
    PscF.PointClaim := joinAtF (eqW r j 1) l[j]? c

/-- The claims on the planes' roots as one claim at the point r. A plane without a claim has the
root 1. -/
def joinF (mu : ℕ) (r : List GE) (l : List PscF.PointClaim) : PscF.PointClaim :=
  (List.range (2 ^ mu)).foldl (joinOneF r l) ⟨r, [], 0⟩

/-- The step in the program's text, at a weight. -/
def joinAtP (w : E) (o : Option PointClaim) (c : PointClaim) : PointClaim :=
  match o with
  | some p =>
    { c with masks := c.masks ++ Psc.scaleForm w p.masks, value := addE c.value (mulE w p.value) }
  | none => { c with value := addE c.value w }

/-- One step at a weight, read. -/
theorem read_joinAt (w : E) (o : Option PointClaim) (c : PointClaim) :
    readPC (joinAtP w o c) = joinAtF (readE w) (o.map readPC) (readPC c) := by
  cases o with
  | none =>
    show readPC { c with value := addE c.value w } =
      { readPC c with value := (readPC c).value + readE w }
    unfold readPC
    simp only
    rw [readE_add]
  | some p =>
    show readPC { c with masks := c.masks ++ Psc.scaleForm w p.masks,
                         value := addE c.value (mulE w p.value) } =
      { readPC c with
        masks := (readPC c).masks ++ PscF.scaleForm (readE w) (readPC p).masks,
        value := (readPC c).value + readE w * (readPC p).value }
    unfold readPC
    simp only
    rw [readForm_append, read_scaleForm, readE_add, readE_mul]

/-- A loop, read: if each step reads as a step on the readings, so does the loop. -/
theorem foldl_read {α β γ : Type} (f : α → γ → α) (g : β → γ → β) (rd : α → β)
    (h : ∀ a j, rd (f a j) = g (rd a) j) : ∀ (js : List γ) (a : α),
    rd (js.foldl f a) = js.foldl g (rd a)
  | [], _ => rfl
  | j :: js, a => by
    rw [List.foldl_cons, List.foldl_cons, foldl_read f g rd h js, h]

/-- **The program's join of the planes' claims, read.** -/
theorem read_joinF (S : Lkp.Public) (r : List E) (l : List PointClaim) :
    readPC (Lkp.joinPlanes S r l) = joinF S.mu (r.map readE) (l.map readPC) := by
  have h1 : ∀ (c : PointClaim) (j : ℕ), readPC (joinAtP (eqWeight r j oneE) l[j]? c) =
      joinOneF (r.map readE) (l.map readPC) (readPC c) j := fun c j => by
    rw [read_joinAt, read_eqW, readE_one, ← List.getElem?_map]
    rfl
  have h0 : readPC ⟨r, [], zeroE⟩ = (⟨r.map readE, [], 0⟩ : PscF.PointClaim) := by
    show (⟨r.map readE, readForm [], readE zeroE⟩ : PscF.PointClaim) = _
    rw [readE_zero]
    rfl
  have h : ∀ js : List ℕ,
      readPC (js.foldl (fun c j => joinAtP (eqWeight r j oneE) l[j]? c) ⟨r, [], zeroE⟩) =
      js.foldl (joinOneF (r.map readE) (l.map readPC)) ⟨r.map readE, [], 0⟩ := fun js => by
    rw [foldl_read _ _ readPC h1, h0]
  exact h _

/-- What a plane gives to the mask form. -/
def planeMF (r : List GE) (l : List PscF.PointClaim) (j : J) (k : ℕ) : GE :=
  match l[k]? with
  | some p => eqW r k 1 * rdMF sl p.masks j
  | none => 0

/-- What a plane gives to the value. -/
def planeVal (r : List GE) (l : List PscF.PointClaim) (k : ℕ) : GE :=
  match l[k]? with
  | some p => eqW r k 1 * p.value
  | none => eqW r k 1

/-- The loop leaves the point, and adds each plane's share to mask form and value. -/
theorem join_loop (r : List GE) (l : List PscF.PointClaim) (j : J) : ∀ (ks : List ℕ)
    (c : PscF.PointClaim),
    (ks.foldl (joinOneF r l) c).point = c.point ∧
    rdMF sl (ks.foldl (joinOneF r l) c).masks j =
      rdMF sl c.masks j + (ks.map (planeMF sl r l j)).sum ∧
    (ks.foldl (joinOneF r l) c).value = c.value + (ks.map (planeVal r l)).sum
  | [], c => ⟨rfl, (add_zero _).symm, (add_zero _).symm⟩
  | k :: ks, c => by
    obtain ⟨hp, hm, hv⟩ := join_loop r l j ks (joinOneF r l c k)
    rw [List.foldl_cons, hp, hm, hv, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    unfold joinOneF joinAtF planeMF planeVal
    cases l[k]? with
    | none => exact ⟨rfl, by simp only; ring, by simp only; ring⟩
    | some p =>
      refine ⟨rfl, ?_, by simp only; ring⟩
      simp only
      rw [rdMF_append, rdMF_scale]
      ring

/-- The joined claim's point is the drawn one. -/
theorem joinF_point (mu : ℕ) (r : List GE) (l : List PscF.PointClaim) :
    (joinF mu r l).point = r :=
  (join_loop (fun s : Slot => s) r l ⟨0, 0⟩ (List.range (2 ^ mu)) ⟨r, [], 0⟩).1

/-- **The joined claim's mask form.** -/
theorem rdMF_joinF (mu : ℕ) (r : List GE) (l : List PscF.PointClaim) (j : J) :
    rdMF sl (joinF mu r l).masks j = ((List.range (2 ^ mu)).map (planeMF sl r l j)).sum := by
  have h := (join_loop sl r l j (List.range (2 ^ mu)) ⟨r, [], 0⟩).2.1
  rw [rdMF_nil, zero_add] at h
  exact h

/-- **The joined claim's value.** -/
theorem joinF_value (mu : ℕ) (r : List GE) (l : List PscF.PointClaim) :
    (joinF mu r l).value = ((List.range (2 ^ mu)).map (planeVal r l)).sum := by
  have h := (join_loop (fun s : Slot => s) r l ⟨0, 0⟩ (List.range (2 ^ mu)) ⟨r, [], 0⟩).2.2
  rw [zero_add] at h
  exact h

/-! ## A point put back by variable -/

/-- A point given round by round, with each coordinate put back at its variable's place. -/
def byVarF (byRound : List GE) (order : List ℕ) : List GE :=
  (List.range byRound.length).map fun t => ((order.zip byRound).lookup t).getD 0

/-- Looking up a key in a list of pairs whose second members are read. -/
theorem lookup_read (t : ℕ) : ∀ l : List (ℕ × E),
    (l.map fun p => (p.1, readE p.2)).lookup t = (l.lookup t).map readE
  | [] => rfl
  | (k, x) :: l => by
    show List.lookup t ((k, readE x) :: l.map fun p => (p.1, readE p.2)) = _
    rw [List.lookup_cons, List.lookup_cons]
    cases t == k
    · exact lookup_read t l
    · rfl

/-- The program's putting back by variable, read. -/
theorem read_byVarF (p : List E) (order : List ℕ) :
    (Lkp.byVariable p order).map readE = byVarF (p.map readE) order := by
  unfold Lkp.byVariable byVarF
  rw [List.map_map, List.length_map, zip_read_right]
  refine List.map_congr_left fun t _ => ?_
  show readE (((order.zip p).lookup t).getD zeroE) = _
  rw [lookup_read, read_optD]

end Lk6.PortSim

#print axioms Lk6.PortSim.eqWeight_step
#print axioms Lk6.PortSim.read_eqW
#print axioms Lk6.PortSim.read_lineF
#print axioms Lk6.PortSim.rdMF_lineF
#print axioms Lk6.PortSim.read_joinAt
#print axioms Lk6.PortSim.foldl_read
#print axioms Lk6.PortSim.read_joinF
#print axioms Lk6.PortSim.join_loop
#print axioms Lk6.PortSim.joinF_point
#print axioms Lk6.PortSim.rdMF_joinF
#print axioms Lk6.PortSim.joinF_value
#print axioms Lk6.PortSim.lookup_read
#print axioms Lk6.PortSim.read_byVarF
