--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRowsFit.lean: IN THE KEY FILE'S FIRST CHAIN THE LOOKUPS' ROWS ARE LAID ONTO THE RANGES'
GROUP: the sub-protocol "rng.0.rows" (`layRows`, Johnson/Desc/Key/Link.lean) accepts, whatever was
sent, under hypotheses by name on FORM; and one condition on the chain's state (`Mid`) holds behind
the two sendings, is kept by every lookup's link, and gives that accept. General in the chain's
public values. Statements and proofs; nothing is evaluated.

Why. That sub-protocol adds every row which the lookups have written to the group of the proximity
test on the ranges (`addRowsP`). The step's test on a row has eight clauses (`rowL`,
Johnson/Desc/First/Base/Ground.lean). E2E/RowsFit.lean has the general half. Here: of which make the
lookups' rows are, and that a row of that make passes all eight.

WHICH CLAUSE BY WHAT.
- The group is there; no test has begun: the ranges' group behind "msg.1.send"
  (E2E/KeyLedgers.lean); a taking of mask entries turns no group.
- No sample row; no run; no form: the makers `rowOfAff`, `rowOfPlane` lay none.
- The terms fit: `Wf.planesAt` lays one term a block of planes, on the own message's main table; its
  number of variables hangs on the number of the claim's pairs alone (`termOf_laws`); that this
  number is the table's is A PREMISE ON PUBLIC NUMBERS (hT, hV).
- The single entries fit: each is the home of a slot; A HYPOTHESIS ON WHAT WAS HEARD says that the
  slots are the own message's (`Off`); their indexes were handed out by that message's ledger: they
  lie within its mask table.
- No coefficient on a pad: these indexes lie below the pad; the terms lie on the main table, the pad
  in the mask table: the coefficient is the empty sum.

What is defined.
  `unitsOf`, `blocksOf`, `termOf`, `setStep`, `canon`: names for pieces of the library's texts.
  `OwnOnly f a`: the form names no entry of a virtual row, and slots whose mark in `fromKeys f` is
    false.
  `markAt`, `Off`, `On`: a slot's mark counted from a ledger's slot; every slot of a form has the
    mark false; true.
  **`LookupShapedRow msg B P V r`**: the make of a lookup's rows.   **`Stand d g msg B P V`**: where they
    are laid.
  **`Mid one cs s i a b k₁ k₂ B V sm si`**: what holds of the chain's state in front of link i.
What is shown.
  `addMasks_laws`, `maskSide_homes`, `homesFrom_mark`, `maskSide_own`: a form's mask side names the
    homes of its slots; the home of a slot with the mark false is an entry of the own message.
  `addTerms_laws`, `planesAt_eq`, `setFold_laws`, `termOf_laws`, `inOrder_of`: the terms.
  **`fits_of_plain`**: `Stand` and `LookupShapedRow` give all eight clauses.
  `plain_of_aff`, `plain_of_plane`, `rowsInOrder_mem`, `planesG_pairs`, `ownOnly_of`,
    **`rows_plain`**: all rows that `layer` writes for one lookup are of that make.
  **`mid_of_front`**: `Mid` at 0 behind the two sendings, where both accept.
  **`link_keeps`**: under `Mid` at i and the link's premises the fold over the link accepts, and
    `Mid` holds at i + 1, with the entries taken.
  `addRows_same`: the step that adds open rows turns no message.
  **`layRows_accepts`**: under `Mid` at the number of lookups: "rng.0.rows" accepts, and turns no
    message.

Limits.
- HYPOTHESES BY NAME, shown of no run: `Left` (E2E/KeyLookupAround.lean) and `Off` of the hearing's
  rows and of the three claims' leads; the hearing's accept; `roundsFit`. E2E/KeyRowsFitToy.lean
  evaluates `Off` and `On` at synthetic rounds, at a small lookup and at the two of the full size.
- PREMISES ON PUBLIC NUMBERS, shown at no plan: hT, hV (the terms' variables); that the ledgers have
  as many entries as the links take; that the own message has main rows; that V is its main table's
  number of bits.
- That the two sendings accept is a premise of `mid_of_front`.
- No member of `Mid`, `Stand` or `LookupShapedRow` is typed.
- `link_keeps` is one step: E2E/KeyFirstHalf.lean folds the links of a list of lookups.
- FORM ALONE: that the rows which are laid hold of anything is not touched.
- Nothing on completeness as such, on soundness, or on what a view shows.


-/
import E2E.KeyLedgers

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLookup
open OnBytes
open OnBytes.Model (Fork Aff)
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Own (placeFits tableThere tensorInOrder allZero)
open VerifiableInference.Desc.K13.Law (LedgerAt tableSize_mask)
open OnBytes.Means (tableSize)
open AtPublicFiles.RowsFit

/-! ## 1. What a mask form adds to a row -/

/-- A mask form's members as single entries of a row. -/
def unitsOf (m : MaskForm) : List Single := m.map fun t => ⟨t.1.oracle, .mask, t.1.index, t.2⟩

theorem addMasks_laws : ∀ (m : MaskForm) (r : Row),
    (r.addMasks m).kind = r.kind ∧ (r.addMasks m).terms = r.terms ∧ (r.addMasks m).runs = r.runs ∧
      (r.addMasks m).forms = r.forms ∧ (r.addMasks m).units.toList = r.units.toList ++ unitsOf m
  | [], r => ⟨rfl, rfl, rfl, rfl, (List.append_nil _).symm⟩
  | t :: m, r => by
    obtain ⟨a, b, c, d, e⟩ := addMasks_laws m (r.addUnit t.1.oracle .mask t.1.index t.2)
    refine ⟨a, b, c, d, ?_⟩
    show ((r.addUnit t.1.oracle .mask t.1.index t.2).addMasks m).units.toList = _
    rw [e]
    show (r.units.push _).toList ++ _ = _
    rw [Array.toList_push, List.append_assoc]
    rfl

theorem unitsOf_neg (m : MaskForm) {u : Single} (hu : u ∈ unitsOf (negMasks m)) :
    ∃ p ∈ m, u.oracle = p.1.oracle ∧ u.part = .mask ∧ u.index = p.1.index := by
  unfold unitsOf negMasks at hu
  rw [List.map_map] at hu
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hu
  exact ⟨p, hp, rfl, rfl, rfl⟩

theorem unitsOf_mem (m : MaskForm) {u : Single} (hu : u ∈ unitsOf m) :
    ∃ p ∈ m, u.oracle = p.1.oracle ∧ u.part = .mask ∧ u.index = p.1.index := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hu
  exact ⟨p, hp, rfl, rfl, rfl⟩

/-! ## 2. A form's mask side names the homes of the form's slots -/

theorem fold_homes {F : Fork} {home : Array Slot} : ∀ (l : List (ℕ × E)) (init y : MaskForm × E),
    l.foldlM (fun (y : MaskForm × E) (t : ℕ × E) =>
      match home[t.1]?, F.shown t.1 with
      | some s, some v =>
        some (y.1 ++ [(s, mulE t.2 (F.mf.getD t.1 zeroE))], addE y.2 (mulE t.2 v))
      | _, _ => none) init = some y →
    ∀ p ∈ y.1, p ∈ init.1 ∨ ∃ t ∈ l, home[t.1]? = some p.1
  | [], init, y, h, p, hp => by
    have h' : some init = some y := h
    obtain rfl := Option.some.inj h'
    exact Or.inl hp
  | t :: l, init, y, h, p, hp => by
    rw [List.foldlM_cons] at h
    cases hh : home[t.1]? with
    | none => rw [hh] at h; cases h
    | some s =>
      cases hv : F.shown t.1 with
      | none => rw [hh, hv] at h; cases h
      | some v =>
        rw [hh, hv] at h
        rcases fold_homes l _ y h p hp with h1 | ⟨t', ht', h2⟩
        · rcases List.mem_append.1 h1 with h1 | h1
          · exact Or.inl h1
          · rw [List.mem_singleton] at h1
            subst h1
            exact Or.inr ⟨t, List.mem_cons_self .., hh⟩
        · exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', h2⟩

theorem maskSide_homes {F : Fork} {home : Array Slot} {a : Aff} {y : MaskForm × E}
    (h : maskSide F home a = some y) : ∀ p ∈ y.1, ∃ t ∈ a.slots.toList, home[t.1]? = some p.1 := by
  unfold maskSide at h
  split at h
  · cases h
  · rw [← Array.foldlM_toList] at h
    intro p hp
    rcases fold_homes _ _ y h p hp with h1 | h1
    · cases h1
    · exact h1

/-! ## 3. The home of a slot by its mark -/

theorem homesFrom_mark : ∀ (bs : List Bool) (o k : List Slot) (t : ℕ) (s : Slot),
    (homesFrom bs o k)[t]? = some s →
    (bs[t]? = some false → s ∈ o) ∧ (bs[t]? = some true → s ∈ k)
  | [], _, _, t, s, h => by simp [homesFrom] at h
  | false :: bs, [], _, t, s, h => by simp [homesFrom] at h
  | true :: bs, _, [], t, s, h => by simp [homesFrom] at h
  | false :: bs, a :: o, k, 0, s, h => by
    have h' : some a = some s := by simpa [homesFrom] using h
    obtain rfl := Option.some.inj h'
    exact ⟨fun _ => List.mem_cons_self .., fun hh => by simp at hh⟩
  | false :: bs, a :: o, k, t + 1, s, h => by
    have h' : (homesFrom bs o k)[t]? = some s := by simpa [homesFrom] using h
    obtain ⟨p, q⟩ := homesFrom_mark bs o k t s h'
    exact ⟨fun hh => List.mem_cons_of_mem _ (p (by simpa using hh)),
      fun hh => q (by simpa using hh)⟩
  | true :: bs, o, a :: k, 0, s, h => by
    have h' : some a = some s := by simpa [homesFrom] using h
    obtain rfl := Option.some.inj h'
    exact ⟨fun hh => by simp at hh, fun _ => List.mem_cons_self ..⟩
  | true :: bs, o, a :: k, t + 1, s, h => by
    have h' : (homesFrom bs o k)[t]? = some s := by simpa [homesFrom] using h
    obtain ⟨p, q⟩ := homesFrom_mark bs o k t s h'
    exact ⟨fun hh => p (by simpa using hh),
      fun hh => List.mem_cons_of_mem _ (q (by simpa using hh))⟩

/-- **The form names slots of the lookups' own message alone**: no entry of a virtual row, and slots
whose mark in the library's table (`fromKeys`) is "not from the index-mask message". -/
def OwnOnly (f : Face) (a : Aff) : Prop :=
  a.ents.isEmpty = true ∧ ∀ t ∈ a.slots.toList, (fromKeys f)[t.1]? = some false

/-- The mask side of such a form names entries of the first list alone. -/
theorem maskSide_own {f : Face} {F : Fork} {o k : List Slot} {a : Aff} {y : MaskForm × E}
    (ha : OwnOnly f a) (h : maskSide F (homes f o k) a = some y) : ∀ p ∈ y.1, p.1 ∈ o := by
  intro p hp
  obtain ⟨t, ht, hh⟩ := maskSide_homes h p hp
  have hh' : (homesFrom (fromKeys f) o k)[t.1]? = some p.1 := by
    simpa [homes] using hh
  exact (homesFrom_mark _ _ _ _ _ hh').1 (ha.2 t ht)

/-! ## 4. The terms that a vector on the planes adds to a row -/

/-- The blocks of planes of lookup i in the lookups' own message. -/
def blocksOf (x : Params.WfPublic) (codes : Codes) (i : ℕ) : List Wf.Block :=
  (Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell).filter (·.lookup == i)

/-- The vector that `Wf.planesAt` lays on the main table for one block. -/
def termOf (x : Params.WfPublic) (codes : Codes) (i : ℕ) (v : Tensor) (b : Wf.Block) : Tensor :=
  ((Lkp.onBlock v (x.lookups.getD i default).mu (b.first, b.logPlanes)).insertChoice b.bits
    ((codes.base.getD x.message.shape.code default).logEll - b.bits)
    (b.firstPlace / 2 ^ b.bits)).insertChoice 0 (ceilLog2 x.message.shape.mainRows) b.row

theorem addTerms_laws (o : ℕ) (f : Wf.Block → Tensor) : ∀ (bs : List Wf.Block) (r : Row),
    let r' := bs.foldl (fun r b => r.add o .main (f b)) r
    r'.kind = r.kind ∧ r'.units = r.units ∧ r'.runs = r.runs ∧ r'.forms = r.forms ∧
      r'.target = r.target ∧ r'.terms.toList = r.terms.toList ++ bs.map fun b => ⟨o, .main, f b⟩
  | [], r => ⟨rfl, rfl, rfl, rfl, rfl, (List.append_nil _).symm⟩
  | b :: bs, r => by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := addTerms_laws o f bs (r.add o .main (f b))
    refine ⟨a1, a2, a3, a4, a5, ?_⟩
    show (bs.foldl (fun r b => r.add o .main (f b)) (r.add o .main (f b))).terms.toList = _
    rw [a6]
    show (r.terms.push _).toList ++ _ = _
    rw [Array.toList_push, List.append_assoc]
    rfl

theorem planesAt_eq (x : Params.WfPublic) (codes : Codes) (i : ℕ) (row : Row) (v : Tensor) :
    Wf.planesAt x codes i row v =
      (blocksOf x codes i).foldl (fun r b => r.add x.messageId .main (termOf x codes i v b)) row :=
  rfl

/-! ### How many variables such a vector has hangs on the number of the claim's pairs alone -/

/-- One step of `Lkp.setBits`. -/
def setStep (low high number : ℕ) (part : Tensor) (p : ℕ × E × E) : Tensor :=
  if low ≤ p.1 && p.1 < high then part.scale (if number.testBit p.1 then p.2.2 else p.2.1)
  else part.push p.2.1 p.2.2

theorem setStep_laws (low high number i : ℕ) (p p' : E × E) {acc acc' : Tensor}
    (h : acc.pairs.length = acc'.pairs.length) (hd : acc.denseVars = []) :
    (setStep low high number acc (i, p)).pairs.length =
      (setStep low high number acc' (i, p')).pairs.length ∧
      (setStep low high number acc (i, p)).denseVars = [] := by
  unfold setStep
  by_cases hc : (decide (low ≤ i) && decide (i < high)) = true
  · rw [if_pos hc, if_pos hc]
    simp only [Tensor.scale]
    exact ⟨h, hd⟩
  · rw [if_neg hc, if_neg hc]
    simp only [Tensor.push]
    refine ⟨?_, hd⟩
    rw [List.length_append, List.length_append, h]
    rfl

theorem setFold_laws (low high number : ℕ) : ∀ (is : List ℕ) (l l' : List (E × E))
    (acc acc' : Tensor), l.length = l'.length → acc.pairs.length = acc'.pairs.length →
    acc.denseVars = [] → acc'.denseVars = [] →
    ((is.zip l).foldl (setStep low high number) acc).pairs.length =
      ((is.zip l').foldl (setStep low high number) acc').pairs.length ∧
    ((is.zip l).foldl (setStep low high number) acc).denseVars = []
  | [], _, _, _, _, _, h, hd, _ => ⟨h, hd⟩
  | _ :: _, [], [], _, _, _, h, hd, _ => ⟨h, hd⟩
  | _ :: _, [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | i :: is, p :: l, p' :: l', acc, acc', hl, h, hd, hd' => by
    rw [List.zip_cons_cons, List.zip_cons_cons, List.foldl_cons, List.foldl_cons]
    obtain ⟨a1, a2⟩ := setStep_laws low high number i p p' h hd
    obtain ⟨-, a3⟩ := setStep_laws low high number i p' p h.symm hd'
    exact setFold_laws low high number is l l' _ _ (Nat.succ.inj hl) a1 a2 a3

theorem choicePairs_length : ∀ n v, (choicePairs n v).length = n
  | 0, _ => rfl
  | n + 1, v => by
    show (choicePairs n (v / 2)).length + 1 = n + 1
    rw [choicePairs_length n]

theorem insertChoice_length (v : Tensor) (pos c val : ℕ) :
    (v.insertChoice pos c val).pairs.length = v.pairs.length + c := by
  show (v.pairs.take pos ++ choicePairs c val ++ v.pairs.drop pos).length = _
  rw [List.length_append, List.length_append, choicePairs_length, List.length_take,
    List.length_drop]
  omega

theorem insertChoice_dense {v : Tensor} (h : v.denseVars = []) (pos c val : ℕ) :
    (v.insertChoice pos c val).denseVars = [] := by
  show v.denseVars.map _ = []
  rw [h]
  rfl

/-- **The vector's number of variables hangs on the number of the claim's pairs alone; it has no
written-out factor.** -/
theorem termOf_laws (x : Params.WfPublic) (codes : Codes) (i : ℕ) (b : Wf.Block) {v v' : Tensor}
    (h : v.pairs.length = v'.pairs.length) :
    (termOf x codes i v b).pairs.length = (termOf x codes i v' b).pairs.length ∧
      (termOf x codes i v b).denseVars = [] := by
  have hs := setFold_laws b.logPlanes (x.lookups.getD i default).mu b.first
    (List.range v.pairs.length) v.pairs v'.pairs { scalar := v.scalar } { scalar := v'.scalar } h
    rfl rfl rfl
  have h1 : (Lkp.onBlock v (x.lookups.getD i default).mu (b.first, b.logPlanes)).pairs.length =
      (Lkp.onBlock v' (x.lookups.getD i default).mu (b.first, b.logPlanes)).pairs.length := by
    show (((List.range v.pairs.length).zip v.pairs).foldl (setStep _ _ _) _).pairs.length =
      (((List.range v'.pairs.length).zip v'.pairs).foldl (setStep _ _ _) _).pairs.length
    rw [← h]
    exact hs.1
  refine ⟨?_, insertChoice_dense (insertChoice_dense hs.2 _ _ _) _ _ _⟩
  unfold termOf
  rw [insertChoice_length, insertChoice_length, insertChoice_length, insertChoice_length, h1]

theorem inOrder_of {v : Tensor} (hd : v.denseVars = []) (hl : v.pairs.length ≤ 63) :
    tensorInOrder v = true := by
  unfold tensorInOrder
  simp [hd, hl]

/-! ## 5. A row of the make of a lookup's rows passes the test on a row -/

/-- **A row of the make of a lookup's rows**: plain; no run, no form; its single entries lie in
message msg's mask table, at indexes below B and below P; its terms lie on msg's main table, are in
order and have V variables. -/
structure LookupShapedRow (msg B P V : ℕ) (r : Row) : Prop where
  kind : r.kind = .plain
  runs : r.runs = #[]
  forms : r.forms = #[]
  units : ∀ u ∈ r.units.toList, u.oracle = msg ∧ u.part = .mask ∧ u.index < B ∧ u.index < P
  terms : ∀ t ∈ r.terms.toList, t.oracle = msg ∧ t.part = .main ∧ tensorInOrder t.v = true ∧
    t.v.vars = V

section
variable {L : Type}

/-- **Where the rows are laid**: group g has the one member msg and no test has begun; msg has main
and mask rows; its pad lies in its mask table from P on; B and V are its two tables' numbers. -/
structure Stand (d : DState L) (g msg B P V : ℕ) : Prop where
  group : ∃ G, d.st.groups[g]? = some G ∧ G.members = #[msg] ∧ G.inRun = false
  there : ∃ x, d.st.oracles[msg]? = some x ∧ 0 < x.shape.maskRows ∧ 0 < x.shape.mainRows ∧
    ∀ q ∈ x.pad, q.1 = Part.mask ∧ P ≤ q.2
  mask : 2 ^ d.st.tableBits msg .mask = B
  main : d.st.tableBits msg .main = V

/-- **Such a row passes all eight clauses**, whatever its coefficients are. -/
theorem fits_of_plain {d : DState L} {g msg B P V : ℕ} {r : Row} (hS : Stand d g msg B P V)
    (hr : LookupShapedRow msg B P V r) : ok (rowL d.st g r) = true := by
  obtain ⟨G, hG, hmem, hrun⟩ := hS.group
  obtain ⟨x, hx, hmask, hmain, hpad⟩ := hS.there
  have hc : G.members.contains msg = true := by rw [hmem]; simp
  have tMask : tableThere d.st msg .mask = true := by
    unfold tableThere
    rw [hx]
    exact decide_eq_true hmask
  have tMain : tableThere d.st msg .main = true := by
    unfold tableThere
    rw [hx]
    exact decide_eq_true hmain
  have c4 : (r.terms.all fun t => tensorInOrder t.v &&
      placeFits d.st G t.oracle t.part t.v.vars 0) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro t ht
    obtain ⟨a1, a2, a3, a4⟩ := hr.terms t (Array.mem_toList_iff.2 ht)
    unfold placeFits
    rw [a1, a2, a3, a4, hc, tMain, hS.main]
    simp
  have c5 : (r.units.all fun u =>
      placeFits d.st G u.oracle u.part (d.st.tableBits u.oracle u.part) u.index) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro u hu
    obtain ⟨a1, a2, a3, -⟩ := hr.units u (Array.mem_toList_iff.2 hu)
    unfold placeFits
    rw [a1, a2, hc, tMask, hS.mask]
    simp [a3]
  have c8 := noPad_of_zero (S := d.st) (G := G) (row := r) (by
    intro o ho y hy q hq
    rw [hmem] at ho
    obtain rfl : o = msg := by simpa using ho
    obtain rfl : x = y := Option.some.inj (hx.symm.trans hy)
    obtain ⟨q1, q2⟩ := hpad q hq
    refine coefficient_zero (fun t ht => ?_) (fun u hu => ?_) (fun w hw => ?_) (fun f hf => ?_)
    · rw [(hr.terms t ht).2.1, q1]
      simp
    · have h4 := (hr.units u hu).2.2.2
      have : (u.index == q.2) = false := beq_false_of_ne (by omega)
      rw [this]
      simp
    · rw [hr.runs] at hw
      cases hw
    · rw [hr.forms] at hf
      cases hf)
  simp only [ok, rowL, hG, has, hrun, hr.kind, hr.runs, hr.forms, c4, c5, c8, List.all_cons,
    List.all_nil, Option.isSome_some, Option.map_some, Option.getD_some, Bool.not_false,
    Bool.and_true]
  simp

end

/-! ## 6. The rows that a lookup's claims become are of that make -/

/-- A vector of n variables, for counting alone. -/
def canon (n : ℕ) : Tensor := { pairs := List.replicate n (oneE, oneE) }

section
variable {f : Face} {F : Fork} {o k : List Slot} {msg B P V : ℕ}

theorem units_own {m : MaskForm} (hm : ∀ p ∈ m, p.1 ∈ o)
    (ho : ∀ s ∈ o, s.oracle = msg ∧ s.index < B ∧ s.index < P) {u : Single}
    (hu : ∃ p ∈ m, u.oracle = p.1.oracle ∧ u.part = .mask ∧ u.index = p.1.index) :
    u.oracle = msg ∧ u.part = .mask ∧ u.index < B ∧ u.index < P := by
  obtain ⟨p, hp, a1, a2, a3⟩ := hu
  obtain ⟨b1, b2, b3⟩ := ho p.1 (hm p hp)
  exact ⟨a1.trans b1, a2, a3 ▸ b2, a3 ▸ b3⟩

/-- A claim on hidden values alone. -/
theorem plain_of_aff {a : Aff} {r : Row} (ha : OwnOnly f a)
    (ho : ∀ s ∈ o, s.oracle = msg ∧ s.index < B ∧ s.index < P)
    (h : rowOfAff F (homes f o k) a = some r) : LookupShapedRow msg B P V r := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨a1, a2, a3, a4, a5⟩ := addMasks_laws (negMasks y.1) { target := subE zeroE y.2 }
  refine ⟨a1, a3, a4, fun u hu => ?_, fun t ht => ?_⟩
  · rw [a5] at hu
    exact units_own (maskSide_own ha hy) ho (unitsOf_neg y.1 (by simpa using hu))
  · rw [a2] at ht
    cases ht

/-- A claim that reads the planes. -/
theorem plain_of_plane {x : Params.WfPublic} {codes : Codes} {i n : ℕ} {turned : Bool}
    {c : PlaneClaim} {r : Row} (ha : OwnOnly f c.lead)
    (ho : ∀ s ∈ o, s.oracle = x.messageId ∧ s.index < B ∧ s.index < P)
    (hn : c.pairs.length = n)
    (hT : ∀ b ∈ blocksOf x codes i, (termOf x codes i (canon n) b).pairs.length = V)
    (hV : V ≤ 63)
    (h : rowOfPlane (Wf.planesAt x codes i) F (homes f o k) turned c = some r) :
    LookupShapedRow x.messageId B P V r := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  have key : ∀ (tg sc : E) (m : MaskForm),
      (∀ u ∈ unitsOf m, ∃ p ∈ y.1, u.oracle = p.1.oracle ∧ u.part = .mask ∧
        u.index = p.1.index) →
      LookupShapedRow x.messageId B P V ((Wf.planesAt x codes i { target := tg }
               { scalar := sc, pairs := c.pairs }).addMasks m) := by
    intro tg sc m hm
    obtain ⟨a1, a2, a3, a4, a5⟩ := addMasks_laws m
      (Wf.planesAt x codes i { target := tg } { scalar := sc, pairs := c.pairs })
    rw [planesAt_eq] at a1 a2 a3 a4 a5 ⊢
    obtain ⟨b1, b2, b3, b4, -, b6⟩ := addTerms_laws x.messageId
      (termOf x codes i { scalar := sc, pairs := c.pairs }) (blocksOf x codes i) { target := tg }
    refine ⟨a1.trans b1, a3.trans b3, a4.trans b4, fun u hu => ?_, fun t ht => ?_⟩
    · rw [a5, b2] at hu
      exact units_own (maskSide_own ha hy) ho (hm u (by simpa using hu))
    · rw [a2, b6] at ht
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (by simpa using ht)
      obtain ⟨l1, l2⟩ := termOf_laws x codes i b
        (v := { scalar := sc, pairs := c.pairs }) (v' := canon n)
        (by show c.pairs.length = (List.replicate n (oneE, oneE)).length
            rw [List.length_replicate, hn])
      have hlen : (termOf x codes i { scalar := sc, pairs := c.pairs } b).pairs.length = V :=
        l1.trans (hT b hb)
      exact ⟨rfl, rfl, inOrder_of l2 (hlen ▸ hV), hlen⟩
  cases turned with
  | true => exact key _ _ _ fun u hu => unitsOf_neg y.1 hu
  | false => exact key _ _ _ fun u hu => unitsOf_mem y.1 hu

end

theorem mem_of_mapM {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ b ∈ r, ∃ a ∈ l, f a = some b
  | [], r, h, b, hb => by
    have h' : some [] = some r := h
    obtain rfl := Option.some.inj h'
    cases hb
  | a :: l, r, h, b, hb => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some y =>
      cases hl : l.mapM f with
      | none => rw [ha, hl] at h; cases h
      | some ys =>
        rw [ha, hl] at h
        have h' : some (y :: ys) = some r := h
        obtain rfl := Option.some.inj h'
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ⟨a, List.mem_cons_self .., ha⟩
        · obtain ⟨a', ha', e⟩ := mem_of_mapM f l ys hl b hb
          exact ⟨a', List.mem_cons_of_mem _ ha', e⟩

/-- Every row that the layer writes is the row of one of the link's claims. -/
theorem rowsInOrder_mem {planesAt : OnBytes.Row → Tensor → OnBytes.Row}
    {tab : List (Bool × ℕ × Bool)} {F : Fork} {home : Array Slot} {cls : List Claim}
    {rows : List OnBytes.Row} (h : rowsInOrder planesAt tab F home cls = some rows) :
    ∀ r ∈ rows, ∃ c ∈ cls, ∃ turned, rowOfClaim planesAt F home turned c = some r := by
  unfold rowsInOrder at h
  dsimp only at h
  split at h
  · cases h
  · intro r hr
    obtain ⟨t, -, ht⟩ := mem_of_mapM _ _ _ h r hr
    obtain ⟨c, hc, hrow⟩ := Option.bind_eq_some_iff.1 ht
    have hm := List.mem_of_getElem? hc
    refine ⟨c, ?_, t.2.2, hrow⟩
    split at hm
    · exact (List.mem_filter.1 hm).1
    · exact (List.mem_filter.1 hm).1

/-! ## 7. The hypotheses on what was heard, and the rows of one lookup -/

theorem fl_bind_some {α β : Type} {x : K.Kc.Fl α} {f : α → K.Kc.Fl β} {F : Fork} {t : K.Kc.Tape}
    {r : β × Fork × K.Kc.Tape} (h : (x >>= f) F t = some r) :
    ∃ a G u, x F t = some (a, G, u) ∧ f a G u = some r := by
  have h' : K.Kc.Fl.andThen x f F t = some r := h
  unfold K.Kc.Fl.andThen at h'
  cases hx : x F t with
  | none => rw [hx] at h'; cases h'
  | some y =>
    obtain ⟨a, G, u⟩ := y
    rw [hx] at h'
    exact ⟨a, G, u, rfl, h'⟩

/-- The three claims on the planes have mu + d pairs each. -/
theorem planesG_pairs {f : Face} {g : HeardG} {F G₂ : Fork} {t rest : K.Kc.Tape}
    {cl : List PlaneClaim} (h : planesG f g F t = some (cl, G₂, rest)) :
    ∀ c ∈ cl, c.pairs.length = f.mu + f.d := by
  unfold planesG at h
  obtain ⟨a, G, u, -, hf⟩ := fl_bind_some h
  obtain ⟨row, p⟩ := a
  have hf' : some (_, G, u) = some (cl, G₂, rest) := hf
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hf')
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simp [eqPairs]
    · simp [eqPairs]
    · simp

/-- A slot's mark in the library's table, counted from the ledger's slot lo. -/
def markAt (f : Face) (lo j : ℕ) : Bool := (fromKeys f).getD (j - lo) false

/-- Every slot that the form names has the mark "not from the index-mask message". -/
def Off (f : Face) (lo : ℕ) (a : Aff) : Prop := ∀ x ∈ a.slots.toList, markAt f lo x.1 = false

/-- Every slot that the form names has the mark "from the index-mask message". -/
def On (f : Face) (lo : ℕ) (a : Aff) : Prop := ∀ x ∈ a.slots.toList, markAt f lo x.1 = true

theorem ownOnly_of {f : Face} {a : Aff} (hs : Scoped f.slots a) (ho : Off f 0 a) : OwnOnly f a := by
  refine ⟨hs.1, fun t ht => ?_⟩
  have hlt : t.1 < (fromKeys f).length := by
    rw [fromKeys_length]
    exact hs.2 t ht
  have h0 := ho t ht
  unfold markAt at h0
  rw [Nat.sub_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] at h0
  rw [List.getElem?_eq_getElem hlt]
  exact congrArg some h0

/-- **All rows that the layer writes for one lookup are of the make of section 5.** -/
theorem rows_plain {x : Params.WfPublic} {codes : Codes} {i : ℕ} {y : Lookup} {F : Fork}
    {o k : List Slot} {B P V : ℕ} {objs : List Aff} {cl : List PlaneClaim}
    {tab : List (Bool × ℕ × Bool)} {rows : List OnBytes.Row}
    (ho : ∀ s ∈ o, s.oracle = x.messageId ∧ s.index < B ∧ s.index < P)
    (h1 : ∀ a ∈ objs, OwnOnly (faceOfLkp y) a) (h2 : ∀ c ∈ cl, OwnOnly (faceOfLkp y) c.lead)
    (hn : ∀ c ∈ cl, c.pairs.length = (faceOfLkp y).mu + (faceOfLkp y).d)
    (hT : ∀ b ∈ blocksOf x codes i,
      (termOf x codes i (canon ((faceOfLkp y).mu + (faceOfLkp y).d)) b).pairs.length = V)
    (hV : V ≤ 63)
    (h : rowsInOrder (Wf.planesAt x codes i) tab F (homes (faceOfLkp y) o k)
      (objs.map Sum.inl ++ cl.map Sum.inr) = some rows) :
    ∀ r ∈ rows, LookupShapedRow x.messageId B P V r := by
  intro r hr
  obtain ⟨c, hc, turned, hrow⟩ := rowsInOrder_mem h r hr
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    exact plain_of_aff (h1 a ha) ho hrow
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact plain_of_plane (h2 c' hc') ho (hn c' hc') hT hV hrow

/-! ## 8. What holds between the links, and that the rows are laid -/

open VerifiableInference.Desc (foldBlocks roundsFit noDigest OpenedColumn)
open VerifiableInference.Desc.K13.Law (takeMasksP_within)

/-- **What holds of the first chain's state in front of link i**: no ledger of a lookup is open; i
lookups have written their rows and claims on keys; the two messages differ; their ledgers of mask
entries are open, with just a and b entries left, behind k₁ and k₂ takes; the own message's pad lies
above what its ledger hands out; the ranges' group has that message alone, no row, no test begun;
and every row written is of the make of section 5. -/
structure Mid (one : Params.OneTime) (cs : Codes) (s : FirstState) (i a b k₁ k₂ B V : ℕ)
    (sm si : OracleShape) : Prop where
  codes : s.d.st.codes = cs
  fork : s.base.fork = none
  keys : s.base.keys.length = i
  rowsN : s.base.rows.length = i
  ne : s.idx ≠ one.ranges.messageId
  own : LeftIs s.d one.ranges.messageId a sm
  idx : LeftIs s.d s.idx b si
  ownAt : LedgerAt s.d.st one.ranges.messageId k₁
  idxAt : LedgerAt s.d.st s.idx k₂
  pad : PadAbove s.d one.ranges.messageId
  group : GroupIs s.d s.grp one.ranges.messageId
  size : tableSize s.d.st one.ranges.messageId .mask = B
  plain : ∀ r ∈ s.base.rows.flatten, LookupShapedRow one.ranges.messageId B (padFirst cs sm) V r

/-- **It holds behind the two sendings**, in front of the first link: where both accept, from a
state in which no lookup has written anything. -/
theorem mid_of_front {one : Params.OneTime} {N : Pieces} {g₁ g₂ : List (List ℕ)}
    {s s₁ s₂ : FirstState} {rs₁ rs₂ : List Fmt.RoundView} {gs₁ gs₂ : List (List (ℕ × List UInt64))} (V : ℕ)
    (e₁ : (sendIndexMasks (Cl := Claim) one N g₁).decide s rs₁ gs₁ = .ok s₁)
    (e₂ : (sendOwnMessage (Cl := Claim) one N g₂).decide s₁ rs₂ gs₂ = .ok s₂)
    (i0 : one.indexMasks.shape.answers ≠ 0) (im : 0 < one.indexMasks.shape.maskRows)
    (m0 : one.ranges.message.shape.answers ≠ 0) (mm : 0 < one.ranges.message.shape.maskRows)
    (hf : s.base.fork = none) (hk : s.base.keys = []) (hr : s.base.rows = []) :
    Mid one s.d.st.codes s₂ 0 (freeOf s.d.st.codes one.ranges.message.shape)
      (freeOf s.d.st.codes one.indexMasks.shape) 0 0
      (tableSize s₂.d.st one.ranges.messageId .mask) V one.ranges.message.shape
      one.indexMasks.shape := by
  obtain ⟨b, c, ne, l1, t1, l2, t2, p2, gr⟩ := front_laws e₁ e₂ i0 im m0 mm
  refine ⟨c, by rw [b]; exact hf, by rw [b, hk]; rfl, by rw [b, hr]; rfl, ne, l2, l1, t2, t1, p2,
    gr, rfl, fun r hr' => ?_⟩
  rw [b, hr] at hr'
  cases hr'

/-- **A link is passed, and what holds in front of it holds behind it**, with the entries taken. -/
theorem link_keeps (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup) (ft : ℕ)
    {s : FirstState} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {es : List Fmt.Entry} {gV : HeardV}
    {G G₂ : Fork} {cl : List PlaneClaim} {a b k₁ k₂ B V : ℕ} {sm si : OracleShape} {cs : Codes}
    (hM : Mid one cs s i ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length + a)
      (2 * (faceOfLkp x).parts.length + b) k₁ k₂ B V sm si)
    (hv : ∀ v ∈ (faceOfLkp x).parts, 1 ≤ v)
    (hes : (lookupPlace set i x).entries = some es) (hlen : es.length ≤ rs.length)
    (hfit : roundsFit (es.map fun e => { entry := e }) (rs.take es.length) = true)
    (hh : hearV (faceOfLkp x) (({} : Fork).slots (faceOfLkp x).slots)
      ((rs.take es.length).map noDigest) = some (gV, G))
    (hL : Left (lookupPlace set i x) (toHeardG gV) G cl G₂)
    (hO : ∀ c ∈ (toHeardG gV).rows.toList, Off (faceOfLkp x) 0 c)
    (hO' : ∀ c ∈ cl, Off (faceOfLkp x) 0 c.lead)
    (hT : ∀ bl ∈ blocksOf one.ranges one.codes i, (termOf one.ranges one.codes i
      (canon ((faceOfLkp x).mu + (faceOfLkp x).d)) bl).pairs.length = V)
    (hV : V ≤ 63) :
    ∃ s', foldBlocks ft (lookupLink one set i x).blocksInOrder s rs cols =
        .ok (s', rs.drop es.length, cols) ∧
      Mid one cs s' (i + 1) a b (k₁ + ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length))
        (k₂ + 2 * (faceOfLkp x).parts.length) B V sm si := by
  obtain ⟨o, d₁, k, d₂, rows, keys, e1, e2, hrows, hfold⟩ := link_fold one set i x ft (cols := cols)
    hM.fork hM.keys hM.ne (hM.own.room (Nat.le_add_right _ _)) (hM.idx.room (Nat.le_add_right _ _))
    hv hes hlen hfit hh hL
  obtain ⟨q1, q2, q3, q4, q5, -, q7, q8, q9⟩ :=
    behind_takings hM.ne hM.own hM.idx hM.ownAt hM.idxAt e1 e2
  obtain ⟨-, -, c1, -, -⟩ := takeMasks_laws e1
  obtain ⟨-, -, c2, -, -⟩ := takeMasks_laws e2
  have hne' : one.ranges.messageId ≠ s.idx := fun e => hM.ne e.symm
  have hcodes : d₂.st.codes = s.d.st.codes := (c2 _ hne').1.trans (c1 _ hM.ne).1
  have hsz1 := (takeMasksP_within hM.ownAt e1).2.1
  have hsz2 : tableSize d₂.st one.ranges.messageId .mask =
      tableSize d₁.st one.ranges.messageId .mask := by
    obtain ⟨y, l, hy, -, hm, -⟩ := (takeMasksP_within hM.ownAt e1).2.2
    obtain ⟨y', hy', sh, -⟩ := (c2 _ hne').2 y hy
    rw [tableSize_mask hy hm, tableSize_mask hy' (sh ▸ hm), sh, (c2 _ hne').1]
  obtain ⟨rest, hp⟩ := hL.planes
  have hnew := rows_plain (x := one.ranges) (codes := one.codes) (i := i) (y := x) (B := B)
    (P := padFirst cs sm) (V := V)
    (o := o.map fun j => (⟨one.ranges.messageId, j⟩ : Slot))
    (by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
      exact ⟨rfl, hM.size ▸ q5 j hj, hM.codes ▸ q8 j hj⟩)
    (fun c hc => ownOnly_of (hL.rows c hc) (hO c hc))
    (fun c hc => ownOnly_of (hL.leads c hc) (hO' c hc)) (planesG_pairs hp) hT hV hrows
  refine ⟨_, hfold, hcodes.trans hM.codes, rfl, ?_, ?_, hM.ne, q1, q2, q3, q4, q9 hM.pad, ?_, ?_,
    ?_⟩
  · show (s.base.keys ++ [keys]).length = i + 1
    rw [List.length_append, hM.keys]
    rfl
  · show (s.base.rows ++ [rows]).length = i + 1
    rw [List.length_append, hM.rowsN]
    rfl
  · obtain ⟨Gr, hGr, r⟩ := hM.group
    exact ⟨Gr, by show d₂.st.groups[s.grp]? = _; rw [q7]; exact hGr, r⟩
  · show tableSize d₂.st one.ranges.messageId .mask = B
    rw [hsz2, hsz1, hM.size]
  · intro r hr
    have hr' : r ∈ (s.base.rows ++ [rows]).flatten := hr
    rw [List.flatten_append, List.mem_append] at hr'
    rcases hr' with hr' | hr'
    · exact hM.plain r hr'
    · exact hnew r (by simpa using hr')

theorem rowsFrom_same {L : Type} (g : ℕ) : ∀ (rows : List Row) (d d' : DState L),
    addRowsFrom g rows d = some d' → ∀ o, SameAt d d' o
  | [], d, d', h, o => by
    have h' : some d = some d' := h
    obtain rfl := Option.some.inj h'
    exact SameAt.refl d o
  | row :: l, d, d', h, o => by
    unfold addRowsFrom addRowP at h
    split at h
    · exact (show SameAt d { d with st := Slice.withRow d.st g row } o from
        ⟨rfl, fun x hx => ⟨x, hx, rfl, rfl, rfl, rfl⟩⟩).trans (rowsFrom_same g l _ d' h o)
    · cases h

/-- The step that adds open rows turns no message. -/
theorem addRows_same {L : Type} {d d' : DState L} {g : ℕ} {rows : List Row}
    (h : addRowsP d g rows = some d') (o : ℕ) : SameAt d d' o := by
  unfold addRowsP at h
  split at h
  · exact rowsFrom_same g rows d d' h o
  · cases h

/-- **Behind the last link the rows are laid onto the ranges' group**; no message is turned. -/
theorem layRows_accepts (one : Params.OneTime) {s : FirstState} {a b k₁ k₂ B V : ℕ}
    {sm si : OracleShape} {cs : Codes} (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hM : Mid one cs s (lookupsOf one).length a b k₁ k₂ B V sm si) (hmain : 0 < sm.mainRows)
    (hV : ceilLog2 sm.mainRows + (cs.base.getD sm.code default).logEll = V) :
    ∃ d, (layRows one).decide s rs cols = .ok { s with d := d } ∧ ∀ o, SameAt s.d d o := by
  obtain ⟨Gr, hGr, hmem, hrows, hrun⟩ := hM.group
  obtain ⟨y, l, hy, hs, -⟩ := hM.own
  obtain ⟨y', _, hy', -, hm, -⟩ := hM.ownAt
  obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
  obtain ⟨y'', hy'', hpad⟩ := hM.pad
  obtain rfl : y = y'' := Option.some.inj (hy.symm.trans hy'')
  have hB : 2 ^ s.d.st.tableBits one.ranges.messageId .mask = B := by
    have h := hM.size
    unfold tableSize Statement.has at h
    rw [hy] at h
    have hm' : 0 < y.shape.rows .mask := hm
    simpa [hm'] using h
  have hmain' : 0 < y.shape.rows .main := hs ▸ hmain
  have hV' : s.d.st.tableBits one.ranges.messageId .main = V := by
    unfold Statement.tableBits Statement.rowBits Statement.placeBits
    rw [hy]
    have h0 : (y.shape.rows .main == 0) = false := beq_false_of_ne (by omega)
    simp only [h0, Bool.false_eq_true, if_false]
    rw [hM.codes, ← hV, ← hs]
    rfl
  have hS : Stand s.d s.grp one.ranges.messageId B (padFirst cs sm) V :=
    ⟨⟨Gr, hGr, hmem, hrun⟩, ⟨y, hy, hm, hs ▸ hmain, hM.codes ▸ hs ▸ hpad⟩, hB, hV'⟩
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (addRows_of_fits hGr hrun
    fun r hr => fits_of_plain hS (hM.plain r hr))
  exact ⟨d, layRows_decide one rs cols hM.rowsN (by rw [hGr]; simp [hrows, hrun]) hd,
    addRows_same hd⟩

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.maskSide_own
#print axioms AtPublicFiles.KeyLookup.termOf_laws
#print axioms AtPublicFiles.KeyLookup.fits_of_plain
#print axioms AtPublicFiles.KeyLookup.plain_of_aff
#print axioms AtPublicFiles.KeyLookup.plain_of_plane
#print axioms AtPublicFiles.KeyLookup.planesG_pairs
#print axioms AtPublicFiles.KeyLookup.ownOnly_of
#print axioms AtPublicFiles.KeyLookup.rows_plain
#print axioms AtPublicFiles.KeyLookup.mid_of_front
#print axioms AtPublicFiles.KeyLookup.link_keeps
#print axioms AtPublicFiles.KeyLookup.layRows_accepts
