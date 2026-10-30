-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysWv.lean: the vectors of the weight claims at the end of the batched sumcheck,
read from the committed matrix of weights.

At the end of the batched sumcheck of a layer sub-proof the B side of a panel whose B side is a
weight matrix is known to the verifier through one end value for each weight claim. What
Johnson/Road/FormsKeysEnd.lean proves of that end asks that each such end value is the extension, at
the end point's coordinates of the panel's columns or places, of a vector (the fields rowV and allV
of the record EndsTrue there), and leaves the vectors free: one function wv for all panels. This
file names the vectors. wvOf a is made from claim number a of the verifier's list and from a matrix
W: it is the sum that the claim speaks of in W (claimVal in Johnson/Road/FormsKeysWm.lean), with the
factor on the group kk, and on the group e if the unit has one, replaced by the indicator of an
index. The main theorem: if every end value is what its claim says of W, then rowV and allV hold
with these vectors.

What is compared with what. The verifier's functions (its lists of panels and of claims, its layout
of the weights, its factor facRs) against definitions of these files: claimVal and facAt, which say
what a claim and a factor mean, eqR and gsum of FormsKeysEnd.lean, and wvOf of this file. No name of
the library stands in a statement.

The file goes in eight steps.
 1. The definitions: hasE, wkOf, selOf (which index a number Y picks in a group), sumSel, wvClaim,
    wvOf.
 2. If facRs returns a factor, the group's indices fit the bits (facRs_le).
 3. For the three shapes of a unit, kk x, hd cd kk and kk e x: the sum sumIdx is the extension of
    the sums sumSel (row_two, row_last, all_three).
 4. The unit of a claim, in a layout that wsLayOf returns: it is one of the asked units, with the
    names, classes and sizes of the text (unit_found, groups_found, first_found, kk_first). With
    that, step 3 for a claim as the verifier makes it (claim_row_two, claim_row_last,
    claim_all_three).
 5. On the verifier's own lists, through claims_of_panels of Johnson/Road/FormsKeysFold.lean, which
    ties a panel to its claims: ends_of_claims; for the placed panels, as the record EndsTrue:
    endsTrue_of_claims.
 6. Where a vector is 0: from the number of the indices of kk on (claim_zero_two). For the down
    matrix of a layer with routed experts that is from fe on, while the panel has f columns
    (claim_zero_D).
 7. The vectors do not hang on the batched sumcheck's point: the claims are made with the
    sumcheck's challenges, but only in the factors that wvOf replaces (wvClaim_congr, wvOf_rs).
    Without that, "the end value is the extension of the vector at the point" would say little:
    any end value is the extension of a constant vector.
 8. With the end of the batched sumcheck: endsTrue_of_claims joined with stack_masked of
    FormsKeysEnd.lean (stack_claims).

What is asked, and what shows that it can be met.
 - hv, hp, hc: the two lists are made from one environment and both functions return: as in
   FormsKeysFold.lean.
 - hl: the claims' layout of the weights is what wsLayOf returns, with routed experts, for a shape
   s; hd, hfe: s has the widths d and fe of the layer sub-proof's shape.
   Johnson/Road/FormsKeysRunW.lean evaluates hp, hc and hl in one environment at made-up shapes
   (withW there), with the shape wsShapeR of Johnson/Road/FormsKeysRun.lean, which has these two
   widths by its definition. These are runs, not theorems. The shape from which the verifier's
   caller builds its layout of the weights is the matter of Johnson/Road/FormsKeysAimV.lean.
 - hV: every end value is what its claim says of W. It can be met for every W (vvOf, vvOf_spec), by
   definition. That it holds of the hidden values of a proof that the verifier accepts is what the
   merge of the weight claims and the pending row are there to enforce; nothing here shows it.
 - hH, in endsTrue_of_claims: the two fields of EndsTrue on the never-sent vectors. They stay a
   hypothesis; ends_met in FormsKeysEnd.lean meets them by constant vectors.

Main definitions: selOf, sumSel, wvClaim, wvOf; kkSize; vvOf.
Main theorems: ends_of_claims, endsTrue_of_claims, wvOf_rs, stack_claims; claim_row_two,
claim_row_last, claim_all_three; claim_zero_two, claim_zero_D; wvClaim_congr; unit_found,
groups_found; facRs_le.

What is not claimed. That wvOf is the B side of the library's panel is not shown here. Every theorem
on the verifier's functions begins "if the function returns a value": none says that it does.
Nothing is said for a layout of the weights without routed experts, on the embedding's claim, on how
a claim is settled on W, or on what a verifier's acceptance shows. See also
Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysClaim

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqLow WsShape WsGrp WsUnit WsLay WsFac WsClaim wsLayOf)
open OnBytes.Model.Layer (ClaimEnv SBlk Panels PanelEnv StackEnd isAcc panelA panelT panelsA
  panelsT placePanels stackEnd)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The vector of a claim -/

/-- True if one of the groups is named e: the unit holds the matrices of routed experts. -/
def hasE (gs : List WsGrp) : Bool := gs.any fun g => g.name == "e"

/-- The bits of a column of the claim's panel: those of an index of the group named kk. -/
def wkOf (gs : List WsGrp) : ℕ :=
  ceilLog2 (((gs.find? fun g => g.name == "kk").map (·.R)).getD 0)

/-- The index that the number Y picks in a group of a unit with the groups gs. Without a group e: Y
is a column of the claim's panel, and picks the index Y in the group kk. With a group e: Y is a
place in the panel, row times 2^wk plus column; it picks the column in kk and the row in e. In
another group it picks nothing. -/
def selOf (gs : List WsGrp) (Y : ℕ) (g : WsGrp) : Option ℕ :=
  if g.name == "kk" then some (if hasE gs then Y % 2 ^ wkOf gs else Y)
  else if g.name == "e" then some (Y / 2 ^ wkOf gs)
  else none

/-- The sum sumIdx of Johnson/Road/FormsKeysWm.lean, with the factor of each group in which sel
picks an index replaced by the indicator of that index: such a group is not summed over; it has the
picked index, and the whole is 0 if the group has no such index. -/
def sumSel (sel : WsGrp → Option ℕ) : List (WsFac × WsGrp) → (List ℕ → K) → K
  | [], F => F []
  | (x, g) :: rest, F =>
    match sel g with
    | some v => if v < g.R then sumSel sel rest (fun idx => F (v :: idx)) else 0
    | none => ∑ v ∈ range g.R, facAt ρ x g v * sumSel sel rest fun idx => F (v :: idx)

/-- The vector of the claim c in the matrix W, at Y: the sum that the claim speaks of (claimVal),
with the factors on the groups kk and e replaced by the indicator of what Y picks. 0 if the layout
has no such unit. -/
def wvClaim (lay : WsLay) (W : Wm K) (c : WsClaim) (Y : ℕ) : K :=
  match lay.U[c.ui]? with
  | none => 0
  | some u => sumSel ρ (selOf u.g Y) (c.f.zip u.g) (wgtOf u W)

/-- The vector of claim number a of the list cl. 0 if the list has no such claim. -/
def wvOf (lay : WsLay) (W : Wm K) (cl : List WsClaim) (a Y : ℕ) : K :=
  match cl[a]? with
  | none => 0
  | some c => wvClaim ρ lay W c Y

/-! ## What is picked -/

/-- In the group kk. -/
theorem selOf_kk (gs : List WsGrp) (Y : ℕ) {g : WsGrp} (h : g.name = "kk") :
    selOf gs Y g = some (if hasE gs then Y % 2 ^ wkOf gs else Y) := by
  unfold selOf
  rw [h]
  rfl

/-- In the group e. -/
theorem selOf_e (gs : List WsGrp) (Y : ℕ) {g : WsGrp} (h : g.name = "e") :
    selOf gs Y g = some (Y / 2 ^ wkOf gs) := by
  unfold selOf
  rw [h]
  rfl

/-- In a group with another name. -/
theorem selOf_other (gs : List WsGrp) (Y : ℕ) {g : WsGrp} (h1 : (g.name == "kk") = false)
    (h2 : (g.name == "e") = false) : selOf gs Y g = none := by
  unfold selOf
  rw [h1, h2]
  rfl

/-- One step of sumSel at a group in which an index is picked. -/
theorem sumSel_some {sel : WsGrp → Option ℕ} {g : WsGrp} {v : ℕ} (h : sel g = some v) (x : WsFac)
    (rest : List (WsFac × WsGrp)) (F : List ℕ → K) :
    sumSel ρ sel ((x, g) :: rest) F =
      if v < g.R then sumSel ρ sel rest (fun idx => F (v :: idx)) else 0 := by
  simp only [sumSel, h]

/-- One step of sumSel at a group in which nothing is picked. -/
theorem sumSel_none {sel : WsGrp → Option ℕ} {g : WsGrp} (h : sel g = none) (x : WsFac)
    (rest : List (WsFac × WsGrp)) (F : List ℕ → K) :
    sumSel ρ sel ((x, g) :: rest) F =
      ∑ v ∈ range g.R, facAt ρ x g v * sumSel ρ sel rest fun idx => F (v :: idx) := by
  simp only [sumSel, h]

/-! ## The factor from the place's coordinates -/

/-- If facRs returns a factor, the group's o 2^z indices fit the wtot bits. -/
theorem facRs_le {c : ClaimEnv} {G : WsGrp} {lo0 wtot : ℕ} {X : WsFac}
    (h : c.facRs G lo0 wtot = some X) : G.o * 2 ^ G.z ≤ 2 ^ wtot := by
  have h' : (do
      if G.z > wtot || lo0 + wtot > c.rs.size then none
      let HV ← (Array.range G.o).mapM fun hi => (eqLow c.rs (lo0 + G.z) (lo0 + wtot))[hi]?
      pure ({ pt := (Array.range G.z).map fun i => c.rs.getD (lo0 + G.z - 1 - i) zeroE,
              HV := HV } : WsFac)) = some X := h
  have hc : ¬ (G.z > wtot || lo0 + wtot > c.rs.size) = true := by
    intro hc
    simp only [hc, ↓reduceIte] at h'
    cases h'
  simp only [hc] at h'
  have hz : G.z ≤ wtot := by
    by_contra hh
    exact hc (by simp; omega)
  have hsz : lo0 + wtot ≤ c.rs.size := by
    by_contra hh
    exact hc (by simp; omega)
  obtain ⟨_, _, h2⟩ := bind_some h'
  obtain ⟨HV, hm, h3⟩ := bind_some h2
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at hm
  obtain ⟨l, hl, -⟩ := map_some hm
  have ho : G.o ≤ 2 ^ (wtot - G.z) := by
    rcases Nat.eq_zero_or_pos G.o with e | hpos
    · rw [e]
      exact Nat.zero_le _
    · obtain ⟨b, -, hf⟩ := (list_mapM_some _ _ l hl).2 (G.o - 1) (G.o - 1)
        (List.getElem?_range (by omega))
      have h1 : G.o - 1 < (eqLow c.rs (lo0 + G.z) (lo0 + wtot)).size := by
        by_contra hh
        rw [Array.getElem?_eq_none (by omega)] at hf
        cases hf
      unfold eqLow at h1
      rw [eqTab_size, rev_size c.rs hsz] at h1
      have e : lo0 + wtot - (lo0 + G.z) = wtot - G.z := by omega
      rw [e] at h1
      omega
  calc G.o * 2 ^ G.z ≤ 2 ^ (wtot - G.z) * 2 ^ G.z := Nat.mul_le_mul_right _ ho
    _ = 2 ^ wtot := by rw [← pow_add, Nat.sub_add_cancel hz]

/-- A sum over the indices of a group under weights that are the equality weights of wy bits, as a
sum over all numbers of wy bits. -/
theorem sum_eqR_trunc (rs : Array E) {lo wy R : ℕ} (hle : R ≤ 2 ^ wy) (w A : ℕ → K)
    (hw : ∀ v, v < R → w v = eqR ρ rs lo (lo + wy) v) :
    ∑ v ∈ range R, w v * A v =
      ∑ yv ∈ range (2 ^ wy), eqR ρ rs lo (lo + wy) yv * (if yv < R then A yv else 0) := by
  simp only [mul_ite, mul_zero]
  rw [sum_trunc hle]
  exact sum_congr rfl fun v hv => by rw [hw v (mem_range.mp hv)]

/-! ## A unit with the groups kk and x -/

section Two

variable {g1 g2 : WsGrp} (n1 : g1.name = "kk") (n2 : g2.name = "x")
include n1 n2

omit [Field K] in
/-- Such a unit has no group e. -/
theorem hasE_two : hasE [g1, g2] = false := by
  unfold hasE
  rw [List.any_cons, List.any_cons, List.any_nil, n1, n2]
  rfl

/-- The vector at Y: the rest of the sum at the index Y of kk, and 0 from the number of the indices
of kk on. -/
theorem sumSel_two (X1 X2 : WsFac) (F : List ℕ → K) (Y : ℕ) :
    sumSel ρ (selOf [g1, g2] Y) [(X1, g1), (X2, g2)] F =
      if Y < g1.R then ∑ w ∈ range g2.R, facAt ρ X2 g2 w * F [Y, w] else 0 := by
  have s1 : selOf [g1, g2] Y g1 = some Y := by
    rw [selOf_kk _ _ n1, hasE_two n1 n2]
    rfl
  have s2 : selOf [g1, g2] Y g2 = none :=
    selOf_other _ _ (by rw [n2]; rfl) (by rw [n2]; rfl)
  rw [sumSel_some ρ s1, sumSel_none ρ s2]
  rfl

/-- The sum that a claim on such a unit speaks of is the extension of the claim's vector at the
lowest wy coordinates of the batched sumcheck's place, if the factor on kk is made from these. -/
theorem row_two (c : ClaimEnv) {wy : ℕ} {X1 : WsFac} (X2 : WsFac) (hE : g1.cls = 'E')
    (hR : g1.R = g1.o * 2 ^ g1.z) (h1 : c.facRs g1 0 wy = some X1) (F : List ℕ → K) :
    sumIdx ρ [(X1, g1), (X2, g2)] F = ∑ yv ∈ range (2 ^ wy), eqR ρ c.rs 0 wy yv *
      sumSel ρ (selOf [g1, g2] yv) [(X1, g1), (X2, g2)] F := by
  have hle : g1.R ≤ 2 ^ wy := by
    rw [hR]
    exact facRs_le h1
  simp only [sumSel_two ρ n1 n2]
  have e := sum_eqR_trunc ρ c.rs (lo := 0) hle (facAt ρ X1 g1)
    (fun v => ∑ w ∈ range g2.R, facAt ρ X2 g2 w * F [v, w])
    (fun v hv => facRs_at ρ c g1 0 wy (beq_iff_eq.mpr hE) h1 v (hR ▸ hv))
  rw [Nat.zero_add] at e
  exact e

end Two

/-! ## A unit with the groups hd, cd and kk -/

section Last

variable {g1 g2 g3 : WsGrp} (n1 : g1.name = "hd") (n2 : g2.name = "cd") (n3 : g3.name = "kk")
include n1 n2 n3

omit [Field K] in
/-- Such a unit has no group e. -/
theorem hasE_last : hasE [g1, g2, g3] = false := by
  unfold hasE
  rw [List.any_cons, List.any_cons, List.any_cons, List.any_nil, n1, n2, n3]
  rfl

/-- The vector at Y: the rest of the sum at the index Y of kk, and 0 from the number of the indices
of kk on. -/
theorem sumSel_last (X1 X2 X3 : WsFac) (F : List ℕ → K) (Y : ℕ) :
    sumSel ρ (selOf [g1, g2, g3] Y) [(X1, g1), (X2, g2), (X3, g3)] F =
      if Y < g3.R then ∑ a ∈ range g1.R, ∑ b ∈ range g2.R,
        facAt ρ X1 g1 a * (facAt ρ X2 g2 b * F [a, b, Y]) else 0 := by
  have s1 : selOf [g1, g2, g3] Y g1 = none :=
    selOf_other _ _ (by rw [n1]; rfl) (by rw [n1]; rfl)
  have s2 : selOf [g1, g2, g3] Y g2 = none :=
    selOf_other _ _ (by rw [n2]; rfl) (by rw [n2]; rfl)
  have s3 : selOf [g1, g2, g3] Y g3 = some Y := by
    rw [selOf_kk _ _ n3, hasE_last n1 n2 n3]
    rfl
  rw [sumSel_none ρ s1]
  simp only [sumSel_none ρ s2, sumSel_some ρ s3]
  by_cases h : Y < g3.R
  · simp only [if_pos h, Finset.mul_sum]
    rfl
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero]

/-- The sum that a claim on such a unit speaks of is the extension of the claim's vector at the
lowest wy coordinates of the batched sumcheck's place, if the factor on kk is made from these. -/
theorem row_last (c : ClaimEnv) {wy : ℕ} (X1 X2 : WsFac) {X3 : WsFac} (hE : g3.cls = 'E')
    (hR : g3.R = g3.o * 2 ^ g3.z) (h3 : c.facRs g3 0 wy = some X3) (F : List ℕ → K) :
    sumIdx ρ [(X1, g1), (X2, g2), (X3, g3)] F = ∑ yv ∈ range (2 ^ wy), eqR ρ c.rs 0 wy yv *
      sumSel ρ (selOf [g1, g2, g3] yv) [(X1, g1), (X2, g2), (X3, g3)] F := by
  have hle : g3.R ≤ 2 ^ wy := by
    rw [hR]
    exact facRs_le h3
  simp only [sumSel_last ρ n1 n2 n3]
  have e := sum_eqR_trunc ρ c.rs (lo := 0) hle (facAt ρ X3 g3)
    (fun v => ∑ a ∈ range g1.R, ∑ b ∈ range g2.R,
      facAt ρ X1 g1 a * (facAt ρ X2 g2 b * F [a, b, v]))
    (fun v hv => facRs_at ρ c g3 0 wy (beq_iff_eq.mpr hE) h3 v (hR ▸ hv))
  rw [Nat.zero_add] at e
  rw [← e]
  have e0 : sumIdx ρ [(X1, g1), (X2, g2), (X3, g3)] F =
      ∑ a ∈ range g1.R, facAt ρ X1 g1 a * ∑ b ∈ range g2.R, facAt ρ X2 g2 b *
        ∑ v ∈ range g3.R, facAt ρ X3 g3 v * F [a, b, v] := rfl
  rw [e0]
  simp only [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine sum_congr rfl fun v _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  ring

end Last

/-! ## A unit with the groups kk, e and x -/

section Three

variable {g1 g2 g3 : WsGrp} (n1 : g1.name = "kk") (n2 : g2.name = "e") (n3 : g3.name = "x")
include n1 n2 n3

omit [Field K] in
/-- Such a unit has a group e. -/
theorem hasE_three : hasE [g1, g2, g3] = true := by
  unfold hasE
  rw [List.any_cons, List.any_cons, List.any_cons, List.any_nil, n1, n2, n3]
  rfl

omit [Field K] n2 n3 in
/-- The bits of a column are those of an index of the first group. -/
theorem wkOf_three : wkOf [g1, g2, g3] = ceilLog2 g1.R := by
  unfold wkOf
  rw [List.find?_cons_of_pos (by rw [n1]; rfl)]
  rfl

/-- The vector at the place i 2^wk + yv, yv below 2^wk: the rest of the sum at the index yv of kk
and the index i of e, and 0 where one of the two groups has no such index. -/
theorem sumSel_three (X1 X2 X3 : WsFac) (F : List ℕ → K) {wk : ℕ} (hwk : ceilLog2 g1.R = wk)
    (i : ℕ) {yv : ℕ} (hy : yv < 2 ^ wk) :
    sumSel ρ (selOf [g1, g2, g3] (i * 2 ^ wk + yv)) [(X1, g1), (X2, g2), (X3, g3)] F =
      if yv < g1.R then (if i < g2.R then ∑ x ∈ range g3.R, facAt ρ X3 g3 x * F [yv, i, x] else 0)
      else 0 := by
  have hpos : 0 < 2 ^ wk := by positivity
  have em : (i * 2 ^ wk + yv) % 2 ^ wk = yv := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  have ed : (i * 2 ^ wk + yv) / 2 ^ wk = i := by
    rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hy, Nat.add_zero]
  have s1 : selOf [g1, g2, g3] (i * 2 ^ wk + yv) g1 = some yv := by
    rw [selOf_kk _ _ n1, hasE_three n1 n2 n3, wkOf_three n1, hwk, if_pos rfl, em]
  have s2 : selOf [g1, g2, g3] (i * 2 ^ wk + yv) g2 = some i := by
    rw [selOf_e _ _ n2, wkOf_three n1, hwk, ed]
  have s3 : selOf [g1, g2, g3] (i * 2 ^ wk + yv) g3 = none :=
    selOf_other _ _ (by rw [n3]; rfl) (by rw [n3]; rfl)
  rw [sumSel_some ρ s1, sumSel_some ρ s2, sumSel_none ρ s3]
  rfl

/-- The sum that a claim on such a unit speaks of is the extension of the claim's vector at the
lowest wk + wr coordinates of the batched sumcheck's place, if the factor on kk is made from the
lowest wk of them and the factor on e from the wr above. Asked beside: wk is the number of bits of
an index of kk. -/
theorem all_three (c : ClaimEnv) {wk wr : ℕ} {X1 X2 : WsFac} (X3 : WsFac) (hE1 : g1.cls = 'E')
    (hR1 : g1.R = g1.o * 2 ^ g1.z) (hE2 : g2.cls = 'E') (hR2 : g2.R = g2.o * 2 ^ g2.z)
    (h1 : c.facRs g1 0 wk = some X1) (h2 : c.facRs g2 wk wr = some X2)
    (hwk : ceilLog2 g1.R = wk) (F : List ℕ → K) :
    sumIdx ρ [(X1, g1), (X2, g2), (X3, g3)] F =
      ∑ i ∈ range (2 ^ wr), ∑ yv ∈ range (2 ^ wk),
        eqR ρ c.rs wk (wk + wr) i * eqR ρ c.rs 0 wk yv *
          sumSel ρ (selOf [g1, g2, g3] (i * 2 ^ wk + yv)) [(X1, g1), (X2, g2), (X3, g3)] F := by
  have hle1 : g1.R ≤ 2 ^ wk := by
    rw [hR1]
    exact facRs_le h1
  have hle2 : g2.R ≤ 2 ^ wr := by
    rw [hR2]
    exact facRs_le h2
  have inner : ∀ i, ∑ yv ∈ range (2 ^ wk), eqR ρ c.rs wk (wk + wr) i * eqR ρ c.rs 0 wk yv *
        sumSel ρ (selOf [g1, g2, g3] (i * 2 ^ wk + yv)) [(X1, g1), (X2, g2), (X3, g3)] F =
      eqR ρ c.rs wk (wk + wr) i * (if i < g2.R then ∑ v ∈ range g1.R, facAt ρ X1 g1 v *
        ∑ x ∈ range g3.R, facAt ρ X3 g3 x * F [v, i, x] else 0) := by
    intro i
    have e := sum_eqR_trunc ρ c.rs (lo := 0) hle1 (facAt ρ X1 g1)
      (fun v => if i < g2.R then ∑ x ∈ range g3.R, facAt ρ X3 g3 x * F [v, i, x] else 0)
      (fun v hv => facRs_at ρ c g1 0 wk (beq_iff_eq.mpr hE1) h1 v (hR1 ▸ hv))
    rw [Nat.zero_add] at e
    have e' : (if i < g2.R then ∑ v ∈ range g1.R, facAt ρ X1 g1 v *
          ∑ x ∈ range g3.R, facAt ρ X3 g3 x * F [v, i, x] else 0) =
        ∑ v ∈ range g1.R, facAt ρ X1 g1 v *
          (if i < g2.R then ∑ x ∈ range g3.R, facAt ρ X3 g3 x * F [v, i, x] else 0) := by
      by_cases h : i < g2.R
      · simp only [if_pos h]
      · simp only [if_neg h, mul_zero, Finset.sum_const_zero]
    rw [e', e, Finset.mul_sum]
    refine sum_congr rfl fun yv hyv => ?_
    rw [sumSel_three ρ n1 n2 n3 X1 X2 X3 F hwk i (mem_range.mp hyv), mul_assoc]
  simp only [inner]
  rw [← sum_eqR_trunc ρ c.rs (lo := wk) hle2 (facAt ρ X2 g2)
    (fun i => ∑ v ∈ range g1.R, facAt ρ X1 g1 v * ∑ x ∈ range g3.R, facAt ρ X3 g3 x * F [v, i, x])
    (fun v hv => facRs_at ρ c g2 wk wr (beq_iff_eq.mpr hE2) h2 v (hR2 ▸ hv))]
  have e0 : sumIdx ρ [(X1, g1), (X2, g2), (X3, g3)] F =
      ∑ v ∈ range g1.R, facAt ρ X1 g1 v * ∑ i ∈ range g2.R, facAt ρ X2 g2 i *
        ∑ x ∈ range g3.R, facAt ρ X3 g3 x * F [v, i, x] := rfl
  rw [e0]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun v _ => sum_congr rfl fun x _ => ?_
  ring

end Three

/-! ## The unit of a claim, in a layout that wsLayOf returns -/

section Units

variable {s : WsShape} {lk : ℕ} {lay : WsLay}

omit [Field K] in
/-- The unit that the verifier finds under a kind and a layer is one of the asked units, placed; it
has that kind and layer, and its numbers fit. -/
theorem unit_found (h : wsLayOf s true lk = .ok lay) {X l ui : ℕ} {u : WsUnit}
    (h1 : lay.unitOf X l = some ui) (h2 : lay.U[ui]? = some u) :
    UnitOK lk u ∧ ∃ a ∈ allAsks (shapeOf s true), ∃ o, u = unitP lk o a ∧ a.X = X ∧ a.l = l := by
  have hm : u ∈ lay.U := Array.mem_of_getElem? h2
  obtain ⟨-, hall⟩ := unitOK_of_layout h
  obtain ⟨-, hU, -, -⟩ := wsLayOf_units h
  have hu' : u ∈ unitsFrom lk 0 (allAsks (shapeOf s true)) := by
    rw [← hU]
    exact Array.mem_toList_iff.mpr hm
  obtain ⟨-, a, ha, o, e⟩ := unitsFrom_in lk _ _ u hu'
  unfold WsLay.unitOf at h1
  rw [arr_findIdx, List.findIdx?_eq_some_iff_getElem] at h1
  obtain ⟨hi, hp, -⟩ := h1
  have e2 : lay.U.toList[ui] = u := by
    have e3 : lay.U.toList[ui]? = some u := by rw [Array.getElem?_toList]; exact h2
    rw [List.getElem?_eq_getElem hi] at e3
    exact Option.some.inj e3
  rw [e2] at hp
  have hp' : u.X = X ∧ u.l = l := by simpa using hp
  rw [e] at hp'
  exact ⟨(hall u hm).1, a, ha, o, e, hp'.1, hp'.2⟩

omit [Field K] in
/-- Placing a group does not change its number of indices. -/
theorem sizes_placeP : ∀ (g : List WsGrp) (left cb : ℕ),
    (placeP g left cb).map (·.R) = g.map (·.R)
  | [], _, _ => rfl
  | x :: g, left, cb => by
    show x.R :: (placeP g (left - tP x left) (cb + tP x left)).map (·.R) = x.R :: g.map (·.R)
    rw [sizes_placeP g]

omit [Field K] in
/-- An asked unit of a kind up to 11 is asked for by a layer. -/
theorem ask_of_layer {s' : WsShape} {a : AskW} (ha : a ∈ allAsks s') (hX : a.X ≤ 11) :
    ∃ l, a ∈ layerAsks s' l := by
  unfold allAsks at ha
  rcases List.mem_append.mp ha with h | h
  · obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp h
    exact ⟨l, hl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with e | e <;> rw [e] at hX <;> exact absurd hX (by simp)

omit [Field K] in
/-- The names and classes of the groups of the unit of a kind up to 11. -/
theorem groups_found (h : wsLayOf s true lk = .ok lay) {X l ui : ℕ} {u : WsUnit}
    (h1 : lay.unitOf X l = some ui) (h2 : lay.U[ui]? = some u) (hX : X ≤ 11) :
    u.g.map (fun y => (y.name, y.cls)) = groupsOf X := by
  obtain ⟨-, a, ha, o, e, eX, -⟩ := unit_found h h1 h2
  obtain ⟨l', hl'⟩ := ask_of_layer ha (by rw [eX]; exact hX)
  rw [e, ← eX]
  show (placeP a.g lk 0).map (fun y => (y.name, y.cls)) = groupsOf a.X
  rw [names_placeP]
  exact layer_groups _ l' a hl'

omit [Field K] in
/-- The first group of an asked unit of routed experts has d indices (kinds 7 and 8) or fe (kind
10). -/
theorem first_size {s' : WsShape} {l : ℕ} {a : AskW} (ha : a ∈ layerAsks s' l)
    (hX : a.X = 7 ∨ a.X = 8 ∨ a.X = 10) :
    (a.g.map (·.R)).head? = some (if a.X = 10 then s'.fe else s'.d) := by
  unfold layerAsks at ha
  by_cases hm : s'.moe.getD l false = true
  · rw [if_pos hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e | e | e | e | e <;> subst e <;>
      first | rfl | (exfalso; simp at hX)
  · rw [if_neg hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e <;> subst e <;> first | rfl | (exfalso; simp at hX)

omit [Field K] in
/-- The same for the unit that the verifier finds. -/
theorem first_found (h : wsLayOf s true lk = .ok lay) {X l ui : ℕ} {u : WsUnit}
    (h1 : lay.unitOf X l = some ui) (h2 : lay.U[ui]? = some u) (hX : X = 7 ∨ X = 8 ∨ X = 10) :
    (u.g.map (·.R)).head? = some (if X = 10 then s.fe else s.d) := by
  obtain ⟨-, a, ha, o, e, eX, -⟩ := unit_found h h1 h2
  obtain ⟨l', hl'⟩ := ask_of_layer ha (by rw [eX]; omega)
  rw [e, ← eX]
  show ((placeP a.g lk 0).map (·.R)).head? = _
  rw [sizes_placeP]
  have r := first_size hl' (by rw [eX]; exact hX)
  exact r

end Units

/-! ## One claim of the verifier -/

section Claim

variable {c : ClaimEnv} {s : WsShape} {lk : ℕ}

/-- A claim on a unit with the groups kk and x, whose factor on kk is made from the lowest wy
coordinates of the batched sumcheck's place: the sum that the claim speaks of is the extension of
the claim's vector at these coordinates. fx: the factor on the other group, whatever it is. -/
theorem claim_row_two (hl : wsLayOf s true lk = .ok c.wsLay) (W : Wm K) {X lam wy : ℕ}
    {fx : WsGrp → Option WsFac} {x : WsClaim}
    (hcl : c.claim X lam (fun G => if G.name == "kk" then c.facRs G 0 wy else fx G) = some x)
    (hg : groupsOf X = [("kk", 'E'), ("x", 'E')]) (hX : X ≤ 11) :
    claimVal ρ c.wsLay W x =
      ∑ yv ∈ range (2 ^ wy), eqR ρ c.rs 0 wy yv * wvClaim ρ c.wsLay W x yv := by
  obtain ⟨u, h1, h2, h3⟩ := claim_inv hcl
  have ok := (unit_found hl h1 h2).1
  have hgr := groups_found hl h1 h2 hX
  rw [hg] at hgr
  obtain ⟨g1, g2, hu, e1, e2⟩ := map_two hgr
  have m1 : g1 ∈ u.g := by rw [hu]; simp
  have n1 : g1.name = "kk" := congrArg Prod.fst e1
  have c1 : g1.cls = 'E' := congrArg Prod.snd e1
  have n2 : g2.name = "x" := congrArg Prod.fst e2
  rw [hu] at h3
  obtain ⟨X1, r1, f1, ha, hf⟩ := mapM_cons_some h3
  obtain ⟨X2, r2, -, hb, rfl⟩ := mapM_cons_some ha
  have hr : r2 = [] := by simpa using hb.symm
  subst hr
  have f1' : (if g1.name == "kk" then c.facRs g1 0 wy else fx g1) = some X1 := f1
  rw [if_pos (beq_iff_eq.mpr n1)] at f1'
  unfold claimVal wvClaim
  simp only [h2, hu, hf]
  exact row_two ρ n1 n2 c X2 c1 (size_of_ok ok m1 c1) f1' _

/-- The same for a claim on a unit with the groups hd, cd and kk. f1, f2: the factors on the first
two groups, whatever they are. -/
theorem claim_row_last (hl : wsLayOf s true lk = .ok c.wsLay) (W : Wm K) {lam wy : ℕ}
    {f1 f2 : Option WsFac} {x : WsClaim}
    (hcl : c.claim 0 lam (fun G => if G.name == "hd" then f1 else if G.name == "cd" then f2
      else c.facRs G 0 wy) = some x) :
    claimVal ρ c.wsLay W x =
      ∑ yv ∈ range (2 ^ wy), eqR ρ c.rs 0 wy yv * wvClaim ρ c.wsLay W x yv := by
  obtain ⟨u, h1, h2, h3⟩ := claim_inv hcl
  have ok := (unit_found hl h1 h2).1
  have hgr : u.g.map (fun y => (y.name, y.cls)) = [("hd", 'A'), ("cd", 'A'), ("kk", 'E')] :=
    groups_found hl h1 h2 (Nat.zero_le _)
  obtain ⟨g1, g2, g3, hu, e1, e2, e3⟩ := map_three hgr
  have m3 : g3 ∈ u.g := by rw [hu]; simp
  have n1 : g1.name = "hd" := congrArg Prod.fst e1
  have n2 : g2.name = "cd" := congrArg Prod.fst e2
  have n3 : g3.name = "kk" := congrArg Prod.fst e3
  have c3 : g3.cls = 'E' := congrArg Prod.snd e3
  rw [hu] at h3
  obtain ⟨X1, r1, -, ha, hf⟩ := mapM_cons_some h3
  obtain ⟨X2, r2, -, hb, rfl⟩ := mapM_cons_some ha
  obtain ⟨X3, r3, k3, hc, rfl⟩ := mapM_cons_some hb
  have hr : r3 = [] := by simpa using hc.symm
  subst hr
  have k3' : (if g3.name == "hd" then f1 else if g3.name == "cd" then f2
      else c.facRs g3 0 wy) = some X3 := k3
  rw [n3] at k3'
  have k3'' : c.facRs g3 0 wy = some X3 := k3'
  unfold claimVal wvClaim
  simp only [h2, hu, hf]
  exact row_last ρ n1 n2 n3 c X1 X2 c3 (size_of_ok ok m3 c3) k3'' _

/-- A claim on a unit of routed experts, with the groups kk, e and x, whose factor on kk is made
from the lowest wk coordinates of the batched sumcheck's place and whose factor on e from the wr
coordinates above: the sum that the claim speaks of is the extension of the claim's vector at these
wk + wr coordinates. Asked beside: wk is the number of bits of an index of kk, by the shape of the
weights. fx: the factor on the third group, whatever it is. -/
theorem claim_all_three (hl : wsLayOf s true lk = .ok c.wsLay) (W : Wm K) {X lam wk wr : ℕ}
    {fx : WsGrp → Option WsFac} {x : WsClaim}
    (hcl : c.claim X lam (fun G => if G.name == "kk" then c.facRs G 0 wk
      else if G.name == "e" then c.facRs G wk wr else fx G) = some x)
    (hX : X = 7 ∨ X = 8 ∨ X = 10) (hwk : ceilLog2 (if X = 10 then s.fe else s.d) = wk) :
    claimVal ρ c.wsLay W x =
      ∑ i ∈ range (2 ^ wr), ∑ yv ∈ range (2 ^ wk),
        eqR ρ c.rs wk (wk + wr) i * eqR ρ c.rs 0 wk yv *
          wvClaim ρ c.wsLay W x (i * 2 ^ wk + yv) := by
  obtain ⟨u, h1, h2, h3⟩ := claim_inv hcl
  have ok := (unit_found hl h1 h2).1
  have hgr := groups_found hl h1 h2 (by omega)
  have hg : groupsOf X = [("kk", 'E'), ("e", 'E'), ("x", 'E')] := by
    rcases hX with e | e | e <;> rw [e] <;> rfl
  rw [hg] at hgr
  obtain ⟨g1, g2, g3, hu, e1, e2, e3⟩ := map_three hgr
  have m1 : g1 ∈ u.g := by rw [hu]; simp
  have m2 : g2 ∈ u.g := by rw [hu]; simp
  have n1 : g1.name = "kk" := congrArg Prod.fst e1
  have c1 : g1.cls = 'E' := congrArg Prod.snd e1
  have n2 : g2.name = "e" := congrArg Prod.fst e2
  have c2 : g2.cls = 'E' := congrArg Prod.snd e2
  have n3 : g3.name = "x" := congrArg Prod.fst e3
  have hR := first_found hl h1 h2 hX
  rw [hu] at hR
  have hR1 : g1.R = if X = 10 then s.fe else s.d := Option.some.inj hR
  rw [hu] at h3
  obtain ⟨X1, r1, k1, ha, hf⟩ := mapM_cons_some h3
  obtain ⟨X2, r2, k2, hb, rfl⟩ := mapM_cons_some ha
  obtain ⟨X3, r3, -, hc, rfl⟩ := mapM_cons_some hb
  have hr : r3 = [] := by simpa using hc.symm
  subst hr
  have k1' : (if g1.name == "kk" then c.facRs g1 0 wk
      else if g1.name == "e" then c.facRs g1 wk wr else fx g1) = some X1 := k1
  rw [if_pos (beq_iff_eq.mpr n1)] at k1'
  have k2' : (if g2.name == "kk" then c.facRs g2 0 wk
      else if g2.name == "e" then c.facRs g2 wk wr else fx g2) = some X2 := k2
  rw [n2] at k2'
  have k2'' : c.facRs g2 wk wr = some X2 := k2'
  unfold claimVal wvClaim
  simp only [h2, hu, hf]
  exact all_three ρ n1 n2 n3 c X3 c1 (size_of_ok ok m1 c1) c2 (size_of_ok ok m2 c2) k1' k2''
    (by rw [hR1]; exact hwk) _

end Claim

/-! ## The bits of a panel's columns -/

section Widths

omit [Field K] in
/-- What is appended to an array can be read off the result. -/
theorem push_inj {α : Type} {a : Array α} {x y : α} (h : a.push x = a.push y) : x = y :=
  (Array.push_eq_push.mp h).1

omit [Field K] in
/-- The bits of a column of the panel that panelA appends for one of its six segments. -/
theorem panelA_wy (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels) {b : SBlk}
    (h : isAcc sn = true) (hb : (panelA p ec el sn s).bl = s.bl.push b) :
    b.wy = ceilLog2
      (if sn == "O" then p.v.y.dq else if sn == "D" then p.v.y.h.f else p.v.y.h.d) := by
  rcases (isAcc_iff sn).mp h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact congrArg SBlk.wy (push_inj hb).symm

omit [Field K] in
/-- The bits of a column of the panel that panelT appends for the segment QK. -/
theorem panelT_QK_wy (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    {b : SBlk} (hs : sn = "QK") (h : panelT p ec el sn s = some s') (hb : s'.bl = s.bl.push b) :
    b.wy = ceilLog2 p.v.y.h.d := by
  subst hs
  rw [panelT_QK_eq] at h
  cases h
  exact congrArg SBlk.wy (push_inj hb).symm

omit [Field K] in
/-- The bits of a column and of a place of the panel that a step of triStep appends. -/
theorem triStep_wy {p : PanelEnv} {ec : E} {el : Array E} {sn : String} {s s' : Panels} {lm : ℕ}
    {b : SBlk} (h : triStep p ec el sn s lm = some s') (hb : s'.bl = s.bl.push b) :
    b.wy = ceilLog2 (if sn == "D" then p.v.y.h.fe else p.v.y.h.d) ∧
      b.w = ceilLog2 (max p.v.y.h.NE 1) + b.wy := by
  simp only [triStep] at h
  split_ifs at h ⊢ <;> first
    | (cases h; obtain rfl := push_inj hb; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h; obtain rfl := push_inj hb; exact ⟨rfl, rfl⟩)

end Widths

/-! ## The claims of the verifier's own lists -/

section Lists

variable {c : ClaimEnv} {s : WsShape} {lk : ℕ}

omit [Field K] in
/-- The unit of a claim of one of the six segments of the lookup's join has the groups kk and x. -/
theorem kindA_groups (sn : String) (m1 m2 : Bool) (h : isAcc sn = true) :
    groupsOf (if sn == "G" then (if m1 then 5 else 3) else if sn == "U" then (if m2 then 6 else 4)
      else if sn == "V" then 1 else if sn == "O" then 2 else if sn == "D" then 9 else 11) =
        [("kk", 'E'), ("x", 'E')] ∧
    (if sn == "G" then (if m1 then 5 else 3) else if sn == "U" then (if m2 then 6 else 4)
      else if sn == "V" then 1 else if sn == "O" then 2 else if sn == "D" then 9 else 11) ≤ 11 := by
  rcases (isAcc_iff sn).mp h with rfl | rfl | rfl | rfl | rfl | rfl <;> cases m1 <;> cases m2 <;>
    exact ⟨rfl, Nat.le_of_ble_eq_true rfl⟩

/-- The vector of claim number a is the vector of the claim that stands there. -/
theorem wvOf_at (lay : WsLay) (W : Wm K) {cl : List WsClaim} {a : ℕ} {x : WsClaim}
    (h : cl[a]? = some x) : wvOf ρ lay W cl a = wvClaim ρ lay W x := by
  funext Y
  unfold wvOf
  rw [h]

/-- A claim of a routed product, as claimsT makes it. -/
theorem routed_claim (hl : wsLayOf s true lk = .ok c.wsLay) (hd : s.d = c.v.y.h.d)
    (hfe : s.fe = c.v.y.h.fe) (W : Wm K) {sn : String} (hs : sn = "G" ∨ sn = "U" ∨ sn = "D")
    {lm : ℕ} {x : WsClaim}
    (hcl : c.claim (if sn == "G" then 7 else if sn == "U" then 8 else 10) (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d))
      else if G.name == "e" then
        c.facRs G (ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d))
          (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G sn (if sn == "D" then 0 else c.v.y.h.fe)) = some x) :
    claimVal ρ c.wsLay W x =
      ∑ i ∈ range (2 ^ ceilLog2 (max c.v.y.h.NE 1)),
        ∑ yv ∈ range (2 ^ ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d)),
          eqR ρ c.rs (ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d))
              (ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d) +
                ceilLog2 (max c.v.y.h.NE 1)) i *
            eqR ρ c.rs 0 (ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d)) yv *
          wvClaim ρ c.wsLay W x
            (i * 2 ^ ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d) + yv) := by
  rcases hs with rfl | rfl | rfl
  · exact claim_all_three ρ hl W hcl (Or.inl rfl)
      (by show ceilLog2 s.d = ceilLog2 c.v.y.h.d; rw [hd])
  · exact claim_all_three ρ hl W hcl (Or.inr (Or.inl rfl))
      (by show ceilLog2 s.d = ceilLog2 c.v.y.h.d; rw [hd])
  · exact claim_all_three ρ hl W hcl (Or.inr (Or.inr rfl))
      (by show ceilLog2 s.fe = ceilLog2 c.v.y.h.fe; rw [hfe])

end Lists

/-! ## The whole -/

/-- The end values of the weight claims are true of the claims' vectors. On the verifier's own list
of panels and its own list of weight claims (hv, hp, hc, as in Johnson/Road/FormsKeysFold.lean), in
a layout of the weights that wsLayOf returns for a shape s with the widths d and fe of the layer
sub-proof's shape: if vv a is, for every claim number a, the sum that the claim speaks of in the
matrix W (hV), then for every panel of the list the two fields of EndsTrue on the weight claims hold
with the vectors wvOf, which are made from the claims and W. First the panels with the selector
(allV), then the others (rowV). -/
theorem ends_of_claims (p : PanelEnv) (c : ClaimEnv) (hv : p.v = c.v) (TS : List ℕ)
    {pans : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans)
    (hc : c.weightClaims TS = some cl) {s : WsShape} {lk : ℕ}
    (hl : wsLayOf s true lk = .ok c.wsLay) (hd : s.d = c.v.y.h.d) (hfe : s.fe = c.v.y.h.fe)
    (W : Wm K) {vv : ℕ → K} (hV : ∀ a x, cl[a]? = some x → vv a = claimVal ρ c.wsLay W x) :
    ∀ b ∈ pans.bl.toList,
      (∀ v0, b.tri = true → b.v0 = some v0 →
        vv v0 = gsum ρ c.rs b (fun i yv => wvOf ρ c.wsLay W cl v0 (i * 2 ^ b.wy + yv))) ∧
      (∀ v0 i, b.tri = false → b.v0 = some v0 → i < b.ni →
        vv (v0 + i) =
          ∑ yv ∈ range (2 ^ b.wy), eqR ρ c.rs 0 b.wy yv * wvOf ρ c.wsLay W cl (v0 + i) yv) := by
  intro b hb
  have G := (claims_of_panels p c hv TS hp hc).2 b hb
  refine ⟨fun v0 ht h0 => ?_, fun v0 i ht h0 hi => ?_⟩
  · obtain ⟨q, -, g, -, lm, st, st', l, h3, hname, hlm, -, hstep, hbl, hcl, hlen, hat⟩ :=
      (G v0 h0).2 ht
    obtain ⟨-, hatr⟩ := claimsT_routed_at c g.name (hv ▸ h3) hname hcl
    have hlm' : lm < l.length := by omega
    have e2 : l[lm]? = some l[lm] := List.getElem?_eq_getElem hlm'
    have hx : cl[v0]? = some l[lm] := hat.trans e2
    obtain ⟨hwy, hw⟩ := triStep_wy hstep hbl
    rw [hv] at hwy hw
    have hw' : b.w = b.wy + ceilLog2 (max c.v.y.h.NE 1) := by omega
    rw [hV _ _ hx, wvOf_at ρ c.wsLay W hx]
    unfold gsum
    rw [hw', Nat.add_sub_cancel_left, hwy]
    exact routed_claim ρ hl hd hfe W hname ((hatr lm hlm').symm.trans e2)
  · rcases (G v0 h0).1 ht with ⟨q, -, g, -, st, l, hacc, -, hbl, hcl, hlen, hat⟩ |
      ⟨q, -, g, -, st, st', l, hname, -, hpt, hbl, hcl, hlen, hat⟩
    · have hi' : i < l.length := by omega
      have e2 : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
      have hx : cl[v0 + i]? = some l[i] := (hat i hi).trans e2
      have hwy := panelA_wy p _ _ _ st hacc hbl
      rw [hv] at hwy
      obtain ⟨k1, k2⟩ := kindA_groups g.name
        (c.v.isMoe (if g.name == "LR" then 2 * i + 1 else i))
        (c.v.isMoe (if g.name == "LR" then 2 * i + 1 else i)) hacc
      rw [hV _ _ hx, wvOf_at ρ c.wsLay W hx, hwy]
      exact claim_row_two ρ hl W ((claimsA_at c g.name hcl hacc i hi').symm.trans e2) k1 k2
    · have hi' : i < l.length := by omega
      have e2 : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
      have hx : cl[v0 + i]? = some l[i] := (hat i hi).trans e2
      have hwy := panelT_QK_wy p _ _ _ st st' hname hpt hbl
      rw [hv] at hwy
      rw [hname] at hcl
      obtain ⟨-, AH, lfc, -, hatq⟩ := claimsT_QK_at c hcl
      rw [hV _ _ hx, wvOf_at ρ c.wsLay W hx, hwy]
      exact claim_row_last ρ hl W ((hatq i hi').symm.trans e2)

/-! ## The placed panels -/

/-- EndsTrue for the placed panels, with the vectors of the weight claims read from W. As
ends_of_claims; what EndsTrue says of the never-sent vectors (its fields colH and allH, for end
values h1 and vectors hh) stays a hypothesis (hH). -/
theorem endsTrue_of_claims (p : PanelEnv) (c : ClaimEnv) (hv : p.v = c.v) (TS : List ℕ)
    {pans : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans)
    (hc : c.weightClaims TS = some cl) {s : WsShape} {lk : ℕ}
    (hl : wsLayOf s true lk = .ok c.wsLay) (hd : s.d = c.v.y.h.d) (hfe : s.fe = c.v.y.h.fe)
    (W : Wm K) {vv : ℕ → K} (hV : ∀ a x, cl[a]? = some x → vv a = claimVal ρ c.wsLay W x)
    {h1 : ℕ → K} {hh : ℕ → ℕ → K}
    (hH : ∀ b ∈ (placePanels pans.bl).1.toList,
      (∀ k, b.tri = true → b.virt = some k →
        h1 k = ∑ yv ∈ range (2 ^ b.wy), eqR ρ c.rs 0 b.wy yv * hh k yv) ∧
      (∀ k, b.tri = false → b.virt = some k →
        h1 k = gsum ρ c.rs b (fun i yv => hh k (i * 2 ^ b.wy + yv)))) :
    ∀ b ∈ (placePanels pans.bl).1.toList,
      EndsTrue ρ c.rs h1 vv hh (wvOf ρ c.wsLay W cl) b := by
  intro b' hb'
  obtain ⟨k1, k2⟩ := hH b' hb'
  obtain ⟨b, hb, o, rfl⟩ := placed_from _ b' hb'
  obtain ⟨a1, a2⟩ := ends_of_claims ρ p c hv TS hp hc hl hd hfe W hV b hb
  exact ⟨k1, k2, a1, a2⟩

/-! ## Where a claim's vector is 0 -/

section Zero

variable {c : ClaimEnv} {s : WsShape} {lk : ℕ}

/-- The number of indices of the group kk of the unit of kind X, from 1 to 11, of layer l. -/
def kkSize (s' : WsShape) (l X : ℕ) : ℕ :=
  if X = 2 then s'.dq
  else if X = 9 then (if s'.moe.getD l false = true then s'.fe else s'.f)
  else if X = 10 then s'.fe
  else s'.d

omit [Field K] in
/-- An asked unit of a layer has that layer's number, and, unless its kind is 0, its first group has
kkSize indices. -/
theorem kk_first {s' : WsShape} {l : ℕ} {a : AskW} (ha : a ∈ layerAsks s' l) :
    a.l = l ∧ (a.X ≠ 0 → (a.g.map (·.R)).head? = some (kkSize s' l a.X)) := by
  unfold layerAsks at ha
  by_cases hm : s'.moe.getD l false = true
  · rw [if_pos hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e | e | e | e | e <;> subst e <;>
      refine ⟨rfl, fun h0 => ?_⟩ <;> first
        | exact absurd rfl h0
        | simp [kkSize, hm, WsLay.E_]
  · rw [if_neg hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e <;> subst e <;>
      refine ⟨rfl, fun h0 => ?_⟩ <;> first
        | exact absurd rfl h0
        | simp [kkSize, hm, WsLay.E_]

/-- The vector of a claim on a unit with the groups kk and x is 0 from the number of the indices of
kk on. -/
theorem claim_zero_two (hl : wsLayOf s true lk = .ok c.wsLay) (W : Wm K) {X lam : ℕ}
    {fac : WsGrp → Option WsFac} {x : WsClaim} (hcl : c.claim X lam fac = some x)
    (hg : groupsOf X = [("kk", 'E'), ("x", 'E')]) (hX : X ≤ 11) :
    ∀ Y, kkSize (shapeOf s true) (c.v.lay lam) X ≤ Y → wvClaim ρ c.wsLay W x Y = 0 := by
  intro Y hY
  obtain ⟨u, h1, h2, h3⟩ := claim_inv hcl
  have hgr := groups_found hl h1 h2 hX
  rw [hg] at hgr
  obtain ⟨g1, g2, hu, e1, e2⟩ := map_two hgr
  have n1 : g1.name = "kk" := congrArg Prod.fst e1
  have n2 : g2.name = "x" := congrArg Prod.fst e2
  have hX0 : X ≠ 0 := by
    rintro rfl
    exact absurd (congrArg List.length hg) (by decide)
  obtain ⟨-, a, ha, o, e, eX, el⟩ := unit_found hl h1 h2
  obtain ⟨l', hl'⟩ := ask_of_layer ha (by rw [eX]; exact hX)
  obtain ⟨k1, k2⟩ := kk_first hl'
  have hR : (u.g.map (·.R)).head? = some (kkSize (shapeOf s true) (c.v.lay lam) X) := by
    rw [e, ← eX, ← el, k1]
    show ((placeP a.g lk 0).map (·.R)).head? = _
    rw [sizes_placeP]
    exact k2 (by rw [eX]; exact hX0)
  rw [hu] at hR
  have hR1 : g1.R = kkSize (shapeOf s true) (c.v.lay lam) X := Option.some.inj hR
  rw [hu] at h3
  obtain ⟨X1, r1, -, hb, hf⟩ := mapM_cons_some h3
  obtain ⟨X2, r2, -, hb2, rfl⟩ := mapM_cons_some hb
  have hr : r2 = [] := by simpa using hb2.symm
  subst hr
  unfold wvClaim
  simp only [h2, hu, hf]
  show sumSel ρ (selOf [g1, g2] Y) [(X1, g1), (X2, g2)] (wgtOf u W) = 0
  rw [sumSel_two ρ n1 n2, if_neg (by omega)]

/-- The vector of a claim on the down matrix (kind 9) of a layer of the model with an odd number,
which has routed experts, is 0 from fe on: the number of hidden units that are not routed. The panel
of the down product has f columns on every layer. This holds by the definition of sumSel, which is 0
where the picked index is not one of the group's, and by the size of the unit's group kk. That the
vector so defined is the one whose extension the claim's end value is, so that the columns from fe
on add nothing to the batched sum, is what claim_row_two and ends_of_claims say. -/
theorem claim_zero_D (hl : wsLayOf s true lk = .ok c.wsLay) (W : Wm K) {lam : ℕ}
    {fac : WsGrp → Option WsFac} {x : WsClaim} (hcl : c.claim 9 lam fac = some x)
    (hL : c.v.lay lam < s.L) (hodd : c.v.lay lam % 2 = 1) :
    ∀ Y, s.fe ≤ Y → wvClaim ρ c.wsLay W x Y = 0 := by
  obtain ⟨-, -, -, B⟩ := wsLayOf_units hl
  have hm : (shapeOf s true).moe.getD (c.v.lay lam) false = true := by
    rw [B.moe _ hL, hodd]
    rfl
  have e : kkSize (shapeOf s true) (c.v.lay lam) 9 = s.fe := by
    unfold kkSize
    rw [if_neg (by decide), if_pos rfl, if_pos hm]
    rfl
  intro Y hY
  exact claim_zero_two ρ hl W hcl rfl (by decide) Y (by rw [e]; exact hY)

end Zero

/-! ## The vectors do not hang on the batched sumcheck's point -/

section NoPoint

/-- sumSel does not read the factor of a group in which an index is picked. -/
theorem sumSel_congr (sel : WsGrp → Option ℕ) :
    ∀ (fg fg' : List (WsFac × WsGrp)) (F : List ℕ → K),
      List.Forall₂ (fun a b : WsFac × WsGrp => a.2 = b.2 ∧ (sel a.2 = none → a.1 = b.1)) fg fg' →
      sumSel ρ sel fg F = sumSel ρ sel fg' F
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | (x, g) :: fg, (x', g') :: fg', F, h => by
    cases h with
    | cons h1 h2 =>
      obtain ⟨e1, e2⟩ := h1
      have e1' : g = g' := e1
      subst e1'
      cases hs : sel g with
      | some v =>
        rw [sumSel_some ρ hs, sumSel_some ρ hs, sumSel_congr sel fg fg' _ h2]
      | none =>
        have e2' : x = x' := e2 hs
        subst e2'
        rw [sumSel_none ρ hs, sumSel_none ρ hs]
        exact sum_congr rfl fun v _ => by rw [sumSel_congr sel fg fg' _ h2]

omit [Field K] in
/-- Two functions that give the same factor for every group of a list in which nothing is picked
give lists of factors that differ only where an index is picked. -/
theorem zip_rel (sel : WsGrp → Option ℕ) {fac fac' : WsGrp → Option WsFac} :
    ∀ (gs : List WsGrp) (Fs Fs' : List WsFac), (∀ g ∈ gs, sel g = none → fac g = fac' g) →
      gs.mapM fac = some Fs → gs.mapM fac' = some Fs' →
      List.Forall₂ (fun a b : WsFac × WsGrp => a.2 = b.2 ∧ (sel a.2 = none → a.1 = b.1))
        (Fs.zip gs) (Fs'.zip gs)
  | [], Fs, Fs', _, h, h' => by
    have e : Fs = [] := by simpa using h.symm
    have e' : Fs' = [] := by simpa using h'.symm
    subst e e'
    exact List.Forall₂.nil
  | g :: gs, Fs, Fs', hf, h, h' => by
    obtain ⟨x, r, hx, hr, rfl⟩ := mapM_cons_some h
    obtain ⟨x', r', hx', hr', rfl⟩ := mapM_cons_some h'
    refine List.Forall₂.cons ⟨rfl, fun hs => ?_⟩
      (zip_rel sel gs r r' (fun g' hg' => hf g' (List.mem_cons_of_mem _ hg')) hr hr')
    have e : some x = some x' := by rw [← hx, ← hx', hf g List.mem_cons_self hs]
    exact Option.some.inj e

/-- Two claims on the unit of one kind and layer, made in one layout by two functions that give the
same factor for every group of the unit that is not named kk or e, have the same vector. c and c'
need agree only in the environment and in the layout of the weights. -/
theorem wvClaim_congr {c c' : ClaimEnv} (hv : c'.v = c.v) (hw : c'.wsLay = c.wsLay) (W : Wm K)
    {X lam : ℕ} {fac fac' : WsGrp → Option WsFac} {x x' : WsClaim}
    (hx : c.claim X lam fac = some x) (hx' : c'.claim X lam fac' = some x')
    (hf : ∀ u, c.wsLay.unitOf X (c.v.lay lam) = some x.ui → c.wsLay.U[x.ui]? = some u →
      ∀ g ∈ u.g, (g.name == "kk") = false → (g.name == "e") = false → fac g = fac' g) :
    wvClaim ρ c.wsLay W x = wvClaim ρ c.wsLay W x' := by
  obtain ⟨u, h1, h2, h3⟩ := claim_inv hx
  obtain ⟨u', h1', h2', h3'⟩ := claim_inv hx'
  rw [hv, hw] at h1'
  rw [hw] at h2'
  have eui : x.ui = x'.ui := Option.some.inj (h1.symm.trans h1')
  rw [← eui] at h2'
  have eu : u = u' := Option.some.inj (h2.symm.trans h2')
  subst eu
  funext Y
  unfold wvClaim
  rw [← eui, h2]
  refine sumSel_congr ρ _ _ _ _ (zip_rel _ u.g x.f x'.f (fun g hg hs => ?_) h3 h3')
  have k1 : (g.name == "kk") = false := by
    cases hk : (g.name == "kk") with
    | false => rfl
    | true =>
      rw [selOf_kk _ _ (beq_iff_eq.mp hk)] at hs
      cases hs
  have k2 : (g.name == "e") = false := by
    cases hk : (g.name == "e") with
    | false => rfl
    | true =>
      unfold selOf at hs
      rw [k1, hk] at hs
      cases hs
  exact hf u h1 h2 g hg k1 k2

section Rel

variable {α β : Type}

omit [Field K] in
/-- Two functions run over one list, neither refusing: the results are related member by member, if
the two results of each member are. -/
theorem mapM_rel {f f' : α → Option β} (R : β → β → Prop) :
    ∀ (xs : List α) (l l' : List β), xs.mapM f = some l → xs.mapM f' = some l' →
      (∀ x ∈ xs, ∀ y y', f x = some y → f' x = some y' → R y y') → List.Forall₂ R l l'
  | [], l, l', h, h', _ => by
    have e : l = [] := by simpa using h.symm
    have e' : l' = [] := by simpa using h'.symm
    subst e e'
    exact List.Forall₂.nil
  | x :: xs, l, l', h, h', H => by
    obtain ⟨y, r, hy, hr, rfl⟩ := mapM_cons_some h
    obtain ⟨y', r', hy', hr', rfl⟩ := mapM_cons_some h'
    exact List.Forall₂.cons (H x List.mem_cons_self y y' hy hy')
      (mapM_rel R xs r r' hr hr' fun z hz => H z (List.mem_cons_of_mem _ hz))

omit [Field K] in
/-- Lists that are related member by member stay so when they are joined. -/
theorem rel_append {R : β → β → Prop} : ∀ {l1 l1' l2 l2' : List β}, List.Forall₂ R l1 l1' →
    List.Forall₂ R l2 l2' → List.Forall₂ R (l1 ++ l2) (l1' ++ l2')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h1 h2, h => List.Forall₂.cons h1 (rel_append h2 h)

omit [Field K] in
/-- The same for lists of lists, all joined. -/
theorem rel_flatten {R : β → β → Prop} : ∀ {a a' : List (List β)},
    List.Forall₂ (List.Forall₂ R) a a' → List.Forall₂ R a.flatten a'.flatten
  | _, _, .nil => List.Forall₂.nil
  | _, _, .cons h1 h2 => rel_append h1 (rel_flatten h2)

omit [Field K] in
/-- In lists that are related member by member, a number has a member in both, and the two are
related, or in neither. -/
theorem rel_get {R : β → β → Prop} : ∀ {l l' : List β}, List.Forall₂ R l l' → ∀ a : ℕ,
    (l[a]? = none ∧ l'[a]? = none) ∨ ∃ x x', l[a]? = some x ∧ l'[a]? = some x' ∧ R x x'
  | _, _, .nil, _ => Or.inl ⟨rfl, rfl⟩
  | _, _, .cons (a := x) (b := x') h1 _, 0 => Or.inr ⟨x, x', rfl, rfl, h1⟩
  | _, _, .cons _ h2, a + 1 => by
    simpa using rel_get h2 a

end Rel

/-- The vectors of the weight claims do not hang on the batched sumcheck's point. In a layout of the
weights that wsLayOf returns: if weightClaims returns a list at the challenges c.rs and a list at
other challenges rs', all else being the same, the two lists give the same vectors wvOf, in every
matrix W. So in ends_of_claims the end values are extensions, at the point made of c.rs, of vectors
that are the same for every such point. -/
theorem wvOf_rs (c : ClaimEnv) {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok c.wsLay)
    (rs' : Array E) (TS : List ℕ) {cl cl' : List WsClaim} (hc : c.weightClaims TS = some cl)
    (hc' : ({ c with rs := rs' } : ClaimEnv).weightClaims TS = some cl') (W : Wm K) :
    wvOf ρ c.wsLay W cl = wvOf ρ c.wsLay W cl' := by
  obtain ⟨a, t, ha, ht, rfl⟩ :=
    weightClaims_some (p := ⟨c.v, #[], #[], #[], fun _ _ _ => 0⟩) rfl hc
  obtain ⟨a', t', ha', ht', rfl⟩ := weightClaims_some (c := { c with rs := rs' })
    (p := ⟨c.v, #[], #[], #[], fun _ _ _ => 0⟩) rfl hc'
  have rA : List.Forall₂ (List.Forall₂ fun x x' : WsClaim =>
      wvClaim ρ c.wsLay W x = wvClaim ρ c.wsLay W x') a a' := by
    refine mapM_rel _ _ a a' ha ha' fun sn _ l l' hl1 hl2 => ?_
    cases hacc : isAcc sn with
    | false =>
      rw [claimsA_not c _ hacc] at hl1
      rw [claimsA_not _ _ hacc] at hl2
      cases hl1
      cases hl2
      exact List.Forall₂.nil
    | true =>
      rw [claimsA_eq c sn hacc] at hl1
      rw [claimsA_eq _ sn hacc] at hl2
      refine mapM_rel _ _ l l' hl1 hl2 fun i _ x x' hx hx' => ?_
      refine wvClaim_congr ρ (c' := { c with rs := rs' }) rfl rfl W hx hx'
        fun u _ _ g _ k1 _ => ?_
      simp only [k1]
      rfl
  have rT : List.Forall₂ (List.Forall₂ fun x x' : WsClaim =>
      wvClaim ρ c.wsLay W x = wvClaim ρ c.wsLay W x') t t' := by
    refine mapM_rel _ _ t t' ht ht' fun sn _ l l' hl1 hl2 => ?_
    by_cases hQ : (sn == "QK") = true
    · have e : sn = "QK" := beq_iff_eq.mp hQ
      subst e
      rw [claimsT_QK_eq] at hl1 hl2
      obtain ⟨⟨AH, lfc⟩, hw, hl1⟩ := bind_some hl1
      obtain ⟨⟨AH', lfc'⟩, hw', hl2⟩ := bind_some hl2
      have ew : (AH, lfc) = (AH', lfc') := Option.some.inj (hw.symm.trans hw')
      cases ew
      refine mapM_rel _ _ l l' hl1 hl2 fun i _ x x' hx hx' => ?_
      refine wvClaim_congr ρ (c' := { c with rs := rs' }) rfl rfl W hx hx'
        fun u h1 h2 g hg k1 _ => ?_
      have hgr : u.g.map (fun y => (y.name, y.cls)) = [("hd", 'A'), ("cd", 'A'), ("kk", 'E')] :=
        groups_found hl h1 h2 (Nat.zero_le _)
      have hm : (g.name, g.cls) ∈ [("hd", 'A'), ("cd", 'A'), ("kk", 'E')] := by
        rw [← hgr]
        exact List.mem_map.mpr ⟨g, hg, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨e1, -⟩
      · simp only [e1]
        rfl
      · simp only [e1]
        rfl
      · rw [e1] at k1
        exact Bool.noConfusion (show true = false from k1)
    · by_cases hR : (c.v.y.h.p3 && (sn == "G" || sn == "U" || sn == "D")) = true
      · have hR' := hR
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hR'
        obtain ⟨h3, hgud⟩ := hR'
        have hname : sn = "G" ∨ sn = "U" ∨ sn = "D" := by
          rcases hgud with (h | h) | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        rw [claimsT_routed_eq c sn h3 hname] at hl1
        rw [claimsT_routed_eq ({ c with rs := rs' } : ClaimEnv) sn h3 hname] at hl2
        refine mapM_rel _ _ l l' hl1 hl2 fun i _ x x' hx hx' => ?_
        refine wvClaim_congr ρ (c' := { c with rs := rs' }) rfl rfl W hx hx'
          fun u _ _ g _ k1 k2 => ?_
        simp only [k1, k2]
        rfl
      · rw [claimsT_other c _ hQ hR] at hl1
        rw [claimsT_other ({ c with rs := rs' } : ClaimEnv) _ hQ hR] at hl2
        cases hl1
        cases hl2
        exact List.Forall₂.nil
  have rAll := rel_append (rel_flatten rA) (rel_flatten rT)
  funext n
  rcases rel_get rAll n with ⟨e1, e2⟩ | ⟨x, x', e1, e2, e⟩
  · funext Y
    unfold wvOf
    rw [e1, e2]
  · rw [wvOf_at ρ c.wsLay W e1, wvOf_at ρ c.wsLay W e2, e]

end NoPoint

/-! ## With the end of the batched sumcheck -/

/-- endsTrue_of_claims joined with stack_masked of Johnson/Road/FormsKeysEnd.lean: what the
verifier's own two elements of the field are at the end of the batched sumcheck, on its own lists of
panels and of weight claims, in a world Wo whose hidden value under the slot of each weight claim is
what the claim says of a matrix M (hVal). The long B vector then holds, for the panels whose B side
is a weight matrix, the vectors wvOf, which are made from the claims and M. The other hypotheses are
those of the two theorems; what EndsTrue says of the never-sent vectors stays one of them (hH). -/
theorem stack_claims {Wo : World K} {p : PanelEnv} {c : ClaimEnv} (hv : p.v = c.v) {TS : List ℕ}
    {pans : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans)
    (hc : c.weightClaims TS = some cl) {s : WsShape} {lk : ℕ}
    (hl : wsLayOf s true lk = .ok c.wsLay) (hd : s.d = c.v.y.h.d) (hfe : s.fe = c.v.y.h.fe)
    (M : Wm K) {lam : ℕ} {om H1 V : Array E} {hh : ℕ → ℕ → K} {shownA shownB : E}
    {s' : StackEnd} (hlam : (ceilLog2 (placePanels pans.bl).2 == lam) = true)
    (hrs : lam ≤ c.rs.size) {sA0 sH1 sB0 sV : ℕ}
    (hVal : ∀ a x, cl[a]? = some x → Wo.slot (sV + a) = claimVal ρ c.wsLay M x)
    (hH : ∀ b ∈ (placePanels pans.bl).1.toList,
      (∀ k, b.tri = true → b.virt = some k →
        Wo.slot (sH1 + k) = ∑ yv ∈ range (2 ^ b.wy), eqR ρ c.rs 0 b.wy yv * hh k yv) ∧
      (∀ k, b.tri = false → b.virt = some k →
        Wo.slot (sH1 + k) = gsum ρ c.rs b (fun i yv => hh k (i * 2 ^ b.wy + yv))))
    (h : stackEnd p.v.y (placePanels pans.bl).1 c.rs lam om H1 V shownA shownB = some s')
    (cA : (Aff.slot sA0 - s'.Alin).value ρ Wo = 0) (cB : (Aff.slot sB0 - s'.Blin).value ρ Wo = 0)
    (hH1 : nVirt p.v.y ≤ H1.size) (hVs : pans.nextV ≤ V.size) {β mA mB : K} {m1 mv : ℕ → K}
    (eA : ρ.val shownA = Wo.slot sA0 + β * mA) (eB : ρ.val shownB = Wo.slot sB0 + β * mB)
    (e1 : ∀ k, k < H1.size → ρ.val (H1.getD k zeroE) = Wo.slot (sH1 + k) + β * m1 k)
    (eV : ∀ n, n < V.size → ρ.val (V.getD n zeroE) = Wo.slot (sV + n) + β * mv n) :
    ρ.val s'.As = ∑ Y ∈ range (2 ^ lam), eqR ρ c.rs 0 lam Y *
          vecOf (aG ρ Wo p.v.y om hh) (placePanels pans.bl).1.toList Y +
        β * AsAt ρ Wo p.v.y c.rs lam om m1 mv mA (placePanels pans.bl).1.toList ∧
      ρ.val s'.Bs = ∑ Y ∈ range (2 ^ lam), eqR ρ c.rs 0 lam Y *
          vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans.bl).1.toList Y +
        β * BsAt ρ Wo p.v.y c.rs lam om m1 mv mB (placePanels pans.bl).1.toList :=
  stack_masked hp hlam hrs
    (endsTrue_of_claims ρ p c hv TS hp hc hl hd hfe M
      (vv := fun n => Wo.slot (sV + n)) hVal (h1 := fun k => Wo.slot (sH1 + k)) hH)
    h cA cB hH1 hVs eA eB e1 eV

/-! ## The hypothesis on the end values can be met -/

/-- The end values that are what the claims say of W: for each claim number of the list the sum that
the claim speaks of; 0 where the list has no claim. -/
def vvOf (lay : WsLay) (W : Wm K) (cl : List WsClaim) (a : ℕ) : K :=
  match cl[a]? with
  | none => 0
  | some x => claimVal ρ lay W x

/-- These end values meet the hypothesis hV of ends_of_claims and endsTrue_of_claims, for every
matrix W, by their definition. This says nothing on whether the hidden values of a proof that the
verifier accepts are these. -/
theorem vvOf_spec (lay : WsLay) (W : Wm K) (cl : List WsClaim) :
    ∀ a x, cl[a]? = some x → vvOf ρ lay W cl a = claimVal ρ lay W x := by
  intro a x h
  unfold vvOf
  rw [h]

#print axioms facRs_le
#print axioms row_two
#print axioms row_last
#print axioms all_three
#print axioms unit_found
#print axioms groups_found
#print axioms claim_row_two
#print axioms claim_row_last
#print axioms claim_all_three
#print axioms ends_of_claims
#print axioms endsTrue_of_claims
#print axioms claim_zero_two
#print axioms claim_zero_D
#print axioms vvOf_spec
#print axioms wvClaim_congr
#print axioms wvOf_rs
#print axioms stack_claims

end OnBytes.Road
