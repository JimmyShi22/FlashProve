-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LayTablesInScope.lean (kind K9): AT EACH OF THE TWELVE LAYERS' SEGMENTS
THE LIBRARY's LAYING OF THE TABLES, `Layer.layTables` (OnBytes/Model/LayerForms.lean), RETURNS AT
THE PLAN's OWN LIST OF MATRICES, AND WHAT IT LAYS IS NOT EMPTY. In the goals' scope. So the test
`posPlanB` (K9PosAsk.lean) says yes at all 25 segments. Statements and proofs.

Why. `posPlan_layers` (PosPlanBuilt.lean) speaks over the skeleton
`layShapes`, which is the empty list where layTables refuses: there the sentence would be idle; that
  layTables returns at the plan's own matrices was proved nowhere. The nearest law,
  `Meaning.P34.hl_in_scope` (Johnson/Goal/Meaning/HlScope.lean), has it at SOME list of matrices,
    one made for the purpose.

How. layTables refuses a family without an entry and nothing else. A family whose parts all have m
rows and k columns takes parts · (k · (m / L)) entries (`layParts_eq`,
Johnson/Road/FormsKeysTab.lean).
  `FamPos mats a`: the family has an entry: a part; a column; 0 < L ≤ m.
  `layTables_of_pos`: **where every family is such, layTables returns**; it lays every family, each
    with a part.
  `SizesPos y`: what that asks of a layout's sizes. `famPos_of`, `famPos_b`, `asks_pos`: **under it
    every family of tableAsks y rd g is such at matsR y g**, the plan's own list (`tails_pair`, the
    same file; `tailsOf_b`, OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean). The walk over
    tableAsks' nine lists is after `Meaning.P34.asks_good`.
  `sizesPos_in_scope`: **SizesPos X.y in scope.** The rows: from the layout's own tests (`Laid2`,
    Johnson/Road/FormsKeysAddr.lean): general. The numbers of parts and the columns of the six
    matrices are closed numbers at the hand-written shape hKF: SIX FACTS BY LEAN's KERNEL: one on
    the parts, four on the columns of af, ad, ar, qa, one on the columns of the two matrices of the
    stream. The columns of the matrix b: the number of calls times a power of two (`layout_kbm`);
    eight calls (`look_eight`, Johnson/Goal/Meaning/LookScope.lean).
  `layTables_in_scope`: **MAIN: g < 12 ⊢ layTables returns at the very term that Layer.hearOwn,
    layShapes and layTriples read.**
  `layTriples_in_scope`: the segment's tables are there, and the list is not empty.
  `posAsked_lay`, `posAsked_whole`: **the twelve clauses of `PosAsked Z` at the layers' segments in
    the test's own form (over `posTables_lay`, K9PosLayPaid.lean); so, with `posAsked_att` and
    `posAsked_head`, all 25.**
  `layShapes_ne`: **the skeleton of posPlan_layers is not empty.** `posAsked_open`,
    `posAsked_of_head`: PosAsked at an opening's letters; from the head (which holds the scope and
      the reading of the files).
Limits. No law spends these. NOT SAID: that the tables tile the array;
anything on the entries' values. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.PosPlanBuilt
import Johnson.Goal.Meaning.HlScope
import Johnson.Goal.Meaning.LookScope
import Johnson.Goal.Meaning.Pub34All
import Johnson.Road.FormsKeysTab
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Reads TableAsk TableAt layParts layTables tableAsks matIx tailsOf)

/-- A family with an entry: its parts all have m rows and k columns; it has a part; k is not 0; one
entry sums over at least one and at most m rows. -/
def FamPos (mats : Array (ℕ × ℕ)) (a : TableAsk) : Prop :=
  ∃ m k, (∀ p, p < a.parts → mats.getD (a.M0 + p) (0, 0) = (m, k)) ∧ 1 ≤ a.parts ∧ 0 < k ∧
    0 < a.L ∧ a.L ≤ m

/-- **Where every family has an entry the laying returns**; it lays every family, each with a
part. -/
theorem layTables_of_pos {mats : Array (ℕ × ℕ)} : ∀ (asks : List TableAsk),
    (∀ a ∈ asks, FamPos mats a) → ∀ p, ∃ r, layTables mats asks p = some r ∧
      r.2.1.length = asks.length ∧ ∀ x ∈ r.2.1, x.2 ≠ []
  | [], _, p => ⟨_, rfl, rfl, fun _ hx => nomatch hx⟩
  | a :: rest, H, p => by
    obtain ⟨m, k, hm, h1, hk, hL, hLm⟩ := H a List.mem_cons_self
    have e := layParts_eq mats a m k hm p
    have hq : 0 < m / a.L := Nat.div_pos hLm hL
    have hpos : 0 < a.parts * (k * (m / a.L)) := Nat.mul_pos h1 (Nat.mul_pos hk hq)
    have hne : ((layParts mats a a.parts p).2 == p) = false := by
      rw [e, beq_eq_false_iff_ne]
      show p + a.parts * (k * (m / a.L)) ≠ p
      omega
    obtain ⟨r, hr, hl, hx⟩ := layTables_of_pos rest
      (fun b hb => H b (List.mem_cons_of_mem _ hb)) (layParts mats a a.parts p).2
    rw [layTables]
    simp only [hne, Bool.false_eq_true, if_false, hr, Option.map_some]
    refine ⟨_, rfl, by simp [hl], fun x hx' => ?_⟩
    rcases List.mem_cons.1 hx' with rfl | h'
    · show (layParts mats a a.parts p).1 ≠ []
      rw [e]
      intro h0
      have := congrArg List.length h0
      simp at this
      omega
    · exact hx x h'

/-- What is asked of a layout's sizes: each of the seven matrices has a column; a long table's run
and a short table's run fit the rows of the matrices on which they are asked. -/
structure SizesPos (y : Lay) : Prop where
  p0 : 1 ≤ y.parts.getD 0 0
  p1 : 1 ≤ y.parts.getD 1 0
  T0 : 0 < y.T
  cols : ∀ mat, mat ≤ 5 → 0 < colsM y mat
  kbm : 0 < y.kbm
  long : ∀ mat ∈ [0, 3, 4, 5], 2 ^ y.h.la ≤ rowsM y mat
  short : ∀ mat ∈ [1, 2, 3], y.T ≤ rowsM y mat

/-- A family on the matrix with the kit's number mat. -/
theorem famPos_of {y : Lay} {g : ℕ} (hg : g < y.NGr) (a : TableAsk) {mat : ℕ} (hmat : mat ≤ 5)
    (hM : a.M0 = firstM y mat) (hP : a.parts = partsM y mat) (h1 : 1 ≤ a.parts)
    (hk : 0 < colsM y mat) (hL : 0 < a.L) (hLm : a.L ≤ rowsM y mat) : FamPos (matsR y g) a :=
  ⟨rowsM y mat, colsM y mat, fun p hp => by
    rw [hM]
    exact tails_pair y hg hmat (hP ▸ hp), h1, hk, hL, hLm⟩

/-- A family on the matrix b. -/
theorem famPos_b {y : Lay} {g : ℕ} (hg : g < y.NGr) (hk : 0 < y.kbm) (nm : String) :
    FamPos (matsR y g) ⟨nm, (matIx y).iB, 1, 2 ^ y.h.lmb, "", false⟩ := by
  obtain ⟨b1, b2⟩ := _root_.Fo.PlaneMatG.tailsOf_b y g hg
  refine ⟨2 ^ y.h.lmb, y.kbm, fun p hp => ?_, Nat.le_refl 1, hk, Nat.two_pow_pos _, Nat.le_refl _⟩
  obtain rfl : p = 0 := by
    have : p < 1 := hp
    omega
  have hi : (matIx y).iB < ((tailsOf y).getD g {}).mats.size := by
    rw [(tails_sizes y hg).1]
    show y.parts.getD 0 0 + y.parts.getD 1 0 + 1 < _
    omega
  show (matsR y g).getD ((matIx y).iB + 0) (0, 0) = _
  unfold matsR
  rw [Nat.add_zero, getD_map_sizes _ hi, b1, b2]

/-- **Every family of a group's reads has an entry, at the plan's own list of matrices.** -/
theorem asks_pos {y : Lay} (rd : Reads) {g : ℕ} (hg : g < y.NGr) (H : SizesPos y) :
    ∀ a ∈ tableAsks y rd g, FamPos (matsR y g) a := by
  have pa : 0 < 2 ^ y.h.la := Nat.two_pow_pos _
  intro a ha
  unfold tableAsks at ha
  simp only [List.mem_append] at ha
  rcases ha with (((((((ha | ha) | ha) | ha) | ha) | ha) | ha) | ha) | ha
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact famPos_of hg _ (mat := 0) (by decide) rfl rfl H.p0 (H.cols 0 (by decide)) pa
      (H.long 0 (by simp))
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact famPos_of hg _ (mat := 3) (by decide) rfl rfl (Nat.le_refl 1) (H.cols 3 (by decide)) pa
      (H.long 3 (by simp))
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact famPos_of hg _ (mat := 4) (by decide) rfl rfl (Nat.le_refl 1) (H.cols 4 (by decide)) pa
      (H.long 4 (by simp))
  · split at ha
    · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
      exact famPos_of hg _ (mat := 4) (by decide) rfl rfl (Nat.le_refl 1) (H.cols 4 (by decide))
        pa (H.long 4 (by simp))
    · cases ha
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact famPos_of hg _ (mat := 5) (by decide) rfl rfl (Nat.le_refl 1) (H.cols 5 (by decide)) pa
      (H.long 5 (by simp))
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact famPos_of hg _ (mat := 1) (by decide) rfl rfl H.p1 (H.cols 1 (by decide)) H.T0
      (H.short 1 (by simp))
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact famPos_of hg _ (mat := 2) (by decide) rfl rfl (Nat.le_refl 1) (H.cols 2 (by decide))
      H.T0 (H.short 2 (by simp))
  · split at ha
    · obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
      exact famPos_of hg _ (mat := 3) (by decide) rfl rfl (Nat.le_refl 1) (H.cols 3 (by decide))
        H.T0 (H.short 3 (by simp))
    · cases ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact famPos_b hg H.kbm _
    · exact famPos_b hg H.kbm _
    · exact famPos_b hg H.kbm _

section
open OnBytes.Model.Verify (publicOf Public)
open Meaning.P34

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- **THE SIZES, in the goals' scope.** -/
theorem sizesPos_in_scope (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : SizesPos X.y := by
  have B := Hd.public_of_core h (Hd.core_of_scope hS hR h)
  have L2 := laid2_of_layout B.lay
  have hh := (shape_of_public h).trans (shape_in_scope hS hR h)
  have hp : X.y.parts = #[3, 1, 1, 1] := by
    rw [L2.parts, hh]
    show ((sizesOf hKF).map (·.2.2.2.2)).toArray = #[3, 1, 1, 1]
    decide +kernel
  have two : 0 < 2 := by decide
  have hk : ∀ i, i < 4 → 0 < X.y.kcol.getD i 0 := by
    intro i hi
    rw [L2.kcol, hh]
    show 0 < (((sizesOf hKF).map (·.2.2.1)).toArray).getD i 0
    interval_cases i <;> decide +kernel
  have hx : 0 < X.y.kxb := by
    rw [L2.kxb, hh]
    show 0 < roundUp (hKF.xl * hKF.d) (2 ^ hKF.lmx / 2 ^ hKF.lt) / (2 ^ hKF.lmx / 2 ^ hKF.lt)
    decide +kernel
  refine ⟨by rw [hp]; decide, by rw [hp]; decide, by rw [L2.T]; exact Nat.two_pow_pos _, ?_, ?_,
    ?_, ?_⟩
  · intro mat hmat
    interval_cases mat
    · exact hk 0 (by decide)
    · exact hk 1 (by decide)
    · exact hk 2 (by decide)
    · exact hk 3 (by decide)
    · exact hx
    · exact hx
  · rw [_root_.Fo.PlaneMatG.layout_kbm B.lay]
    unfold _root_.Fo.planeCols
    rw [look_eight hS hR h]
    exact Nat.mul_pos (by decide) (Nat.two_pow_pos _)
  · intro mat hm
    obtain ⟨lm, h1, h2⟩ := rows_of_laid2 L2 mat hm
    rw [h2]
    exact Nat.pow_le_pow_right two h1
  · intro mat hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rw [L2.T]
    rcases hm with rfl | rfl | rfl
    · show 2 ^ X.y.h.lt ≤ X.y.mrow.getD 1 0
      rw [L2.mrow1]
      exact Nat.pow_le_pow_right two L2.lt_ad
    · show 2 ^ X.y.h.lt ≤ X.y.mrow.getD 2 0
      rw [L2.mrow2]
      exact Nat.pow_le_pow_right two L2.lt_ar
    · show 2 ^ X.y.h.lt ≤ X.y.mrow.getD 3 0
      rw [L2.mrow3]
      exact Nat.pow_le_pow_right two L2.lt_q

/-- **THE LAYING RETURNS AT THE PLAN's OWN MATRICES, in the goals' scope**; it lays every family,
each with a part. -/
theorem layTables_in_scope (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    ∃ r, layTables ((X.layers.tails.getD g {}).mats.map fun M => (M.m, M.k))
        (tableAsks X.layers.y X.layers.rd g) 0 = some r ∧
      r.2.1.length = (tableAsks X.layers.y X.layers.rd g).length ∧ ∀ x ∈ r.2.1, x.2 ≠ [] := by
  have ey : X.layers.y = X.y := (pub_more (more_of_public h).2.2.2.1).1
  have hN : X.y.NGr = 12 := (pub34_all hS hR h gl_numerals).2.1
  rw [mats_of_public h g, ey]
  exact layTables_of_pos _ (asks_pos X.layers.rd (by rw [hN]; exact hg)
    (sizesPos_in_scope hS hR h)) 0

/-- The list of a group's families is not empty: it ends in the three on the matrix b. -/
theorem asks_ne (y : Lay) (rd : Reads) (g : ℕ) : tableAsks y rd g ≠ [] := by
  unfold tableAsks
  simp

/-- **THE SEGMENT's TABLES ARE THERE, AND THE LIST IS NOT EMPTY.** -/
theorem layTriples_in_scope (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    ∃ ts, layTriples X.layers g = some ts ∧ ts.isEmpty = false := by
  obtain ⟨r, hr, hl, hx⟩ := layTables_in_scope hS hR h hg
  unfold layTriples
  rw [hr]
  refine ⟨_, rfl, ?_⟩
  cases hq : r.2.1 with
  | nil =>
    rw [hq] at hl
    exact absurd (List.length_eq_zero_iff.1 hl.symm) (asks_ne _ _ _)
  | cons a rest =>
    have ha := hx a (by rw [hq]; exact List.mem_cons_self)
    cases hb : a.2 with
    | nil => exact absurd hb ha
    | cons m ms =>
      show (r.2.1.flatMap fun a => a.2.map fun m => (m.1, a.1.L, m.2)).isEmpty = false
      rw [hq, List.flatMap_cons, hb]
      rfl

end

section
variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
  {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}

/-- **The clauses of PosAsked Z at the twelve layers' segments, in the test's own form.** -/
theorem posAsked_lay (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pureRoad.pub o Pb.pol ly Pb.KL = .ok Z)
    (hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X) {g : ℕ} (hg : g < 12) :
    ∃ X, Z.p.built.links[2 * g]? = some X ∧ posPlanB Z.p.X (2 * g) X = true := by
  obtain ⟨X, hX, hall⟩ := posTables_lay hS hR hZ hpub hg
  obtain ⟨ts, hts, hne⟩ := layTriples_in_scope hS hR hpub hg
  refine ⟨X, hX, ?_⟩
  have e : triplesAt Z.p.X (2 * g) = some ts := by
    unfold triplesAt
    rw [if_neg (by omega), if_pos (by omega), Nat.mul_div_cancel_left g (by decide : 0 < 2)]
    exact hts
  unfold posPlanB
  rw [e]
  simp only [hne, hall ts hts, Bool.not_false, Bool.and_self]

/-- **`PosAsked Z` WHOLE: ALL 25 CLAUSES, IN THE TEST's OWN FORM.** -/
theorem posAsked_whole (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pureRoad.pub o Pb.pol ly Pb.KL = .ok Z)
    (hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X) : PosAsked Z := by
  intro l hl
  by_cases h24 : l = 24
  · subst h24
    exact posAsked_head hS hR hZ hpub
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact posAsked_lay hS hR hZ hpub (by omega)
    · exact posAsked_att hS hR hZ hpub (by omega)

end

section
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Closed (layShapes)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE SKELETON OVER WHICH `posPlan_layers` (PosPlanBuilt.lean) SPEAKS IS NOT EMPTY**: so that
sentence is not idle at any of the twelve layers' segments. -/
theorem layShapes_ne (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    layShapes Bs.G₀.W.layers g ≠ [] := by
  obtain ⟨ts, hts, hne⟩ := layTriples_in_scope hS hR (publicOf_open O) hg
  rw [ProofFile.Law.blankBy_W O.blank]
  intro h0
  rw [layTriples_is hts, h0] at hne
  exact nomatch hne

/-- `PosAsked` at an opening's letters. -/
theorem posAsked_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : PosAsked Z :=
  posAsked_whole hS hR O.pub (publicOf_open O)

/-- **FROM THE HEAD**: the head holds the scope and the reading of the files. -/
theorem posAsked_of_head {Zl : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Zl D r Zp Np cF) {F' : FileDescription ProofFile.Inst} {Bs' : ProofFile.PureBase}
    {base' : List (Block S Cl)} {A' : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL F' Zp Bs' base' cF A' B') : PosAsked Zp :=
  posAsked_open h.scope h.reads O

end

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.layTables_of_pos
#print axioms VerifiableInference.Desc.K9Asks.famPos_of
#print axioms VerifiableInference.Desc.K9Asks.famPos_b
#print axioms VerifiableInference.Desc.K9Asks.asks_pos
#print axioms VerifiableInference.Desc.K9Asks.sizesPos_in_scope
#print axioms VerifiableInference.Desc.K9Asks.layTables_in_scope
#print axioms VerifiableInference.Desc.K9Asks.asks_ne
#print axioms VerifiableInference.Desc.K9Asks.layTriples_in_scope
#print axioms VerifiableInference.Desc.K9Asks.posAsked_lay
#print axioms VerifiableInference.Desc.K9Asks.posAsked_whole
#print axioms VerifiableInference.Desc.K9Asks.layShapes_ne
#print axioms VerifiableInference.Desc.K9Asks.posAsked_open
#print axioms VerifiableInference.Desc.K9Asks.posAsked_of_head
