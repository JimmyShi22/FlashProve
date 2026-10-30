-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ArraysAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's
OWN BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING, IN THE GOALS' SCOPE, THE OPEN LEDGER's ARRAYS OF
THE DIGITS (ZZ), OF THE BITS (BZ) AND OF EACH MATRIX's SYMBOLS HAVE THE KIND, THE ROWS, THE COLUMNS
AND THE NUMBER OF VIRTUAL ROWS THAT THE STATE's OWN DATA NAME. Of the seventeen sentences of
`AllFront` (Johnson/Desc/K8/Honest/LeftAtLink.lean) it shows two whole there (bits · syms) and three
of the four fields of a third (digits). Definitions and lemmas; none of the library's goals.

  `ArraysLook tl F`   the three sentences, in the library's "look" of an array (kind, rows,
                   columns, number of virtual rows: Johnson/Desc/First/Batch/Law/Look.lean); the
                   third at each matrix whose shape has a row of cells
  `look_trimL`, `name_trimL`   freeing the weights (Fork.trimL) leaves an array's look and name
  **`arraysLook_fromAdd`**   FromAdd tlc Fc (Johnson/Desc/K8/Honest/FromAddTrees.lean) ⊢ ArraysLook
                   tlc Fc, and the digits' array has the name "ZZ"
  `arraysLook_built`   so at each of the 25 built segments
  `arraysView`, `planned_arrays`, `arraysLook_congr`   the eight fields of the data that the
                   sentences read; they are planned fields; the sentences hang on them and on the
                   looks alone
  **`arraysLook_at_batch`**   at the state's own data and ledger
  `shape_pos`   sizesB tl = true (Johnson/P1K8R/MadeAtPlans.lean) ⊢ every shape has a row of cells
  `fronts_of_look`   ArraysLook tl F · every shape has a row of cells ⊢ the sentences on the front
  **`fronts_at_batch`**   so there: BitsFront tl G · SymbolArrays tl G · of DigitsFront tl G the
                   rows, the columns and the number of virtual rows
By: `addTreesF_atB` (Johnson/Desc/Kinds/Law/AddTreesLooks.lean) · `addTreesF_zzTree`
(Johnson/P1K8R/ZzRowsAtPlans.lean) · `addTreesF_syms` (Johnson/Desc/K8/Honest/SymbolsMade.lean) ·
`addTreesF_sameP` (OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean) · `built_fromAdd` · `looks_at_batch`
(Johnson/P1K8R/StaticAtBatch.lean) · LinkJoin.planned_at_batch
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean) · `sizes_at_batch`
(Johnson/P1K8R/TiesAtBatch.lean).
Limits. IN SCOPE ALONE: the full size's 25 segments; under an opening of the description; the first
chain; the family of states from the description's own first state. Nothing says that any state is
reached. THE NAME "ZZ" IS SHOWN AT THE BUILT SEGMENT's PLANNED LEDGER ALONE: a look holds no name,
so `DigitsFront`'s first field is not shown of a state. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.LeftAtLink
import Johnson.Desc.K8.Honest.FromAddTrees
import Johnson.Desc.K8.Honest.SymbolsMade
import Johnson.Desc.Kinds.Law.AddTreesLooks
import Johnson.P1K8R.ZzRowsAtPlans
import Johnson.P1K8R.StaticAtBatch
import Johnson.P1K8R.TiesAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The looks of the digits', the bits' and the symbols' arrays, by the data's own numbers. -/
structure ArraysLook (tl : HTailF2) (F : Fork) : Prop where
  zz : LinkJoin.look (F.trees.getD tl.ix.ZZ {}) =
    (HKind.table, tl.tau, 2 * tl.mz, 2 * tl.zzBlocks + 2)
  bz : LinkJoin.look (F.trees.getD tl.ix.BZ {}) = (HKind.table, 32, tl.bzColumns, 3)
  sym : ∀ mu, mu < tl.NM → 0 < (tl.shp.getD mu {}).m →
    LinkJoin.look (F.trees.getD (tl.gtTree.getD mu 0) {}) =
      (HKind.symbols, (tl.shp.getD mu {}).Rr, (tl.shp.getD mu {}).Kc, 1)

/-- Freeing the weights leaves an array's look. -/
theorem look_trimL (F : Fork) (t : Nat) :
    LinkJoin.look (F.trimL.trees.getD t {}) = LinkJoin.look (F.trees.getD t {}) := by
  unfold Fork.trimL
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases F.trees[t]? with
  | none => rfl
  | some X => simp [LinkJoin.look]

/-- And its name. -/
theorem name_trimL (F : Fork) (t : Nat) :
    (F.trimL.trees.getD t {}).name = (F.trees.getD t {}).name := by
  unfold Fork.trimL
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases F.trees[t]? with
  | none => rfl
  | some X => rfl

/-- **At whatever one call of addTreesF has laid.** -/
theorem arraysLook_fromAdd {tlc : HTailF2} {Fc : Fork} (M : FromAdd tlc Fc) :
    ArraysLook tlc Fc ∧ (Fc.trees.getD tlc.ix.ZZ {}).name = "ZZ" := by
  obtain ⟨tl, tl', F, G, T, T', nU, aTX, hb, hbLine, ha, hr, hF⟩ := M
  have P := _root_.Fo.ZPlan.addTreesF_sameP ha
  have cI : tlc.ix = tl'.ix := congrArg (·.ix) hr
  have cT : tlc.tau = tl'.tau := congrArg (·.tau) hr
  have cZ : tlc.mz = tl'.mz := congrArg (·.mz) hr
  have cB : tlc.blocks = tl'.blocks := congrArg (·.blocks) hr
  have cF : tlc.f9 = tl'.f9 := congrArg (·.f9) hr
  have cN : tlc.NM = tl'.NM := congrArg (·.NM) hr
  have cG : tlc.gtTree = tl'.gtTree := congrArg (·.gtTree) hr
  have cS : tlc.shp = tl'.shp := congrArg (·.shp) hr
  have lk : ∀ t, LinkJoin.look (Fc.trees.getD t {}) = LinkJoin.look (G.trees.getD t {}) := by
    intro t
    rcases hF with rfl | rfl
    · rfl
    · exact look_trimL G t
  have nm : ∀ t, (Fc.trees.getD t {}).name = (G.trees.getD t {}).name := by
    intro t
    rcases hF with rfl | rfl
    · rfl
    · exact name_trimL G t
  have tZ := _root_.P1K8.addTreesF_zzTree ha
  obtain ⟨X, hX, -, b1, b2, b3, b4⟩ := Kinds.Head.Law.Plan.addTreesF_atB ha
  have tB : G.trees.getD tl.ix.BZ {} = X := by
    rw [Array.getD_eq_getD_getElem?, hX]
    rfl
  refine ⟨⟨?_, ?_, fun mu hmu hpos => ?_⟩, ?_⟩
  · rw [lk, cI, P.same.ix, tZ, cT, P.tau, cZ, P.mz]
    unfold HTailF2.zzBlocks
    rw [cB, P.same.blocks]
    simp [LinkJoin.look]
  · rw [lk, cI, P.same.ix, tB]
    unfold HTailF2.bzColumns
    rw [cF, P.f9]
    unfold HTailF2.bzColumns at b3
    unfold LinkJoin.look
    rw [b1, b2, b3, b4]
  · rw [lk, cG, cS]
    exact (addTreesF_syms ha).1 mu (by rw [← cN]; exact hmu) (by rw [← cS]; exact hpos)
  · rw [nm, cI, P.same.ix, tZ]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At each of the 25 built segments. -/
theorem arraysLook_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    ArraysLook Xl.tl Xl.Fp ∧ (Xl.Fp.trees.getD Xl.tl.ix.ZZ {}).name = "ZZ" :=
  arraysLook_fromAdd (built_fromAdd hS hR O hl e3)

end

/-- The eight fields of the data that the three sentences read. -/
def arraysView (tl : HTailF2) :=
  (tl.ix, tl.NM, tl.gtTree, tl.tau, tl.mz, tl.blocks, tl.f9, tl.shp)

/-- They are planned fields. -/
theorem planned_arrays : LinkJoin.Planned arraysView :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- The sentences hang on the eight fields and the looks alone. -/
theorem arraysLook_congr {a b : HTailF2} {F F' : Fork} (hv : arraysView a = arraysView b)
    (hl : F.trees.map LinkJoin.look = F'.trees.map LinkJoin.look) (H : ArraysLook b F') :
    ArraysLook a F := by
  simp only [arraysView, Prod.mk.injEq] at hv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  refine ⟨?_, ?_, fun mu hmu hpos => ?_⟩
  · rw [look_at hl, h1, h4, h5]
    unfold HTailF2.zzBlocks
    rw [h6]
    exact H.zz
  · rw [look_at hl, h1]
    unfold HTailF2.bzColumns
    rw [h7]
    exact H.bz
  · rw [look_at hl, h3, h8]
    exact H.sym mu (by rw [← h2]; exact hmu) (by rw [← h8]; exact hpos)

/-- Every shape has a row of cells. -/
theorem shape_pos {tl : HTailF2} (h : _root_.P1K8.sizesB tl = true) :
    ∀ mu, mu < tl.NM → 0 < (tl.shp.getD mu {}).m := by
  intro mu hmu
  unfold _root_.P1K8.sizesB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨e1, -⟩, e2⟩ := h.1 mu hmu
  rw [e1]
  exact e2

/-- From the looks to the sentences on the front. -/
theorem fronts_of_look {tl : HTailF2} {F : Fork} (H : ArraysLook tl F)
    (hp : ∀ mu, mu < tl.NM → 0 < (tl.shp.getD mu {}).m) :
    BitsFront tl F ∧ SymbolArrays tl F ∧ (F.trees.getD tl.ix.ZZ {}).R = tl.tau ∧
      (F.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz ∧
      (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2 :=
  ⟨⟨congrArg (·.2.2.2) H.bz, congrArg (·.2.1) H.bz, congrArg (·.2.2.1) H.bz⟩,
    ⟨fun mu hmu => congrArg (·.1) (H.sym mu hmu (hp mu hmu)),
      fun mu hmu => congrArg (·.2.2.2) (H.sym mu hmu (hp mu hmu)),
      fun mu hmu => congrArg (·.2.1) (H.sym mu hmu (hp mu hmu)),
      fun mu hmu => congrArg (·.2.2.1) (H.sym mu hmu (hp mu hmu))⟩,
    congrArg (·.2.1) H.zz, congrArg (·.2.2.1) H.zz, congrArg (·.2.2.2) H.zz⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the state's own data and ledger.** -/
theorem arraysLook_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    ArraysLook tl G := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have g := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_arrays hS hR O hx e3 (z, s) h') tl ht
  exact arraysLook_congr g
    (LinkJoin.looks_array (_root_.P1K8.looks_at_batch hS hR O hl e3 h hG))
    (arraysLook_built hS hR O hl e3).1

/-- **So the sentences on the front hold there.** -/
theorem fronts_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    BitsFront tl G ∧ SymbolArrays tl G ∧ (G.trees.getD tl.ix.ZZ {}).R = tl.tau ∧
      (G.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz ∧
      (G.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2 := by
  obtain ⟨tl₂, ht₂, hz⟩ := _root_.P1K8.sizes_at_batch hS hR O hl h
  obtain rfl : tl₂ = tl := Option.some.inj (ht₂.symm.trans ht)
  exact fronts_of_look (arraysLook_at_batch hS hR O hl e3 h ht hG) (shape_pos hz)

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.look_trimL
#print axioms VerifiableInference.Desc.First.K8.Honest.name_trimL
#print axioms VerifiableInference.Desc.First.K8.Honest.arraysLook_fromAdd
#print axioms VerifiableInference.Desc.First.K8.Honest.arraysLook_built
#print axioms VerifiableInference.Desc.First.K8.Honest.planned_arrays
#print axioms VerifiableInference.Desc.First.K8.Honest.arraysLook_congr
#print axioms VerifiableInference.Desc.First.K8.Honest.shape_pos
#print axioms VerifiableInference.Desc.First.K8.Honest.fronts_of_look
#print axioms VerifiableInference.Desc.First.K8.Honest.arraysLook_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.fronts_at_batch
