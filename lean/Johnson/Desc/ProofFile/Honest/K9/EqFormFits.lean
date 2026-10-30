-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqFormFits.lean: THE ONE CLAUSE OF THE TESTS ON SIZES AT "THE ONE EQUATION" THAT THE SHAPE OF THE
STATE DOES NOT HOLD: "each product form of a virtual row is well formed" (`rowFormFits`, Johnson/Desc/First/Batch/Lay.lean;
the test "K9.row-form"; gathered as `fitsB`, Honest/K9/EqSizes.lean): IT ACCEPTS AT THE LEDGER THAT THE STEP "BEHIND THE
BATCHING" LEAVES, from a yes of that step, one premise on the ledger in front of it, and one Bool on the shape behind it.

Why it holds. The forms are laid by the verifier itself, in the run "K8.tests" of that step, by three makes (1 on every row;
the powers of an element; the equality polynomial's table on an aligned block of rows: `coefBody`,
Johnson/Desc/First/TailClaims/Coefficients.lean). Behind the laying the same run asks its "test by a second computation", whose
yes says the numbers that the forms' sizes hang on. The walk over the writes is that of the library's
Johnson/AtFull/Shape/RowFormLedger.lean (`forms_coefAll`), which shows the forms' VALUES; here, with the same tools
(`EachRow`, `eachRow_onRow`, `eachRow_foldl`), their SIZES. No fact on a value is spent: of that file's fourteen letters eight.

  `fitsBut R r`, `fits_of_but`    `rowFormFits` without its clause "the first row is one of the array's", which reads what the
                               shape holds; the two together give the test
  `but_ones`, `but_point`, `but_powers`   the three makes
  `SizeLetters`, `sizeLetters_of_tested`   the eight letters; a yes of the test by a second computation gives them (after the
                               library's `coefLetters_of_tested`, Johnson/AtFull/Shape/RowFormTested.lean)
  **`sizes_coefAll`**           at the letters, from a fresh ledger (`NoForm`, Honest/K9/EqBack.lean): behind the step every virtual row
                               that has a form meets `fitsBut`
  `sizes_of_testsP`            so behind a yes of the three tests in a row (`testsP`)
  `behind_testsP`              at each l < 25, in the goals' scope: a yes of the step behind the batching is, at the ledger, a yes of
                               `testsP` (after the library's `termsV_at_link`, `termsV_scope`, Johnson/AtFull/Shape/RowFormSeat.lean)
  `firstsS`, `oneFirsts`        the clause that was taken out, as a Bool on the chain's shape
  **`fitsB_behind`**            under `AtMgA`: Lk.runBehind s₁ = .ok s, the ledger at s₁ is fresh, `oneFirsts (chainSh s) = true` ⊢
                               `fitsB L F = true` at the link L and the ledger F that are open at s

Limits. Implications from a yes of the step. That a ledger behind an adding is fresh is not proved here (Honest/K9/EqBack.lean's
`noForm_behind` carries it back over the batching). That `oneFirsts` accepts at any shape is not proved here. The hash function
`secondHashFunction` alone. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqBack
import Johnson.Desc.ProofFile.Honest.K9.EqSizes
import Johnson.AtFull.Shape.RowFormSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (rowAt HasRow Frame coefAll coefTables coefPieces coefPowers coefBZ coefMats allPieces pieceF)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim claimsInBy afterIn)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh LinkSh linkSh LedSh ledSh rowSh)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open VerifiableInference.Desc.K9 (rowFormFits)
open Johnson.AtFull.Shape (EachRow eachRow_onRow eachRow_foldl NoLists piecePoint piece_letters_tested squaresW_size
  LeavesLedger)
open ProofFile (Cl)
open IM
open TocK8 (K8At afterIn_of_behind k08_scope ixOf preOf postOf midOf)

/-! ## 1 The test, cut in two -/

/-- `rowFormFits` without its clause "the first row is one of the array's". R: the array's number of rows. -/
def fitsBut (R : ℕ) (r : HRow) : Bool :=
  decide (r.rowPoint.size ≤ clog2 R) &&
    !((r.rowOnes || (!r.rowLo.isEmpty || !r.rowHi.isEmpty)) && (r.rowPoint.size != 0 || r.rowFirst != 0)) &&
    r.rowFirst % 2 ^ r.rowPoint.size == 0 &&
    !((!r.rowLo.isEmpty || !r.rowHi.isEmpty) &&
      (r.rowOnes || r.rowLo.size != clog2 R || r.rowHi.size != clog2 R))

theorem fits_of_but (X : HTree) (r : HRow) (h : fitsBut X.R r = true) (hf : r.rowFirst < X.R) :
    rowFormFits X r = true := by
  unfold fitsBut at h
  unfold rowFormFits
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2⟩, decide_eq_true hf⟩, h.2⟩

/-! ## 2 The three makes -/

theorem but_ones (row : HRow) (c : Array E) (h : NoLists row) (R : ℕ) :
    fitsBut R (formOnes { row with coef := c }) = true := by
  unfold fitsBut formOnes
  simp [h.1, h.2]

theorem but_point (row : HRow) (c z : Array E) (first R : ℕ) (h : NoLists row) (hz : z.size ≤ clog2 R)
    (ha : first % 2 ^ z.size = 0) : fitsBut R (formPoint { row with coef := c } z first) = true := by
  unfold fitsBut formPoint
  simp [h.1, h.2, hz, ha]

theorem but_powers (row : HRow) (c : Array E) (b : E) (n : ℕ) :
    fitsBut n (formPowers { row with coef := c } b n) = true := by
  unfold fitsBut formPowers
  simp [squaresW_size]

/-! ## 3 The letters -/

/-- The eight letters on which the forms' sizes hang. F: the ledger in front. -/
structure SizeLetters (tl : HTailF2) (g : Forest.Heard) (F : Fork) : Prop where
  pieceFits : ∀ a ∈ allPieces tl, (piecePoint tl g a).size ≤ clog2 (F.trees.getD a.2.tree {}).R
  pieceAligned : ∀ a ∈ allPieces tl, a.2.r0 % 2 ^ (piecePoint tl g a).size = 0
  digits : (F.trees.getD tl.ix.ZZ {}).R = tl.tau
  planes : (F.trees.getD tl.ix.BZ {}).R = 32
  point0 : 5 ≤ (g.zb 0).size
  point1 : 5 ≤ (g.zb 1).size
  apart : tl.ix.BZ ≠ tl.ix.ZZ
  matRows : ∀ mu, mu < tl.NM → (F.trees.getD (tl.gtTree.getD mu 0) {}).R = (tl.shp.getD mu {}).mS

/-- **A yes of the test by a second computation gives the eight letters.** G: the ledger at which it is asked; F: a ledger
with the same arrays, numbers of rows and of virtual rows. -/
theorem sizeLetters_of_tested {tl : HTailF2} {g : Forest.Heard} {F G : Fork} (hfr : Frame F G)
    (hg : tl.heard = some g) (h : rkSelfTestP tl G = .ok ()) : SizeLetters tl g F := by
  obtain ⟨g', jo, nbW, Wn, hg', -, hw, g1, g2, -, -, g5, -⟩ := rk_all tl G h
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  simp only [Bool.and_eq_true] at g1 g5
  have hcall : ∀ q, q < 2 → tl.callHeld g nbW q = true := fun q hq =>
    List.all_eq_true.1 g1.2 q (by
      have : q = 0 ∨ q = 1 := by omega
      rcases this with rfl | rfl <;> simp)
  have hpc : ∀ a ∈ allPieces tl, a.1 < 2 ∧ a.2 ∈ (tl.zOf a.1).pieces.toList := by
    intro a ha
    unfold allPieces at ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact ⟨by omega, hp⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact ⟨by omega, hp⟩
  have four := fun a (ha : a ∈ allPieces tl) =>
    piece_letters_tested tl g G nbW Wn hw (hpc a ha).1 (hcall _ (hpc a ha).1) g2 (hpc a ha).2
  have g2' := g2
  unfold HTailF2.piecesTile at g2'
  simp only [Bool.and_eq_true] at g2'
  have hZrows : (G.trees.getD tl.ix.ZZ {}).rows.size = 2 * nbW + 2 := beq_iff_eq.1 g1.1.1
  have hZR : (G.trees.getD tl.ix.ZZ {}).R = tl.tau := beq_iff_eq.1 g2'.1.1.1.1.2
  have hp := g5.2
  unfold HTailF2.planesShapeHeld at hp
  simp only [Bool.and_eq_true] at hp
  have hBrows : (G.trees.getD tl.ix.BZ {}).rows.size = 3 := beq_iff_eq.1 hp.1.1.1.1.1.1.1.1
  have hBR : (G.trees.getD tl.ix.BZ {}).R = 32 := beq_iff_eq.1 hp.1.1.1.1.1.1.1.2
  have hz0 := beq_iff_eq.1 hp.1.2
  have hz1 := beq_iff_eq.1 hp.2
  refine
    { pieceFits := fun a ha => by rw [← (hfr.2 _).1]; exact (four a ha).2.1
      pieceAligned := fun a ha => (four a ha).2.2.1
      digits := by rw [← (hfr.2 _).1]; exact hZR
      planes := by rw [← (hfr.2 _).1]; exact hBR
      point0 := by
        show 5 ≤ g.zb0.size
        omega
      point1 := by
        show 5 ≤ g.zb1.size
        omega
      apart := fun he => by
        rw [he] at hBrows
        omega
      matRows := fun mu hmu => ?_ }
  have hm := List.all_eq_true.1 g5.1.1.2 mu (List.mem_range.2 hmu)
  unfold HTailF2.tieShapeHeld at hm
  simp only [Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, c3⟩, -⟩, -⟩, c6⟩, -⟩, -⟩, c9⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩, -⟩, -⟩ := hm
  rw [← (hfr.2 _).1]
  exact (beq_iff_eq.1 c3).trans ((beq_iff_eq.1 c9).trans (beq_iff_eq.1 c6))

/-! ## 4 The walk -/

/-- Where the row has a product form, the form's sizes fit an array of R rows. -/
def FormSizes (R : ℕ) (row : HRow) : Prop := row.rowForm = true → fitsBut R row = true

/-- No lists of factors; and the sizes fit where there is a form. -/
def RowOk (_ : ℕ) (R : ℕ) (row : HRow) : Prop := NoLists row ∧ FormSizes R row

/-- The same, but that the rows of array zz may have lists. -/
def RowOkBut (zz : ℕ) (t : ℕ) (R : ℕ) (row : HRow) : Prop := (t ≠ zz → NoLists row) ∧ FormSizes R row

theorem rowOk_of_noForm (F : Fork) (h : NoForm F) : EachRow RowOk F := fun t e hr =>
  ⟨(h t e hr).2, fun hf => absurd hf (by rw [(h t e hr).1]; exact Bool.false_ne_true)⟩

/-- The first stage: the tables' rows. -/
theorem sizes_tables (tl : HTailF2) (F : Fork) (h0 : EachRow RowOk F) : EachRow RowOk (coefTables tl F) := by
  unfold coefTables
  refine Fo.forIn_inv (fun s => EachRow RowOk s) _ (fun n s hs => ?_) _ _ h0
  dsimp only
  split
  · split
    · exact ⟨_, rfl, eachRow_onRow _ _ _ hs fun row hrow =>
        ⟨⟨hrow.1.1, hrow.1.2⟩, fun _ => but_ones row _ hrow.1 _⟩⟩
    · exact ⟨_, rfl, hs⟩
  · exact ⟨_, rfl, hs⟩

/-- **Behind the step every virtual row that has a product form has a form whose sizes fit.** -/
theorem sizes_coefAll (tl : HTailF2) (g : Forest.Heard) (F : Fork) (hL : SizeLetters tl g F)
    (h0 : EachRow RowOk F) : EachRow (fun _ R row => FormSizes R row) (coefAll tl g F) := by
  -- the tables
  have s1 : Frame F (coefTables tl F) := Fo.frame_tables tl F
  have a1 : EachRow RowOk (coefTables tl F) := sizes_tables tl F h0
  -- the pieces
  have s2 : Frame F (coefPieces tl g (coefTables tl F)) := s1.trans (Fo.frame_pieces tl g _)
  have a2 : EachRow RowOk (coefPieces tl g (coefTables tl F)) := by
    rw [Fo.coefPieces_eq]
    exact eachRow_foldl F (fun a : ℕ × Piece => a.2.tree) (fun a => a.2.row) (pieceF tl g)
      _ _ s1 a1 fun a ha G hG row hrow =>
        ⟨⟨hrow.1.1, hrow.1.2⟩, fun _ => but_point row _ (piecePoint tl g a) a.2.r0 _ hrow.1 (hL.pieceFits a ha)
          (hL.pieceAligned a ha)⟩
  -- the two rows under powers
  have s3 : Frame F (coefPowers tl F.theta (coefPieces tl g (coefTables tl F))) :=
    s2.trans (Fo.frame_powers tl _ _)
  have a3 : EachRow (RowOkBut tl.ix.ZZ)
      (coefPowers tl F.theta (coefPieces tl g (coefTables tl F))) := by
    have b0 : EachRow (RowOkBut tl.ix.ZZ) (coefPieces tl g (coefTables tl F)) :=
      a2.mono fun _ _ _ h => ⟨fun _ => h.1, h.2⟩
    unfold coefPowers
    refine eachRow_onRow _ _ _ (eachRow_onRow _ _ _ b0 fun row _ => ?_) fun row _ => ?_
    · rw [(s2.2 _).1, hL.digits]
      exact ⟨fun hne => absurd rfl hne, fun _ => but_powers row _ _ _⟩
    · rw [((Fo.frame_onRow _ _ _ _).2 _).1, (s2.2 _).1, hL.digits]
      exact ⟨fun hne => absurd rfl hne, fun _ => but_powers row _ _ _⟩
  -- the planes' three rows
  have s4 : Frame F (coefBZ tl g (coefPowers tl F.theta (coefPieces tl g (coefTables tl F)))) :=
    s3.trans (Fo.frame_bz tl g _)
  have z0 : ((g.zb 0).extract 0 5).size = 5 := by
    rw [Array.size_extract]
    have := hL.point0
    omega
  have z1 : ((g.zb 1).extract 0 5).size = 5 := by
    rw [Array.size_extract]
    have := hL.point1
    omega
  have c32 : clog2 32 = 5 := rfl
  have a4 : EachRow (RowOkBut tl.ix.ZZ)
      (coefBZ tl g (coefPowers tl F.theta (coefPieces tl g (coefTables tl F)))) := by
    unfold coefBZ
    refine eachRow_onRow _ _ _ (eachRow_onRow _ _ _ (eachRow_onRow _ _ _ a3 fun row hrow => ?_)
      fun row hrow => ?_) fun row hrow => ?_
    · rw [(s3.2 _).1, hL.planes]
      exact ⟨fun _ => ⟨(hrow.1 hL.apart).1, (hrow.1 hL.apart).2⟩,
        fun _ => but_point row _ _ 0 32 (hrow.1 hL.apart) (by rw [z0, c32]) (Nat.zero_mod _)⟩
    · rw [((Fo.frame_onRow _ _ _ _).2 _).1, (s3.2 _).1, hL.planes]
      exact ⟨fun _ => ⟨(hrow.1 hL.apart).1, (hrow.1 hL.apart).2⟩,
        fun _ => but_point row _ _ 0 32 (hrow.1 hL.apart) (by rw [z1, c32]) (Nat.zero_mod _)⟩
    · rw [((Fo.frame_onRow _ _ _ _).2 _).1, ((Fo.frame_onRow _ _ _ _).2 _).1, (s3.2 _).1,
        hL.planes]
      exact ⟨fun _ => ⟨(hrow.1 hL.apart).1, (hrow.1 hL.apart).2⟩,
        fun _ => but_ones row _ (hrow.1 hL.apart) _⟩
  -- the matrices' rows
  unfold coefAll
  rw [Fo.coefMats_eq]
  exact eachRow_foldl F (fun mu => tl.gtTree.getD mu 0) (fun _ => 0)
    (fun _ mu row => formPowers { row with coef := tl.rowX.getD mu #[] } (powE F.theta tl.stepF)
      (tl.shp.getD mu {}).mS) _ _ s4 (a4.mono fun _ _ _ h => h.2)
    fun mu hmu _ _ row _ => by
      rw [hL.matRows mu (List.mem_range.1 hmu)]
      exact fun _ => but_powers row _ _ _

/-- **Behind a yes of the three tests in a row.** -/
theorem sizes_of_testsP {nU : Array ℕ} {tl : HTailF2} {F Fc : Fork} (h : testsP nU tl F = .ok Fc) (hf : NoForm F) :
    EachRow (fun _ R row => FormSizes R row) Fc := by
  obtain ⟨-, h2, h3⟩ := tests_ok h
  unfold coefficientsP at h2
  split at h2
  · cases h2
  · rename_i g hg
    obtain rfl := Except.ok.inj h2
    exact sizes_coefAll tl g F (sizeLetters_of_tested (G := coefBody tl g F) (Fo.frame_all tl g F) hg h3)
      (rowOk_of_noForm F hf)

/-! ## 5 The step behind the batching, at the ledger -/

/-- At a link with the library's `K8At`: a yes of the step is, at the ledger, a yes of the three tests in a row. -/
theorem behind_testsP_at_link {Lk : Link S Cl} {p : VerifiableInference.Desc.First.K8.ParW} {i : ℕ}
    {pre post mid : List (ℕ × String)} (K : K8At Lk p i pre post mid)
    (hF : ∀ o ∈ mid, LeavesLedger Lk.hear o) (sB sE : S) (h2 : Lk.runBehind sB = .ok sE) :
    ∃ F tl Fc, sB.fork? = some F ∧ testsP p.nU tl F = .ok Fc ∧ sE.fork? = some Fc := by
  have ha := afterIn_of_behind h2
  rw [K.after] at ha
  obtain ⟨rL', s₁, hlL, hrL, ha'⟩ := afterIn_cons ha
  obtain ⟨s₂, -, hkeep, ha''⟩ :=
    afterIn_keeps (fun s : S => (k8Field s, s.fork?)) mid [(i, "K8.tests")] s₁ sE
      (fun o ho run hl e e₁ hr =>
        Prod.ext (K.hmid o ho run hl e e₁ hr) (hF o ho run hl e e₁ hr)) ha'
  obtain ⟨rT', s₃, hlT, hrT, hend⟩ := afterIn_cons ha''
  obtain rfl : s₃ = sE := Except.ok.inj hend
  obtain ⟨rL, mL, uL⟩ := K.hL rL' hlL
  obtain ⟨rT, mT, uT⟩ := K.hT rT' hlT
  obtain ⟨q, hq, rfl⟩ := (sits_lsTail p rL mL sB s₁).1 (uL _ _ hrL)
  obtain ⟨q₂, Fc, hq₂, ht, rfl⟩ := (sits_tests p rT mT s₂ _).1 (uT _ _ hrT)
  obtain ⟨-, b2, -⟩ := partOf_some.1 hq
  obtain ⟨-, c2, -⟩ := partOf_some.1 (part_set hq
    { q with tl := { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } })
  obtain ⟨-, d2, -⟩ := partOf_some.1 hq₂
  obtain ⟨-, k2⟩ := Prod.mk.inj hkeep
  have e2 : q₂.F = q.F := Option.some.inj (d2.symm.trans (k2.trans c2))
  rw [e2] at ht
  obtain ⟨-, g2, -⟩ := partOf_some.1 (part_set hq₂ { q₂ with F := Fc })
  exact ⟨q.F, q₂.tl, Fc, b2, ht, g2⟩

/-- At each of the 25 segments, in the goals' scope, at an opening. -/
theorem behind_testsP {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (Lk : Link S Cl)
    (hLk : c.links[l]? = some Lk) (sB sE : S) (h2 : Lk.runBehind sB = .ok sE) :
    ∃ nU F tl Fc, sB.fork? = some F ∧ testsP nU tl F = .ok Fc ∧ sE.fork? = some Fc := by
  obtain ⟨Lk', Xl, e, -, K, -⟩ := k08_scope hS hR O l hl
  obtain rfl : Lk' = Lk := Option.some.inj (e.symm.trans hLk)
  have hLL : ∀ o ∈ midOf (subAt l), LeavesLedger Lk'.hear o := by
    intro o ho run hlk e₀ e₁ hr
    by_cases h24 : l = 24
    · subst h24
      exact nomatch ho
    · by_cases he : l % 2 = 0
      · have ej : 2 * (l / 2) = l := by omega
        have hs : subAt l = .layers := by
          rw [← ej]
          exact subAt_layers (l / 2) (by omega)
        rw [hs] at ho
        obtain rfl := List.mem_singleton.1 ho
        obtain ⟨L4, b4, x, e4, hb4, -, la4, -⟩ := k4_of hS hR O (l / 2) (by omega)
        rw [ej] at e4
        obtain rfl : Lk' = L4 := Option.some.inj (e.symm.trans e4)
        rw [show ((2, "free-slot") : ℕ × String).1 = 2 from rfl, hb4] at hlk
        obtain ⟨r', hl', -, hy⟩ := after_yes la4 hlk
        exact (freeSlot_field (p := { x.2 with k3Runs := true }) hl' ((hy e₀ e₁).1 hr).1).2
      · have ej : 2 * (l / 2) + 1 = l := by omega
        have hs : subAt l = .attention := by
          rw [← ej]
          exact subAt_attention (l / 2)
        rw [hs] at ho
        exact nomatch ho
  obtain ⟨F₀, tl, Fc, a1, a2, a3⟩ := behind_testsP_at_link K hLL sB sE h2
  exact ⟨_, F₀, tl, Fc, a1, a2, a3⟩

/-! ## 6 The clause that was taken out, on shapes; and the test whole -/

/-- Each product form's first row is one of its array's rows: over the listed arrays, on shapes. -/
def firstsS (L : LinkSh) (F : LedSh) : Bool :=
  (List.range L.list.nt.size).all fun ti =>
    (treeAt F ti).rows.all fun r => !r.form || decide (r.first < (treeAt F ti).R)

/-- The same as a Bool on the chain's shape. Where no link or no ledger is open it says no. -/
def oneFirsts (a : ChainSh) : Bool :=
  match a.link, a.led with
  | some L, some F => firstsS L F
  | _, _ => false

/-- The test whole, from the two halves. -/
theorem fitsB_of (L : LinkCtx) (F : Fork) (h1 : EachRow (fun _ R row => FormSizes R row) F)
    (h2 : firstsS (linkSh L) (ledSh F) = true) : fitsB L F = true := by
  unfold fitsB
  refine List.all_eq_true.2 fun ti hti => ?_
  unfold firstsS at h2
  have f1 := List.all_eq_true.1 h2 ti hti
  beta_reduce at f1
  rw [treeAt_sh] at f1
  refine Array.all_eq_true'.2 fun x hx => ?_
  have f2 : (!x.rowForm || decide (x.rowFirst < (F.trees.getD ti {}).R)) = true :=
    List.all_eq_true.1 f1 (rowSh x) (List.mem_map.2 ⟨x, Array.mem_toList_iff.2 hx, rfl⟩)
  cases hform : x.rowForm with
  | false => rfl
  | true =>
    rw [hform] at f2
    have f3 : x.rowFirst < (F.trees.getD ti {}).R := of_decide_eq_true f2
    obtain ⟨e, he, rfl⟩ := Array.mem_iff_getElem.1 hx
    by_cases ht : ti < F.trees.size
    · have e1 : rowAt F ti e = (F.trees.getD ti {}).rows[e] := by
        unfold rowAt
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he]
        rfl
      have k := h1 ti e ⟨ht, he⟩
      rw [e1] at k
      exact fits_of_but _ _ (k hform) f3
    · exfalso
      have e0 : F.trees.getD ti {} = {} := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt ht)]
        rfl
      rw [e0] at he
      exact Nat.not_lt_zero _ he

/-- **Under the library's hypothesis: the clause accepts behind the step behind the batching.** -/
theorem fitsB_behind {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) (Lk : Link S Cl)
    (hLk : cF.links[l]? = some Lk) (s₁ s : S) (h2 : Lk.runBehind s₁ = .ok s)
    (hfresh : ∀ F, s₁.fork? = some F → NoForm F) (hfirst : oneFirsts (chainSh s) = true) {L : LinkCtx} {F : Fork}
    (hL : s.link? = some L) (hF : s.fork? = some F) : fitsB L F = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨nU, F₀, tl, Fc, a1, a2, a3⟩ := behind_testsP h.scope h.reads O l hl Lk hLk s₁ s h2
  obtain rfl : Fc = F := Option.some.inj (a3.symm.trans hF)
  have l1 : (chainSh s).link = some (linkSh L) := by
    show s.link?.map linkSh = _
    rw [hL]
    rfl
  have l2 : (chainSh s).led = some (ledSh Fc) := by
    show s.fork?.map ledSh = _
    rw [hF]
    rfl
  unfold oneFirsts at hfirst
  rw [l1, l2] at hfirst
  exact fitsB_of L Fc (sizes_of_testsP a2 (hfresh F₀ a1)) hfirst

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.fits_of_but
#print axioms ProofFile.Honest.K9.but_ones
#print axioms ProofFile.Honest.K9.but_point
#print axioms ProofFile.Honest.K9.but_powers
#print axioms ProofFile.Honest.K9.sizeLetters_of_tested
#print axioms ProofFile.Honest.K9.sizes_tables
#print axioms ProofFile.Honest.K9.sizes_coefAll
#print axioms ProofFile.Honest.K9.sizes_of_testsP
#print axioms ProofFile.Honest.K9.behind_testsP_at_link
#print axioms ProofFile.Honest.K9.behind_testsP
#print axioms ProofFile.Honest.K9.fitsB_of
#print axioms ProofFile.Honest.K9.fitsB_behind
