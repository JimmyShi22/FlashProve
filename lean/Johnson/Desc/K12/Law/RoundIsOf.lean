-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKYes
/-
Johnson/Desc/K12/Law/RoundIsOf.lean: FROM A YES OF Block.step ON A REAL VIEW TO A YES OF accK: what the step's own first test gives of RoundIs, and what is left as premises. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p.
  forall₂_of_zip   the test drawsMarkedNonzeroHaveNonzeroWords's zip, the two lengths and «canonical» give DrawnIs' clause on the elements
  roundIs_of_fit   the converse of roundsFit_written (Johnson/Desc/K12/Law/FitWritten.lean): Forall₂ IsOfK ds ws · roundsFit ds rs = true · at every declared round drawNZ ≤ drawE and logN ≤ 64 · every drawn element canonical ⇒ Forall₂ RoundIs ws rs
  step_cols        Block.step reads of its columns the first so many as it wants, and no more
  CanonK rs · LogK ds   the two new premises, as propositions: every element that a round drew has its three words below the field's size (ON THE VIEW) · every declared round's logN is at most 64 (ON THE PLAN)
  accK_yes_view    nzOk · the place's declared and written rounds (FormK's four equations) · LogK · CanonK · A YES OF Block.step AT A VIEW (r0 :: rs', cols) · «THE VIEW's COLUMNS ARE THE TABLES'»: cols.take ‹as many as the step wants› = colsOf … (srcK p c (blOf c τ₀) ts (wAt c W0 ft fM (blOf c τ₀))) ⇒ ∃ τ that shows just the rounds rs' (the sealed digests apart) and holds τ₀'s oracles, accK p F t0 r0 c ts (wAt c W0 ft fM) τ = true, AND THE VIEW's COLUMNS ARE τ's OWN WRITTEN COLUMNS: htab AGAIN, AT τ IN τ₀'s PLACE
ONE ACCEPTING TRANSCRIPT IS NOT «A PROVER THAT IS NOT DOOMED»: see Johnson/Desc/K12/Law/AccKYes.lean's head. WHAT IS LEFT BETWEEN THIS AND «accK SAYS YES AT A REAL PROOF»: the step's yes: has run · nzOk: has run · LogK · CanonK: two Booleans (Johnson/Desc/K12/Law/CanonOk.lean; the first on the plan, the second on the view) · THE PREMISE ON THE COLUMNS: that tables W0 | τ₀ exist of which the view's columns are columns: SHOWN, FOR A CONSTANT fM: Johnson/Desc/K12/Law/TabsView.lean's tables_of_view; the closed form: Johnson/Desc/K12/Law/AccKHas.lean.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Onto (Canon DrawnIs RoundIs orcsOf)
open H2K.Fit (IsOf IsOfK dsElems_length layW_isOf forall₂_map_right roundsFit_cons nz_of_ok)
open H2K.Pub (WR writtenOf)
open H2K.First (nzOk)

theorem forall₂_of_zip : ∀ (l : List Fmt.Draw) (m : List Fmt.Ext), l.length = m.length →
    ((l.zip m).all fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true → (∀ x ∈ m, Canon x) →
    List.Forall₂ (fun d x => Canon x ∧ (d = Fmt.Draw.elemNZ → x ≠ ((0, 0, 0) : Fmt.Ext))) l m
  | [], [], _, _, _ => List.Forall₂.nil
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h
  | d :: l, x :: m, hl, hz, hc => by
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hz
    refine List.Forall₂.cons ⟨hc x List.mem_cons_self, fun hd hx => ?_⟩
      (forall₂_of_zip l m (Nat.succ.inj hl) hz.2 fun y hy => hc y (List.mem_cons_of_mem _ hy))
    subst hd
    subst hx
    simp at hz

/-- What the step's first test gives of RoundIs. -/
theorem roundIs_of_fit : ∀ (ds : List Fmt.DeclaredRound) (ws : List PQ.RD) (rs : List Fmt.RoundView),
    List.Forall₂ IsOfK ds ws → roundsFit ds rs = true →
    (∀ d ∈ ds, d.entry.drawNZ ≤ d.entry.drawE ∧ d.entry.logN ≤ 64) →
    (∀ r ∈ rs, ∀ x ∈ r.drawn.elems, Canon x) → List.Forall₂ RoundIs ws rs
  | [], [], [], _, _, _, _ => List.Forall₂.nil
  | [], [], _ :: _, _, h, _, _ => nomatch h
  | _ :: _, _ :: _, [], _, h, _, _ => nomatch h
  | d :: ds, w :: ws, r :: rs, hk, h, hz, hc => by
    cases hk with
    | cons hw hws =>
      obtain ⟨⟨he, hi⟩, hkind⟩ := hw
      unfold roundsFit at h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
        Bool.or_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
      have hd := hz d List.mem_cons_self
      refine List.Forall₂.cons ⟨by rw [hi]; exact h1, by rw [he]; exact hd.2, ?_⟩
        (roundIs_of_fit ds ws rs hws h8 (fun d' hd' => hz d' (List.mem_cons_of_mem _ hd'))
          fun r' hr' => hc r' (List.mem_cons_of_mem _ hr'))
      rw [he]
      refine ⟨h3, h5, h4, fun t ht => ?_, ?_⟩
      · rcases h6 t ht with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · unfold drawsMarkedNonzeroHaveNonzeroWords at h7
        rw [hkind, Option.any_some] at h7
        exact forall₂_of_zip _ _ (by rw [dsElems_length _ _ hd.1, h2]) h7
          (hc r List.mem_cons_self)

/-- Block.step reads of its columns the first so many as it wants. -/
theorem step_cols {S Cl : Type} (F : ℕ) (b : Block S Cl) (s : S) (rs : List Fmt.RoundView)
    (cols cols' : List OpenedColumn)
    (h : cols.take (b.want F rs).length = cols'.take (b.want F rs).length) :
    b.step F s rs cols = b.step F s rs cols' := by
  unfold Block.want at h
  unfold Block.step
  simp only [h]

/-- Every element that a round drew has its three words below the field's size. -/
def CanonK (rs : List Fmt.RoundView) : Prop := ∀ r ∈ rs, ∀ x ∈ r.drawn.elems, Canon x

/-- Every declared round draws positions of at most 64 bits. -/
def LogK (ds : List Fmt.DeclaredRound) : Prop := ∀ d ∈ ds, d.entry.logN ≤ 64

/-- From a yes of the step on a view to a yes of accK. -/
theorem accK_yes_view (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s)
    (ts : List ℕ) (W0 : ℕ → WO) (ft : ℕ) (fM : H2K.Pub.Msg1 c → WO)
    (hfM : ∀ m m', orc1 c m = orc1 c m' → fM m = fM m')
    (w0 : WR) (ws : List WR) (d0 : Fmt.DeclaredRound) (ds : List Fmt.DeclaredRound)
    (hplan : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true)
    (hwr : writtenOf p.nums = some (w0 :: ws)) (hrds : c.rds = ws.map WR.rd)
    (hro : H2U.roundsOfNums p.nums = some (d0 :: ds)) (hlog : LogK ds)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hcan : CanonK rs') (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (τ₀ : Tr (PQ.uL (ckP .two) c.rds))
    (htab : cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
      colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
        (srcK p c (blOf c τ₀) ts fun z x =>
          colW (wAt c W0 ft fM (blOf c τ₀) z).1 (wAt c W0 ft fM (blOf c τ₀) z).2 x)) :
    ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
      orcsOf c.rds τ = orcsOf c.rds τ₀ ∧ accK p F t0 r0 c ts (wAt c W0 ft fM) τ = true ∧
      cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
        colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
          (srcK p c (blOf c τ) ts fun z x =>
            colW (wAt c W0 ft fM (blOf c τ) z).1
              (wAt c W0 ft fM (blOf c τ) z).2 x) := by
  have hr : (proximityTestKind guardedProximityTestParts p : Blk').rounds = d0 :: ds :=
    Option.some.inj ((K12.k12_rounds guardedProximityTestParts p hplan).symm.trans hro)
  have hfit := ((step_iff _ _ _ _ _ _ _).1 hstep).1.1
  rw [hr, roundsFit_cons, Bool.and_eq_true] at hfit
  have hk : List.Forall₂ IsOfK ds (ws.map WR.rd) := by
    have hw := hwr
    unfold writtenOf at hw
    rw [hro] at hw
    cases layW_isOf (d0 :: ds) _ (w0 :: ws) hw with
    | cons _ h2 => exact forall₂_map_right IsOfK WR.rd ds ws h2
  have hR : List.Forall₂ RoundIs c.rds rs' := by
    rw [hrds]
    exact roundIs_of_fit ds _ rs' hk hfit.2
      (fun d hd => ⟨nz_of_ok p _ hro hnz d (List.mem_cons_of_mem _ hd), hlog d hd⟩) hcan
  obtain ⟨τ, a1, a2, a3⟩ := accK_yes_wAt p F t0 r0 c ts W0 ft fM hfM τ₀ rs' hR tE n (by
    rw [← hstep]
    refine step_cols F _ t0 _ _ _ ?_
    rw [htab, List.take_of_length_le]
    have := congrArg List.length htab
    rw [← this]
    exact List.length_take_le _ _)
  refine ⟨τ, a1, a2, a3, ?_⟩
  have hw : wAt c W0 ft fM (blOf c τ) = wAt c W0 ft fM (blOf c τ₀) := by
    unfold wAt
    rw [hfM _ _ (orc1_of_orcs c τ τ₀ a2)]
  rw [htab, srcK_congr p c _ _ (sameOrc_of_orcs c τ τ₀ a2), hw]

end H2K.JointK

#print axioms H2K.JointK.roundIs_of_fit
#print axioms H2K.JointK.accK_yes_view
