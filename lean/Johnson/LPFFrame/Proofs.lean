-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFFrame/Proofs.lean: the proofs of the statements of Johnson/LPFFrame/Statements.lean: the
frame's accept. Statements there; proofs here.

Main names, in the file's order.
* One round: `ok_grOf`, `pass_lo_eq`, `pass_sh_eq`: the wire record's test of a written round is the
  round's own test of work. `old_put`: what is written in as a nonce leaves the old plain part.
* Shapes laid behind each other: `pass_app`, `puts_app`, `puts_rho`.
* A chain: `pass_wiresLo`, `pass_wiresSh`; `SameShown`, `shown_cons`, `shown_lo`, `shown_sh`: under
  `Puts` what a view is made of stays: the rounds as shown, the verifier messages, the columns.
* The whole file: `pass_silent`, `pass_whole`, `colOf_congr`, `viewOf_congr`, `puts_same`.
* `table_lt`, `carries_of`; `accept_iff_run`; `frame_accLaw` (THE LINK).
* `fullOf_within`, `fullAt_bare`, `bare_of_storedFit`, `withinB`, `within_of`, `within_proofFull`,
  `within_keyFull`, `fullAt_written`, `fullAt_writtenK`, `fullAt_live`, `fullAt_liveK`.
* `carries_honestTab`, `gate_of_run`, `frame_at_slot`, `frame_at_slotK`.

What it leans on in the sealed tree: `wholeIOR_out_iff` (OnBytes/Maker/WholeViews.lean), `rhoT_eq`
(OnBytes/Maker/TreesLaws.lean), `Tr.rho_fst`, `Tr.rho_snd` (Iop/ShapeKit.lean), `GrW.ok_ofBits`,
`GChal.pass_zero_bits` (Iop/GrindWire.lean), `GPlain.old_mk` (Iop/GrindProofs.lean),
`mem_wantsOf_table` (OnBytes/Maker/AcceptOfYes.lean), `Fmt.listOf_mem` (Fmt/Rules6Laws.lean),
`Run.planPull_fits` (Run/PlanPull.lean), `LPFD.fullOf_bare`
(Johnson/Top/Fire/Code/PieceYesBare.lean), `storedFit_proofFull`, `whole_proofFull`
(Johnson/G/DryProofTestsFull.lean), `storedFit_keyFull`, `whole_eq` (Johnson/G/DryKeyTests.lean),
`theLive_made` (Johnson/Goal/Description/Live.lean), `laidPOf_written`
(Johnson/Desc/Laid/ProofFullScope.lean), `laid_data_written`
(Johnson/Goal/Numbers/KeySeatLaidAt.lean), `writtenPFull_at`, `writtenKFull_at`
(Johnson/Flat/Dec/DataAtWritten.lean), `theProofGate_live` (Johnson/Goal/Description/Gates.lean).
`within_proofFull` and `within_keyFull` are evaluations by the kernel (`decide +kernel`) of a test
over the 68 rounds of each file's second chain, behind the sealed written values, in the idiom of
the two files of tests named above.

Limits. Statements.lean's six, whole. Above all: the link's premise is shown of no strategy.

For proofs only; no program imports this file.


-/
import Johnson.LPFFrame.Statements
import Johnson.Top.Fire.Code.PieceYesBare
import OnBytes.Maker.AcceptOfYes
import Johnson.G.DryProofTestsFull
import Run.PlanPull
import Fmt.Rules6Laws
import OnBytes.Maker.TreesLaws
import Johnson.G.DryKeyTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFFrame

open OnBytes OnBytes.Maker TypedOracleCompiler.Iop TypedOracleCompiler.Joined _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open OnBytes.Prover (AccLaw Puts)

/-! ## One round's test of work, and its nonce -/

/-- The wire record's test of a written round is the round's own test of work. -/
theorem ok_grOf : ∀ (b : ℕ) (Ch P : Type) (c : GChal b Ch),
    ((grOf Dn Ch P b).map TypedOracleCompiler.Tagged.ofGr).elim true (fun g => g.ok c) = GChal.pass c
  | 0, _, _, c => (GChal.pass_zero_bits c).symm
  | b + 1, Ch, P, c => _root_.Iop.GrW.ok_ofBits Dn b Ch P c

/-- A local round's test reads the record of the slot's query. -/
theorem pass_lo_eq {lam K : ℕ} {r : Round} (w : WireRB lam K r (RAnn.allLocal r)) (c : r.Chal) :
    w.pass c = w.grJ.elim true fun g => g.ok c := by
  unfold TypedOracleCompiler.Iop.WireRB.pass
  cases w.grJ <;> rfl

/-- A shared round's test reads the record of the shared query. -/
theorem pass_sh_eq {lam K : ℕ} {r : Round} (w : WireRB lam K r (RAnn.ofShared .sh r))
    (c : r.Chal) : w.pass c = w.gr0.elim true fun g => g.ok c := by
  unfold TypedOracleCompiler.Iop.WireRB.pass
  cases w.gr0 <;> rfl

/-- What is written in as a nonce leaves the old plain part. -/
theorem old_put : ∀ (b : ℕ) (Ch P : Type) (g : GrW (GChal b Ch) (GPlain ℕ b P)),
    (grOf Dn Ch P b).map TypedOracleCompiler.Tagged.ofGr = some g → ∀ (n : ℕ) (p : GPlain ℕ b P),
    GPlain.old (g.put n p) = GPlain.old p
  | 0, _, _, _, h, _, _ => by cases h
  | b + 1, _, _, _, h, _, _ => by
      cases h
      exact GPlain.old_mk _ _ _

/-! ## Shapes laid behind each other -/

section App
variable {lam K : ℕ}

theorem pass_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B) (ρ : Rho (s ++ u)),
    RoundsQueryLayout.pass (s ++ u) (RoundSplits.app A B) (WireSB.app W V) ρ =
      (RoundsQueryLayout.pass s A W (Rho.fst ρ) && RoundsQueryLayout.pass u B V (Rho.snd (s := s) ρ))
  | [], _, _, _, _, _, _ => (Bool.true_and _).symm
  | _ :: s, _, (_, A), _, (w, W), V, (c, ρ) => by
      show (w.pass c && RoundsQueryLayout.pass _ _ (WireSB.app W V) ρ) =
        ((w.pass c && RoundsQueryLayout.pass s A W (Rho.fst ρ)) && RoundsQueryLayout.pass _ _ V (Rho.snd (s := s) ρ))
      rw [pass_app W V ρ, Bool.and_assoc]

theorem puts_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B) (τ τ' : Tr (s ++ u)),
    Puts (s ++ u) (RoundSplits.app A B) (WireSB.app W V) τ τ' →
      Puts s A W (Tr.fst τ) (Tr.fst τ') ∧ Puts u B V (Tr.snd (s := s) τ) (Tr.snd (s := s) τ')
  | [], _, _, _, _, _, _, _, h => ⟨trivial, h⟩
  | _ :: _, _, (_, _), _, (_, W), V, (_, _, τ), (_, _, τ'), ⟨h1, h2, h3, h4⟩ =>
      ⟨⟨h1, h2, h3, (puts_app W V τ τ' h4).1⟩, (puts_app W V τ τ' h4).2⟩

theorem puts_rho : ∀ {s : Shape} {A : RoundSplits s} (W : RoundsQueryLayout lam K s A) (τ τ' : Tr s),
    Puts s A W τ τ' → τ'.rho = τ.rho
  | [], _, _, _, _, _ => rfl
  | _ :: _, (_, _), (_, W), (_, c, τ), (_, c', τ'), ⟨_, h2, _, h4⟩ => by
      show (c', Tr.rho τ') = (c, Tr.rho τ)
      rw [h2, puts_rho W τ τ' h4]

end App

/-! ## A chain of written rounds -/

section Chain
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem pass_wiresLo : ∀ (ds : List RDT) (ρ : Rho (uLT C ds)),
    RoundsQueryLayout.pass _ _ (wiresLo C K chal ds) ρ = passT C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show ((wireLo C K chal d).pass c && RoundsQueryLayout.pass _ _ (wiresLo C K chal ds) ρ) =
        (GChal.pass (b := d.entry.work) c && passT C ds ρ)
      rw [pass_wiresLo ds ρ]
      exact congrArg (· && passT C ds ρ) ((pass_lo_eq (wireLo C K chal d) c).trans
        (ok_grOf d.entry.work (C.Ch d.entry d.kind) (PlainOf d.items) c))

theorem pass_wiresSh : ∀ (ds : List RDT) (ρ : Rho (uLT C ds)),
    RoundsQueryLayout.pass _ _ (wiresSh C K chal ds) ρ = passT C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show ((wireSh C K chal d).pass c && RoundsQueryLayout.pass _ _ (wiresSh C K chal ds) ρ) =
        (GChal.pass (b := d.entry.work) c && passT C ds ρ)
      rw [pass_wiresSh ds ρ]
      exact congrArg (· && passT C ds ρ) ((pass_sh_eq (wireSh C K chal d) c).trans
        (ok_grOf d.entry.work (C.Ch d.entry d.kind) (PlainOf d.items) c))

/-- What a view is made of, of one chain's part of a transcript. -/
structure SameShown (ds : List RDT) (τ τ' : Tr (uLT C ds)) : Prop where
  rv : rvT C ds τ' = rvT C ds τ
  rho : rhoT C ds τ' = rhoT C ds τ
  col : colAtST C ds τ' = colAtST C ds τ

theorem shown_cons (d : RDT) (ds : List RDT) (m m' : (roundT C d).up.Msg)
    (c c' : (roundT C d).up.Chal) (τ τ' : Tr (uLT C ds)) (h1 : m'.1 = m.1) (h2 : c' = c)
    (ho : GPlain.old (b := d.entry.work) m'.2 = GPlain.old (b := d.entry.work) m.2)
    (ih : SameShown C ds τ τ') :
    SameShown C (d :: ds) (m, c, τ) (m', c', τ') where
  rv := by
    show (⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m'.2),
        C.dr d.entry d.kind (GChal.old (b := d.entry.work) c')⟩ :: rvT C ds τ' : List RV) =
      ⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
        C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ :: rvT C ds τ
    rw [ho, h2, ih.rv]
  rho := by
    show (c', rhoT C ds τ') = (c, rhoT C ds τ)
    rw [h2, ih.rho]
  col := by
    funext n x
    show (if n < d.trees.length then
        (TypedOracleCompiler.Run.PQ.posAtT d.trees n x).map fun p => TypedOracleCompiler.Run.PQ.colT d.trees p (m'.1 p)
      else colAtST C ds τ' (n - d.trees.length) x) =
      (if n < d.trees.length then
        (TypedOracleCompiler.Run.PQ.posAtT d.trees n x).map fun p => TypedOracleCompiler.Run.PQ.colT d.trees p (m.1 p)
      else colAtST C ds τ (n - d.trees.length) x)
    rw [h1, ih.col]

theorem shown_lo : ∀ (ds : List RDT) (τ τ' : Tr (uLT C ds)),
    Puts _ _ (wiresLo C K chal ds) τ τ' → SameShown C ds τ τ'
  | [], _, _, _ => ⟨rfl, rfl, rfl⟩
  | d :: ds, (m, c, τ), (m', c', τ'), ⟨h1, h2, h3, h4⟩ => by
      refine shown_cons C d ds m m' c c' τ τ' h1 h2 ?_ (shown_lo ds τ τ' h4)
      rcases h3 with h | ⟨g, n, -, hg, h⟩ | ⟨g, n, hk, -, -⟩
      · rw [h]
      · rw [h]
        exact old_put d.entry.work _ _ g hg n m.2
      · cases hk

theorem shown_sh : ∀ (ds : List RDT) (τ τ' : Tr (uLT C ds)),
    Puts _ _ (wiresSh C K chal ds) τ τ' → SameShown C ds τ τ'
  | [], _, _, _ => ⟨rfl, rfl, rfl⟩
  | d :: ds, (m, c, τ), (m', c', τ'), ⟨h1, h2, h3, h4⟩ => by
      refine shown_cons C d ds m m' c c' τ τ' h1 h2 ?_ (shown_sh ds τ τ' h4)
      rcases h3 with h | ⟨g, n, hk, -, -⟩ | ⟨g, n, -, hg, h⟩
      · rw [h]
      · cases hk
      · rw [h]
        exact old_put d.entry.work _ _ g hg n m.2

end Chain

/-! ## The silent rounds -/

theorem pass_silent (K : ℕ) (T : Type) (t : T) (a : RAnn (plainRound T t))
    (c : (plainRound T t).Chal) : (wireSilent K T t a).pass c = true := by
  unfold TypedOracleCompiler.Iop.WireRB.pass
  cases a.kind <;> rfl

/-! ## The whole file -/

section Whole
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

theorem pass_whole : Spec.pass_whole C K chal D tF tJ t3 silent run := by
  rintro ⟨mF, cF, τ⟩
  show ((wireSilent (K + 1) TF tF _).pass cF &&
      RoundsQueryLayout.pass _ _ (WireSB.app (wiresLo C K chal D.ds₁)
                   (wiresOf C K chal D tF tJ t3).shJ) (Tr.rho τ)) = _
  rw [pass_silent, Bool.true_and, pass_app, pass_wiresLo, ← Tr.rho_fst, ← Tr.rho_snd, ← rhoT_eq]
  generalize hJ : Tr.snd (s := (chainsOf C D tF tJ t3).s₁) τ = τJ
  obtain ⟨mJ, cJ, τ2⟩ := τJ
  show (_ && ((wireSilent (K + 1) TJ tJ _).pass cJ &&
      RoundsQueryLayout.pass _ _ (WireSB.app (wiresSh C K chal D.ds₂)
                   (wiresOf C K chal D tF tJ t3).sh₃) (Tr.rho τ2))) = _
  rw [pass_silent, Bool.true_and, pass_app, pass_wiresSh, ← Tr.rho_fst, ← Tr.rho_snd, ← rhoT_eq]
  generalize h3 : Tr.snd (s := (chainsOf C D tF tJ t3).s₂) τ2 = τ3
  obtain ⟨m3, c3, τ4⟩ := τ3
  show (_ && (_ && ((wireSilent (K + 1) T3 t3 _).pass c3 &&
      RoundsQueryLayout.pass _ _ (wiresLo C K chal D.ds₃) (Tr.rho τ4)))) = _
  rw [pass_silent, Bool.true_and, pass_wiresLo, ← rhoT_eq, ← Bool.and_assoc]
  show _ = (passT C D.ds₁ (rhoT C D.ds₁ (Tr.fst τ)) &&
    passT C D.ds₂ (rhoT C D.ds₂ (Tr.fst (Tr.snd (s := (chainsOf C D tF tJ t3).s₁) τ).2.2)) &&
    passT C D.ds₃ (rhoT C D.ds₃ (Tr.snd (s := (chainsOf C D tF tJ t3).s₂)
      (Tr.snd (s := (chainsOf C D tF tJ t3).s₁) τ).2.2).2.2))
  rw [hJ]
  show _ = (_ && _ && passT C D.ds₃ (rhoT C D.ds₃
    (Tr.snd (s := (chainsOf C D tF tJ t3).s₂) τ2).2.2))
  rw [h3]

theorem colOf_congr (y : (oneExternalString (2 ^ D.a) SgX).Str) {τ₁ τ₁' : Tr (uLT C D.ds₁)}
    {τ₂ τ₂' : Tr (uLT C D.ds₂)} {τ₃ τ₃' : Tr (uLT C D.ds₃)}
    (h₁ : colAtST C D.ds₁ τ₁' = colAtST C D.ds₁ τ₁) (h₂ : colAtST C D.ds₂ τ₂' = colAtST C D.ds₂ τ₂)
    (h₃ : colAtST C D.ds₃ τ₃' = colAtST C D.ds₃ τ₃) :
    colOf C D y τ₁' τ₂' τ₃' = colOf C D y τ₁ τ₂ τ₃ := by
  funext w
  cases w with
  | table _ _ => rfl
  | tree j x =>
    show (if j < D.t₁ then colAtST C D.ds₁ τ₁' j x
      else if j - D.t₁ < D.t₂ then colAtST C D.ds₂ τ₂' (j - D.t₁) x
      else colAtST C D.ds₃ τ₃' (j - D.t₁ - D.t₂) x) =
      (if j < D.t₁ then colAtST C D.ds₁ τ₁ j x
      else if j - D.t₁ < D.t₂ then colAtST C D.ds₂ τ₂ (j - D.t₁) x
      else colAtST C D.ds₃ τ₃ (j - D.t₁ - D.t₂) x)
    rw [h₁, h₂, h₃]

theorem viewOf_congr (y : (oneExternalString (2 ^ D.a) SgX).Str) {τ₁ τ₁' : Tr (uLT C D.ds₁)}
    {τ₂ τ₂' : Tr (uLT C D.ds₂)} {τ₃ τ₃' : Tr (uLT C D.ds₃)}
    (hc : colOf C D y τ₁' τ₂' τ₃' = colOf C D y τ₁ τ₂ τ₃) {rs rs' : List RV} (hr : rs' = rs)
    (key : ℕ → ℕ) {ws ws' : List Want} (hw : ws' = ws) :
    viewOf C D y τ₁' τ₂' τ₃' rs' key ws' = viewOf C D y τ₁ τ₂ τ₃ rs key ws := by
  subst hr hw
  unfold Maker.viewOf
  rw [hc]

theorem puts_same : Spec.puts_same C K chal D tF tJ t3 silent run := by
  intro τ τ' h
  have hρ := puts_rho _ τ τ' h
  obtain ⟨mF, cF, τa⟩ := τ
  obtain ⟨mF', cF', τa'⟩ := τ'
  obtain ⟨-, -, hF, h⟩ := h
  obtain ⟨p₁, hJ⟩ := puts_app (wiresLo C K chal D.ds₁) (wiresOf C K chal D tF tJ t3).shJ τa τa' h
  have s₁ := shown_lo C K chal D.ds₁ _ _ p₁
  have eJ : ∀ (a a' : Tr (chainsOf C D tF tJ t3).shJ),
      Puts _ _ (wiresOf C K chal D tF tJ t3).shJ a a' →
      a'.1.2 = a.1.2 ∧ SameShown C D.ds₂ (Tr.fst a.2.2) (Tr.fst a'.2.2) ∧
        (Tr.snd (s := (chainsOf C D tF tJ t3).s₂) a'.2.2).1.2 =
          (Tr.snd (s := (chainsOf C D tF tJ t3).s₂) a.2.2).1.2 ∧
        SameShown C D.ds₃ (Tr.snd (s := (chainsOf C D tF tJ t3).s₂) a.2.2).2.2
          (Tr.snd (s := (chainsOf C D tF tJ t3).s₂) a'.2.2).2.2 := by
    rintro ⟨mJ, cJ, b⟩ ⟨mJ', cJ', b'⟩ ⟨-, -, hj, hb⟩
    obtain ⟨p₂, h3⟩ :=
      puts_app (wiresSh C K chal D.ds₂) (wiresOf C K chal D tF tJ t3).sh₃ b b' hb
    have e3 : ∀ (z z' : Tr (chainsOf C D tF tJ t3).sh₃),
        Puts _ _ (wiresOf C K chal D tF tJ t3).sh₃ z z' →
        z'.1.2 = z.1.2 ∧ SameShown C D.ds₃ z.2.2 z'.2.2 := by
      rintro ⟨m3, c3, q⟩ ⟨m3', c3', q'⟩ ⟨-, -, hs, hq⟩
      refine ⟨?_, shown_lo C K chal D.ds₃ q q' hq⟩
      rcases hs with e | ⟨g, n, -, hg, -⟩ | ⟨g, n, -, hg, -⟩
      · exact e
      · cases hg
      · cases hg
    refine ⟨?_, shown_sh C K chal D.ds₂ _ _ p₂, (e3 _ _ h3).1, (e3 _ _ h3).2⟩
    rcases hj with e | ⟨g, n, -, hg, -⟩ | ⟨g, n, -, hg, -⟩
    · exact e
    · cases hg
    · cases hg
  obtain ⟨ej, s₂, e3, s₃⟩ := eJ _ _ hJ
  have eF : mF'.2 = mF.2 := by
    rcases hF with e | ⟨g, n, -, hg, -⟩ | ⟨g, n, -, hg, -⟩
    · exact e
    · cases hg
    · cases hg
  refine ⟨hρ, fun y => ?_, eF, ej, e3⟩
  have hc := colOf_congr C D y s₁.col s₂.col s₃.col
  exact ⟨viewOf_congr C D y hc s₁.rv _
      (congrArg (fun r => wantsOf D.a D.depth D.ds₁ (drawnT C D.ds₁ r)) s₁.rho),
    viewOf_congr C D y hc s₂.rv _
      (congrArg (fun r => wantsOf D.a D.depth D.ds₂ (drawnT C D.ds₂ r)) s₂.rho),
    viewOf_congr C D y hc s₃.rv _
      (congrArg (fun r => wantsOf D.a D.depth D.ds₃ (drawnT C D.ds₃ r)) s₃.rho)⟩

/-! ## The table's positions -/

theorem table_lt (a : ℕ) (dep : ℕ → Option ℕ) (item x : ℕ) (ds : List RDT)
    (Rs : List Fmt.Drawn) (h : Want.table item x ∈ wantsOf a dep ds Rs) : x < 2 ^ a := by
  obtain ⟨p, -, s, -, hx⟩ := mem_wantsOf_table a dep item x ds Rs h
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))

theorem carries_of {y : (oneExternalString (2 ^ D.a) SgX).Str} (hy : Carries y) (ws : List Want)
    (H : ∀ item x, Want.table item x ∈ ws → x < 2 ^ D.a) : carriesOf D y ws = true := by
  unfold carriesOf
  rw [List.all_eq_true]
  intro w hw
  cases w with
  | tree _ _ => rfl
  | table item x =>
    show (if h : x < 2 ^ D.a then (y ⟨x, h⟩).1 == x else false) = true
    rw [dif_pos (H item x hw)]
    exact beq_iff_eq.2 (hy ⟨x, H item x hw⟩)

/-! ## The accept, and the link -/

theorem accept_iff_run : Spec.accept_iff_run C K chal D tF tJ t3 silent run := by
  intro hF x y hy τ
  show ((reductionOfWholeFile C D tF tJ t3 silent run).out x y τ).isSome = true ↔ _
  rw [wholeIOR_out_iff, pass_whole C K chal D tF tJ t3 silent run τ, Bool.and_eq_true,
    Bool.and_eq_true]
  constructor
  · rintro ⟨⟨p1, p2, p3⟩, -, -, hs, hr⟩
    exact ⟨⟨⟨p1, p2⟩, p3⟩, hs, hr⟩
  · rintro ⟨⟨⟨p1, p2⟩, p3⟩, hs, hr⟩
    refine ⟨⟨p1, p2, p3⟩, ⟨hF.1 _, hF.2.1 _, hF.2.2 _⟩, ?_, hs, hr⟩
    refine carries_of D hy _ fun item x hx => ?_
    rcases List.mem_append.1 hx with h | h
    · exact table_lt _ _ _ _ _ _ h
    · rcases List.mem_append.1 h with h | h
      · exact table_lt _ _ _ _ _ _ h
      · exact table_lt _ _ _ _ _ _ h

/-- **THE LINK.** -/
theorem frame_accLaw : Spec.frame_accLaw C K chal D tF tJ t3 silent run := by
  intro hF x y hy σ B H
  unfold AccLaw
  intro τ hp hputs hB
  obtain ⟨-, hv, eF, eJ, e3⟩ := puts_same C K chal D tF tJ t3 silent run _ _ hputs
  obtain ⟨hs, hr⟩ := H τ.rho hp hB
  refine (accept_iff_run C K chal D tF tJ t3 silent run hF x y hy τ).2 ⟨hp, ?_, ?_⟩
  · rw [eF, eJ, e3]
    exact hs
  · rw [(hv y).1, (hv y).2.1, (hv y).2.2]
    exact hr

end Whole

/-! ## The draws are complete -/

theorem fullOf_within : ∀ (ds : List RDT) (ρ : Rho (uLT (ckP .two) ds)),
    (∀ d ∈ ds, ∀ s ∈ d.stored, s.lo + s.count ≤ d.entry.poss) →
    fullOf ds (drawnT (ckP .two) ds ρ) = true
  | [], _, _ => rfl
  | d :: ds, (c, ρ), h => by
      show ((d.stored.all fun s => (Fmt.partOf s ((ckP .two).dr d.entry d.kind
          (GChal.old (b := d.entry.work) c)).poss).length == s.count) &&
        fullOf ds (drawnT (ckP .two) ds ρ)) = true
      rw [fullOf_within ds ρ fun e he => h e (List.mem_cons_of_mem _ he), Bool.and_true,
        List.all_eq_true]
      intro s hs
      have hl := (Run.planPull_fits .two d.entry d.kind).2 (GChal.old (b := d.entry.work) c)
      have hb := h d List.mem_cons_self s hs
      rw [beq_iff_eq]
      unfold Fmt.partOf
      rw [List.length_take, List.length_drop, hl]
      omega

theorem fullAt_bare : Spec.fullAt_bare := fun _ h1 h3 h2 =>
  ⟨fun _ => LPFD.fullOf_bare _ _ h1, fun ρ => fullOf_within _ ρ h2,
    fun _ => LPFD.fullOf_bare _ _ h3⟩

/-- What the makers' test on the stored tables gives of the first and the third chain. -/
theorem bare_of_storedFit {a : ℕ} {W : Three.Whole} (h : storedFit a W = true) :
    (∀ d ∈ (WholeD.of a W).ds₁, d.stored = []) ∧ ∀ d ∈ (WholeD.of a W).ds₃, d.stored = [] := by
  unfold storedFit at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  constructor
  · intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    exact List.isEmpty_iff.1
      (h.1 e (List.mem_append_left _ ((List.dropLast_sublist _).subset he)))
  · intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    exact List.isEmpty_iff.1 (h.1 e (List.mem_append_right _ he))

/-- The test on the second chain's stored parts, as a Boolean. -/
def withinB (D : WholeD) : Bool :=
  D.ds₂.all fun d => d.stored.all fun s => decide (s.lo + s.count ≤ d.entry.poss)

theorem within_of {D : WholeD} (h : withinB D = true) :
    ∀ d ∈ D.ds₂, ∀ s ∈ d.stored, s.lo + s.count ≤ d.entry.poss := by
  unfold withinB at h
  rw [List.all_eq_true] at h
  intro d hd s hs
  exact of_decide_eq_true (List.all_eq_true.1 (h d hd) s hs)

set_option maxRecDepth 1000000 in
theorem within_proofFull : withinB Johnson.G.writtenPFull = true := by
  show withinB (WholeD.of 32 (Three.Whole.of Johnson.G.dryProofFull.1 Johnson.G.dryProofFull.2.1
    Johnson.G.dryProofFull.2.2)) = true
  rw [Johnson.G.whole_proofFull]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem within_keyFull : withinB Johnson.G.writtenKFull = true := by
  show withinB (WholeD.of 32 (Three.Whole.of Johnson.G.dryKeyFull.1 Johnson.G.dryKeyFull.2.1
    Johnson.G.dryKeyFull.2.2)) = true
  rw [Johnson.G.whole_eq]
  decide +kernel

theorem fullAt_written : Spec.fullAt_written :=
  fullAt_bare _ (bare_of_storedFit Johnson.G.storedFit_proofFull).1
    (bare_of_storedFit Johnson.G.storedFit_proofFull).2 (within_of within_proofFull)

theorem fullAt_writtenK : Spec.fullAt_writtenK :=
  fullAt_bare _ (bare_of_storedFit Johnson.G.storedFit_keyFull).1
    (bare_of_storedFit Johnson.G.storedFit_keyFull).2 (within_of within_keyFull)

theorem fullAt_live : Spec.fullAt_live := by
  intro Z hZ live
  obtain ⟨_, P, -, -, hP, -⟩ := FlashProve.theLive_made (VerifierAndGoals.asDescriptionFiles Z) live
  have e : FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles Z) = Johnson.G.writtenPFull := by
    rw [FlashProve.theProofData_ok hP]
    exact LPFD.Full.laidPOf_written (o := OnBytes.secondHashFunction) (r := P.2) hZ hP
  rw [e, VerifiableInference.OnPublicFiles.writtenPFull_at]
  exact fullAt_written

theorem fullAt_liveK : Spec.fullAt_liveK := by
  intro Z hZ live
  obtain ⟨Kk, _, -, hK, -, -⟩ := FlashProve.theLive_made (VerifierAndGoals.asDescriptionFiles Z) live
  have e : FlashProve.theKeyData (VerifierAndGoals.asDescriptionFiles Z) = Johnson.G.writtenKFull := by
    rw [FlashProve.theKeyData_ok hK]
    exact VerifiableInference.PlanWritten.laid_data_written (o := OnBytes.secondHashFunction) (r := Kk.2) hZ hK
  rw [e, VerifiableInference.OnPublicFiles.writtenKFull_at]
  exact fullAt_writtenK

/-! ## The table, the gate, and the compiled verifiers' letters -/

theorem carries_honestTab : Spec.carries_honestTab := fun _ _ _ _ => rfl

theorem gate_of_run : Spec.gate_of_run := by
  intro Zk h z v₁ v₂ v₃ hr
  rw [FlashProve.theProofGate_live Zk h]
  exact hr

section Slot
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.RunA
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

theorem frame_at_slot : Spec.frame_at_slot T := fun hF x rec y hy σ B H =>
  frame_accLaw (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty silP runP hF (x, rec) y hy σ B H

theorem frame_at_slotK : Spec.frame_at_slotK T := fun hF rec y hy σ B H =>
  frame_accLaw (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty silK runK hF rec y hy σ B H

end Slot

end LPFFrame

#print axioms LPFFrame.pass_whole
#print axioms LPFFrame.puts_same
#print axioms LPFFrame.accept_iff_run
#print axioms LPFFrame.frame_accLaw
#print axioms LPFFrame.fullAt_bare
#print axioms LPFFrame.fullAt_written
#print axioms LPFFrame.fullAt_writtenK
#print axioms LPFFrame.fullAt_live
#print axioms LPFFrame.fullAt_liveK
#print axioms LPFFrame.carries_honestTab
#print axioms LPFFrame.gate_of_run
#print axioms LPFFrame.frame_at_slot
#print axioms LPFFrame.frame_at_slotK
