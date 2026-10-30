-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/BaseGives.lean: the base case's part of the proximity test gives the chain's
last test in the field.

Proves `BaseGives` (Johnson/Desc/K12/Law/JointK.lean) for the base case's part `baseJ5` of
Johnson/Desc/K12/JoinGuarded.lean, which decides by `baseDecide` of Johnson/Desc/Prox/BaseCase.lean.
Statements and proofs.
Main names:
  `baseJ5_ok`: what a yes of `baseJ5`'s decision holds: the claim written out, the yes of
    `baseDecide`, and three facts in the program's terms, each from a plain test of `baseJ5`: the
    last rows can be made (from `lastMember`), the main code is there, and the fixed form fits the
    main message (both from the test with `Own.formFits`, by `formFits_agrees`,
    Johnson/Desc/Own/ShapesAgree.lean).
  `stmIn_claimAt`: the bridge: the claim written out (`claimAt`: the form with its one row variable
    fixed at 0), read as the format reads a row (`stmIn`), is the program's row read in the field
    (`stmGk s 1 0`).
  `ranged_ok`: a yes behind the guard on drawn positions holds the part's own yes, and that every
    drawn position lies in its declared range.
  `baseGives`: `BaseGives X p` for every X whose base case's yes holds `baseJ5`'s yes, by
    `decide_yes` (Johnson/Top/H0/P5Law/Law.lean) and `accept_of_baseOK` (OnBytes/Slice/Base.lean).
  `foldKeeps_P5`, `baseGives_P5`: the two propositions at `guardedProximityTestParts`; `foldKeeps_joined`: the first
    at `proximityTestParts`.
Limits: `BaseGives proximityTestParts p` is not proved, and from this joint it cannot be: the base case's part
of Join.lean reads its symbols through the book, to which `JointK` at the last stage ties nothing.
No statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); that program's plain
records and pure functions, some with names that begin with `Blk.`, and lemmas on them, are used. No
soundness is claimed. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.FoldKeeps
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.Own.ShapesAgree

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok)

theorem named_ok {α : Type} {n : String} {x : Option α} {a : α}
    (h : VerifiableInference.Desc.named n x = .ok a) : x = some a := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

theorem optB_ok {α : Type} {n : String} {x : Option α} {a : α}
    (h : First.Base.opt n x = .ok a) : x = some a := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

theorem needB_ok {n : String} {b : Bool} {u : Unit} (h : First.Base.need n b = .ok u) :
    b = true := by
  unfold First.Base.need at h
  cases b with
  | true => rfl
  | false => cases h

/-- What a yes of the base case's part holds. -/
theorem baseJ5_ok (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (row : GroupRow) (L : GroupLayout) (cu : IoppStage)
    (hp : t.pass = .claim row L) (hc : stageAt p j cur = some cu)
    (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) :
    ∃ (cl cl' : Prox.BaseClaim) (R : SingleRows) (code : OnBytes.Code),
      claimAt t.st.codes cu row = some cl ∧ Prox.baseDecide (basePar p cur) cl rs gs = .ok cl' ∧
      ioppLastRows cu L row = some R ∧ t.st.codes.base[R.code]? = some code ∧
      R.c.fits (ceilLog2 code.ell) = true := by
  unfold baseJ5 at h
  dsimp only at h
  split at h
  · rename_i row' L' c' dL dB e1 e2
    cases hp.symm.trans e1
    cases hc.symm.trans e2
    obtain ⟨cl, h1, h⟩ := bind_ok h
    obtain ⟨_, hfit, h⟩ := bind_ok h
    obtain ⟨cl', h2, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨m, hm, h⟩ := bind_ok h
    have hfit' := H2K.FoldLaw.need_ok hfit
    obtain ⟨code, hcode, hff⟩ := (Option.any_eq_true _ _).1 hfit'
    have hL : (L.k == 1 && L.h == 0 && L.members.size == 1) = true := by
      have hm' := named_ok hm
      unfold lastMember at hm'
      split at hm'
      · rename_i hc6
        simp only [Bool.and_eq_true] at hc6 ⊢
        exact ⟨⟨hc6.1.1.1.1.1, hc6.1.1.1.1.2⟩, hc6.1.1.1.2⟩
      · cases hm'
    have hR : ∃ R, ioppLastRows cu L row = some R ∧ R.code = cu.code ∧
        R.c = row.c.fixLow [zeroE] := by
      unfold ioppLastRows
      rw [if_pos hL]
      exact ⟨_, rfl, rfl, rfl⟩
    obtain ⟨R, r1, r2, r3⟩ := hR
    exact ⟨cl, cl', R, code, named_ok h1, h2, r1, by rw [r2]; exact hcode,
      by rw [r3]; exact (Own.formFits_agrees _ _).trans hff⟩
  · cases h

theorem sentOf_elems : ∀ (vs : List Fmt.ItemValue) (l : List Fmt.M1.E), Prox.elems vs = some l →
    Fmt.M1.sentOf vs = l
  | [], l, h => by cases h; rfl
  | .e x :: vs, l, h => by
    simp only [Prox.elems] at h
    cases hr : Prox.elems vs with
    | none => simp [hr] at h
    | some r =>
      simp [hr] at h
      subst h
      show x :: Fmt.M1.sentOf vs = x :: r
      rw [sentOf_elems vs r hr]
  | .f _ :: _, _, h => by cases h
  | .word _ :: _, _, h => by cases h
  | .root _ :: _, _, h => by cases h
  | .answer _ :: _, _, h => by cases h

/-- The bridge: the claim written out, read as the format reads a row, is the program's row read in
the field. -/
theorem stmIn_claimAt (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (K : Codes) (cu : IoppStage)
    (row : GroupRow) (cl : Prox.BaseClaim) (cd : OnBytes.Code) (hcd : K.base[cu.code]? = some cd)
    (hl : cd.ell = s.C.l) (hk : cu.k = 0) (hcl : claimAt K cu row = some cl)
    (hfit : (row.c.fixLow [zeroE]).fits (ceilLog2 cd.ell) = true)
    (hfix : FixLaw row.c [zeroE]) : stmIn s ⟨cl.c, cl.d, cl.tau⟩ = stmGk s 1 0 row := by
  have hcl' : cl = ⟨dense (row.c.fixLow [zeroE]) (ceilLog2 cd.ell), row.d.map (·.triple),
      row.target.triple⟩ := by
    unfold claimAt at hcl
    simp only [hcd, hk] at hcl
    by_cases hke : row.kept.isEmpty = true
    · simp [hke] at hcl
      exact hcl.symm
    · simp [hke] at hcl
  subst hcl'
  have hkk : s.h + s.g = 0 := by omega
  refine Prod.ext rfl (funext fun jx => ?_)
  rcases jx with ⟨x1, x2⟩ | ⟨x1, x2⟩
  · have hx : x1 = fun _ => false := funext fun i => absurd i.isLt (by omega)
    show vec (dense (row.c.fixLow [zeroE]) (ceilLog2 cd.ell))
      (Sz.rowNo x1 + 2 ^ (s.h + s.g) * x2.val) = formAt row.c (Sz.rowNo x1 + 2 ^ 1 * x2.val)
    rw [hx, rowNo_false, hkk, pow_zero, Nat.zero_add, Nat.one_mul, pow_one, Nat.zero_add]
    have hJ : x2.val < 2 ^ ceilLog2 cd.ell :=
      lt_of_lt_of_le (by rw [hl]; exact x2.isLt) (le_two_pow_ceilLog2 cd.ell)
    have hw := (Form.writeOut_val rdE (row.c.fixLow [zeroE]) (ceilLog2 cd.ell)
      (fun v hv => (fits_tensors _ _ hfit v hv).1) x2.val hJ).2
    show vec (((row.c.fixLow [zeroE]).writeOut (ceilLog2 cd.ell)).map E.triple) x2.val = _
    rw [← readV_eq_vec]
    exact hw.trans (fix_zero row.c hfix x2.val)
  · have hx : x1 = fun _ => false := funext fun i => absurd i.isLt (by omega)
    show vec (row.d.map E.triple) (Sz.rowNo x1 + 2 ^ s.h * x2.val) =
      readV row.d (Sz.rowNo x1 + 2 ^ 0 * x2.val)
    rw [← readV_eq_vec, hx, rowNo_false, h0]

/-- The base case's yes gives the chain's last test in the field. -/
theorem baseGives (X : Parts T12) (p : P12)
    (hX : ∀ (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' →
      (baseJ5 p j cur cut).decide t rs gs = .ok t') : BaseGives X p := by
  intro s e dL dB fu fs εb q y z g τ j cur l t tE rs gs hJ h
  obtain ⟨row, L, cu, restI, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hJ
  obtain ⟨_, hP⟩ := h4
  obtain ⟨hq, hfix, h0, g0⟩ := h5
  obtain ⟨col, mk, rfl, rfl, hcols⟩ := h11
  have hcur : s.st = cur := (List.cons.inj h12).1
  subst hcur
  replace h := hX _ _ _ _ _ _ _ h
  obtain ⟨cl, cl', R, code, hcl, hdec, hR, hcode, hfit⟩ :=
    baseJ5_ok p j _ _ t tE rs gs row L cu h1 h2 h
  obtain ⟨_, _, _, v, hv, hok⟩ := Prox.decide_yes _ _ _ _ _ hdec
  have hRc : R.code = cu.code ∧ R.c = row.c.fixLow [zeroE] := by
    unfold ioppLastRows at hR
    split at hR
    · cases hR; exact ⟨rfl, rfl⟩
    · cases hR
  rw [hRc.1] at hcode
  rw [hRc.2] at hfit
  obtain ⟨cd, hcd, hC⟩ := hP.codes.base
  have hcc : code = cd := Option.some.inj (hcode.symm.trans hcd)
  subst hcc
  have hbridge := stmIn_claimAt s h0 g0 t.st.codes cu row cl code hcode (congrArg (·.l) hC)
    (by rw [hP.codes.k]; omega) hcl hfit hfix
  obtain ⟨m1, c1, m2, c2, u⟩ := τ
  subst h8
  obtain ⟨nB, hB⟩ := hP.draws
  have hQ : ∀ i, (gPos s.C.a s.t _ (valsOf dB c2) i).val ∈ (rvOf dB m2 c2).poss := by
    intro i
    have hlt : i.val < (rvOf dB m2 c2).poss.length := by
      rw [hB.poss_length]
      exact i.isLt
    rw [hB.gPos_val m2 c2 i, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
      Option.getD_some]
    exact List.getElem_mem hlt
  rcases gs with _ | ⟨grp, _ | ⟨g2, gr⟩⟩
  · cases hv
  · have hv' : (match (PQ.PlainOf.gots dL.items (GPlain.old (b := dL.entry.work) m1.2)),
          ((ckP .two).dr dL.entry dL.kind (GChal.old (b := dL.entry.work) c1)).elems,
          Prox.elems (PQ.PlainOf.gots dB.items (GPlain.old (b := dB.entry.work) m2.2)) with
        | [.e tauS], [lam], some sent => some (⟨tauS, lam, sent,
            ((ckP .two).dr dB.entry dB.kind (GChal.old (b := dB.entry.work) c2)).poss, grp⟩ :
              Prox.BaseHeard)
        | _, _, _ => none) = some v := hv
    split at hv'
    · rename_i tauS lam sent e1 e2 e3
      cases hv'
      have hacc := accept_of_baseOK s h0 g0 ⟨cl.c, cl.d, cl.tau⟩ col mk (Prox.colOf grp)
        (hcols grp (List.mem_singleton.2 rfl)) tauS lam _ _ _ _ _
        (gPos s.C.a s.t _ (valsOf dB c2)) hQ hok
      rw [hbridge, hq] at hacc
      have hu : fu m1 = toE tauS := by
        rw [hP.fu]
        show lst (Fmt.M1.sentOf (PQ.PlainOf.gots dL.items (GPlain.old (b := dL.entry.work) m1.2))) 0
          = _
        rw [e1]
        rfl
      have hlam : gOne _ (valsOf dL c1) = toE lam := gOne_of_els dL m1 c1 e2
      have hs : fs m2 = shown s (sent.take s.C.l) ((sent.drop s.C.l).take s.Z.l)
          ((sent.drop (s.C.l + s.Z.l)).take s.C.r) (sent.drop (s.C.l + s.Z.l + s.C.r)) := by
        rw [hP.fs]
        show shownW s (Fmt.M1.sentOf _) = _
        rw [sentOf_elems _ _ e3]
        rfl
      show LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) q) q.1
        (s.cIn.T (wordIn s col)) (s.cIn.T (wordMk s mk)) (fu m1) (gOne _ (valsOf dL c1)) (fs m2)
        (gPos s.C.a s.t _ (valsOf dB c2))
      rw [hu, hlam, hs]
      exact hacc
    · cases hv'
  · cases hv

/-- A yes behind guard (z). -/
theorem ranged_ok (cut : List Fmt.DeclaredRound) (Y : K12.Part T12) (t t' : T12) (rs : List Fmt.RoundView)
    (gs : Gs) (h : (ranged cut Y).decide t rs gs = .ok t') :
    Y.decide t rs gs = .ok t' ∧ inRange cut rs = true := by
  unfold ranged at h
  obtain ⟨_, h1, h⟩ := bind_ok h
  exact ⟨h, needD_ok h1⟩

/-- The two propositions at `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean), not at `proximityTestParts`, the parts of
Johnson/Desc/K12/Join.lean themselves. -/
theorem foldKeeps_P5 (p : P12) : FoldKeeps guardedProximityTestParts p :=
  foldKeeps guardedProximityTestParts p fun _ _ _ _ _ _ _ h => (ranged_ok _ _ _ _ _ _ h).1

/-- The fold's part keeps the joint also at `proximityTestParts`, the parts of Johnson/Desc/K12/Join.lean
themselves. -/
theorem foldKeeps_joined (p : P12) : FoldKeeps K12.proximityTestParts p :=
  foldKeeps K12.proximityTestParts p fun _ _ _ _ _ _ _ h => h

theorem baseGives_P5 (p : P12) : BaseGives guardedProximityTestParts p :=
  baseGives guardedProximityTestParts p fun _ _ _ _ _ _ _ h => (ranged_ok _ _ _ _ _ _ h).1

end H2K.JointK
