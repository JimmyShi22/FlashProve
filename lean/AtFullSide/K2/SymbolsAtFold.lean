-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/SymbolsAtFold.lean: the symbols of a code switch's complex, at what a segment's closing
returns. The closing lays a group's rows anew and folds them; the symbols were opened at the tables
of the rows that the senders sent. Where the two lists of rows are one below the number of members,
and the fresh masks have one mask part, SymbolsAre at the senders' rows is SymbolsAre at what the
closing returned.

  foldEndAt_below      what a fold leaves reads the rows below the number of members alone, and the
                       fresh mask through its mask rows and their tails alone
  foldEndAt_kept_below the same of a kept member that lies below the number of members
  frozenLeft_same      two ends that agree at what frozenLeft reads are frozen alike
  symbols_of_fold      the step from the senders' rows to the closing's return

Limits. Every premise of symbols_of_fold is a premise: nothing here says that a run meets them.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentLeftInv
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.Desc.K2.Honest.Carry.LayoutSame
import Johnson.Desc.K2.Honest.Inner.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open OnBytes
open OnBytes.Slice (GE)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc.K2.Honest (Left Held Sizes GroupMember SymbolsAre foldEnd foldEndAt
  foldEnd_eq_at foldEndAt_lay groupLayout keptNo shapeOf tableRow tableRow_lt zeroG)
open ProofFile.Honest.K2 (FreshTable GroupRows SegmentPub challengesOr0 freshTable frozenLeft segmentLeft
  segmentLeft_inv segmentGroupRows zeroMessage)

/-- A row of a member's main part lies at a member of the list. -/
theorem main_below {ms : List GroupMember} {w b : Nat} (h : b < (shapeOf ms w).mainRows) :
    w < ms.length := by
  by_contra hw
  have e : ms[w]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hw)
  unfold shapeOf at h
  rw [e] at h
  exact Nat.not_lt_zero _ h

/-- A row of a member's mask part lies at a member of the list. -/
theorem mask_below {ms : List GroupMember} {w b : Nat} (h : b < (shapeOf ms w).maskRows) :
    w < ms.length := by
  by_contra hw
  have e : ms[w]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hw)
  unfold shapeOf at h
  rw [e] at h
  exact Nat.not_lt_zero _ h

/-- **What a fold leaves reads the rows below the number of members alone**, and the fresh mask
through its mask rows and their tails alone. -/
theorem foldEndAt_below (L : GroupLayout) (codes : Codes)
    (code maskCode : Nat) (ms : List GroupMember) (M M' : Nat → Rows) (fresh fresh' : Rows)
    (γ : List Cb.Gl.E) (hM : ∀ w, w < ms.length → M' w = M w) (hm : fresh'.mask = fresh.mask)
    (ht : fresh'.maskTl = fresh.maskTl) :
    (foldEndAt L codes code maskCode ms M' fresh' γ).main =
        (foldEndAt L codes code maskCode ms M fresh γ).main ∧
      (foldEndAt L codes code maskCode ms M' fresh' γ).mainTail =
        (foldEndAt L codes code maskCode ms M fresh γ).mainTail ∧
      (foldEndAt L codes code maskCode ms M' fresh' γ).mask =
        (foldEndAt L codes code maskCode ms M fresh γ).mask ∧
      (foldEndAt L codes code maskCode ms M' fresh' γ).maskTail =
        (foldEndAt L codes code maskCode ms M fresh γ).maskTail := by
  have c1 : ∀ (get : Rows → Bool → Nat → Nat → GE) (ρ j : Nat),
      (match tableRow L.mainFirst (fun w => (shapeOf ms w).mainRows) ρ with
        | some (w, b) => get (M' w) ((shapeOf ms w).mainDeg == 3) b j
        | none => zeroG) =
      match tableRow L.mainFirst (fun w => (shapeOf ms w).mainRows) ρ with
        | some (w, b) => get (M w) ((shapeOf ms w).mainDeg == 3) b j
        | none => zeroG := by
    intro get ρ j
    cases h : tableRow L.mainFirst (fun w => (shapeOf ms w).mainRows) ρ with
    | none => rfl
    | some p =>
      have e := hM p.1 (main_below (tableRow_lt _ _ _ _ _ h))
      show get (M' p.1) _ p.2 j = get (M p.1) _ p.2 j
      rw [e]
  have c2 : ∀ (get : Rows → Nat → Nat → GE) (ρ j : Nat),
      (match tableRow L.maskFirst (fun w => (shapeOf ms w).maskRows) ρ with
        | some (w, b) => get (M' w) b j
        | none => zeroG) =
      match tableRow L.maskFirst (fun w => (shapeOf ms w).maskRows) ρ with
        | some (w, b) => get (M w) b j
        | none => zeroG := by
    intro get ρ j
    cases h : tableRow L.maskFirst (fun w => (shapeOf ms w).maskRows) ρ with
    | none => rfl
    | some p =>
      have e := hM p.1 (mask_below (tableRow_lt _ _ _ _ _ h))
      show get (M' p.1) p.2 j = get (M p.1) p.2 j
      rw [e]
  unfold foldEndAt
  dsimp only
  refine ⟨funext fun j => ?_, funext fun q => ?_, funext fun r => funext fun i => ?_,
    funext fun r => funext fun q => ?_⟩
  · split
    · exact congrFun (congrFun (congrArg₂ (Johnson.Prover.Link.foldMsg _)
        (funext fun x => by
          rcases x with x | x
          · exact c1 (fun R e => R.main e) _ _
          · exact c2 (fun R => R.mask) _ _)
        (funext fun x => congrFun (congrFun hm _) _)) _) _
    · rfl
  · split
    · exact congrFun (congrFun (congrArg₂ (Johnson.Prover.Link.foldTl _)
        (funext fun x => by
          rcases x with x | x
          · exact c1 (fun R e b q => if e then R.mainTlE b q else
              OnBytes.Slice.toE (OnBytes.Slice.ofF (R.mainTlF b q), 0, 0)) _ _
          · exact c2 (fun R => R.maskTl) _ _)
        (funext fun x => congrFun (congrFun ht _) _)) _) _
    · rfl
  · split
    · split
      · exact congrFun (congrFun (congrArg₂ (Johnson.Prover.Link.foldMsg _)
          (funext fun x => by
            rcases x with x | x
            · exact c1 (fun R e => R.main e) _ _
            · exact c2 (fun R => R.mask) _ _)
          (funext fun x => congrFun (congrFun hm _) _)) _) _
      · exact congrFun (congrFun (congrArg₂ (Johnson.Prover.Link.foldMsg _)
          (funext fun x => by
            rcases x with x | x
            · exact c1 (fun R e => R.main e) _ _
            · exact c2 (fun R => R.mask) _ _)
          (funext fun x => congrFun (congrFun hm _) _)) _) _
    · rfl
  · split
    · split
      · exact congrFun (congrFun (congrArg₂ (Johnson.Prover.Link.foldTl _)
          (funext fun x => by
            rcases x with x | x
            · exact c1 (fun R e b q => if e then R.mainTlE b q else
                OnBytes.Slice.toE (OnBytes.Slice.ofF (R.mainTlF b q), 0, 0)) _ _
            · exact c2 (fun R => R.maskTl) _ _)
          (funext fun x => congrFun (congrFun ht _) _)) _) _
      · exact congrFun (congrFun (congrArg₂ (Johnson.Prover.Link.foldTl _)
          (funext fun x => by
            rcases x with x | x
            · exact c1 (fun R e b q => if e then R.mainTlE b q else
                OnBytes.Slice.toE (OnBytes.Slice.ofF (R.mainTlF b q), 0, 0)) _ _
            · exact c2 (fun R => R.maskTl) _ _)
          (funext fun x => congrFun (congrFun ht _) _)) _) _
    · rfl

/-- **A kept member below the number of members is read off the rows below that number.** -/
theorem foldEndAt_kept_below (L : GroupLayout) (codes : Codes)
    (code maskCode : Nat) (ms : List GroupMember) (M M' : Nat → Rows) (fresh fresh' : Rows)
    (γ : List Cb.Gl.E) (a : Nat) (e : M' (keptNo ms a) = M (keptNo ms a)) :
    (foldEndAt L codes code maskCode ms M' fresh' γ).kept a =
      (foldEndAt L codes code maskCode ms M fresh γ).kept a :=
  congrArg (fun R : Rows => (⟨R.main ((shapeOf ms (keptNo ms a)).mainDeg == 3), fun b q =>
    if ((shapeOf ms (keptNo ms a)).mainDeg == 3) then R.mainTlE b q else
      OnBytes.Slice.toE (OnBytes.Slice.ofF (R.mainTlF b q), 0, 0)⟩ : Held)) e

/-- **Two ends that agree at what frozenLeft reads are frozen alike.** -/
theorem frozenLeft_same (c z : Code) (kept : List OracleShape) {W W' : Left}
    (h1 : W'.main = W.main) (h2 : W'.mainTail = W.mainTail) (h3 : W'.mask = W.mask)
    (h4 : W'.maskTail = W.maskTail) (h5 : ∀ a, a < kept.length → W'.kept a = W.kept a) :
    frozenLeft c z kept W' = frozenLeft c z kept W := by
  have hr : (kept.toArray.zipIdx.map fun x =>
      (Array.range x.1.mainRows).map fun b =>
        ((Array.range c.ell).map ((W'.kept x.2).main b),
          (Array.range c.r).map ((W'.kept x.2).tail b))) =
      kept.toArray.zipIdx.map fun x =>
        (Array.range x.1.mainRows).map fun b =>
          ((Array.range c.ell).map ((W.kept x.2).main b),
            (Array.range c.r).map ((W.kept x.2).tail b)) := by
    refine Array.ext (by simp) fun i hi _ => ?_
    have hi' : i < kept.length := by simpa using hi
    simp only [Array.getElem_map, Array.getElem_zipIdx, Nat.zero_add, h5 i hi']
  unfold frozenLeft
  simp only [h1, h2, h3, h4, hr]

/-- **The step from the senders' rows to what the closing returned.** M, fr: the rows and the fresh
mask that the senders sent. R: the rows that the closing laid anew. -/
theorem symbols_of_fold {Z : Sizes} {old : SingleRows} {pos : Positions} {y : Array E}
    {ms : List GroupMember} (M : Nat → Rows) (fr : Rows) (γ : List Cb.Gl.E) {Sg : SegmentPub}
    {prev : Option Left} {prevKept : List OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {kk : Nat → Except String ProofFile.Honest.K2.Stretch} {base : Nat}
    {Wl : Left} {R : GroupRows}
    (hL : segmentLeft freshTable Sg prev prevKept own heard kk base = .ok (Wl, Z.kept))
    (hR : segmentGroupRows freshTable Sg prev prevKept own kk base true = .ok R)
    (hc : Sg.sizes.codes = Z.codes) (hcode : Sg.sizes.code = Z.code)
    (hmask : Sg.sizes.maskCode = Z.maskCode) (hms : R.members = ms)
    (hγ : challengesOr0 heard Sg.gamma = γ)
    (l1 : (groupLayout Z.codes Z.code Z.maskCode ms).k = old.layout.k)
    (l2 : (groupLayout Z.codes Z.code Z.maskCode ms).h = old.layout.h)
    (l3 : (groupLayout Z.codes Z.code Z.maskCode ms).mainFirst = old.layout.mainFirst)
    (l4 : (groupLayout Z.codes Z.code Z.maskCode ms).maskFirst = old.layout.maskFirst)
    (hV : ∀ w, w < ms.length → R.rows.getD w zeroMessage = M w)
    (hFm : (R.fresh.getD zeroMessage).mask = fr.mask)
    (hFt : (R.fresh.getD zeroMessage).maskTl = fr.maskTl)
    (hK : ∀ a, a < Z.kept.length → keptNo ms a < ms.length)
    (hS : SymbolsAre Z old
      (frozenLeft (Z.codes.base.getD Z.code default) (Z.codes.mask.getD Z.maskCode default) Z.kept
        (foldEndAt old.layout Z.codes Z.code Z.maskCode ms M fr γ)) pos y) :
    SymbolsAre Z old Wl pos y := by
  obtain ⟨R', eR, -, hWl⟩ := segmentLeft_inv hL
  have eR' : R' = R := Except.ok.inj (eR.symm.trans hR)
  rw [eR'] at hWl
  obtain ⟨e1, e2, e3, e4⟩ := foldEndAt_below old.layout Z.codes Z.code Z.maskCode ms M
    (R.rows.getD · zeroMessage) fr (R.fresh.getD zeroMessage) γ hV hFm hFt
  rw [hWl, hc, hcode, hmask, hms, hγ, foldEnd_eq_at, foldEndAt_lay old.layout _ l1 l2 l3 l4,
    frozenLeft_same _ _ _ e1 e2 e3 e4 fun a ha =>
      foldEndAt_kept_below old.layout Z.codes Z.code Z.maskCode ms M _ fr _ γ a (hV _ (hK a ha))]
  exact hS

end AtFullSide.K2

#print axioms AtFullSide.K2.main_below
#print axioms AtFullSide.K2.mask_below
#print axioms AtFullSide.K2.foldEndAt_below
#print axioms AtFullSide.K2.foldEndAt_kept_below
#print axioms AtFullSide.K2.frozenLeft_same
#print axioms AtFullSide.K2.symbols_of_fold
