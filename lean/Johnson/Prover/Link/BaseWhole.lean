-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BaseWhole.lean: the base case whole: the last part of the proximity test's
block, with its guard on the drawn positions (`guardedProximityTestParts.base`, Johnson/Desc/K12/JoinGuarded.lean), says
yes to what an honest prover writes, where the record in front is in order and the row that it
bears is true.

Main names (namespace `Johnson.Prover.Link`).
  `base_yes`   `BaseFront` (Johnson/Prover/Link/BasePart.lean) at the stage s.st · s has no row
      variable · the main code is in the record's list, its message length is the stage's and a
      power of two · the row's vector on the mask table has the mask code's message length · the
      law of fixing the row's one variable at 0 (`FixLaw`, OnBytes/Slice/BaseLast.lean) · the row
      is true at w (`Slf.Holds` of `stmGk s 1 0 row`) · the two rounds hold `tauSW` and `shownAll` ·
      the group of columns stands at the list of the drawn positions and holds the written columns ·
      the drawn positions are in range: then the part returns the record with the masking message
      spent, the tree counted as opened, nothing handed on and no mask
  `code_of_pair`   `lastPairOk` holds that the stage's main code is in the record's list, with the
      place's message length
  `base_yes_five`   `base_yes` with these two premises drawn from `BaseFront`: five public clauses
      are left beside it

By: `baseJ5_yes`, `ranged_yes`, `baseDecide_cols` (BasePart.lean), `claim_of_holds`,
`sizes_of_claim` (BaseClaim.lean), `formFits_agrees` (Johnson/Desc/Own/ShapesAgree.lean).

Limits. Every premise is asked, none is shown here: that a run of the stages in front leaves such a
record and a true row; that a strategy's two last messages are these; that `Block.step` hands these
columns. Nothing on how the masking message or a tail is chosen. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BaseClaim
import Johnson.Desc.Own.ShapesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12

/-- **BASE WHOLE**: the block's last part, with its guard (z), says yes to what an honest prover
writes, where the record in front is in order and the row that it bears is true. -/
theorem base_yes (p : P12) (j : ℕ) (s : Sg) (d₁ d₂ : Fmt.DeclaredRound) (t : T12) (row : GroupRow)
    (L : GroupLayout) (c : IoppStage) (cl : BaseClaim) (m star a : ℕ) (cd : OnBytes.Code)
    (rL rB : Fmt.RoundView) (g : List (ℕ × List UInt64)) (lam : Fmt.M1.E) (w : s.cIn.J → GE)
    (r0 r1 h0 s0 h1 s1 : ℕ → GE)
    (hF : BaseFront p j s.st t row L c cl m star a) (hh : s.h = 0) (hgg : s.g = 0)
    (hcd : t.st.codes.base[c.code]? = some cd) (hl : cd.ell = s.C.l)
    (hp : cd.ell = 2 ^ ceilLog2 cd.ell) (hd : row.d.size = s.Z.l) (hfix : FixLaw row.c [zeroE])
    (hw : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmGk s 1 0 row) w)
    (hL : rL.vals = [Fmt.ItemValue.e (tauSW s.C s.Z cl.c cl.d h0 h1)]) (hlam : rL.drawn.elems = [lam])
    (hB : rB.vals =
      (shownAll s.C s.Z lam (mainOf s w) r0 (maskOf s w) r1 h0 s0 h1 s1).map Fmt.ItemValue.e)
    (hg : g.map (·.1) = Fmt.listOf rB.drawn.poss)
    (hcols : ∀ y ∈ g,
      y.2 = words12 (baseColW s.C s.Z (mainOf s w) r0 (maskOf s w) r1 h0 s0 h1 s1 y.1))
    (hz : inRange [d₁, d₂] [rL, rB] = true) :
    (guardedProximityTestParts.base p j s.st [d₁, d₂]).decide t [rL, rB] [g] = .ok { t with
                       st :=
                         { t.st with oracles := t.st.oracles.modify star fun x => { x with spentAsMask := true } }
                       book :=
                         { t.book with trees := t.book.trees.modify a fun x => { x with lists := x.lists + 1 } }
                       pass := .nothing, mask := none } := by
  have hk : c.k = 0 := by
    have h := hF.stage
    unfold stageAt at h
    obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 h
    show s.h + s.g = 0
    omega
  have hfit : (row.c.fixLow [zeroE]).fits (ceilLog2 cd.ell) = true := by
    have h := hF.fits
    rw [hcd] at h
    rw [Own.formFits_agrees]
    exact h
  obtain ⟨hc, hd'⟩ := sizes_of_claim s t.st.codes c row cl cd hcd hl hF.claim hfit hp hd
  have hcl := claim_of_holds s hh hgg t.st.codes c row cl cd hcd hl hk hF.claim hfit hfix w hw
  show (ranged [d₁, d₂] (baseJ5 p j s.st [d₁, d₂])).decide t [rL, rB] [g] = _
  rw [ranged_yes _ _ _ _ _ hz]
  exact baseJ5_yes p j s.st d₁ d₂ t row L c cl m star a rL rB g hF
    (baseDecide_cols (basePar p s.st) cl rL rB g lam (mainOf s w) r0 (maskOf s w) r1 h0 s0 h1 s1
      hc hd' hcl hL hlam hB hg hcols) hg

/-- What `lastPairOk` says of the main code. -/
theorem code_of_pair (P : BasePar) (S : Statement) (c : IoppStage) (m star : ℕ)
    (h : lastPairOk P S c m star = true) :
    ∃ k, S.codes.base[c.code]? = some k ∧ k.ell = P.C.l := by
  unfold lastPairOk at h
  cases h1 : S.codes.base[c.code]? with
  | none => simp [h1] at h
  | some k =>
    cases h2 : S.codes.mask[c.maskCode]? with
    | none => simp [h1, h2] at h
    | some z =>
      cases h3 : S.oracles[m]? with
      | none => simp [h1, h2, h3] at h
      | some x =>
        cases h4 : S.oracles[star]? with
        | none => simp [h1, h2, h3, h4] at h
        | some o =>
          simp only [h1, h2, h3, h4, Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq] at h
          exact ⟨k, rfl, h.1.1.1.1.1.1.1.1.2.1⟩

/-- **BASE WHOLE, with five public clauses beside `BaseFront`.** -/
theorem base_yes_five (p : P12) (j : ℕ) (s : Sg) (d₁ d₂ : Fmt.DeclaredRound) (t : T12)
    (row : GroupRow) (L : GroupLayout) (c : IoppStage) (cl : BaseClaim) (m star a : ℕ)
    (rL rB : Fmt.RoundView) (g : List (ℕ × List UInt64)) (lam : Fmt.M1.E) (w : s.cIn.J → GE)
    (r0 r1 h0 s0 h1 s1 : ℕ → GE)
    (hF : BaseFront p j s.st t row L c cl m star a) (hh : s.h = 0) (hgg : s.g = 0)
    (hp : s.C.l = 2 ^ ceilLog2 s.C.l) (hd : row.d.size = s.Z.l) (hfix : FixLaw row.c [zeroE])
    (hw : (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmGk s 1 0 row) w)
    (hL : rL.vals = [Fmt.ItemValue.e (tauSW s.C s.Z cl.c cl.d h0 h1)]) (hlam : rL.drawn.elems = [lam])
    (hB : rB.vals =
      (shownAll s.C s.Z lam (mainOf s w) r0 (maskOf s w) r1 h0 s0 h1 s1).map Fmt.ItemValue.e)
    (hg : g.map (·.1) = Fmt.listOf rB.drawn.poss)
    (hcols : ∀ y ∈ g,
      y.2 = words12 (baseColW s.C s.Z (mainOf s w) r0 (maskOf s w) r1 h0 s0 h1 s1 y.1))
    (hz : inRange [d₁, d₂] [rL, rB] = true) :
    (guardedProximityTestParts.base p j s.st [d₁, d₂]).decide t [rL, rB] [g] = .ok { t with
                       st :=
                         { t.st with oracles := t.st.oracles.modify star fun x => { x with spentAsMask := true } }
                       book :=
                         { t.book with trees := t.book.trees.modify a fun x => { x with lists := x.lists + 1 } }
                       pass := .nothing, mask := none } := by
  obtain ⟨cd, hcd, hl⟩ := code_of_pair _ _ _ _ _ hF.pair
  have hl' : cd.ell = s.C.l := hl
  exact base_yes p j s d₁ d₂ t row L c cl m star a cd rL rB g lam w r0 r1 h0 s0 h1 s1 hF hh hgg hcd
    hl' (by rw [hl']; exact hp) hd hfix hw hL hlam hB hg hcols hz

end Johnson.Prover.Link
