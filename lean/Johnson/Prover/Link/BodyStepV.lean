-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyStepV.lean: THE VALUES' CLAUSE AGAIN BEHIND A STAGE, AT WHAT THE FORM's STEP
HANDS (StepDone, Johnson/Prover/Link/FormStep.lean) AND AT bodyAll's OWN PIECES. Statements and
proofs.

  shapesKeep_foldT, seatP_foldT   a tree's seat rides over the fold
  beta_at       the factor that the switch takes is the drawn element behind the point; it is a unit
  val_later     the stage's tree was sent by a switch: the plan's step · the form's half · the claim
                true at the state · the packing · the column · the seat · StepDone at sRF | sRS |
                sGS ⟹ the claim behind the batching is true at sNext's message

By: fold_at · gam_at · ans_at · next_at · cols_at (BodyStepAt.lean) · switch_law (SwitchLaw.lean) ·
unit_of_factor (BodyUnit.lean).
Not shown here. The first stage (its tree is the link's own). Nothing on soundness; nothing on
what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyStepAt
import Johnson.Prover.Link.BodyUnit
import Johnson.Prover.Link.BodyYes
import Johnson.Prover.Link.BodyCausal
import Johnson.Prover.Link.FormStep
import Johnson.Prover.Link.FormRooms
import OnBytes.Slice.BlkHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK
open H2K.Pub (sgOf)

theorem shapesKeep_foldT (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : ℕ × ℕ)
    (id : ℕ) (rs : List Fmt.RoundView) : ShapesKeep t.st (foldT t row L c n id rs).st := fun o x h => by
  have e := foldT_shape t row L c n id rs o
  rw [h] at e
  cases h' : (foldT t row L c n id rs).st.oracles[o]? with
  | none => rw [h'] at e; cases e
  | some x' => rw [h'] at e; exact ⟨x', rfl, Option.some.inj e⟩

theorem seatP_foldT {t : T12} {ids : List ℕ} {k a : ℕ} {shapes : List OracleShape}
    (h : SeatP t.st t.book ids k a shapes) (row : GroupRow) (L : GroupLayout) (c : IoppStage)
    (n : ℕ × ℕ) (id : ℕ) (rs : List Fmt.RoundView) :
    SeatP (foldT t row L c n id rs).st (foldT t row L c n id rs).book ids k a shapes :=
  h.keeps (BookKeeps.refl _) (shapesKeep_foldT t row L c n id rs)

/-- Where a list's tail from b on is one element, that element stands at b (beside the library's
getD_of_drop, OnBytes/Slice/BlkHead.lean, which says it of getD). -/
theorem get_of_drop {α : Type} (l : List α) (b : ℕ) (x : α) (h : l.drop b = [x]) :
    l[b]? = some x := by
  have := congrArg (·[0]?) h
  simpa [List.getElem?_drop] using this

/-- **The factor is the drawn element behind the point, and a unit.** -/
theorem beta_at (els : List Fmt.Ext) (b : ℕ) (beta : E)
    (hs : (els.map E.ofTriple).drop b = [beta]) (hz : Own.allZero beta = false)
    (hlt : ∀ x ∈ els, ltE x = true) :
    (unitOf (readE ((els.map E.ofTriple).getD b zeroE))).val = readE beta := by
  have e1 := get_of_drop _ b beta hs
  rw [getD_of_drop _ b beta zeroE hs]
  rw [List.getElem?_map] at e1
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 e1
  exact unit_of_factor x (hlt x (List.mem_of_getElem? hx)) hz

section
variable {p : P12} {K : BCoins} {last : Bool} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {o : ℕ}
  {t : T12} {P : PS} {col : ℕ → List UInt64} {row : GroupRow} {L : GroupLayout} {c n : IoppStage}
  {dS dC : Fmt.DeclaredRound} {id tN : ℕ} {tr : Tree} {Dr : ℕ → Fmt.Drawn}

/-- **The claim behind the batching is true at sNext's message.** -/
theorem val_later (Pl : StepPlan p t.st.codes j cur next last l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr)
    (hin : (Slf.idf (E := GE) (J := (sgOf cur).cIn.J)).Holds (stmGk (sgOf cur) L.k L.h row)
      (μOf (sgOf cur) P))
    (hpk : P.fM = packedN (sgOf cur) (K.W (sgOf cur) j))
    (hc : col = stageColW (sgOf cur) P.tabM P.tabZ P.tM P.tZ P.fM P.fT) (oo k : ℕ)
    (hL : LayAt [oo] #[some 0] #[some 0] L)
    (seat : SeatP t.st t.book [oo, id] k (sgOf cur).C.a (stageShapes (sgOf cur) c))
    (hlt : ∀ x ∈ (Dr (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems, ltE x = true)
    (e1 : sT1 p K j cur l o t P row Dr =
      foldT t row L c (n.code, n.maskCode) id ((sRF K j cur o P row Dr).map noDigest))
    {Dk : Taken} {x : Fmt.Ext} {row' : GroupRow}
    (Dn : StepDone (sgOf cur) (sgOf next) p n last dS dC
      (foldT t row L c (n.code, n.maskCode) id ((sRF K j cur o P row Dr).map noDigest))
      (noDigest ⟨[], Dr (o + 1 + ((sgOf cur).h + (sgOf cur).g))⟩)
      (noDigest ⟨[.answer (ofE (sAns p K j cur next l o t P row Dr))],
        Dr (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩)
      (sGS cur o col Dr) (foldOut t row L c id ((sRF K j cur o P row Dr).map noDigest))
      t.st.groups.size j cur next tN (ofE (sAns p K j cur next l o t P row Dr)) Dk x row') :
    (Slf.idf (E := GE) (J := (sgOf next).cIn.J)).Holds
      (stmGk (sgOf next)
        (stepL p n last (foldT t row L c (n.code, n.maskCode) id
          ((sRF K j cur o P row Dr).map noDigest)) t.st.groups.size Dk).k
        (stepL p n last (foldT t row L c (n.code, n.maskCode) id
          ((sRF K j cur o P row Dr).map noDigest)) t.st.groups.size Dk).h row')
      (μOf (sgOf next) (sNext K last j cur next o P row Dr)) := by
  have hZ : (t.st.codes.mask.getD c.maskCode default).ell = (sgOf cur).Z.l :=
    congrArg (·.l) Pl.codes.mask
  have hH := fold_at p K j cur o t P row Dr I.front Pl.codes.k Pl.codes.h hZ I.layK I.layH hin
    Pl.room hpk
  rw [gam_at] at hH
  have hG : (foldT t row L c (n.code, n.maskCode) id
      ((sRF K j cur o P row Dr).map noDigest)).st.groups[t.st.groups.size]? =
      some { code := n.code, maskCode := n.maskCode } := by
    show (t.st.groups.push _)[t.st.groups.size]? = _
    simp
  have eT : swTarget p n =
      switchTargetStage n.code n.maskCode ((sgOf next).h + (sgOf next).g) (sgOf next).h 1 := by
    unfold swTarget
    rw [Pl.nk, Pl.nh, Pl.one]
  have hseed := Dn.front.seed
  rw [eT] at hseed
  have hβ := beta_at (Dr (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems _ Dk.beta hseed
    Dn.front.factor hlt
  have hA := ans_at p K j cur next l o t P row Dr Pl.fits
  rw [e1, Pl.stageN, gam_at] at hA
  have h3 := (switch_law Pl.fits Pl.sized P.tabM P.tabZ P.tM P.tZ P.fM P.fT (K.fr j) cur Dn.front
    Dn.bfront Pl.nk Pl.nh Dn.ff hG Pl.poss _ hβ c L oo id k Pl.codes.k Pl.codes.h Pl.folds hL
    (seatP_foldT seat row L c _ id _)
    (fun q hq => by
      have := cols_at p cur o col Dr [dS, dC] q hq
      rw [hc] at this
      exact this)
    (μOf (sgOf cur) P) (ρOf (sgOf cur) P) (φOf (sgOf cur) P) (ψOf (sgOf cur) P)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (spent t.st id) row _ _
    (((sRF K j cur o P row Dr).map noDigest).tail.map drawnOf) rfl I.kept0
    (by
      rw [List.length_map, List.length_tail, List.length_map, length_sRF]
      omega)
    hH
    (by
      rw [Dn.alpha]
      exact hA)).2.2
  rw [next_at K last j cur next o P row Dr Pl.fits, gam_at]
  exact h3

end

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.shapesKeep_foldT
#print axioms Johnson.Prover.Link.seatP_foldT
#print axioms Johnson.Prover.Link.get_of_drop
#print axioms Johnson.Prover.Link.beta_at
#print axioms Johnson.Prover.Link.val_later
