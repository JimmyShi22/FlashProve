-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/BatchYes.lean: THE BATCHING's ONE TEST ON VALUES (cellV) ACCEPTS WHEREVER THE MEMBER HAS SAID
YES AT A REACHED STATE: so at the batchings the table's step on shapes carries the shape with no test on values
in hand and no coin.

  eqPreB_of_k8        a yes of the row "K8.equations" passes that row's test.
  preAll_yes          the tests along the rows, along a yes of the gathering.
  **cellV_of_yes**    cellV from the yes, the ledger's emptiness and the rows' tests other than "K8.equations".
  **cellV_yes_lay**   at a feed-forward segment, under the head, at a reached state.
  **vals_of_step_lay**   the table's test on values there, from a reached state and the member's step.

Limits. The feed-forward segments. Implications. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.EqPreOfRun
import Johnson.Desc.ProofFile.Honest.K9.BatchValuesJ
import Johnson.Desc.ProofFile.Honest.K4.Law.PlanEnvAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (FieldRests)
open VerifiableInference.Desc.K9.Shape (guardRun guardRun_iff)
open VerifiableInference.Desc.First.K8.Honest (eqPreB eqPreB_iff)
open VerifiableInference.Desc.First.TailClaims.Law (partOf_some eq_heads eq_live)
open Johnson.AtFull.Shape (preAllT batchVT cellV tabOf rowsLay)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA)

/-- **A yes of the row "K8.equations" passes that row's test.** -/
theorem eqPreB_of_k8 {run : ℕ → S → Except String (List Claim × S)}
    (hU : VerifiableInference.Desc.LinkJoin.Under run K9L.k8Run.2) {n : ℕ} {u : S}
    {y : List Claim × S} (h : run n u = .ok y) : eqPreB u = true := by
  obtain ⟨c, e₁⟩ := y
  obtain ⟨F, tl, funs, tl', F1, h1, h2, h3, h4, -⟩ := K9L.k8Run_ok n u e₁ c (hU n u c e₁ h)
  rw [eqPreB_iff]
  intro q hq
  obtain ⟨q1, q2, q3⟩ := partOf_some.1 hq
  obtain rfl : tl = q.tl := Option.some.inj (h2.symm.trans q1)
  obtain rfl : F = q.F := Option.some.inj (h1.symm.trans q2)
  obtain rfl : funs = q.funs := Option.some.inj (h3.symm.trans q3)
  obtain ⟨a, b⟩ := eq_heads h4
  exact ⟨a, b, eq_live h4⟩

section
variable {Lk : Link S Claim} {rows : List ((ℕ × String) × Johnson.AtFull.Shape.Row)} {i : ℕ}
  {pre post : List (ℕ × String)}
  (tied : ∀ (j : ℕ) (o : ℕ × String), Lk.order[j]? = some o → Tied Lk j (tabOf rows o).run)
  (rests : ∀ {γ : Type} (g : S → γ), FieldRests g → ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o →
    claimsRunOf Lk.hear o = some r → ∀ m e z, r m e = .ok z → g z.2 = g e)
  (cores : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → RunKeeps r)
  (carries : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r →
    ∀ n u y, r n u = .ok y → Desc.K9.CF S.lookHeard? u y.2)
  (PT : PlainTies Lk i pre post)

include tied rests cores carries PT

/-- **The tests along the rows, along a yes of the gathering.** -/
theorem preAll_yes {t₁ : S} (each : ℕ × String → List Claim → S → Except String Unit)
    (hrow : ∀ o, o ∈ pre ∨ o ∈ post → ∀ n u r y, Along t₁ u → claimsRunOf Lk.hear o = some r →
      r n u = .ok y → (tabOf rows o).pre n u = true)
    (heq : ∀ n u, (tabOf rows (i, "K8.equations")).pre n u = eqPreB u) :
    ∀ (os : List (ℕ × String)) (x y : List Claim × S), (∀ o ∈ os, o ∈ Lk.order) →
      Desc.K9.Shape.foldE (claimsInStep each Lk.hear) os (.ok x) = .ok y → Along t₁ x.2 →
      preAllT (fun o => guardRun ProofFile.sameReply (tabOf rows o).run) (fun o => (tabOf rows o).pre) os
        x.1.length x.2 = true
  | [], _, _, _, _, _ => rfl
  | o :: os, x, y, ho, hy, ha => by
    rw [Desc.K9.Shape.fold_cons] at hy
    cases hz : claimsInStep each Lk.hear x o with
    | error e =>
      rw [hz] at hy
      cases hy
    | ok z =>
      rw [hz] at hy
      obtain ⟨run, v, hr, hv, rfl⟩ := step_ok each Lk.hear x z o hz
      have hO : o ∈ Lk.order := ho o (by simp)
      have hP : (tabOf rows o).pre x.1.length x.2 = true := by
        have hc : o ∈ pre ∨ o = (i, "K8.equations") ∨ o ∈ post := by
          have hO' := hO
          rw [PT.order] at hO'
          simpa [List.mem_append, List.mem_cons] using hO'
        rcases hc with h1 | rfl | h1
        · exact hrow o (Or.inl h1) _ _ _ _ ha hr hv
        · rw [heq]
          exact eqPreB_of_k8 (PT.eq run hr) hv
        · exact hrow o (Or.inr h1) _ _ _ _ ha hr hv
      show ((tabOf rows o).pre x.1.length x.2 &&
        match guardRun ProofFile.sameReply (tabOf rows o).run x.1.length x.2 with
        | .ok w => preAllT (fun o => guardRun ProofFile.sameReply (tabOf rows o).run)
            (fun o => (tabOf rows o).pre) os (x.1.length + w.1.length) w.2
        | .error _ => true) = true
      rw [hP, Bool.true_and]
      cases hg : guardRun ProofFile.sameReply (tabOf rows o).run x.1.length x.2 with
      | error e => rfl
      | ok w =>
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hO
        obtain ⟨r, hr', hw⟩ := run_of_table tied hj hg
        obtain rfl : r = run := Option.some.inj (hr'.symm.trans hr)
        obtain rfl : w = v := Except.ok.inj (hw.symm.trans hv)
        have ha' : Along t₁ w.2 := along_step tied rests cores carries hO ha hg
        have k := preAll_yes each hrow heq os (x.1 ++ w.1, w.2) y
          (fun o' h' => ho o' (List.mem_cons_of_mem _ h')) hy ha'
        simpa [List.length_append] using k

/-- **cellV FROM THE MEMBER's YES.** -/
theorem cellV_of_yes {p : Desc.K9.Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (each : ℕ × String → List Claim → S → Except String Unit)
    (empty : ∀ F, s.fork? = some F → Desc.K9.ledgerEmpty F = true)
    (heq : ∀ n u, (tabOf rows (i, "K8.equations")).pre n u = eqPreB u)
    (hrow : ∀ t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s rs gs = .ok t₁ →
      ∀ o, o ∈ pre ∨ o ∈ post → ∀ n u r y, Along t₁ u → claimsRunOf Lk.hear o = some r →
        r n u = .ok y → (tabOf rows o).pre n u = true)
    (hy : (Desc.K9.batch Desc.K9.atS p (claimsInBy each Lk.hear Lk.order)).decide s rs gs = .ok s') :
    cellV p rows Lk.order s rs gs = true := by
  unfold cellV batchVT
  have e1 : (s.fork?.map Desc.K9.ledgerEmpty).getD true = true := by
    cases hF : s.fork? with
    | none => rfl
    | some F => exact empty F hF
  rw [e1, Bool.true_and]
  cases hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s rs gs with
  | error e => rfl
  | ok t₁ =>
    show preAllT _ _ Lk.order 0 t₁ = true
    have hy' : ((Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s rs gs >>= fun t₁ =>
        (Desc.K9.adds (Cl := Claim) Desc.K9.atS p p.piece "the segment's"
          (claimsInBy each Lk.hear Lk.order)).decide t₁ [] []) = .ok s' := hy
    rw [hd] at hy'
    have hy2 : (Desc.K9.atS.part t₁ >>= fun s₀ => Desc.K9.need "K9.draw-has-run" s₀.L.handed >>= fun _ =>
        claimsInBy each Lk.hear Lk.order t₁ >>= fun x => Desc.K9.atS.part x.2 >>= fun q =>
          Desc.K9.addList q.F x.1 >>= fun F =>
            (pure (Desc.K9.atS.set x.2 { q with F := F }) : Except String S)) = .ok s' := hy'
    cases hc : claimsInBy each Lk.hear Lk.order t₁ with
    | error e =>
      exfalso
      cases h1 : Desc.K9.atS.part t₁ with
      | error e₁ =>
        rw [h1] at hy2
        cases hy2
      | ok a =>
        rw [h1] at hy2
        cases h2 : Desc.K9.need "K9.draw-has-run" a.L.handed with
        | error e₂ =>
          simp only [bind, Except.bind, h2] at hy2
          cases hy2
        | ok b =>
          simp only [bind, Except.bind, h2, hc] at hy2
          cases hy2
    | ok y =>
      have k := preAll_yes tied rests cores carries PT each (hrow t₁ hd) heq Lk.order ([], t₁) y
        (fun _ h => h) hc (Along.refl t₁)
      exact k

end

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Lk : Link S ProofFile.Cl}
  {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} {k : ℕ}

/-- A round that drew one element is, to the draw, that element's round. -/
theorem draw_rd {s : S} {rd : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    {y : UInt64 × UInt64 × UInt64} (hr : rd.drawn.elems = [y]) :
    (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [rd] gs =
      (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple y)⟩] [] := by
  have e : Desc.K9.chiOf rd = Desc.K9.chiOf ⟨[], drawnOne (E.ofTriple y)⟩ := by
    unfold Desc.K9.chiOf
    rw [hr]
    show _ = Desc.K9.there _ (match [(E.ofTriple y).triple] with
      | [x] => some (E.ofTriple x)
      | _ => none)
    rw [E.triple_ofTriple]
  show (Desc.K9.atS.part s >>= fun a => Desc.K9.chiOf rd >>= _) =
    (Desc.K9.atS.part s >>= fun a => Desc.K9.chiOf _ >>= _)
  rw [e]

/-- **AT A FEED-FORWARD SEGMENT, AT A REACHED STATE: cellV FROM THE MEMBER's YES.** -/
theorem cellV_yes_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (Sd : SeatedFree cF Zp (2 * g) k Lk p w) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {z : ProofFile.InstPub} {s s' : S}
    (hz : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g) + IM.nAt (2 * g) + 2) (z, s))
    {rd : Fmt.RoundView} {y : UInt64 × UInt64 × UInt64} (hr : rd.drawn.elems = [y])
    {gs : List (List (ℕ × List UInt64))}
    (hy : (Desc.K9.batch Desc.K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide s [rd] gs = .ok s') :
    cellV p (rowsLay Bs.G₀.W g) Lk.order s [rd] gs = true := by
  have hl : 2 * g < 25 := by omega
  have hn : IM.nAt (2 * g) = 7 := by simp [IM.nAt]; omega
  obtain ⟨Bs', hB', tied⟩ := tied_lay h hg Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  have env : OnBytes.Desc.First.K4.Rt.planEnvB Bs.G₀.W.layers s = true := by
    rw [hn] at hz
    exact ProofFile.Honest.K4.planEnvB_at_head h hB hg (by
            have e : 14 * (2 * g) + 7 + 2 = 28 * g + 9 := by omega
            rw [← e]
            exact hz)
  refine cellV_of_yes tied (fun g R => rests_at_head h hl Sd g R) (cores_at_head h hl Sd)
    (carries_at_head h hl Sd) (plainTies_lay_at_head h hg Sd) Lk.each
    (empty_at_batching h hl hz) (fun _ _ => rfl) ?_ hy
  intro t₁ hd o ho n u _ _ hu _ _
  have hE : OnBytes.Desc.First.K4.Rt.planEnvB Bs.G₀.W.layers u = true := by
    unfold OnBytes.Desc.First.K4.Rt.planEnvB at env ⊢
    rw [own_along (by rw [← draw_rd hr]; exact hd) hu]
    exact env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with (rfl | rfl | rfl | rfl | rfl) | rfl
  · rfl
  · rfl
  · exact hE
  · rfl
  · rfl
  · exact hE

/-- **THE TABLE's TEST ON VALUES AT THE BATCHING OF A FEED-FORWARD SEGMENT, FROM A REACHED STATE AND THE MEMBER's STEP:** no
silence of a fall, no coin in the premises. -/
theorem vals_of_step_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {blk : Block S ProofFile.Cl} (hblk : cF.blocksInOrder[14 * (2 * g) + 8 + 1]? = some blk) {z : ProofFile.InstPub}
    {s s' : S} (hz : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g) + 8 + 1) (z, s)) {ft n : ℕ}
    {R : List Fmt.RoundView} {c : List VerifiableInference.Desc.OpenedColumn} (hs : blk.step ft s R c = .ok (s', n)) :
    Johnson.AtFull.Shape.Tab.vals Zp Bs.G₀ (14 * (2 * g) + 8 + 1) s (R.map noDigest)
      (blk.shown ft R c) = true := by
  have hl : 2 * g < 25 := by omega
  have hn : IM.nAt (2 * g) = 7 := by simp [IM.nAt]; omega
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h (2 * g) hl
  rw [if_neg (by omega)] at Sd
  have eb : 14 * (2 * g) + 8 + 1 = 14 * (2 * g) + 7 + 2 := by omega
  have hbk := Sd.batching
  rw [← eb, hblk] at hbk
  obtain rfl := Option.some.inj hbk
  obtain ⟨a, ka, la⟩ := Sd.alone
  have h3 := (VerifiableInference.Desc.step_iff ft _ s s' R c n).1 hs
  have hf : roundsFit [{ entry := Desc.K9.entry p }] R = true := by
    have e : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).rounds =
        [{ entry := Desc.K9.entry p }] := IM.alone_rounds la
    rw [← e]
    exact h3.1.1
  obtain ⟨rd, y, rfl, hy⟩ := Johnson.AtFull.Shape.batch_fit hf
  have hb := ((IM.yes_alone la ka s s' [noDigest rd] _).1 h3.2.1).1
  rw [vals_lay hg Sd Bs.G₀]
  exact cellV_yes_lay h hg Sd hB (by rw [hn, ← eb]; exact hz) (rd := noDigest rd) hy hb

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.vals_of_step_lay
#print axioms ProofFile.Honest.K9.eqPreB_of_k8
#print axioms ProofFile.Honest.K9.preAll_yes
#print axioms ProofFile.Honest.K9.cellV_of_yes
#print axioms ProofFile.Honest.K9.cellV_yes_lay
