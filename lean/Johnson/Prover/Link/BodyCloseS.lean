-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyCloseS.lean: THE ONE INVARIANT IS KEPT BY A STAGE, AND SO THE STAGES OF THE
PROXIMITY TEST ACCEPT WHAT bodyAll SHOWS WHEREVER THE INVARIANT HOLDS IN FRONT OF THEM. Statements
and proofs. "Nothing is left untested" is no part of the invariant: it goes along beside it.

  lastMember_kh   a last stage's layout has one row variable and no mask row variable
  hstep_at        BodyInv (BodyInv.lean), over PlanAll, in front of a stage that is not the last ⟹
                  that stage's parts accept bodyAll's pieces (StageYes, BodyYes.lean), and BodyInv
                  again in front of the next: hstep of body_yes_of
  hstep_left      under the same: if nothing is left untested in front of the stage, nothing is
                  behind it
  body_yes        THE ACCEPT ALONE: BodyInv in front of the stages ⟹ stagesFrom's decision accepts
                  bodyAll's rounds and groups. No clause on what is left untested, in front or
                  behind: its premise does not bar a statement with a group still to be tested
  body_left       with "nothing is left untested" in front: the same accept, and nothing is left
                  untested at the state that it leaves

By: form_at | formNext_at | formLast_at | formRides_at | formLeft_at (FormAt.lean: the form's
half) · val_later (BodyStepV.lean) | val_first (BodyStepF.lean): the values' half · hbase_at |
hbase_left (BodyCloseB.lean) · body_yes_of (BodyYes.lean), at two pairs of its letters.
Not shown here. That BodyInv holds in front of the first stage. Nothing on soundness or any other
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.BodyCloseB
import Johnson.Prover.Link.BodyStepF
import Johnson.Prover.Link.FormAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK
open H2K.Pub (sgOf)

theorem lastMember_kh {L : GroupLayout} {m : ℕ} (h : lastMember L = some m) :
    L.k = 1 ∧ L.h = 0 := by
  unfold lastMember at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1.1.1.1, hc.1.1.1.1.2⟩
  · cases h

/-- **The premise hstep of body_yes_of (BodyYes.lean), at BodyInv over PlanAll.** -/
theorem hstep_at (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
    (col : ℕ → List UInt64) (h : BodyInv p K (PlanAll p) D (next :: rest) j cur l o t P col) :
    StageYes p K rest j cur next l o t P col D ∧
      BodyInv p K (PlanAll p) D rest (j + 1) next (l.drop (cur.k + 3))
        (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
        (sNext K rest.isEmpty j cur next o P (rowOf t) D)
        (sCol K rest.isEmpty j cur next o P (rowOf t) D) := by
  obtain ⟨⟨hP, hS⟩, hF, row, L, c, nn, id, tN, tr, I, V⟩ := h
  obtain ⟨n, dS, dC, Dk, x, row', Pl, rfl, Y, e1, e3, Dn⟩ := form_at p K D P hP hS hF I
  refine ⟨Y, ?_⟩
  have hr : rowOf t = row := rowOf_claim I.front.pass
  rw [hr] at e1 e3 Dn ⊢
  rw [e3]
  -- what the two rounds of the switch sampled
  obtain ⟨-, ⟨-, g3, -, g5⟩, -⟩ := fit_says Dn.front.fit
  have hlog : dC.entry.logN = (sgOf cur).C.a := (switchCut_says Pl.cutSw).2.2.2.2.2.2.2.2.2.1
  have ht : (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss.length = (sgOf cur).t :=
    g3.trans Pl.poss
  have hx : ∀ y ∈ (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss, y < 2 ^ (sgOf cur).C.a := by
    intro y hy
    have := List.all_eq_true.1 g5 y hy
    rw [hlog] at this
    exact of_decide_eq_true this
  have hlt : ∀ y ∈ (D (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems, ltE y = true := by
    have hc2 := congrArg List.length Pl.cutS
    rw [List.length_map, List.length_take, List.length_drop] at hc2
    have hlen : 1 + cur.k < l.length := by
      have : min 2 (l.length - (1 + cur.k)) = 2 := hc2
      omega
    have := (hF (1 + cur.k) l[1 + cur.k] (List.getElem?_eq_getElem hlen)).2
    rw [kk_eq Pl.hk, Nat.add_assoc]
    exact this
  -- the values' clause behind the batching
  have hV : (Slf.idf (E := GE) (J := (sgOf next).cIn.J)).Holds
      (stmGk (sgOf next)
        (stepL p n rest.isEmpty (foldT t row L c (n.code, n.maskCode) id
          ((sRF K j cur o P row D).map noDigest)) t.st.groups.size Dk).k
        (stepL p n rest.isEmpty (foldT t row L c (n.code, n.maskCode) id
          ((sRF K j cur o P row D).map noDigest)) t.st.groups.size Dk).h row')
      (μOf (sgOf next) (sNext K rest.isEmpty j cur next o P row D)) := by
    cases V.colIs with
    | later hc oo k hL seat => exact val_later Pl I V.holds V.packs hc oo k hL seat hlt e1 Dn
    | first S₁ t₁ m tN' φN ψN hs hPe hc o0 o1 k sh frS hst hk1 hRw h3 hz hfm hfz hwid hL seat =>
      subst hPe
      exact val_first Pl I S₁ t₁ m tN' φN ψN hs V.holds V.packs hc o0 o1 k sh frS hst hk1 hRw h3
        hz hfm hfz hwid hL seat hlt ht hx e1 Dn
  obtain ⟨hP', hS', hF'⟩ := formRides_at hP hS hF Pl Dn
  cases rest with
  | nil =>
    have LF := formLast_at hP Pl I Dn
    obtain ⟨k1, k0⟩ := lastMember_kh LF.front.member
    simp only [List.isEmpty_nil] at hV
    rw [k1, k0] at hV
    exact ⟨⟨hP', hS'⟩, hF', row', _, n, _, _, _, _, ⟨LF, hV, rfl⟩⟩
  | cons nx rest' =>
    obtain ⟨tr', n', I', hL', seat'⟩ := formNext_at hP Pl I Dn K o P row D
    exact ⟨⟨hP', hS'⟩, hF', row', _, n, _, _, _, tr', I',
      ⟨hV, rfl, ColIs.later rfl _ _ hL' seat'⟩⟩

/-- **"Nothing is left untested" goes on over a stage.** -/
theorem hstep_left (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
    (col : ℕ → List UInt64) (h : BodyInv p K (PlanAll p) D (next :: rest) j cur l o t P col)
    (hl : ChainEnd.NothingLeft t.st) :
    ChainEnd.NothingLeft (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D).st := by
  obtain ⟨⟨hP, hS⟩, hF, row, L, c, nn, id, tN, tr, I, -⟩ := h
  exact formLeft_at p K D P hP hS hF I hl

/-- **The stages accept wherever the invariant holds in front of them.** -/
theorem body_yes (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (h : BodyInv p K (PlanAll p) D rest j cur l o t P col) :
    ∃ t', (stagesFrom guardedProximityTestParts p j cur rest l : Block T12 Unit).decide t
        ((bodyAll p K rest j cur l o t P col D).rs.map noDigest)
        (bodyAll p K rest j cur l o t P col D).gs = .ok t' :=
  let ⟨t', a, _⟩ := body_yes_of p K D (BodyInv p K (PlanAll p) D) (fun _ => True) (hstep_at p K D)
    (fun j cur l o t P col h =>
      let ⟨t', a⟩ := hbase_at p K D j cur l o t P col h
      ⟨t', a, trivial⟩) rest j cur l o t P col h
  ⟨t', a⟩

/-- **And nothing is left untested behind them, where nothing was in front.** -/
theorem body_left (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (h : BodyInv p K (PlanAll p) D rest j cur l o t P col) (hl : ChainEnd.NothingLeft t.st) :
    ∃ t', (stagesFrom guardedProximityTestParts p j cur rest l : Block T12 Unit).decide t
        ((bodyAll p K rest j cur l o t P col D).rs.map noDigest)
        (bodyAll p K rest j cur l o t P col D).gs = .ok t' ∧ ChainEnd.NothingLeft t'.st :=
  body_yes_of p K D
    (fun rest j cur l o t P col =>
      BodyInv p K (PlanAll p) D rest j cur l o t P col ∧ ChainEnd.NothingLeft t.st)
    (fun t' => ChainEnd.NothingLeft t'.st)
    (fun next rest j cur l o t P col h =>
      ⟨(hstep_at p K D next rest j cur l o t P col h.1).1,
        (hstep_at p K D next rest j cur l o t P col h.1).2,
        hstep_left p K D next rest j cur l o t P col h.1 h.2⟩)
    (fun j cur l o t P col h => hbase_left p K D j cur l o t P col h.1 h.2)
    rest j cur l o t P col ⟨h, hl⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.lastMember_kh
#print axioms Johnson.Prover.Link.hstep_at
#print axioms Johnson.Prover.Link.hstep_left
#print axioms Johnson.Prover.Link.body_yes
#print axioms Johnson.Prover.Link.body_left
