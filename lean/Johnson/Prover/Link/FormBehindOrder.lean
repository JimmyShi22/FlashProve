-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormBehindOrder.lean: a code switch of the proximity test and the batching
behind it keep the statement in order (`Means.InOrder`, Johnson/Desc/Means/Order.lean), stated over
what they have done (`Did`, Johnson/Desc/K12/Law/SwDid.lean), whatever trees the old rows stood in.

Why. `inOrder_switch` (Johnson/Prover/Link/SwitchOrder.lean) says the like over `SwitchFront`, which
is typed at written terms. `Did` keeps neither the joining's nor the adding's own acceptance: both
are shown here from its fields and public premises.

Main names (namespace `Johnson.Prover.Link`).
  `sample_on_did`   the sample row that the sending makes lies on the new message
  `join_did`   the new message joins its group
  `add_did`   every row that the switch makes is added
  `inOrder_did`   in order in front: in order with the claims as open rows, and behind the batching

By: `join_of` (Johnson/Prover/Link/FormSwitchPay.lean), `seat_stJ`
(Johnson/Prover/Link/SwitchSeat.lean), `made_add` (Johnson/Prover/Link/SwitchRows.lean),
`inOrder_join`, `inOrder_addRows` (Johnson/Prover/Link/SwitchOrder.lean).

Limits. Every premise is asked. The new group is asked to be empty, of the target's two codes. The
old claim's form is asked to be dense (`DenseForm`, OnBytes/Slice/BlkProxDense.lean) and to fit the
old message. Nothing on values or on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchOrder
import Johnson.Prover.Link.FormSwitchPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

variable {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget} {gp : ℕ}
  {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

/-- **The sample row that the sending makes lies on the new message.** -/
theorem sample_on_did (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hl : S.codes.lengthsOk = true) (hfit : Blk.shapeOk S.codes T.shape = true) :
    Means.RowOn (stSent S (Slice.sentOf T others)) S.oracles.size D.sample := by
  have hx : (stSent S (Slice.sentOf T others)).oracles[S.oracles.size]? =
      some { shape := T.shape } := sent_first S ⟨T.shape, T.leafClass⟩ others
  have hlen : (D.rS.drawn.elems.map E.ofTriple).length = (Send.cube S.codes T.shape).bits + 1 := by
    have := congrArg List.length h.seed
    rw [List.length_drop] at this
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hform : Own.formMade S.codes T.shape S.oracles.size
      ⟨(D.rS.drawn.elems.map E.ofTriple).take (Send.cube S.codes T.shape).bits, D.beta⟩ 0 =
      some D.smp := h.form
  have H := H2K.Out.sampleFit_of (stSent S (Slice.sentOf T others)) { shape := T.shape }
    [⟨(D.rS.drawn.elems.map E.ofTriple).take (Send.cube S.codes T.shape).bits, D.beta⟩] D.places hl
    hfit
    (fun sd hsd => by
      obtain rfl := List.mem_singleton.1 hsd
      show (Send.cube S.codes T.shape).bits ≤ (List.take _ _).length
      rw [List.length_take, hlen]
      omega)
    h.pad
  have hr : Desc.Plain.rowsFor S.codes T.shape S.oracles.size
      [⟨(D.rS.drawn.elems.map E.ofTriple).take (Send.cube S.codes T.shape).bits, D.beta⟩] [0]
      [D.alpha] #[] = some (#[D.sample], []) := by
    simp only [Desc.Plain.rowsFor, List.getElem?_cons_zero, hform]
    rfl
  exact H2K.Out.rowsFor_on _ _ _ hx _ H [0] [D.alpha] [] #[] #[D.sample]
    (fun r hr' => by simp at hr') hr D.sample (by simp)

/-- **The new message joins its group.** -/
theorem join_did (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hG : D.G = { code := T.shape.code, maskCode := T.shape.maskCode }) :
    Tw.L9.joinS (ledgerShut (D.stA T others S) T S.oracles.size) gp S.oracles.size false =
      .ok (D.stJ T gp others S) := by
  have hgr : S.groups[gp]? = some D.G := by
    rw [← shut_groups D T others S]
    exact h.group
  obtain ⟨S2, h2⟩ := ok_of_isSome (join_of D T gp others S hgr (by rw [hG]) h.fresh (by rw [hG])
    (by rw [hG]))
  obtain ⟨G, hG', -, rfl⟩ := joinS_ok h2
  obtain rfl : G = D.G := Option.some.inj (hG'.symm.trans h.group)
  exact h2

section Stage
variable {s s' : Sg} {nc nz : ℕ}

/-- **Every row that the switch makes is added.** -/
theorem add_did (hf : CsFit s s')
    (h : Did ft cols old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk'
      out row lay theta D)
    (ff : FoldedFit s s' S.codes nc nz old) (hG : D.G = { code := nc, maskCode := nz })
    (hsmall : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ 63 ∧ 2 ^ s'.h * s'.Z.l ≤ 2 ^ 63)
    (hc : Means.CFits (ceilLog2 s.C.l) old.c) (hp : DenseForm old.c)
    (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a) :
    D.rows.foldlM (fun S r => Tw.L9.addRowS S gp r)
      (D.stJ (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S) =
      .ok (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S) := by
  have hl := h.rows
  obtain ⟨W, hW, -⟩ := switchRows_eq _ old _ _ _ _ D.rows ff.kept ff.prog.masks
    (fun W1 h1 => by
      have hk := (switchFrame_fields _ old _ _ W1 h1).2.2.2.2.2.2.2.2.1
      rw [ff.prog.noKept] at hk
      exact List.length_eq_zero_iff.1 hk) hl
  obtain ⟨hF, hC, hZ, hSeat⟩ := seat_stJ hf D gp others S old nc nz ff.prog h.pad (by rw [hG])
    h.fresh hsmall W hW
  have eZl : W.zk.ell = s.Z.l := congrArg (·.l) hZ
  have eCl : W.code.ell = s.C.l := congrArg (·.l) hC
  have eCa : W.code.logN = s.C.a := congrArg (·.a) hC
  exact made_add (joined_group _ gp _ false D.G h.group) hW hF hSeat ff.kept ff.prog.masks
    (ff.d0.trans eZl.symm) (ff.d1.trans eZl.symm)
    (by
      show Means.CFits (ceilLog2 W.code.ell) old.c
      rw [eCl]
      exact hc) hp
    (fun x hx' => by
      rw [eCa]
      rw [h.positions] at hx'
      exact hx x (by simpa [Positions.ofDraws] using hx')) hl

/-- **The statement stays in order across a switch and the batching behind it.** -/
theorem inOrder_did (hf : CsFit s s')
    (h : Did ft cols old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk'
      out row lay theta D)
    (ff : FoldedFit s s' S.codes nc nz old) (hG : D.G = { code := nc, maskCode := nz })
    (hsmall : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ 63 ∧ 2 ^ s'.h * s'.Z.l ≤ 2 ^ 63)
    (hc : Means.CFits (ceilLog2 s.C.l) old.c) (hp : DenseForm old.c)
    (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a) (hS : Means.InOrder S)
    (hl : S.codes.lengthsOk = true)
    (hfit : Blk.shapeOk S.codes (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape = true) :
    Means.InOrder (D.stR (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S) ∧
      Means.InOrder S' := by
  have h2 : Means.InOrder (D.stA (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) others S) :=
    (hS.stSent (Slice.sentOf (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) others)).admitted
      S.oracles.size (switchTargetStage nc nz (s'.h + s'.g) s'.h 1).shape D.places #[D.sample]
      (fun r hr => by
        obtain rfl : r = D.sample := by simpa using hr
        exact sample_on_did h hl hfit)
  have h3 : Means.InOrder (ledgerShut
      (D.stA (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) others S)
      (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S.oracles.size) := by
    unfold ledgerShut
    split
    · exact Means.InOrder.onOracle h2 _ _ (fun _ => rfl) (fun _ => rfl)
    · exact h2
  have hO := inOrder_addRows gp D.rows _ _ (inOrder_join h3 (join_did h hG))
    (add_did hf h ff hG hsmall hc hp hx)
  refine ⟨hO, ?_⟩
  rw [h.st]
  exact hO.begun gp _ h.group_stR

end Stage

end Johnson.Prover.Link
