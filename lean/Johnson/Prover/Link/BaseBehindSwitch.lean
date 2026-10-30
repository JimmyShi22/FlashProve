-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BaseBehindSwitch.lean: behind the last code switch of a proximity test and its
batching, the record meets what the last part asks (`BaseFront`, Johnson/Prover/Link/BasePart.lean).

Main names (namespace `Johnson.Prover.Link`).
  `cfits_of_batch`   at a statement in order the batched row's form has the group's table's index
      bits
  `new_behind`, `rider_behind`   the new message's record behind the batching (the target's shape;
      in one group) and the record of the message that rode with it (as announced, untouched)
  `five_behind`   the last main code's message length is a power of two · the row's vector on the
      mask table has the mask code's message length · the law of fixing the lowest variable at 0
  `baseFront_behind` the soundness side's record `Did` of the last switch into an empty group, the
      statement behind the switch in order, the claim's form dense (`DenseForm`,
      OnBytes/Slice/BlkProxDense.lean), the seat of the two new messages in one tree (`ReadSeat`)
      with the declared number and shape: then `BaseFront` at the record behind, with the claim
      written out

Limits. Every premise is asked: the seat of the new tree and its number among them. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BaseBehind
import Johnson.Prover.Link.FormNextSwitch
import Johnson.Prover.Link.FormSwitchFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12
open H2K.Sw
open OnBytes.Slice.ProxRun (DenseForm fixLaw_of_dense)

/-- At a statement in order the batched row's form has the group's table's index bits. -/
theorem cfits_of_batch {S : Statement} {g : ℕ} {G : Group} {x : E} {row : GroupRow}
    (hO : InOrder S) (hG : S.groups[g]? = some G)
    (hc : Bat.combine (begun S g G) g ⟨layoutOf S G, runRows S G⟩ x = some row) :
    CFits ((layoutOf S G).k + (layoutOf S G).logEll) row.c := by
  have hE := extends_begun S g G
  have hG' := begun_group S g G hG
  have hOk := hO.groups g G hG
  have hOk' : GroupOk (begun S g G) { G with inRun := true, rows := #[] } :=
    hOk.extends hE rfl rfl rfl rfl
  have hL' : (begun S g G).layout g = some (layoutOf S G) := by
    rw [layout_eq _ g _ hG',
      layoutOf_extends (G' := { G with inRun := true, rows := #[] }) hE hOk rfl rfl rfl rfl]
  have hr' : ∀ r ∈ (runRows S G).toList,
      RowIn (begun S g G) { G with inRun := true, rows := #[] } r :=
    fun r h => RowIn.extends (G := G) hE (fun _ c => c) (hO.runRows g G hG r h)
  exact combine_cfits hG' hL' hOk' hr' hc

/-- The new message behind the batching: the target's shape; in one group. -/
theorem new_behind (D : Taken) (T : SwitchTarget) (gp : ℕ) (others : Array OracleNotice)
    (S : Statement) :
    ∃ x, (begun (D.stR T gp others S) gp (D.grown S)).oracles[S.oracles.size]? = some x ∧
      x.shape = T.shape ∧ x.groups = [gp] := by
  have hx := sent_first S ⟨T.shape, T.leafClass⟩ others
  obtain ⟨y, hy, hys, hyg⟩ : ∃ y, (ledgerShut (D.stA T others S) T
      S.oracles.size).oracles[S.oracles.size]? = some y ∧ y.shape = T.shape ∧ y.groups = [] := by
    unfold ledgerShut Taken.stA admitted
    split
    · unfold closeLedgers
      simp only [List.foldl_cons, List.foldl_nil, Array.getElem?_modify, if_true]
      unfold OnBytes.Slice.sentOf
      rw [hx]
      exact ⟨_, rfl, rfl, rfl⟩
    · simp only [Array.getElem?_modify, if_true]
      unfold OnBytes.Slice.sentOf
      rw [hx]
      exact ⟨_, rfl, rfl, rfl⟩
  have hJ : (D.stR T gp others S).oracles[S.oracles.size]? =
      some { y with groups := y.groups ++ [gp] } := by
    unfold Taken.stR Taken.stJ
    rw [(withRows_oracles gp D.rows _).1]
    exact joined_same _ _ _ _ _ y hy
  show ∃ x, (closeLedgers (D.stR T gp others S) _).oracles[S.oracles.size]? = some x ∧ _
  rw [ProxRun.closeLedgers_get, hJ]
  by_cases c : S.oracles.size ∈ (D.grown S).members.toList
  · refine ⟨ProxRun.shut { y with groups := y.groups ++ [gp] }, ?_, hys, ?_⟩
    · simp only [Option.map_some, if_pos c]
    · show y.groups ++ [gp] = _
      rw [hyg]
      rfl
  · refine ⟨{ y with groups := y.groups ++ [gp] }, ?_, hys, ?_⟩
    · simp only [Option.map_some, if_neg c]
    · show y.groups ++ [gp] = _
      rw [hyg]
      rfl

/-- The message that rode with it, behind the batching: as announced, untouched. -/
theorem rider_behind (D : Taken) (T : SwitchTarget) (gp : ℕ) (N : OracleNotice) (S : Statement)
    (hm : D.G.members = #[]) :
    (begun (D.stR T gp #[N] S) gp (D.grown S)).oracles[S.oracles.size + 1]? =
      some { shape := N.shape } := by
  rw [begun_at _ _ _ _ (by
    show S.oracles.size + 1 ∉ D.G.members.insertIdxIfInBounds _ _
    rw [hm]
    simp)]
  exact rider_at D T gp N S

section
variable {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {nc nz gp : ℕ}
  {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

/-- **Three of the five public clauses of `base_yes_five`** (Johnson/Prover/Link/BaseWhole.lean),
behind the last switch. -/
theorem five_behind {s s' : Sg} (hf : CsFit s s')
    (h : Did ft cols old (switchTargetStage nc nz 0 0 1) gp others S Bk roots S' Bk' out row lay
      theta D) (hG : D.G = { code := nc, maskCode := nz })
    (hZ : (S.codes.mask[nz]?).map codeOf = some s'.Z) (hp : DenseForm row.c) :
    s'.C.l = 2 ^ ceilLog2 s'.C.l ∧ row.d.size = s'.Z.l ∧ FixLaw row.c [zeroE] := by
  have hm : D.G.members = #[] := by rw [hG]
  have hk : D.G.kept = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  have lgC : ceilLog2 s'.C.l = Fmt.M1.lg s'.C.l := by
    conv_lhs => rw [hf.powC]
    exact ceilLog2_two_pow _
  have lgZ : ceilLog2 s'.Z.l = Fmt.M1.lg s'.Z.l := by
    conv_lhs => rw [hf.powZ]
    exact ceilLog2_two_pow _
  refine ⟨by rw [lgC]; exact hf.powC, ?_, fixLaw_of_dense row.c hp _ (h.vars hm hk hr)⟩
  rw [combine_dsize _ gp _ theta row h.row]
  show 2 ^ (lay.h + lay.logEllZk) = _
  rw [h.lay_eq hm hk]
  show 2 ^ (0 + (S.codes.mask.getD D.G.maskCode default).logEll) = _
  rw [hG]
  show 2 ^ (0 + ceilLog2 (S.codes.mask.getD nz default).ell) = _
  rw [show (S.codes.mask.getD nz default).ell = s'.Z.l from
    congrArg (·.l) (getD_of_map_some hZ), Nat.zero_add, lgZ]
  exact hf.powZ.symm

/-- **`BaseFront` behind the last switch.** t₃: the record behind. -/
theorem baseFront_behind {p : P12} {j' : ℕ} {next : Fmt.M1.Stage} {n : IoppStage} {t₃ : T12}
    (h : Did ft cols old (switchTargetStage n.code n.maskCode 0 0 1) gp (othersOf true n) S Bk
      roots S' Bk' out row lay theta D) (hG : D.G = { code := n.code, maskCode := n.maskCode })
    (hO : InOrder (D.stR (switchTargetStage n.code n.maskCode 0 0 1) gp (othersOf true n) S))
    (hst : t₃.st = S') (hbk : t₃.book = Bk') (hpass : t₃.pass = .claim row lay)
    (hmask : t₃.mask = out.others[0]?) (hstage : stageAt p j' next = some n) (hk : n.k = 0)
    (hC : (S.codes.base[n.code]?).map codeOf = some next.C)
    (hZ : (S.codes.mask[n.maskCode]?).map codeOf = some next.Z) (hp : DenseForm row.c)
    (h63 : 1 + ceilLog2 next.C.l ≤ 63) (a : ℕ) (tr : Tree)
    (R : ReadSeat S' Bk' [S.oracles.size] (S.oracles.size + 1) a tr)
    (hn : tr.number = (basePar p next).label)
    (hs : tr.shape = ⟨next.C.a, next.Z.a, #[3, 3], #[3, 3]⟩) :
    BaseFront p j' next t₃ row lay n
      ⟨dense (row.c.fixLow [zeroE]) (ceilLog2 next.C.l), row.d.map (·.triple), row.target.triple⟩
      S.oracles.size (S.oracles.size + 1) a := by
  have hm : D.G.members = #[] := by rw [hG]
  have hkp : D.G.kept = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  have hcodes : S'.codes = S.codes := h.codes
  obtain ⟨k, hkc, ek⟩ : ∃ k, S.codes.base[n.code]? = some k ∧ codeOf k = next.C := by
    cases hh : S.codes.base[n.code]? with
    | none => rw [hh] at hC; cases hC
    | some k => rw [hh] at hC; exact ⟨k, rfl, Option.some.inj hC⟩
  have kl : k.ell = next.C.l := congrArg (·.l) ek
  have hlay := h.lay_eq hm hkp
  -- the group behind the switch, and the layout
  have hgrp : (D.stR (switchTargetStage n.code n.maskCode 0 0 1) gp (othersOf true n)
      S).groups[gp]? = some (D.grown S) :=
    withRows_group gp D.rows _ _ (joined_group _ gp _ false D.G h.group)
  have elay : lay = layoutOf (D.stR (switchTargetStage n.code n.maskCode 0 0 1) gp
      (othersOf true n) S) (D.grown S) :=
    Option.some.inj (h.layout.symm.trans (layout_eq _ gp _ hgrp))
  have hcf : CFits (1 + ceilLog2 next.C.l) row.c := by
    have h1 := cfits_of_batch hO hgrp (x := theta) (row := row) (by rw [← elay]; exact h.row)
    rw [← elay, hlay] at h1
    have e2 : (S.codes.base.getD D.G.code default).logEll = ceilLog2 next.C.l := by
      rw [hG]
      show ceilLog2 (S.codes.base.getD n.code default).ell = _
      rw [Array.getD_eq_getD_getElem?, hkc]
      show ceilLog2 k.ell = _
      rw [kl]
    have e1 : (max (max 0 0) 1 : ℕ) = 1 := rfl
    simpa only [e1, e2] using h1
  obtain ⟨x, hx, hxs, hxg⟩ := new_behind D (switchTargetStage n.code n.maskCode 0 0 1) gp
    (othersOf true n) S
  have ho := rider_behind D (switchTargetStage n.code n.maskCode 0 0 1) gp
    (baseMaskNotice n.code n.maskCode 1 0) S hm
  rw [← h.st] at hx
  have ho' : S'.oracles[S.oracles.size + 1]? =
      some { shape := (baseMaskNotice n.code n.maskCode 1 0).shape } := by
    rw [h.st]
    exact ho
  rw [← kl]
  refine baseFront_of hpass hstage hk k (by rw [hst, hcodes]; exact hkc)
    (h.noKept hm hkp hr) (by rw [kl]; exact lastFits_of row _ hcf hp h63)
    (by rw [hlay]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (hmask.trans (did_mask h rfl)) ?_ (by rw [hbk]; exact lastTree_of _ S' Bk' _ _ a tr R hn hs)
  rw [hst]
  exact lastPair_of _ S' n _ _ x _ (by rw [hcodes]; exact hC) (by rw [hcodes]; exact hZ) hx ho'
    (by omega) hxs (by rw [hxg]; exact Nat.le_refl 1) rfl rfl rfl

end

end Johnson.Prover.Link
