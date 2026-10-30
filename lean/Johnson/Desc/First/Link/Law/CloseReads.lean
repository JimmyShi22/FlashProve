-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CloseReads.lean: WHAT THE ROWS THAT K10's CLOSING WRITES READ OF THE
STATE IN FRONT, OFF THE CLOSING's OWN YES: their layout is the statement in front's own layout of
the frame's group; their fresh mask is the frame's mask. So `hF_of_end`'s premises hLm | hLk | hA
(HFOfEnd.lean) come from ShapesAre in front, and rows.fresh is a number of the state in front. And
the sentence on kept rows that `hCar_ren` asks of the switch's typed row (HCarRen.lean), from that
row's public equations. Theorems.

  `closing_reads`: closing P S g mask rs = .ok (out, S') ⊢ ∃ L m, S.layout g = some L ∧ out.layout =
    L ∧ mask = some m ∧ out.fresh = m. By `closing_iff`, `bat_inv_layout`,
    `fold_inv2`.
  `closeFrame_reads`: the same at the frame's closing.
  `layout_behind`: **closeFrame … = .ok x · the statement in front has the group Gr at the frame's
    group · ShapesAre S Gr lo kb no · LayoutAgrees lo kb ⊢ x.1.rows.layout has Gr's members and
    flags, and AgreesWith lo kb x.1.rows.layout.** By `layout_of_shapes`.
  `keptRows_of_pub`: r.lo = lo · (kb i = true ↔ i ∈ r.kept) ⊢ ∀ n, keptRowsAt r.lo r.mem r.kp n =
    keptRowsAt lo (memMain lo) (fun a => kb a.1 = true) n.
Limits. Book-keeping on the closing's text. Nothing on soundness.
-/
import Johnson.Desc.First.Close.Law.CarriedRows
import Johnson.Desc.First.Close.Law.LayoutOfShapes
import Johnson.Desc.First.Link.Law.KeptEquiv
import Johnson.Top.H0.K2Caller.CarryClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes Johnson.G
open VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First.K2Caller (SwRow)

theorem closing_reads {P : Plan} {S S' : Statement} {g : ℕ} {mask : Option ℕ}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    ∃ L m, S.layout g = some L ∧ out.layout = L ∧ mask = some m ∧ out.fresh = m := by
  obtain ⟨eB, es, rB, rs', -, -, m, hm, row, L, S1, hB, ⟨hk, hh⟩, hF⟩ :=
    (closing_iff P S g mask rs out S').1 h
  obtain ⟨G, x, -, -, -, -, hl0, -⟩ := bat_inv_layout ((bat_iff _ _ _ _ _ _ _).2 hB)
  obtain ⟨rE, rR, sum, eps, qs, gs, S2, -, -, -, -, -, -, -, -, b9⟩ :=
    fold_inv2 ((fold_iff _ _ _ _ _ _ _ _).2 hF)
  subst b9
  refine ⟨L, m, hl0, ?_, hm, rfl⟩
  show ({ L with k := P.k, h := P.h } : GroupLayout) = L
  rw [← hk, ← hh]

theorem closeFrame_reads {owed : Option ℕ} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f S es rs = .ok x) :
    ∃ L m, S.layout f.group = some L ∧ x.1.rows.layout = L ∧ f.mask = some m ∧
      x.1.rows.fresh = m := by
  obtain ⟨f', S'⟩ := x
  obtain ⟨-, Lk, -, G, -, -, rows, hc, rfl⟩ := (closeFrame_iff owed f S es rs f' S').1 h
  exact closing_reads ((closing_iff _ _ _ _ _ _ _).2 hc)

/-- **THE WRITTEN ROWS' LAYOUT, FROM ShapesAre IN FRONT.** -/
theorem layout_behind {owed : Option ℕ} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f S es rs = .ok x)
    {Gr : Group} (hG : S.groups[f.group]? = some Gr) {lo : List (OracleShape × ℕ)}
    {kb : Fin lo.length → Bool} {no : Fin lo.length → ℕ} (H : ShapesAre S Gr lo kb no)
    (hLA : LayoutAgrees lo kb) :
    x.1.rows.layout.members = Gr.members ∧ x.1.rows.layout.kept = Gr.kept ∧
      AgreesWith lo kb x.1.rows.layout := by
  obtain ⟨L, m, h1, h2, -, -⟩ := closeFrame_reads h
  obtain ⟨L', k1, k2, k3, k4⟩ := layout_of_shapes hG H hLA
  rw [h1] at k1
  obtain rfl : L = L' := Option.some.inj k1
  rw [h2]
  exact ⟨k3, k4, k2⟩

/-- The sentence on kept rows, from the typed row's public equations. -/
theorem keptRows_of_pub (r : SwRow) (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool)
    (hl : r.lo = lo) (hkb : ∀ i : Fin lo.length, kb i = true ↔ i.val ∈ r.kept) (n : ℕ) :
    keptRowsAt r.lo r.mem r.kp n = keptRowsAt lo (memMain lo) (fun a => kb a.1 = true) n := by
  subst hl
  unfold keptRowsAt
  by_cases h : n < r.lo.length
  · rw [dif_pos h, dif_pos h]
    by_cases hm : r.mem ⟨n, h⟩
    · have hm' : memMain r.lo ⟨n, h⟩ := hm
      rw [dif_pos hm, dif_pos hm']
      by_cases hk : kb ⟨n, h⟩ = true
      · have hk' : r.kp ⟨⟨n, h⟩, hm⟩ := (hkb _).1 hk
        rw [if_pos hk', if_pos hk]
      · have hk' : ¬ r.kp ⟨⟨n, h⟩, hm⟩ := fun c => hk ((hkb ⟨n, h⟩).2 c)
        rw [if_neg hk', if_neg hk]
    · have hm' : ¬ memMain r.lo ⟨n, h⟩ := hm
      rw [dif_neg hm, dif_neg hm']
  · rw [dif_neg h, dif_neg h]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.closing_reads
#print axioms VerifiableInference.Desc.LinkJoin.closeFrame_reads
#print axioms VerifiableInference.Desc.LinkJoin.layout_behind
#print axioms VerifiableInference.Desc.LinkJoin.keptRows_of_pub
