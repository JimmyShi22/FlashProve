-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OpenedSent.lean: THE OUTPUT HEAD's 35 FORMS ARE WORTH 0, AND ITS CLAIM ON THE WEIGHTS IS TRUE, BEHIND AN HONEST SENDING OF ALL ITS ROUNDS: the sender
(Law/HeadSends.lean: head_sendsC) joined to "Opened at the truth" (Law/OpenedAll.lean: opened_all). FOR A TOY OF K06_law.
  headTruth_of_values   WHAT THE SENDER HANDS OF THE HEAD's OWN SUMCHECK (in K: the claimed sum's value is sigP; its own form is worth 0; the two end
                values are the tables AtP | UtP at the challenges) IS Law/OpenedHead.lean's HeadTruth (in E, at atWorld; the double sums at rH | rs).
  bare_*        where a hearing returns, a hidden scalar's variable is a bare slot or the empty form: its constant is written canonically.
  sent_opened   cells that hold (the norm's 17 identities everywhere; HonestHead), any masks, a WellLaid ledger with room, the tests on the request and
                the letters: AT THE DRAWS THAT ARE ALL THE ELEMENT 1 (the sender serves every draw; this theorem takes these) there are rounds rs, canonical, shaped
                as Head.lean's table of rounds says, at which hear F rs = some (H, G, []) · no draw is bad under the block's one rule (row_true, of
                NormTruth and two SumTrueG) · AND, at the ledger G behind, reads read as the stated sums of the cells: WeightTrue ∧ every form of every run of
                claims is 0 (the body of OpenedAt).
WHAT IT IS NOT. A TOY's STONE, NOT A MEMBER: the tape is built in Lean, not sent by the prover's program; no file in scope. NOT HERE: the block's decide on these rounds
(given, the seat's layings, the record): Law/K06Toy.lean · HONEST CELLS AT A REQUEST WITH COSTS: Law/HonestCells.lean meets HonestHead emptily. Holds, HonestHead, WellLaid, Fresh, WeightsOk and the sizes are premises. Nothing on soundness.
IMPORTED, NOT THIS FILE's: head_sendsC and all beneath it; row_true.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OpenedAll
import Johnson.Desc.Kinds.Law.HeadSends
import Johnson.Desc.Kinds.Law.CoveredNormAt
import Johnson.Desc.Kinds.Law.RowTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Aff Fork World)
open OnBytes.Desc.First.P1 (mle)
open Norm (lt ls d lPd T S2)
open Came (val vsG vsG_length)
open Part.MaskedSum (ownSlots)

/-! ## A hidden scalar's variable has a canonical constant -/

/-- The form's constant is written canonically. -/
def OkConst (f : Form) : Prop := okE f.const = true

theorem okConst_slot (j : Nat) : OkConst (Aff.slot j) := by
  show okE zeroE = true
  decide

theorem okConst_empty : OkConst ({} : Form) := by
  show okE zeroE = true
  decide

theorem getD_okConst (arr : Array Hid) (h : ∀ y, y ∈ arr.toList → OkConst y.var) (j : Nat) :
    OkConst (arr.getD j {}).var := by
  by_cases hj : j < arr.size
  · have : arr.getD j {} = arr[j]'hj := by simp [Array.getD, hj]
    rw [this]
    exact h _ (Array.getElem_mem_toList hj)
  · have : arr.getD j {} = {} := by simp [Array.getD, hj]
    rw [this]
    exact okConst_empty

theorem hide_okConst {v : List E} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid}
    (h : hide v F rs = some (c, G, left)) (j : Nat) : OkConst (c.getD j {}).var := by
  obtain ⟨_, h'⟩ := hide_some h
  obtain ⟨_, rfl⟩ := hide_unfold h'
  refine getD_okConst _ (fun y hy => ?_) j
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
  simp only [Array.getElem_toList, Array.getElem_mapIdx]
  exact okConst_slot _

theorem hiddenFrom_okConst {first n : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid}
    (h : hiddenFrom first n F rs = some (c, G, left)) (j : Nat) : OkConst (c.getD j {}).var := by
  unfold hiddenFrom at h
  cases hr : ((List.range n).mapM fun j => (F.shown (first + j)).map fun x =>
      ({ var := Aff.slot (first + j), shown := x } : Hid)) with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, _⟩ := h
    refine getD_okConst _ (fun y hy => ?_) j
    obtain ⟨i, _, e⟩ := mapM_mem _ _ _ hr y (by simpa using hy)
    cases hs : F.shown (first + i) with
    | none => simp [hs] at e
    | some x =>
      simp [hs] at e
      subst e
      exact okConst_slot _

theorem sumcheck_okEnds {z : Point} {n : Nat} {F0 F1 : Fork} {t left : List Fmt.RoundView} {s : Sum}
    (h : sumcheck z n F0 t = some (s, F1, left)) (j : Nat) : OkConst (s.end_ j).var := by
  unfold sumcheck at h
  obtain ⟨⟨c, s0⟩, G, l, h1, k1⟩ := bind_some h
  obtain ⟨rfl, _, _⟩ := pure_some k1
  unfold heardBy at h1
  obtain ⟨rs, Fx, l0, _, k1⟩ := bind_some h1
  obtain ⟨ld, Fy, l1, _, k2⟩ := bind_some k1
  obtain ⟨c', Fz, l2, _, k3⟩ := bind_some k2
  obtain ⟨Fl, Fw, l3, _, k4⟩ := bind_some k3
  obtain ⟨⟨hd, G'⟩, Fv, l4, _, k5⟩ := bind_some k4
  dsimp only at k5
  obtain ⟨G2, Fu, l5, _, k6⟩ := bind_some k5
  obtain ⟨_, Ft, l6, _, k7⟩ := bind_some k6
  obtain ⟨es, Fs, l7, h8, k8⟩ := bind_some k7
  obtain ⟨e9, _, _⟩ := pure_some k8
  simp only [Prod.mk.injEq] at e9
  obtain ⟨_, rfl⟩ := e9
  exact hiddenFrom_okConst h8 j

theorem batch_okConst {n rows : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {W : Array Hid} {g : E}
    (h : sendThenBatch n rows F rs = some ((W, g), G, left)) (j : Nat) :
    OkConst (W.getD j {}).var := by
  unfold sendThenBatch at h
  obtain ⟨⟨v, gs⟩, G1, l1, _, k1⟩ := bind_some h
  dsimp only at k1
  obtain ⟨W', G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨g', G3, l3, _, k3⟩ := bind_some k2
  obtain ⟨e4, _, _⟩ := pure_some k3
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, _⟩ := e4
  exact hide_okConst h2 j

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-! ## From the sender's values to HeadTruth -/

/-- **What the sender hands of the head's own sumcheck is HeadTruth.** -/
theorem headTruth_of_values [Heard] [Reads] (c : Cells) (G : Fork) (mask : Nat → E)
    (ent : Nat → Nat → Nat → E) (hzt : (FinalNorm.zt).size = lt)
    (hr : (logits.r).size = lt + lPd)
    (v0 : val (worldE G mask ent) logits.claimed.var = sigP c)
    (v1 : val (worldE G mask ent)
      (logits.left ((logits.end_ 0).shown * (logits.end_ 1).shown)) = 0)
    (v2 : val (worldE G mask ent) (logits.end_ 0).var =
      mle (lt + lPd) (AtP c) (logits.r.toList.map rd))
    (v3 : val (worldE G mask ent) (logits.end_ 1).var =
      mle (lt + lPd) (UtP c) (logits.r.toList.map rd))
    (ok1 : okE (logits.end_ 1).var.const = true) : HeadTruth c G mask ent where
  claimed := by
    apply eq_of_rd (okE_mulE _ _) (okE_sumTo _ _)
    have h2 : rd (2 : E) = 2 := by rw [rd_ofNat]; norm_num
    show rd ((2 ^ lPd : E) * atWorld G mask ent logits.claimed.var) = rd (trueSum c)
    rw [rd_mul, rd_pow, h2, rd_atWorld]
    have v0' : vW (worldE G mask ent) logits.claimed.var = sigP c := v0
    rw [v0', sigP_eq c hzt, mul_inv_cancel_left₀ (two_pow_ne_zero _)]
  end0 := by
    rw [rd_atWorld]
    exact v2.trans (mle_at_r (fA c) logits.r hr)
  end1 := by
    rw [rd_atWorld]
    exact v3.trans (mle_at_r (fU c) logits.r hr)
  ok1 := ok1
  row := by
    apply zero_of_rd (okE_atWorld G mask ent _ (okE_left _ _))
    rw [rd_atWorld]
    exact v1

/-! ## Behind an honest sending -/

theorem ok_one : okE oneE = true := by decide

theorem ok_replicate (n : Nat) : ∀ x ∈ List.replicate n oneE, okE x = true := fun x hx => by
  rw [List.eq_of_mem_replicate hx]
  exact ok_one

/-- **BEHIND AN HONEST SENDING OF ALL THE BLOCK's ROUNDS** (every draw the element 1: the decision's test on the rounds' shape refuses a 0 where the format's rule never draws one): the hearing returns, no draw is bad under the block's one
rule, and all 35 forms are worth 0 with the claim on the weights true, at the ledger behind. -/
theorem sent_opened (c : NCells) (mask : Nat → E) {F : Fork} (hW : WellLaid F)
    (hH : (dataOf c).Holds) (hC : HonestHead c.toCells) (hreq : Request.ok = true) (hy : y < V)
    (hw : WeightsOk) (hzt : (FinalNorm.zt).size = lt) (hls : ls ≤ lPd) (hdS : S2 ∣ d)
    (hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2))
    {m : Nat}
    (hF : Fresh F (9 + (ownSlots (callOf 0 (zS (List.replicate lt oneE).toArray) 2).all + 2 +
      (7 + (1 + (ownSlots (callOf 1 (List.replicate lt oneE).toArray 4).all + 4 +
        (1 + (ownSlots (callOf 1 FinalNorm.zt 2).all + 2 +
          (1 + (ownSlots (callOf 1 zP 2).all + 2 + m)))))))))) :
    ∃ (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork),
      Canonical rs ∧ hear F rs = some (H, G, []) ∧ Sound.NoBad (Came.rowRuleC c mask F) rs ∧
      WellLaid G ∧ Shaped [oneE] rs rounds ∧
      (let _ : Norm.Heard := H.1
       let _ : FinalNorm.Heard := H.2.1
       let _ : Heard := H.2.2
       let _ : FinalNorm.Reads := normReadsAtCells c
       let _ : Reads := readsAt c.toCells
       WeightTrue c.toCells G mask noEnt ∧
        ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0) := by
  obtain ⟨rs, H, G, hShape, hcan, hhear, hNT, hST, _, hWG, ePV, _, _, eS, eP, eN, eL, hval⟩ :=
    head_sendsC c mask hW hH (List.replicate lt oneE) (List.length_replicate ..)
      oneE oneE oneE oneE oneE oneE oneE
      (List.replicate ((zS (List.replicate lt oneE).toArray).size + 1) oneE)
      (List.replicate ((List.replicate lt oneE).toArray.size + 1) oneE)
      (List.replicate ((FinalNorm.zt).size + 1) oneE) (List.replicate (zP.size + 1) oneE)
      (List.length_replicate ..) (List.length_replicate ..) (List.length_replicate ..)
      (List.length_replicate ..) (ok_replicate _) ok_one ok_one ok_one ok_one ok_one ok_one
      ok_one (ok_replicate _) (ok_replicate _) (ok_replicate _) (ok_replicate _) hF
  have hRT : RowTruth c mask F rs :=
    ⟨hNT, fun pre tN tL Hn Fa Fb F1 SN SL a b c' d' =>
      ⟨(hST pre tN tL Hn Fa Fb F1 SN SL a b c' d').1,
        logits_form _ _ _ _ (hST pre tN tL Hn Fa Fb F1 SN SL a b c' d').2⟩⟩
  have hSh : Shaped [oneE] rs rounds := (hShape hzt).mono fun x hx => by
    simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hx
    have : x = oneE := by
      rcases hx with (((h | h) | h) | h) | h
      · exact h.2
      · rcases h with h | h | h | h
        · exact h
        · exact h
        · exact h
        · exact h.2
      · rcases h with h | h | h
        · exact h
        · exact h
        · exact h.2
      · rcases h with h | h
        · exact h
        · exact h.2
      · rcases h with h | h
        · exact h
        · exact h.2
    rw [this]
    exact List.mem_singleton.mpr rfl
  refine ⟨rs, H, G, hcan, hhear, Came.row_true c mask F hW hhear hRT, hWG, hSh, ?_⟩
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7⟩, ⟨n0, n1, n2, n3⟩, ⟨l0, l1, l2, l3⟩⟩ :=
    hval G (worldE G mask noEnt) (OnBytes.PscRun.Later.refl _) (fun _ _ _ => rfl)
  -- the sizes
  have sPV : H.1.pV.size = lt := by rw [ePV]; simp
  have sS : H.1.squares.r.size = lPd + lt := by
    rw [eS, ← ePV, List.size_toArray, List.length_take, List.length_replicate, zS_size _ sPV]
    omega
  have sP : H.1.products.r.size = lt := by
    rw [eP, List.size_toArray, List.length_take, List.length_replicate]
    simp
  have sN : H.2.1.normed.r.size = lt := by
    rw [eN, List.size_toArray, List.length_take, List.length_replicate, hzt]
    omega
  have szP : zP.size = lt + lPd := by
    unfold zP
    rw [Array.size_append, hzt]
    simp [halves]
  have sL : H.2.2.logits.r.size = lt + lPd := by
    rw [eL, List.size_toArray, List.length_take, List.length_replicate, szP]
    omega
  -- the two constants
  obtain ⟨Fa, Fb, lr, hNorm, _, _, _, hsL, _⟩ := Came.hear_parts hW hhear
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h4, _, _⟩ := norm_parts hW hNorm
  have h6 : okE (H.1.P.getD 6 {}).var.const = true := batch_okConst h4 6
  have ok1 : okE (H.2.2.logits.end_ 1).var.const = true := sumcheck_okEnds hsL 1
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  letI : FinalNorm.Reads := normReadsAtCells c
  letI : Reads := readsAt c.toCells
  have hN : NormTruthW (worldE G mask noEnt) c :=
    { sums := w1, prods := w2, sqRow := w3, sq0 := w4 0 (by omega), sq1 := w4 1 (by omega)
      prClaimed := w5, prRow := w6, prEnd := w7, nmRow := n1
      nm0 := by rw [vsG_length, hzt] at n2; exact n2
      nm1 := by rw [vsG_length, hzt] at n3; exact n3 }
  have hT : HeadTruth c.toCells G mask noEnt :=
    headTruth_of_values c.toCells G mask noEnt hzt sL l0 l1
      (by rw [vsG_length, szP] at l2; exact l2) (by rw [vsG_length, szP] at l3; exact l3) ok1
  exact opened_all H G c mask hreq hy hw hzt hls hdS hblock sPV sS sP sN hH hC hN h6 hT

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.headTruth_of_values
#print axioms VerifiableInference.Desc.Kinds.Head.Law.sent_opened
