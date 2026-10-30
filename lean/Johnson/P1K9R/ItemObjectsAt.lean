-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/ItemObjectsAt.lean: `TableOwes.hitems`' CLAUSES AT THE LOOKUP ARGUMENT's ENTRIES
    "objects" (the field k3i of `HitemsLeft`, Johnson/LPFE1R/HitemsAtConst.lean) AT
    THE COMPOSED MEANING's CLOSED CONSTANT, AT A LINK THAT IS NOT THE OUTPUT HEAD's. Theorems: calls
    of `item_objects` (Johnson/P1K9R/ItemObjects.lean). A law file: no sub-protocol imports it.

What is said. Under the head h : `P5J.AtMgA` at the second hash function, at link m < 25, L the
    constant's link there.
  `objects_in_order`: BY LEAN's KERNEL: at each of the 25 links both lookups' entries "objects" are
      of the sort's order. `objects_not_everywhere`: a negative test.
  `at_objects`: the link states at that entry the kind's own run: `k03_objects_raw`
      (Johnson/Desc/First/Look/K03StatesRaw.lean), read as `At`.
  `item_objects_at`: **the clause at one entry**, m not the output head's link, at φ := phiAll u
      psiAll, general in the tables of terms: from: the table of terms there is `t3Obj ..`
      (Johnson/Desc/First/Link/Law/SortK3Objects.lean); Ok gives `kxAll`; Ok holds of what
      is fixed at every state of the condition in front of the batching (`HitemsLeft`'s own first
      field). PAID BY CALLS: a part is there (`part_at`) · the public test says yes (`hin_at`) · the
      readers' second hole is empty away from the output head's link (by its text).
  `k3i_layers_at`: **AT A LAYERS' LINK: THE FIELD k3i WHOLE**, at the tables `tmL p entUnit tm4
      (t3All ..)`, `lenL p (l3All ..)`.
  `k3i_objects_att_at`: at an attention link: the field's clauses at its two entries "objects".

Limits. IMPLICATIONS. The head, hK and ok are premises: shown of no state here. Nothing at the
    output head's link; nothing on "planes" or "join". The full size alone. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K9R.ItemObjects
import Johnson.LPFE1R.HitemsAtConst
import Johnson.Desc.First.Link.Law.SortLook
import Johnson.Desc.First.Link.Law.SortK3Objects
import Johnson.Desc.First.Batch.ObjectsLawOrder
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart orderOf)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.OnPublicFiles (objectsRun objVals atS2_seatOf hdAt t3Obj heard_at k3Ok_at
        k03_objects_raw)
open IM (subAt)

/-- Both lookups' entries "objects" are of the sort's order, at each of the 25 links. -/
theorem objects_in_order : ∀ m < 25, ∀ d : Bool, (IM.k3Ix m d, "objects") ∈ orderOf (subAt m) := by
  decide +kernel

/-- A negative test: the output head's link's number of the entry is not of a layers' order. -/
theorem objects_not_everywhere : ¬ (IM.k3Ix 24 false, "objects") ∈ orderOf (subAt 0) := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The link states the kind's own run at the entry. -/
theorem at_objects (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25) (d : Bool)
    {L : Link S Claim} (hlk : h.𝔇.lk m = some L) :
    At L (IM.k3Ix m d, "objects") (objectsRun (OnPublicFiles.seatOf K3Lot.ofForm d)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, h1, h2⟩ := k03_objects_raw h.scope h.reads O m hm d
  obtain rfl : Lk = L := Option.some.inj (h1.symm.trans ((h.laid.linkAt m).symm.trans hlk))
  unfold K9.statesOfLink at h2
  show ((Lk.hear[IM.k3Ix m d]?).bind fun b => b.claims.lookup "objects") = some _
  cases hb : Lk.hear[IM.k3Ix m d]? with
  | none =>
    rw [hb] at h2
    exact nomatch h2
  | some b =>
    rw [hb] at h2
    exact (K9.lookup_of_find "objects" _ _ h2).1

section
variable {W : Type} {L : Link S Claim} {u : HTailF2} {Ok : Q BetaAll → Prop} {lmC jC lmD jD : ℕ}

/-- **The clause at one entry "objects", away from the output head's link.** -/
theorem item_objects_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) (h24 : (m == 24) = false) (hlk : h.𝔇.lk m = some L) (hL : SegAt m (subAt m) L)
    (d : Bool) (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (tmOf : ℕ × String → ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8))
    (lenOf : ℕ × String → Q BetaAll → ℕ)
    (ht : tmOf (IM.k3Ix m d, "objects") = t3Obj lmC jC lmD jD d) (rdW : W → ℕ × ℕ → MsgQ)
    (ok : ∀ a, on0At h z m a → Ok (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z m a → ItemIn L (phiAll u psiAll) tmOf lenOf (h.𝔇.Rd m) (h.𝔇.N.group m) rdW
      a w (IM.k3Ix m d, "objects") := by
  intro a w ha
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (part_at h z hm a ha)
  have he := objects_in_order m hm d
  have hin := hin_at h hm z _ a ha he rfl
  rw [readers_at24 h m, K9.readersAt_some _ _ _ _ L hlk] at hin ⊢
  refine item_objects _ L (phiAll u psiAll) (hdAt d) _ _ (OnPublicFiles.seatOf K3Lot.ofForm d)
      (atS2_seatOf d)
    (heard_at u d) tmOf lenOf _ rdW _ (by rw [hL.order]; exact he) rfl (at_objects h hm d hlk) ht
    a w b hb (k3Ok_at hK d _ (ok a ha)) ?_ hin
  show (if m == 24 then _ else fun _ _ _ => none : ℕ → String → S → Option K9.Read) _ _ _ = none
  rw [h24]
  rfl

variable {tm4 : ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8)}
  {bv : Q BetaAll → Bound GE8 → ℕ → ℕ → GE8} {pv kv : Q BetaAll → Bound GE8 → ℕ → GE8}

/-- **AT A LAYERS' LINK: THE FIELD k3i WHOLE.** -/
theorem k3i_layers_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) (hs : subAt m = .layers) (hlk : h.𝔇.lk m = some L) (hL : SegAt m .layers L)
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q) (p : OnBytes.Desc.First.K4.Par)
    (rdW : W → ℕ × ℕ → MsgQ) (ok : ∀ a, on0At h z m a → Ok (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z m a → ∀ e ∈ [((1 : ℕ), "objects"), (6, "objects")],
      ItemIn L (phiAll u psiAll) (tmL p entUnit tm4 (t3All lmC jC lmD jD bv pv kv))
        (lenL p (l3All lmC jC lmD jD)) (h.𝔇.Rd m) (h.𝔇.N.group m) rdW a w e := by
  have hne : m ≠ 24 := by
    rintro rfl
    exact absurd hs (by decide)
  have h24 : (m == 24) = false := by simpa using hne
  have hL' : SegAt m (subAt m) L := by rw [hs]; exact hL
  intro a w ha e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · have e1 : IM.k3Ix m false = 1 := by simp [IM.k3Ix, hne]
    have H := item_objects_at (u := u) h z hm h24 hlk hL' false hK
      (tmL p entUnit tm4 (t3All lmC jC lmD jD bv pv kv)) (lenL p (l3All lmC jC lmD jD))
      (by rw [e1]; simp [tmL, t3All, v3All, t3Obj, hdAt]) rdW ok a w ha
    rw [e1] at H
    exact H
  · have e1 : IM.k3Ix m true = 6 := by simp [IM.k3Ix, hne]
    have H := item_objects_at (u := u) h z hm h24 hlk hL' true hK
      (tmL p entUnit tm4 (t3All lmC jC lmD jD bv pv kv)) (lenL p (l3All lmC jC lmD jD))
      (by rw [e1]; simp [tmL, t3All, v3All, t3Obj, hdAt]) rdW ok a w ha
    rw [e1] at H
    exact H

/-- **At an attention link: the field's clauses at its two entries "objects".** -/
theorem k3i_objects_att_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub)
    {m : ℕ} (hm : m < 25) (hs : subAt m = .attention) (hlk : h.𝔇.lk m = some L)
    (hL : SegAt m .attention L) (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (rd : Phi BetaAll → Option (Forest.Heard × First.Att.P.Heard)) (c : First.Att.P.ParC)
    (rdW : W → ℕ × ℕ → MsgQ) (ok : ∀ a, on0At h z m a → Ok (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z m a → ∀ e ∈ [((1 : ℕ), "objects"), (6, "objects")],
      ItemIn L (phiAll u psiAll) (tmA rd c entUnit tm4 (t3All lmC jC lmD jD bv pv kv))
        (lenA rd c (l3All lmC jC lmD jD)) (h.𝔇.Rd m) (h.𝔇.N.group m) rdW a w e := by
  have hne : m ≠ 24 := by
    rintro rfl
    exact absurd hs (by decide)
  have h24 : (m == 24) = false := by simpa using hne
  have hL' : SegAt m (subAt m) L := by rw [hs]; exact hL
  intro a w ha e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · have e1 : IM.k3Ix m false = 1 := by simp [IM.k3Ix, hne]
    have H := item_objects_at (u := u) h z hm h24 hlk hL' false hK
      (tmA rd c entUnit tm4 (t3All lmC jC lmD jD bv pv kv)) (lenA rd c (l3All lmC jC lmD jD))
      (by rw [e1]; simp [tmA, t3All, v3All, t3Obj, hdAt]) rdW ok a w ha
    rw [e1] at H
    exact H
  · have e1 : IM.k3Ix m true = 6 := by simp [IM.k3Ix, hne]
    have H := item_objects_at (u := u) h z hm h24 hlk hL' true hK
      (tmA rd c entUnit tm4 (t3All lmC jC lmD jD bv pv kv)) (lenA rd c (l3All lmC jC lmD jD))
      (by rw [e1]; simp [tmA, t3All, v3All, t3Obj, hdAt]) rdW ok a w ha
    rw [e1] at H
    exact H

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.objects_in_order
#print axioms VerifiableInference.Desc.LinkJoin.objects_not_everywhere
#print axioms VerifiableInference.Desc.LinkJoin.at_objects
#print axioms VerifiableInference.Desc.LinkJoin.item_objects_at
#print axioms VerifiableInference.Desc.LinkJoin.k3i_layers_at
#print axioms VerifiableInference.Desc.LinkJoin.k3i_objects_att_at
