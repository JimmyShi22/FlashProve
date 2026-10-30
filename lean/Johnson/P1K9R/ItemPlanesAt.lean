-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/ItemPlanesAt.lean: `TableOwes.hitems`' CLAUSES AT THE LOOKUP ARGUMENT's ENTRIES
"planes" (the field k3i of `HitemsLeft`, Johnson/LPFE1R/HitemsAtConst.lean) AT THE
COMPOSED MEANING's CLOSED CONSTANT: at an attention link, entry (1, "planes"), and at the output
head's link, entry (2, "planes"). Theorems: calls of `item_planes_unit`
(Johnson/P1K9R/ItemPlanes.lean), after the form of Johnson/P1K9R/ItemObjectsAt.lean and
ItemObjectsHead.lean. A law file: no sub-protocol imports it.

What is said. Under the head h : `P5J.AtMgA` at the second hash function, L the constant's link m.
  `planes_in_order`: BY LEAN's KERNEL: at each of the twelve attention links and at link 24 the
    entry "planes" is of the sort's order. `planes_not_layers`: a negative test.
  `at_planes`: where the lot's readers at link m are r, the link states at that entry the kind's own
    run at the place's own lm and r: `k03_planes_raw`
    (Johnson/Desc/First/Look/K03StatesRaw.lean), read as `At`.
  `item_planes_core`: **the clause at the entry**, at whatever holes H whose second hole is silent
    there, general in the readers r and in two families bQ, pQ of forms off the fixed part: from: hr
    (the lot's readers are r); hlm (the place's lm is lmC); rB, rP (at a state that goes on from q
    the caller's forms ARE the families'); nB, nP (these name no slot); the table of terms there is
    `plainTm (plVals hdCalls lmC jC ..)` at the values `refValQ .. entUnit`; Ok gives `kxAll`; Ok
    holds of what is fixed; the public test says yes. NO SENTENCE "pinned" IS ASKED, and nothing on
    a full later state.
  `k3i_planes_att_at`: **at an attention link: the field's clause at (1, "planes")**, at the tables
    `tmA .. (t3All .. (bvAtt A) (pvAtt A) kv)`. `k3i_planes_head_at`: **at the output head's link:
    at (2, "planes")**, at `tmH .. (t3All .. (bvHead iU3) (pvHead iU3) kv)`; there the readers'
    second hole is filled, and the clause is had at the empty hole and carried over, where the run's
    own reader answers (`hrun_any_at`, Johnson/LPFE1R/HrunAnyAt.lean; `forms_of_run`,
    `formsIn_congr`, `itemIn_congr`, Johnson/Desc/First/Link/Law/HitemsHead.lean).

Limits. IMPLICATIONS. The head, hK, ok, hr, hlm and, at an attention link, hQ (the attention's
promise on what it heard) are premises: shown of no state here: the theorems may be idle. hr is paid
elsewhere from the public parameters (`readersAt_att`,
Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean; `readersAt_head`,
Johnson/Desc/First/Link/Law/SortK3PlanesRun.lean). Nothing on "join". The full size alone.
No soundness is claimed.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K9R.ItemPlanes
import Johnson.P1K9R.ItemObjectsHead
import Johnson.P1K9R.CallerAtLetters
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart orderOf)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.K3 (seatCalls planesRun)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.OnPublicFiles (plVals heard_at k3Ok_at k03_planes_raw k03_atS2_calls fits_at
        bitOf pinOf refValQ bitQ pinQ attReadersQ headReadersQ bvAtt pvAtt bvHead pvHead att_read_bits
        att_read_pin head_read_bits head_read_pin noSlots_bits_att noSlots_pin_att noSlots_bits_head
        noSlots_pin_head)
open K5Law
open IM (subAt)

/-- The entry "planes" is of the sort's order, at the twelve attention links and at link 24. -/
theorem planes_in_order :
    (∀ g < 12, (IM.k3Ix (2 * g + 1) false, "planes") ∈ orderOf (subAt (2 * g + 1))) ∧
      (IM.k3Ix 24 false, "planes") ∈ orderOf (subAt 24) := by
  decide +kernel

/-- A negative test: it is not of a layers' link's order. -/
theorem planes_not_layers : ¬ (IM.k3Ix 0 false, "planes") ∈ orderOf (subAt 0) := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The link states the kind's own run at the entry, at the place's own lm and the lot's readers. -/
theorem at_planes (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {L : Link S Claim} (hlk : h.𝔇.lk m = some L) {rr : K3.Readers S}
    (hr : K3Lot.readersAt (P5J.At.X Zp) m = some rr) :
    ∃ p : First.Look.P, First.Look.placeAt (P5J.At.X Zp) m false = some p ∧
      At L (IM.k3Ix m false, "planes") (planesRun (seatCalls K3Lot.ofForm) p.lm rr) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have eW : Bs.G₀.W = P5J.At.X Zp := ProofFile.Law.blankBy_W O.blank
  obtain ⟨Lk, p, h1, hp, h2⟩ := k03_planes_raw h.scope h.reads O m hm rr (by rw [eW]; exact hr)
  obtain rfl : Lk = L := Option.some.inj (h1.symm.trans ((h.laid.linkAt m).symm.trans hlk))
  refine ⟨p, by rw [← eW]; exact hp, ?_⟩
  unfold K9.statesOfLink at h2
  show ((Lk.hear[IM.k3Ix m false]?).bind fun b => b.claims.lookup "planes") = some _
  cases hb : Lk.hear[IM.k3Ix m false]? with
  | none =>
    rw [hb] at h2
    exact nomatch h2
  | some b =>
    rw [hb] at h2
    exact (K9.lookup_of_find "planes" _ _ h2).1

section
variable {W : Type} {L : Link S Claim} {u : HTailF2} {Ok : Q BetaAll → Prop} {lmC jC lmD jD : ℕ}

/-- **The clause at the entry "planes"**, at holes whose second hole is silent there. -/
theorem item_planes_core (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) (hlk : h.𝔇.lk m = some L) (hL : SegAt m (subAt m) L)
    (he : (IM.k3Ix m false, "planes") ∈ orderOf (subAt m)) {rr : K3.Readers S}
    (hr : K3Lot.readersAt (P5J.At.X Zp) m = some rr)
    (hlm : ∀ p, First.Look.placeAt (P5J.At.X Zp) m false = some p → p.lm = lmC)
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q) {bQ : ℕ × ℕ → Q BetaAll → Aff}
    {pQ : ℕ → Q BetaAll → Aff}
    (rB : ∀ i q e, Fx9 (phiAll u psiAll) Ok q e → bitOf rr e i.1 i.2 = bQ i q)
    (nB : ∀ i q, (bQ i q).slots = #[])
    (rP : ∀ col q e, Fx9 (phiAll u psiAll) Ok q e → pinOf rr e col = pQ col q)
    (nP : ∀ col q, (pQ col q).slots = #[])
    (tmOf : ℕ × String → ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8))
    (lenOf : ℕ × String → Q BetaAll → ℕ)
    (ht : tmOf (IM.k3Ix m false, "planes") = plainTm (plVals hdCalls lmC jC
      (fun q y k col => refValQ bQ entUnit (k, col) q y) fun q y col => refValQ pQ entUnit col q y))
    (rdW : W → ℕ × ℕ → MsgQ) (ok : ∀ a, on0At h z m a → Ok (fixed9 (phiAll u psiAll) a.1))
    (H : K9.LinkHoles) (a) (w : W) (ha : on0At h z m a)
    (hsil : H.silent (IM.k3Ix m false) "planes" a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) (h.𝔇.N.group m) (IM.k3Ix m false) "planes" a.1 =
      true) :
    ItemIn L (phiAll u psiAll) tmOf lenOf (K9.readersOfLink H L) (h.𝔇.N.group m) rdW a w
      (IM.k3Ix m false, "planes") := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (part_at h z hm a ha)
  obtain ⟨p, hp, hAt⟩ := at_planes h hm hlk hr
  rw [hlm p hp] at hAt
  have hq2 : (fixed9 (phiAll u psiAll) a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hfx : Fx9 (phiAll u psiAll) Ok (fixed9 (phiAll u psiAll) a.1) a.1 :=
    ⟨ok a ha, rfl, pubOf b, b, hq2, hb, goesOn_refl b⟩
  exact item_planes_unit H L (phiAll u psiAll) hdCalls lmC jC (seatCalls K3Lot.ofForm)
    k03_atS2_calls (fits_at false) (heard_at u false) rr _ _ tmOf lenOf _ rdW _
    (by rw [hL.order]; exact he) rfl hAt ht a w b hb (k3Ok_at hK false _ (ok a ha)) hsil hin
    (fun G _ k col => by
      rw [rB (k, col) _ a.1 hfx]
      exact caller_at_table bQ (k, col) _ (pubOf b) hq2 (nB _ _) G _)
    (fun G _ col => by
      rw [rP col _ a.1 hfx]
      exact caller_at_table pQ col _ (pubOf b) hq2 (nP _ _) G _)

variable {tm4 : ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8)}
  {kv : Q BetaAll → Bound GE8 → ℕ → GE8}

/-- **At an attention link: the field's clause at (1, "planes").** -/
theorem k3i_planes_att_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub)
    {g : ℕ} (hg : g < 12) (hlk : h.𝔇.lk (2 * g + 1) = some L)
    (hL : SegAt (2 * g + 1) (subAt (2 * g + 1)) L) (A : Attention.Plan)
    (hr : K3Lot.readersAt (P5J.At.X Zp) (2 * g + 1) = some (P.readersOfO A))
    (hlm : ∀ p, First.Look.placeAt (P5J.At.X Zp) (2 * g + 1) false = some p → p.lm = lmC)
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (hQ : ∀ q v g' h', Ok q → q.2 = some v → rdAll q.1 = some (g', h') →
      K5OkAt (P.parCOf A) g'.zk h' v.F)
    (rd : Phi BetaAll → Option (Forest.Heard × First.Att.P.Heard)) (c : First.Att.P.ParC)
    (rdW : W → ℕ × ℕ → MsgQ)
    (ok : ∀ a, on0At h z (2 * g + 1) a → Ok (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z (2 * g + 1) a →
      ItemIn L (phiAll u psiAll)
        (tmA rd c entUnit tm4 (t3All lmC jC lmD jD (bvAtt A) (pvAtt A) kv))
        (lenA rd c (l3All lmC jC lmD jD)) (h.𝔇.Rd (2 * g + 1)) (h.𝔇.N.group (2 * g + 1)) rdW a w
        (1, "planes") := by
  intro a w ha
  have hm : 2 * g + 1 < 25 := by omega
  have hne : 2 * g + 1 ≠ 24 := by omega
  have h24 : (2 * g + 1 == 24) = false := by simpa using hne
  have e1 : IM.k3Ix (2 * g + 1) false = 1 := by simp [IM.k3Ix, hne]
  have he := planes_in_order.1 g hg
  have hin := hin_at h hm z _ a ha he rfl
  rw [readers_at24 h (2 * g + 1), K9.readersAt_some _ _ _ _ L hlk] at hin ⊢
  have Hc := item_planes_core (u := u) (jC := jC) (lmD := lmD) (jD := jD) h z hm hlk hL he hr hlm hK
    (att_read_bits (phiAll u psiAll) Ok rdAll A (hrd_all u) hQ)
    (noSlots_bits_att rdAll (P.parCOf A))
    (att_read_pin (phiAll u psiAll) Ok rdAll A (hrd_all u) hQ)
    (noSlots_pin_att rdAll (P.parCOf A))
    (tmA rd c entUnit tm4 (t3All lmC jC lmD jD (bvAtt A) (pvAtt A) kv))
    (lenA rd c (l3All lmC jC lmD jD))
    (by
      rw [e1]
      show tmA rd c entUnit tm4 (t3All lmC jC lmD jD (bvAtt A) (pvAtt A) kv) (1, "planes") =
        plainTm (plVals hdCalls lmC jC (bvAtt A) (pvAtt A))
      simp [tmA, t3All, v3All])
    rdW ok _ a w ha
    (by
      show (if 2 * g + 1 == 24 then _ else fun _ _ _ => none :
        ℕ → String → S → Option K9.Read) _ _ _ = none
      rw [h24]
      rfl) hin
  rw [e1] at Hc
  exact Hc

/-- **At the output head's link: the field's clause at (2, "planes").** -/
theorem k3i_planes_head_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub)
    (hlk : h.𝔇.lk 24 = some L) (hL : SegAt 24 (subAt 24) L) (iU3 : ℕ)
    (hr : K3Lot.readersAt (P5J.At.X Zp) 24 = some (callerReaders (planesAt iU3)))
    (hlm : ∀ p, First.Look.placeAt (P5J.At.X Zp) 24 false = some p → p.lm = lmC)
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q) (hS : OnBytes.Model.Head.Shape)
    (p : Kinds.Head.Par) (kap : Phi BetaAll → Option Kinds.Head.Law.Seen)
    (rdW : W → ℕ × ℕ → MsgQ) (ok : ∀ a, on0At h z 24 a → Ok (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z 24 a →
      ItemIn L (phiAll u psiAll)
        (tmH hS iU3 p kap entUnit tm4 (t3All lmC jC lmD jD (bvHead iU3) (pvHead iU3) kv))
        (lenH hS iU3 p kap (l3All lmC jC lmD jD)) (h.𝔇.Rd 24) (h.𝔇.N.group 24) rdW a w
        (2, "planes") := by
  intro a w ha
  have hm : 24 < 25 := by omega
  have he := planes_in_order.2
  have hin := hin_at h hm z _ a ha he rfl
  have hrun := hrun_any_at h z hlk a ha (IM.k3Ix 24 false, "planes") (by decide) rfl
  rw [readers_at24 h 24, K9.readersAt_some _ _ _ _ L hlk] at hin ⊢
  have e0 := forms_of_run (K9.withSmall K9.LinkHoles.none) (K9.holesAt (P5J.At.X Zp) 24 24 L) L
    (IM.k3Ix 24 false) "planes" a.1 rfl hrun
  have hin0 := (formsIn_congr (h.𝔇.N.group 24) (IM.k3Ix 24 false) "planes" a.1 e0).trans hin
  exact itemIn_congr (e := (IM.k3Ix 24 false, "planes")) e0.symm
    (item_planes_core (u := u) (jC := jC) (lmD := lmD) (jD := jD) h z hm hlk hL he hr hlm hK
      (head_read_bits (phiAll u psiAll) Ok kapAll iU3 (hkap_all u))
      (noSlots_bits_head kapAll iU3)
      (head_read_pin (phiAll u psiAll) Ok kapAll iU3 (hkap_all u))
      (noSlots_pin_head kapAll iU3)
      (tmH hS iU3 p kap entUnit tm4 (t3All lmC jC lmD jD (bvHead iU3) (pvHead iU3) kv))
      (lenH hS iU3 p kap (l3All lmC jC lmD jD))
      (by
        show tmH hS iU3 p kap entUnit tm4 (t3All lmC jC lmD jD (bvHead iU3) (pvHead iU3) kv)
          (2, "planes") = plainTm (plVals hdCalls lmC jC (bvHead iU3) (pvHead iU3))
        simp [tmH, t3All, v3All])
      rdW ok _ a w ha rfl hin0)

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.planes_in_order
#print axioms VerifiableInference.Desc.LinkJoin.planes_not_layers
#print axioms VerifiableInference.Desc.LinkJoin.at_planes
#print axioms VerifiableInference.Desc.LinkJoin.item_planes_core
#print axioms VerifiableInference.Desc.LinkJoin.k3i_planes_att_at
#print axioms VerifiableInference.Desc.LinkJoin.k3i_planes_head_at
