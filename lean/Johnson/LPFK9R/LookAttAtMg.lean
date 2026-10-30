-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/LookAttAtMg.lean: AT THE TWELVE ATTENTION LINKS OF THE CLOSED CONSTANT, ON THE
SECOND ROAD: THE LOOKUP ARGUMENT's SEVEN (`LookRest`, Johnson/Desc/First/Link/Law/SortFour.lean)
AND THE FIELD k3k AT THE LINK's FOUR ENTRIES, AT THE WRITTEN LETTERS t3All, l3All (SortLook.lean);
AND SO THE SORT's OWN FIELDS (`AttOwesC`, LinkRestAtSort4C.lean) WHOLE: UNDER TWO PREMISES: THE
FIELD k3 AT "planes" AND AT "join". Theorems: calls, bridges, an assembly.

Whose the payments are. Other files': "objects" (entries 1 and 6) and "planes" (entry 1):
SortK3Objects.lean, SortK3ObjectsKap.lean, SortK3Planes.lean,
SortK3PlanesKap.lean, SortK3More.lean (its theorems named "_layers" ask m ≠ 24 alone, not the sort:
they serve here) · "join" (entry 2): SortK3Join.lean · beneath all: the lookups' theorems on the
bare runs.

What is new here. `att_facts`: what the scope gives at an attention link: Bs.G₀.W.p4 = true, and a
g below the number of groups with m = 2 * g + 1 and "the built segment at m has the group's number
g" (K5's files' own att_only and built_att, Johnson/H2K5R/LawAtEntry.lean) · the premise hr
of the theorems at "planes" ("the readers are there"): readersAt_att
(Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean) · the bridges as in LookLayersAtMg.lean.

What is said.
  `lookRest_att_at`: **LookRest L u psiAll Ok nU [(1, "objects"), (2, "join"), (1, "planes"), (6,
    "objects")] (t3All ..) (l3All ..)**, from h, O, g below the number of groups, p4, the plan a at
    g, the link at 2 * g + 1, hK : Ok q gives kxAll .. q, AND k3pl, k3jn: RunOk of the run at (1,
    "planes") and at (2, "join") at the lookups' own terms.
  `k3k_att_at`: **the field k3k** at the four entries: no such premise.
  `attOwesC_whole`: **AttOwesC m rdAll (parCOf A) Kx (t3All ..) (l3All ..) L u psiAll (k8NU ..) p
    tlD**, at the pinned letters, for every Kx that gives K3's promise, under k3pl, k3jn at the
    bare promise.

Limits. k3pl AND k3jn ARE PREMISES (the caller's clauses hb, hp', hkv stand behind them: other
files' pieces). The head and the opening are premises. h4 and k3 say what follows FROM the promise.
secondHashFunction alone. Nothing on soundness.

-/
import Johnson.LPFK9R.SortOwesAtMgC
import Johnson.LPFK9R.LookLayersAtMg
import Johnson.Desc.First.Link.Law.SortK3PlanesKap
import Johnson.Desc.First.Link.Law.SortK3Join
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.H2K5R.LawAtEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription claimsInBy)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.First.Att.P (att_only built_att)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.PhiAll
open VerifiableInference.OnPublicFiles (objVals objLen plVals jnVals pickLen k3_layers k3p_layers
        k3s_layers k3sL_layers k3k_layers k3d_layers k3g_layers k3f_layers k3p_planes k3s_planes
        k3sL_planes k3k_planes k3d_planes k3g_planes k3f_planes planes_entry_low)
open H2K5.Door (readersAt_att)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMg AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **WHAT THE SCOPE GIVES AT AN ATTENTION LINK.** -/
theorem att_facts (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .attention) :
    Bs.G₀.W.p4 = true ∧ ∃ g, g < Bs.G₀.W.NGr ∧ m = 2 * g + 1 ∧
      ∀ Xl, Bs.G₀.built[m]? = some Xl → Xl.g = g := by
  have hl := IM.subs_scope h.toAtMg.scope h.toAtMg.reads O m hm
  rw [hs] at hl
  obtain ⟨h4, g, hg, rfl⟩ := att_only O.pub O.blank hl
  obtain ⟨Xl', e1, _, e3, _⟩ := built_att O.pub O.blank h4 hg
  refine ⟨h4, g, hg, rfl, fun Xl e => ?_⟩
  obtain rfl : Xl' = Xl := Option.some.inj (e1.symm.trans e)
  exact e3

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (h4 : Bs.G₀.W.p4 = true)
  {g : ℕ} (hg : g < Bs.G₀.W.NGr) {a : Attention.Plan} (ha : Bs.G₀.W.A[g]? = some a)
  (hm : 2 * g + 1 < 25) (L : Link S Cl) (hlk : h.𝔇.lk (2 * g + 1) = some L)
include O h4 hg ha hm hlk

/-- **THE LOOKUP ARGUMENT's SEVEN AT AN ATTENTION LINK OF THE CONSTANT.** -/
theorem lookRest_att_at (u : HTailF2) (Ok : Phi BetaAll × Option Pub9 → Prop) (nU : Array ℕ)
    (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8)
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (k3pl : ∀ run, At L (1, "planes") run → RunOk Reading.gl atS (O9 (phiAll u psiAll) Ok (FullAt
      nU)) (Fx9 (phiAll u psiAll) Ok) run
      (plainTm (plVals hdCalls lmC jC bv pv)) (pickLen hdCalls lmC jC 3))
    (k3jn : ∀ run, At L (2, "join") run → RunOk Reading.gl atS (O9 (phiAll u psiAll) Ok (FullAt
      nU)) (Fx9 (phiAll u psiAll) Ok) run
      (plainTm (jnVals hdCalls lmC jC kv)) (pickLen hdCalls lmC jC 1)) :
    LookRest L u psiAll Ok nU [((1 : ℕ), "objects"), (2, "join"), (1, "planes"), (6, "objects")]
      (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) := by
  have hL := link_of_lk h O (2 * g + 1) L hlk
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have hr₀ := readersAt_att h4 ha
  exact {
  k3 := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · rw [t3_calls lmC jC lmD jD bv pv kv 1 (by omega), l3_calls lmC jC lmD jD 1 (by omega)]
      exact k3_layers h.toAtMg.scope h.toAtMg.reads O hm h24 hL u Ok nU hK (1, "objects") (by simp)
        run hr
    · rw [t3_join lmC jC lmD jD bv pv kv 2, l3_join lmC jC lmD jD 2]
      exact k3jn run hr
    · rw [t3_planes lmC jC lmD jD bv pv kv 1, l3_planes lmC jC lmD jD 1]
      exact k3pl run hr
    · rw [t3_digits lmC jC lmD jD bv pv kv 6 (by omega), l3_digits lmC jC lmD jD 6 (by omega)]
      exact k3_layers h.toAtMg.scope h.toAtMg.reads O hm h24 hL u Ok nU hK (6, "objects") (by simp)
        run hr
  k3d := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact k3d_layers h.toAtMg.scope h.toAtMg.reads O hm hL h24 (1, "objects") (by simp) run hr
    · exact k3d_join O h4 hg ha hL run hr
    · exact k3d_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run (planes_entry_low h24 ▸ hr)
    · exact k3d_layers h.toAtMg.scope h.toAtMg.reads O hm hL h24 (6, "objects") (by simp) run hr
  k3g := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact k3g_layers h.toAtMg.scope h.toAtMg.reads O hm hL h24 (1, "objects") (by simp) run hr
    · exact k3g_join O h4 hg ha hL run hr
    · exact k3g_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run (planes_entry_low h24 ▸ hr)
    · exact k3g_layers h.toAtMg.scope h.toAtMg.reads O hm hL h24 (6, "objects") (by simp) run hr
  k3f := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact k3f_layers h.toAtMg.scope h.toAtMg.reads O hm hL h24 u (1, "objects") (by simp) run hr
    · exact k3f_join O h4 hg ha hL u run hr
    · exact k3f_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ u run (planes_entry_low h24 ▸ hr)
    · exact k3f_layers h.toAtMg.scope h.toAtMg.reads O hm hL h24 u (6, "objects") (by simp) run hr
  k3p := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact k3p_layers h.toAtMg.scope h.toAtMg.reads O hm h24 hL (1, "objects") (by simp) run hr
    · exact k3p_join O h4 hg ha hL run hr
    · exact k3p_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run (planes_entry_low h24 ▸ hr)
    · exact k3p_layers h.toAtMg.scope h.toAtMg.reads O hm h24 hL (6, "objects") (by simp) run hr
  k3s := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact k3s_layers h.toAtMg.scope h.toAtMg.reads O hm h24 hL (1, "objects") (by simp) run hr
    · exact k3s_join O h4 hg ha hL run hr
    · exact k3s_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run (planes_entry_low h24 ▸ hr)
    · exact k3s_layers h.toAtMg.scope h.toAtMg.reads O hm h24 hL (6, "objects") (by simp) run hr
  k3sL := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact k3sL_layers h.toAtMg.scope h.toAtMg.reads O hm h24 hL (1, "objects") (by simp) run hr
    · exact k3sL_join O h4 hg ha hL run hr
    · exact k3sL_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run (planes_entry_low h24 ▸ hr)
    · exact k3sL_layers h.toAtMg.scope h.toAtMg.reads O hm h24 hL (6, "objects") (by simp) run hr }

/-- **k3k AT AN ATTENTION LINK OF THE CONSTANT.** -/
theorem k3k_att_at : ∀ o ∈ [((1 : ℕ), "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀
  run, At L o run →
    ∀ n e c' e₁, run n e = .ok (c', e₁) → kapOf e₁ = kapOf e := by
  have hL := link_of_lk h O (2 * g + 1) L hlk
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have hr₀ := readersAt_att h4 ha
  intro o ho run hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact k3k_layers h.toAtMg.scope h.toAtMg.reads O hm hL h24 (1, "objects") (by simp) run hr
  · exact k3k_join O h4 hg ha hL run hr
  · exact k3k_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run (planes_entry_low h24 ▸ hr)
  · exact k3k_layers h.toAtMg.scope h.toAtMg.reads O hm hL h24 (6, "objects") (by simp) run hr

end

/-- **THE SORT's OWN FIELDS AT AN ATTENTION LINK OF THE CONSTANT, WHOLE, UNDER k3 AT "planes" AND
"join".** -/
theorem attOwesC_whole (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .attention) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) :
    ∃ Xl A X, Bs.G₀.built[m]? = some Xl ∧ Xl.kind = 1 ∧ Bs.G₀.W.A[Xl.g]? = some A ∧
      Bs.G₀.built.toList[m]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (lmC jC lmD jD : ℕ)
        (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
        (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (u tlD : HTailF2),
        (∀ q, Kx q → kxAll lmC jC lmD jD q) →
        (∀ run, At L (1, "planes") run → RunOk Reading.gl atS
          (O9 (phiAll u psiAll) (fun q => OkAtt rdAll (P.parCOf A) (ProofFile.k8NU Bs.G₀ X) tlD q ∧ Kx q)
            (FullAt (ProofFile.k8NU Bs.G₀ X)))
          (Fx9 (phiAll u psiAll)
            (fun q => OkAtt rdAll (P.parCOf A) (ProofFile.k8NU Bs.G₀ X) tlD q ∧ Kx q)) run
          (plainTm (plVals hdCalls lmC jC bv pv)) (pickLen hdCalls lmC jC 3)) →
        (∀ run, At L (2, "join") run → RunOk Reading.gl atS
          (O9 (phiAll u psiAll) (fun q => OkAtt rdAll (P.parCOf A) (ProofFile.k8NU Bs.G₀ X) tlD q ∧ Kx q)
            (FullAt (ProofFile.k8NU Bs.G₀ X)))
          (Fx9 (phiAll u psiAll)
            (fun q => OkAtt rdAll (P.parCOf A) (ProofFile.k8NU Bs.G₀ X) tlD q ∧ Kx q)) run
          (plainTm (jnVals hdCalls lmC jC kv)) (pickLen hdCalls lmC jC 1)) →
        AttOwesC m rdAll (P.parCOf A) Kx (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) L u
          psiAll
          (ProofFile.k8NU Bs.G₀ X) p tlD := by
  obtain ⟨Xl, A, X, h1, h2, h3, h5, H⟩ := attOwesC_at h O m hm hs L p hlk seg drawB kp
  obtain ⟨h4, g, hg, rfl, hXg⟩ := att_facts h O m hm hs
  have ha : Bs.G₀.W.A[g]? = some A := by rw [← hXg Xl h1]; exact h3
  refine ⟨Xl, A, X, h1, h2, h3, h5, fun Kx lmC jC lmD jD bv pv kv u tlD hK k3pl k3jn => ?_⟩
  exact H Kx (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) u tlD
    (sortRest_of_look (tlD := tlD) (rests_all u) (fun _ hq => hq.1.core)
      (lookRest_att_at h O h4 hg ha hm L hlk u _ (ProofFile.k8NU Bs.G₀ X) lmC jC lmD jD bv pv kv
        (fun q hq => hK q hq.2) k3pl k3jn))
    (k3k_att_at h O h4 hg ha hm L hlk)

end LPFK9

#print axioms LPFK9.att_facts
#print axioms LPFK9.lookRest_att_at
#print axioms LPFK9.k3k_att_at
#print axioms LPFK9.attOwesC_whole
