-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/LookHeadAtMg.lean: AT THE HEAD's LINK (NUMBER 24) OF THE CLOSED CONSTANT, ON THE
SECOND ROAD: THE LOOKUP ARGUMENT's SEVEN (`LookRest`, Johnson/Desc/First/Link/Law/SortFour.lean)
AND THE FIELD k3k AT THE LINK's THREE ENTRIES, AT THE WRITTEN LETTERS t3All, l3All (SortLook.lean);
AND SO THE SORT's OWN FIELDS (`HeadOwesC`, LinkRestAtSort4C.lean) WHOLE: UNDER ONE PREMISE: THE
FIELD k3 AT "planes". Theorems: calls, bridges, an assembly. The sister of LookLayersAtMg.lean and
LookAttAtMg.lean.

Whose the payments are. Other files': "objects" (entries 2 and 7):
SortK3Objects.lean, SortK3ObjectsKap.lean, SortK3More.lean · "planes" (entry 2): SortK3Planes.lean,
SortK3PlanesKap.lean, SortK3More.lean, AND SortK3PlanesReaders.lean: readers_of_at_planes: "the
calling kind's readers are there" follows from what the link states at "planes": so the premise hr
of the theorems at "planes" falls. Beneath all: the lookups' theorems on the bare runs. (The head's
own "join" is no entry of the lookup's: it is the output head's kind's.)

What is new here. `eq24_of_head`: the head's link is number 24 · the bridges: link_of_lk; the
entries 2 | 7 are IM.k3Ix 24 false | true by computation; t3All, l3All read back at the three
entries; kapOf by definition.

What is said.
  `lookRest_head_at`: **LookRest L u psiAll Ok nU [(2, "objects"), (2, "planes"), (7, "objects")]
    (t3All ..) (l3All ..)**, from h, O, the link at 24, hK : Ok q gives kxAll .. q, AND k3pl: RunOk
    of the run at (2, "planes") at the lookups' own terms.
  `k3k_head_at`: **the field k3k** at the three entries: no such premise.
  `headOwesC_whole`: **HeadOwesC m W.hS iU3 24 4 (parOf ..) kapAll Kx (t3All ..) (l3All ..) L u
    psiAll (k8NU ..) p tlD**, at the pinned letters, for every Kx that gives K3's promise, under
    k3pl at the bare promise.

Limits. k3pl IS A PREMISE (the caller's clauses hb, hp' stand behind it: other files' pieces). The
head and the opening are premises. h4 and k3 say what follows FROM the promise. secondHashFunction alone.
Nothing on soundness.

-/
import Johnson.LPFK9R.SortOwesAtMgC
import Johnson.LPFK9R.LookLayersAtMg
import Johnson.Desc.First.Link.Law.SortK3PlanesKap
import Johnson.Desc.First.Link.Law.SortK3PlanesReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription claimsInBy)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.PhiAll
open VerifiableInference.OnPublicFiles (objVals objLen plVals pickLen k3_objects k3p_objects k3s_objects
        k3sL_objects k3k_objects k3d_objects k3g_objects k3f_objects k3p_planes k3s_planes k3sL_planes
        k3k_planes k3d_planes k3g_planes k3f_planes readers_of_at_planes)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMg AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- The head's link is number 24. -/
theorem eq24_of_head {m : ℕ} (hs : subAt m = .head) : m = 24 := by
  unfold subAt at hs
  split at hs
  · assumption
  · split at hs <;> exact nomatch hs

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (L : Link S Cl)
  (hlk : h.𝔇.lk 24 = some L)
include O hlk

/-- **THE LOOKUP ARGUMENT's SEVEN AT THE HEAD's LINK OF THE CONSTANT.** -/
theorem lookRest_head_at (u : HTailF2) (Ok : Phi BetaAll × Option Pub9 → Prop) (nU : Array ℕ)
    (lmC jC lmD jD : ℕ) (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8)
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (k3pl : ∀ run, At L (2, "planes") run → RunOk Reading.gl atS
      (O9 (phiAll u psiAll) Ok (FullAt nU)) (Fx9 (phiAll u psiAll) Ok) run
      (plainTm (plVals hdCalls lmC jC bv pv)) (pickLen hdCalls lmC jC 3)) :
    LookRest L u psiAll Ok nU [((2 : ℕ), "objects"), (2, "planes"), (7, "objects")] (t3All lmC jC
      lmD jD bv pv kv) (l3All lmC jC lmD jD) := by
  have hL := link_of_lk h O 24 L hlk
  have hm : 24 < 25 := by omega
  exact {
  k3 := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · rw [t3_calls lmC jC lmD jD bv pv kv 2 (by omega), l3_calls lmC jC lmD jD 2 (by omega)]
      exact k3_objects h.toAtMg.scope h.toAtMg.reads O hm hL false u Ok nU hK run hr
    · rw [t3_planes lmC jC lmD jD bv pv kv 2, l3_planes lmC jC lmD jD 2]
      exact k3pl run hr
    · rw [t3_digits lmC jC lmD jD bv pv kv 7 (by omega), l3_digits lmC jC lmD jD 7 (by omega)]
      exact k3_objects h.toAtMg.scope h.toAtMg.reads O hm hL true u Ok nU hK run hr
  k3d := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact k3d_objects h.toAtMg.scope h.toAtMg.reads O hm hL false run hr
    · obtain ⟨r₀, hr₀⟩ := readers_of_at_planes h.toAtMg.scope h.toAtMg.reads O hm hL (run := run) hr
      exact k3d_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run hr
    · exact k3d_objects h.toAtMg.scope h.toAtMg.reads O hm hL true run hr
  k3g := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact k3g_objects h.toAtMg.scope h.toAtMg.reads O hm hL false run hr
    · obtain ⟨r₀, hr₀⟩ := readers_of_at_planes h.toAtMg.scope h.toAtMg.reads O hm hL (run := run) hr
      exact k3g_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run hr
    · exact k3g_objects h.toAtMg.scope h.toAtMg.reads O hm hL true run hr
  k3f := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact k3f_objects h.toAtMg.scope h.toAtMg.reads O hm hL false u run hr
    · obtain ⟨r₀, hr₀⟩ := readers_of_at_planes h.toAtMg.scope h.toAtMg.reads O hm hL (run := run) hr
      exact k3f_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ u run hr
    · exact k3f_objects h.toAtMg.scope h.toAtMg.reads O hm hL true u run hr
  k3p := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact k3p_objects h.toAtMg.scope h.toAtMg.reads O hm hL false run hr
    · obtain ⟨r₀, hr₀⟩ := readers_of_at_planes h.toAtMg.scope h.toAtMg.reads O hm hL (run := run) hr
      exact k3p_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run hr
    · exact k3p_objects h.toAtMg.scope h.toAtMg.reads O hm hL true run hr
  k3s := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact k3s_objects h.toAtMg.scope h.toAtMg.reads O hm hL false run hr
    · obtain ⟨r₀, hr₀⟩ := readers_of_at_planes h.toAtMg.scope h.toAtMg.reads O hm hL (run := run) hr
      exact k3s_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run hr
    · exact k3s_objects h.toAtMg.scope h.toAtMg.reads O hm hL true run hr
  k3sL := by
    intro o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact k3sL_objects h.toAtMg.scope h.toAtMg.reads O hm hL false run hr
    · obtain ⟨r₀, hr₀⟩ := readers_of_at_planes h.toAtMg.scope h.toAtMg.reads O hm hL (run := run) hr
      exact k3sL_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run hr
    · exact k3sL_objects h.toAtMg.scope h.toAtMg.reads O hm hL true run hr }

/-- **k3k AT THE HEAD's LINK OF THE CONSTANT.** -/
theorem k3k_head_at : ∀ o ∈ [((2 : ℕ), "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o
  run →
    ∀ n e c e₁, run n e = .ok (c, e₁) → kapOf e₁ = kapOf e := by
  have hL := link_of_lk h O 24 L hlk
  have hm : 24 < 25 := by omega
  intro o ho run hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact k3k_objects h.toAtMg.scope h.toAtMg.reads O hm hL false run hr
  · obtain ⟨r₀, hr₀⟩ := readers_of_at_planes h.toAtMg.scope h.toAtMg.reads O hm hL (run := run) hr
    exact k3k_planes h.toAtMg.scope h.toAtMg.reads O hm hL hr₀ run hr
  · exact k3k_objects h.toAtMg.scope h.toAtMg.reads O hm hL true run hr

end

/-- **THE SORT's OWN FIELDS AT THE HEAD's LINK OF THE CONSTANT, WHOLE, UNDER k3 AT "planes".** -/
theorem headOwesC_whole (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (hs : subAt m = .head) (L : Link S Cl) (p : Where) (hlk : h.𝔇.lk m = some L)
    (seg : SegAt m (subAt m) L)
    (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp m = some p) :
    ∃ iU3 X, Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧ Bs.G₀.built.toList[m]? = some X ∧
      ∀ (Kx : Phi BetaAll × Option Pub9 → Prop) (lmC jC lmD jD : ℕ)
        (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
        (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (u tlD : HTailF2),
        (∀ q, Kx q → kxAll lmC jC lmD jD q) →
        (∀ run, At L (2, "planes") run → RunOk Reading.gl atS
          (O9 (phiAll u psiAll) (fun q => OkHead Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW
            Bs.G₀.W)) kapAll (ProofFile.k8NU Bs.G₀ X) tlD q ∧ Kx q)
            (FullAt (ProofFile.k8NU Bs.G₀ X)))
          (Fx9 (phiAll u psiAll) (fun q => OkHead Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW
            Bs.G₀.W)) kapAll (ProofFile.k8NU Bs.G₀ X) tlD q ∧ Kx q)) run
          (plainTm (plVals hdCalls lmC jC bv pv)) (pickLen hdCalls lmC jC 3)) →
        HeadOwesC m Bs.G₀.W.hS iU3 24 4 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) kapAll Kx
          (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) L u psiAll (ProofFile.k8NU Bs.G₀ X) p tlD
            := by
  obtain ⟨iU3, X, h1, h2, H⟩ := headOwesC_at h O m hm hs L p hlk seg drawB kp
  obtain rfl := eq24_of_head hs
  refine ⟨iU3, X, h1, h2, fun Kx lmC jC lmD jD bv pv kv u tlD hK k3pl => ?_⟩
  exact H Kx (t3All lmC jC lmD jD bv pv kv) (l3All lmC jC lmD jD) u tlD
    (sortRest_of_look (tlD := tlD) (rests_all u) (fun _ hq => hq.1.core)
      (lookRest_head_at h O L hlk u _ (ProofFile.k8NU Bs.G₀ X) lmC jC lmD jD bv pv kv
        (fun q hq => hK q hq.2) k3pl))
    (k3k_head_at h O L hlk)

end LPFK9

#print axioms LPFK9.eq24_of_head
#print axioms LPFK9.lookRest_head_at
#print axioms LPFK9.k3k_head_at
#print axioms LPFK9.headOwesC_whole
