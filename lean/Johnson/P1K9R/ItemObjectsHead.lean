-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/ItemObjectsHead.lean: `TableOwes.hitems`' CLAUSES AT THE LOOKUP ARGUMENT's ENTRIES
    "objects" (the field k3i of `HitemsLeft`, Johnson/LPFE1R/HitemsAtConst.lean) AT
    THE COMPOSED MEANING's CLOSED CONSTANT, AT THE OUTPUT HEAD's LINK; AND THAT STRUCTURE AT A
    LAYERS' LINK FROM ITS OTHER TWO FIELDS. Theorems: calls. A law file: no sub-protocol imports it.

Why. At the output head's link the readers' second hole is filled, so `item_objects`
    (Johnson/P1K9R/ItemObjects.lean) does not apply at the link's own readers. The road is that of
    Johnson/Desc/First/Link/Law/HitemsHead.lean: the readers ask the second hole only
    where the run itself is silent; where the run's own reader answers, the clause is had at the
    empty hole and carried over.

What is said. Under the head h : `P5J.AtMgA` at the second hash function, L the constant's link 24.
  `item_objects_head_at`: **the clause at one entry "objects" of link 24**, at φ := phiAll u psiAll,
      general in the tables of terms: from the same premises as `item_objects_at`
      (Johnson/P1K9R/ItemObjectsAt.lean). NEW CALLS: "the run's own reader answers"
      (`hrun_any_at`, Johnson/LPFE1R/HrunAnyAt.lean) · `forms_of_run`, `formsIn_congr`,
      `itemIn_congr` (HitemsHead.lean).
  `k3i_objects_head_at`: the field's clauses at its two entries "objects" (2 and 7), at the tables
      `tmH .. (t3All ..)`, `lenH .. (l3All ..)`.
  `hitemsLeft_layers`: AT A LAYERS' LINK: `HitemsLeft` at the parameters of `hitems_layers_at`, with
      ψ := psiAll, t3 := t3All .., l3 := l3All .., FROM ITS FIRST TWO FIELDS (ok, in8) AND hK: its
          third field is `k3i_layers_at`.
  `hitems_layers_two`: **THE FIELD hitems AT A LAYERS' LINK WITH NO CLAUSE ON THE LOOKUP's ENTRIES
      LEFT IN FRONT**: `hitems_layers_at` (HitemsAtConst.lean) CALLED at
      `hitemsLeft_layers`: so Lean holds that what is built here is what that theorem's premise
      asks.

Limits. IMPLICATIONS. The head, hK, ok and in8 (and, in `hitems_layers_two`, the sort's Take, hAt
    and h4, as in `hitems_layers_at`) are premises: shown of no state here: the theorems
    may be idle. Nothing on "planes" or "join". The full size alone. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K9R.ItemObjectsAt
import Johnson.LPFE1R.HrunAnyAt

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
open VerifiableInference.OnPublicFiles (objectsRun objVals atS2_seatOf hdAt t3Obj heard_at k3Ok_at)
open IM (subAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

section
variable {W : Type} {L : Link S Claim} {u : HTailF2} {Ok : Q BetaAll → Prop} {lmC jC lmD jD : ℕ}

/-- **The clause at one entry "objects" of the output head's link.** -/
theorem item_objects_head_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub)
    (hlk : h.𝔇.lk 24 = some L) (hL : SegAt 24 (subAt 24) L) (d : Bool)
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (tmOf : ℕ × String → ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8))
    (lenOf : ℕ × String → Q BetaAll → ℕ)
    (ht : tmOf (IM.k3Ix 24 d, "objects") = t3Obj lmC jC lmD jD d) (rdW : W → ℕ × ℕ → MsgQ)
    (ok : ∀ a, on0At h z 24 a → Ok (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z 24 a → ItemIn L (phiAll u psiAll) tmOf lenOf (h.𝔇.Rd 24) (h.𝔇.N.group 24)
      rdW a w (IM.k3Ix 24 d, "objects") := by
  intro a w ha
  have hm : 24 < 25 := by omega
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (part_at h z hm a ha)
  have he := objects_in_order 24 hm d
  have hin := hin_at h hm z _ a ha he rfl
  have hrun := hrun_any_at h z hlk a ha (IM.k3Ix 24 d, "objects") (by cases d <;> decide) rfl
  rw [readers_at24 h 24, K9.readersAt_some _ _ _ _ L hlk] at hin ⊢
  have e0 := forms_of_run (K9.withSmall K9.LinkHoles.none) (K9.holesAt (P5J.At.X Zp) 24 24 L) L
    (IM.k3Ix 24 d) "objects" a.1 rfl hrun
  have hin0 := (formsIn_congr (h.𝔇.N.group 24) (IM.k3Ix 24 d) "objects" a.1 e0).trans hin
  exact itemIn_congr (e := (IM.k3Ix 24 d, "objects")) e0.symm
    (item_objects _ L (phiAll u psiAll) (hdAt d) _ _ (OnPublicFiles.seatOf K3Lot.ofForm d)
      (atS2_seatOf d) (heard_at u d) tmOf lenOf _ rdW _ (by rw [hL.order]; exact he) rfl
      (at_objects h hm d hlk) ht a w b hb (k3Ok_at hK d _ (ok a ha)) rfl hin0)

variable {tm4 : ℕ → Q BetaAll → Bound GE8 → List (ℕ × GE8)}
  {bv : Q BetaAll → Bound GE8 → ℕ → ℕ → GE8} {pv kv : Q BetaAll → Bound GE8 → ℕ → GE8}

/-- **At the output head's link: the field's clauses at its two entries "objects".** -/
theorem k3i_objects_head_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub)
    (hlk : h.𝔇.lk 24 = some L) (hL : SegAt 24 .head L) (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (hS : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par)
    (kap : Phi BetaAll → Option Kinds.Head.Law.Seen) (rdW : W → ℕ × ℕ → MsgQ)
    (ok : ∀ a, on0At h z 24 a → Ok (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z 24 a → ∀ e ∈ [((2 : ℕ), "objects"), (7, "objects")],
      ItemIn L (phiAll u psiAll) (tmH hS iU3 p kap entUnit tm4 (t3All lmC jC lmD jD bv pv kv))
        (lenH hS iU3 p kap (l3All lmC jC lmD jD)) (h.𝔇.Rd 24) (h.𝔇.N.group 24) rdW a w e := by
  intro a w ha e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact item_objects_head_at (u := u) h z hlk hL false hK
      (tmH hS iU3 p kap entUnit tm4 (t3All lmC jC lmD jD bv pv kv))
      (lenH hS iU3 p kap (l3All lmC jC lmD jD))
      (by
        show tmH hS iU3 p kap entUnit tm4 (t3All lmC jC lmD jD bv pv kv) (2, "objects") = _
        simp [tmH, t3All, v3All, t3Obj, hdAt]) rdW ok a w ha
  · exact item_objects_head_at (u := u) h z hlk hL true hK
      (tmH hS iU3 p kap entUnit tm4 (t3All lmC jC lmD jD bv pv kv))
      (lenH hS iU3 p kap (l3All lmC jC lmD jD))
      (by
        show tmH hS iU3 p kap entUnit tm4 (t3All lmC jC lmD jD bv pv kv) (7, "objects") = _
        simp [tmH, t3All, v3All, t3Obj, hdAt]) rdW ok a w ha

/-- **At a layers' link: `HitemsLeft` from its first two fields.** -/
theorem hitemsLeft_layers (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) (hs : subAt m = .layers) (hlk : h.𝔇.lk m = some L) (hL : SegAt m .layers L)
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q) (p : OnBytes.Desc.First.K4.Par)
    (rdW : W → ℕ × ℕ → MsgQ) (ok : ∀ a, on0At h z m a → Ok (fixed9 (phiAll u psiAll) a.1))
    (in8 : ∀ a, on0At h z m a →
      K9.formsIn (h.𝔇.Rd m) (h.𝔇.N.group m) 4 "K8.equations" a.1 = true) :
    HitemsLeft (on0At h z m) L (phiAll u psiAll) Ok
      (tmL p entUnit tm4 (t3All lmC jC lmD jD bv pv kv)) (lenL p (l3All lmC jC lmD jD)) (h.𝔇.Rd m)
      (h.𝔇.N.group m) rdW (4, "K8.equations") [(1, "objects"), (6, "objects")] :=
  ⟨ok, in8, k3i_layers_at h z hm hs hlk hL hK p rdW ok⟩

/-- **The field hitems at a layers' link: no clause on the lookup's entries is left in front.** -/
theorem hitems_layers_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) {m : ℕ}
    (hm : m < 25) (hs : subAt m = .layers) (hlk : h.𝔇.lk m = some L) (hL : SegAt m .layers L) (hK :
    ∀ q, Ok q → kxAll lmC jC lmD jD q) {Fu : S → Prop} {nU : Array ℕ} {p :
    OnBytes.Desc.First.K4.Par} (A : LayersTake L u psiAll Ok Fu p nU entUnit tm4 (t3All lmC jC lmD
    jD bv pv kv) (l3All lmC jC lmD jD)) (run : ℕ → S → Except String (List Claim × S)) (hAt : At L
    (4, "K8.equations") run) (v4 : Q BetaAll → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map
    (·.2) = v4 q y) (rdW : W → ℕ × ℕ → MsgQ) (ok : ∀ a, on0At h z m a → Ok (fixed9 (phiAll u psiAll)
    a.1)) (in8 : ∀ a, on0At h z m a → K9.formsIn (h.𝔇.Rd m) (h.𝔇.N.group m) 4 "K8.equations" a.1 =
    true) :
    ∀ a w, on0At h z m a → ∀ e ∈ sortItems .layers, ItemIn L (phiAll u psiAll) (tmL p entUnit tm4
        (t3All lmC jC lmD jD bv pv kv)) (lenL p (l3All lmC jC lmD jD)) (h.𝔇.Rd m) (h.𝔇.N.group m)
        rdW a w e :=
  hitems_layers_at h z hm hs hlk hL A run hAt v4 h4 rdW
    (hitemsLeft_layers h z hm hs hlk hL hK p rdW ok in8)

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.item_objects_head_at
#print axioms VerifiableInference.Desc.LinkJoin.k3i_objects_head_at
#print axioms VerifiableInference.Desc.LinkJoin.hitemsLeft_layers
#print axioms VerifiableInference.Desc.LinkJoin.hitems_layers_two
