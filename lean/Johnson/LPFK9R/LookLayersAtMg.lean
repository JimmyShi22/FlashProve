-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/LookLayersAtMg.lean: AT THE TWELVE LAYERS' LINKS OF THE CLOSED CONSTANT: THE LOOKUP
ARGUMENT's SEVEN (`LookRest`, Johnson/Desc/First/Link/Law/SortFour.lean) AND THE FIELD k3k, AT THE
WRITTEN LETTERS t3All, l3All (SortLook.lean) AND AT ANY PROMISE THAT GIVES K3's PROMISE: ALL EIGHT
FROM THE HEAD. Theorems: calls and a bridge.
k3d, k3g, k3f have payers.

Whose the payments are:
Johnson/Desc/First/Link/Law/SortK3Objects.lean (k3_layers, k3p_layers, k3s_layers, k3sL_layers:
over its tie at_objects_is, an equation: the run that the link states at "objects" IS the lookup's
bare run) · SortK3ObjectsKap.lean (k3k_layers: over PutsKap.lean) · SortK3More.lean
(k3d_layers, k3g_layers, k3f_layers: over PutsMore.lean). A layers' link's order has
the lookup's "objects" alone, at the entries 1 (the calls' seat) and 6 (the digits').

What is new here. THE BRIDGES: (1) those files' hL speaks of the chain's m-th link, the lists of
what the constant's data name at m: link_of_lk (SortTiesAtMg.lean) · (2) their letters t3O, l3O
answer at "objects" alone; the lists' letters are t3All, l3All, which answer at every entry of the
lookup's: at the two entries they have one value (t3_calls, t3_digits, l3_calls, l3_digits) · (3)
their k3k ends in kapOf's text unfolded: kapOf (KapRuns.lean) by definition.

What is said.
  `lookRest_layers_at`: **LookRest L u psiAll Ok nU [(1, "objects"), (6, "objects")] (t3All ..)
    (l3All ..)**, from h, O, m < 25, m ≠ 24, h.𝔇.lk m = some L, and hK : Ok q gives kxAll .. q.
  `k3k_layers_at`: **the field k3k**, from h, O, m < 25, m ≠ 24, the link.

Limits. The head (AtMgA) and the opening are premises; hK is the promise's. k3 says what follows
FROM the promise. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortK3ObjectsKap
import Johnson.Desc.First.Link.Law.SortK3More
import Johnson.Desc.First.Link.Law.SortFour
import Johnson.Desc.First.Link.Law.SortLook
import Johnson.Desc.First.Link.Law.KapRuns
import Johnson.LPFK9R.SortTiesAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.PhiAll
open VerifiableInference.OnPublicFiles (k3_layers k3p_layers k3s_layers k3sL_layers k3k_layers
        k3d_layers k3g_layers k3f_layers)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **THE LOOKUP ARGUMENT's SEVEN AT A LAYERS' LINK OF THE CONSTANT.** -/
theorem lookRest_layers_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (h24 : m ≠ 24) (L : Link S Cl) (hlk : h.𝔇.lk m = some L) (u : HTailF2)
    (Ok : Phi BetaAll × Option Pub9 → Prop) (nU : Array ℕ) (lmC jC lmD jD : ℕ)
    (bv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → ℕ → GE8)
    (pv kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8)
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q) :
    LookRest L u psiAll Ok nU [((1 : ℕ), "objects"), (6, "objects")] (t3All lmC jC lmD jD bv pv kv)
      (l3All lmC jC lmD jD) where
  k3 := by
    have hL := link_of_lk h O m L hlk
    intro o ho run hr
    have k := k3_layers h.toAtMg.scope h.toAtMg.reads O hm h24 hL u Ok nU hK o ho run hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · rw [t3_calls lmC jC lmD jD bv pv kv 1 (by omega), l3_calls lmC jC lmD jD 1 (by omega)]
      exact k
    · rw [t3_digits lmC jC lmD jD bv pv kv 6 (by omega), l3_digits lmC jC lmD jD 6 (by omega)]
      exact k
  k3d := k3d_layers h.toAtMg.scope h.toAtMg.reads O hm (link_of_lk h O m L hlk) h24
  k3g := k3g_layers h.toAtMg.scope h.toAtMg.reads O hm (link_of_lk h O m L hlk) h24
  k3f := k3f_layers h.toAtMg.scope h.toAtMg.reads O hm (link_of_lk h O m L hlk) h24 u
  k3p := k3p_layers h.toAtMg.scope h.toAtMg.reads O hm h24 (link_of_lk h O m L hlk)
  k3s := k3s_layers h.toAtMg.scope h.toAtMg.reads O hm h24 (link_of_lk h O m L hlk)
  k3sL := k3sL_layers h.toAtMg.scope h.toAtMg.reads O hm h24 (link_of_lk h O m L hlk)

/-- **k3k AT A LAYERS' LINK OF THE CONSTANT.** -/
theorem k3k_layers_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) (m : ℕ) (hm : m < 25)
    (h24 : m ≠ 24) (L : Link S Cl) (hlk : h.𝔇.lk m = some L) :
    ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → kapOf e₁ = kapOf e :=
  k3k_layers h.toAtMg.scope h.toAtMg.reads O hm (link_of_lk h O m L hlk) h24

end LPFK9

#print axioms LPFK9.lookRest_layers_at
#print axioms LPFK9.k3k_layers_at
