-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/PolicyHonCells.lean: cells that hold the honest values give the honest numbers of
the acceptance policy, for a request within the policy (`PolOK`) and under the size bounds `Fit`.

The statements are about integer cells t of the head, at the reference sizes, whose ledger cells 99
to 119 are `phr` and whose arrays d1, d2, ex are `pd1`, `pd2`, `pex`
(Inst/Model/Head/PolicyCells.lean):
  `HoldsPolicy`               that hypothesis on the cells
  `K1_hon`, `K2_hon`, `ex_hon`  (no hypothesis but `HoldsPolicy` and v < V) the arrays K_1, K_2, ex
                              of the trace are the honest digits and looked-up values, at every
                              position and every token v < V
  `hidOf_hon`                 `PolOK`, `Fit` ⇒ the numbers read from the cells (`hidOf`,
                              Inst/Model/Head/PolicyRead.lean) are the honest numbers

Notation:
  the reference sizes: `nT`, `nD`, `nV` (Inst/Model/Head/Index.lean), those of `ppref`
    (`nums_ppref`).
Limits. lg is any function with the bound of `Fit`: that it is the array lg of the same cells is not
asked and not used. No cells are built here: `HoldsPolicy` is a hypothesis; the honest trace meets
it (`honP_holds`, Inst/Model/Head/PolicyHonTrace.lean).
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.Head.PolicyRead
import Inst.Model.Head.PolicyCells

set_option autoImplicit false

namespace Inst.Model.Head.Policy

open Inst.Model Finset

section
variable (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance ppref) (t : Cells ℤ)

/-- the cells hold the honest values of the policy -/
structure HoldsPolicy : Prop where
  hr : ∀ n i, 99 ≤ n → n < 120 → t.hr n i = phr lg pol x n i
  d1 : ∀ i, ∀ v < nV, d1 t v i = pd1 lg pol x i v
  d2 : ∀ i, ∀ v < nV, d2 t v i = pd2 lg pol x i v
  ex : ∀ i, ∀ v < nV, Head.ex t v i = pex lg pol x i v

variable {lg pol x t}

theorem b256_hon (hc : HoldsPolicy lg pol x t) (i : ℕ) {a n : ℕ} (h0 : 99 ≤ a) (h1 : a + n ≤ 120) :
    Ledger.b256 (fun m => Dv t m i) a n =
      Ledger.b256 (fun m => hidByte (Honest.honH lg pol x) m i) a n := by
  unfold Ledger.b256
  refine sum_congr rfl fun l hl => ?_
  have := mem_range.1 hl
  show 256 ^ l * (128 + t.hr (a + l) i) = _
  rw [hc.hr (a + l) i (by omega) (by omega), phr_byte]

/-- under `HoldsPolicy`, `PolOK` and `Fit`: the numbers read from the cells are the honest numbers
-/
theorem hidOf_hon (hc : HoldsPolicy lg pol x t) (hp : PolOK lg pol x) (hf : Fit ppref lg pol) :
    hidOf t = Honest.honH lg pol x := by
  have r := honByte_reads (x := x) hp hf
  have e : ∀ (a b : Hid),
      a.c = b.c → a.b = b.b → a.u = b.u → a.k = b.k → a.z = b.z → a.zs = b.zs → a = b := by
    rintro ⟨⟩ ⟨⟩ h1 h2 h3 h4 h5 h6
    simp only at h1 h2 h3 h4 h5 h6
    subst h1 h2 h3 h4 h5 h6
    rfl
  refine e _ _ (funext fun i => ?_) (funext fun i => ?_) (funext fun i => ?_) (funext fun i => ?_)
    (funext fun i => ?_) (funext fun i => ?_)
  · exact (b256_hon hc i (by norm_num) (by norm_num)).trans (r i).1
  · exact (b256_hon hc i (by norm_num) (by norm_num)).trans (r i).2.1
  · exact (b256_hon hc i (by norm_num) (by norm_num)).trans (r i).2.2.1
  · exact (b256_hon hc i (by norm_num) (by norm_num)).trans (r i).2.2.2.1
  · exact (b256_hon hc i (by norm_num) (by norm_num)).trans (r i).2.2.2.2.1
  · exact (b256_hon hc i (by norm_num) (by norm_num)).trans (r i).2.2.2.2.2

theorem K1_hon (hc : HoldsPolicy lg pol x t) (i : ℕ) {v : ℕ} (hv : v < nV) :
    K1 t (Req.of pol x) v i = (Honest.honD lg pol x).K1 v i := by
  rw [← pd1_K1 i (show v < ppref.V from hv), ← hc.d1 i v hv]
  simp [K1, Req.rho, Req.of, rhoR]

theorem K2_hon (hc : HoldsPolicy lg pol x t) (i : ℕ) {v : ℕ} (hv : v < nV) :
    K2 t (Req.of pol x) v i = (Honest.honD lg pol x).K2 v i := by
  rw [← pd2_K2 i (show v < ppref.V from hv), ← hc.d2 i v hv]
  simp [K2, Req.rho, Req.of, rhoR]

theorem ex_hon (hc : HoldsPolicy lg pol x t) (i : ℕ) {v : ℕ} (hv : v < nV) :
    Head.ex t v i = (Honest.honD lg pol x).ex v i := hc.ex i v hv

end

end Inst.Model.Head.Policy
