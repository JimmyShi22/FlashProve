-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SeedCarried.lean: no soundness is claimed.
The sendings' invariant K1.SeedIs («the statement holds the message, marked as sampled, with just the kind's one row at an OOD seed and an OOD answer»; Johnson/Desc/K1/Law/SeedIs.lean) and the reader K1.smpAt (Johnson/Desc/K1/Law/GoodSendForms.lean), carried from the ends of the two earlier chains into the last chain's state behind K14's second part (Laid, Johnson/Desc/Third/Law/LaidDef.lean). For three clauses on a member of the proximity test at the place W (hseed · hsmp · h2 of Johnson/LLT25R/LastMembers.lean's FiveAt).
  renamed_addUnit | renamed_add | renamed_fold   Row.renamed (OnBytes/Iop/Ground.lean) goes through the row's makers
  **sampleRow_renamed**   (K1.sampleRow m o z β i y).renamed n = K1.sampleRow m n z β i y: the kind's row on another message's number is the kind's row at that number
  seedIs_congr     SeedIs reads the codes and the one message
  **seedIs_old**   an elder message: SeedIs at the state in front of K14's second part ⇒ SeedIs behind it, same number, same OOD seed and answer
  **seedIs_copy**  Omega's copy: SeedIs at the shared chain's end, at Omega's number there ⇒ SeedIs behind, at the copy's number, same OOD seed and answer
  smpAt_congr      smpAt reads formsAt and ansAt alone
  **smpAt_of_seeds**  two statements and numbers with SeedIs at one OOD seed and answer: smpAt gives one value
Does not show. That SeedIs holds at either end. No member. Nothing on soundness.
-/
import Johnson.Desc.K1.Law.GoodSendForms
import Johnson.Desc.Third.Law.LaidDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Slice Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc
open VerifiableInference.Desc.Third (S₃ Border Laid)

theorem renamed_addUnit (r : Row) (o n : ℕ) (pt : Part) (idx : ℕ) (c : E) :
    (r.addUnit o pt idx c).renamed n = (r.renamed n).addUnit n pt idx c := by
  simp [Row.renamed, Row.addUnit, Array.map_push]

theorem renamed_add (r : Row) (o n : ℕ) (pt : Part) (v : Tensor) :
    (r.add o pt v).renamed n = (r.renamed n).add n pt v := by
  simp [Row.renamed, Row.add, Array.map_push]

theorem renamed_fold {α : Type} (o n : ℕ) (pt : Part) (f : α → ℕ) (g : α → E) :
    ∀ (l : List α) (r : Row),
      (l.foldl (fun r x => r.addUnit o pt (f x) (g x)) r).renamed n =
        l.foldl (fun r x => r.addUnit n pt (f x) (g x)) (r.renamed n)
  | [], _ => rfl
  | x :: l, r => by
    rw [List.foldl_cons, List.foldl_cons, renamed_fold o n pt f g l, renamed_addUnit]

theorem renamed_target (r : Row) (n : ℕ) (y : E) :
    ({ r with target := y } : Row).renamed n = { r.renamed n with target := y } := rfl

/-- **The kind's row on another message's number is the kind's row at that number.** -/
theorem sampleRow_renamed (m : K1.Msg) (o n : ℕ) (z : List E) (β : E) (i : ℕ) (y : E) :
    (K1.sampleRow m o z β i y).renamed n = K1.sampleRow m n z β i y := by
  have h0 : (({ kind := .sample } : Row).renamed n) = { kind := .sample } := by
    simp [Row.renamed]
  unfold K1.sampleRow
  by_cases h1 : (m.K != 0) = true <;> by_cases h2 : (m.Kzk != 0) = true <;>
    simp only [h1, h2, if_true, if_false, Bool.false_eq_true, renamed_target, renamed_add,
      renamed_fold, h0]

section
variable {cs : Codes} {sh : OracleShape} {ρ : (Fin (bitsZ cs sh) → GE) × GEˣ} {yv : GE}

/-- The invariant reads the codes and the one message. -/
theorem seedIs_congr {St St' : Statement} {o : ℕ} (hc : St'.codes = St.codes)
    (ho : St'.oracles[o]? = St.oracles[o]?) (h : K1.SeedIs cs sh St o ρ yv) :
    K1.SeedIs cs sh St' o ρ yv := by
  obtain ⟨hcs, x, z, β, t, hx, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hc.trans hcs, x, z, β, t, ho.trans hx, h1, h2, h3, h4, h5⟩

variable {S : Params.LinShape} {s₀ s : S₃} {b : Border} {y : OnBytes.Oracle} {G : OnBytes.Group}
  {dot : OnBytes.Row}

/-- **An elder message**: what held in front of K14's second part holds behind it. -/
theorem seedIs_old (L : Laid S s₀ s b y G dot) {i : ℕ} (h : K1.SeedIs cs sh s₀.st i ρ yv) :
    K1.SeedIs cs sh s.st i ρ yv := by
  have hi : i < s₀.st.oracles.size := by
    obtain ⟨_, x, _, _, _, hx, _⟩ := h
    exact (Array.getElem?_eq_some_iff.1 hx).1
  exact seedIs_congr L.codes (L.old i hi) h

/-- **Omega's copy**: what held at the shared chain's end, at Omega's number there, holds behind
K14's second part at the copy's number: the same OOD seed, the same OOD answer. -/
theorem seedIs_copy (L : Laid S s₀ s b y G dot) (hc : s₀.st.codes = cs)
    (h : K1.SeedIs cs sh b.shared.st b.shared.omega ρ yv) :
    K1.SeedIs cs sh s.st s₀.st.oracles.size ρ yv := by
  obtain ⟨_, x, z, β, t, hx, h1, _, h3, h4, h5⟩ := h
  obtain rfl : y = x := Option.some.inj (L.there.symm.trans hx)
  refine ⟨L.codes.trans hc, _, z, β, t, L.copy, h1, rfl, ?_, h4, h5⟩
  show y.sampleRows.map (·.renamed s₀.st.oracles.size) = _
  rw [h3]
  simp [sampleRow_renamed]

end

/-- The reader reads the first sample row's form and target alone. -/
theorem smpAt_congr (cs : Codes) (sh : OracleShape) (e : ℕ) {St St' : Statement} {o o' : ℕ}
    (hf : K1.formsAt cs sh St o = K1.formsAt cs sh St' o') (ha : K1.ansAt St o = K1.ansAt St' o') :
    K1.smpAt cs sh e St o = K1.smpAt cs sh e St' o' := by
  unfold K1.smpAt
  simp only [hf, ha]

/-- **Two statements and numbers that hold the invariant at one OOD seed and answer: the reader gives
one value.** -/
theorem smpAt_of_seeds {cs : Codes} {sh : OracleShape} (e : ℕ) {St St' : Statement} {o o' : ℕ}
    {ρ : (Fin (bitsZ cs sh) → GE) × GEˣ} {yv : GE} (hT : K1.Tie cs sh)
    (h : K1.SeedIs cs sh St o ρ yv) (h' : K1.SeedIs cs sh St' o' ρ yv) :
    K1.smpAt cs sh e St o = K1.smpAt cs sh e St' o' :=
  smpAt_congr cs sh e
    ((K1.forms_of_seedIs cs sh e St o ρ yv hT h).1.trans
      (K1.forms_of_seedIs cs sh e St' o' ρ yv hT h').1.symm)
    ((K1.forms_of_seedIs cs sh e St o ρ yv hT h).2.trans
      (K1.forms_of_seedIs cs sh e St' o' ρ yv hT h').2.symm)

end ToldDesc

#print axioms ToldDesc.sampleRow_renamed
#print axioms ToldDesc.seedIs_old
#print axioms ToldDesc.seedIs_copy
#print axioms ToldDesc.smpAt_congr
#print axioms ToldDesc.smpAt_of_seeds
