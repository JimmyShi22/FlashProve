-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SeedIs.lean: at one answer a message: behind a yes of the sending's decision the
record's sample rows of a new sampled message are just one row, the kind's row at the first seed
drawn and the message's own answer; said as a property of the statement, which travels.

Main names: rowsOf_one; SeedIs (the statement holds the message, marked, with just the kind's row at
a point and a factor that read as the seed ρ, and a target that reads as y); SeedIs.travels;
seedIs_behind.
With Port4.lean's coef_port_main and coef_port_mask the row's coefficients on the real entries are
those of the row of the library's oracle message at ρ.

What is not claimed. One answer a message. That the seeds read is a premise. Nothing on soundness,
on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Port8
import Johnson.Desc.K1.Law.KeepsOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob

variable {L : Type}

/-- At one answer the sample rows are one row. -/
theorem rowsOf_one (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (h1 : s.answers = 1) (sd : List E × E) (y : E) (hs : seeds[0]? = some sd)
    (hy : ys[0]? = some y) :
    rowsOf codes seeds o s ys = #[sampleRow (Msg.of codes s) o sd.1 sd.2 0 y] := by
  cases seeds with
  | nil => simp at hs
  | cons a t =>
    cases ys with
    | nil => simp at hy
    | cons b u =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs hy
      subst hs hy
      simp [rowsOf, h1]

/-- **The record's sample rows of a message are the kind's one row at a seed.** -/
def SeedIs (cs : Codes) (s : OracleShape) (St : Statement) (o : Nat)
    (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (y : GE) : Prop :=
  St.codes = cs ∧ ∃ x z β t, St.oracles[o]? = some x ∧ x.shape = s ∧ x.sampled = true ∧
    x.sampleRows = #[sampleRow (Msg.of cs s) o z β 0 t] ∧ ReadsOne cs s z β ρ ∧ readE t = y

/-- Every message has the shape, the mark and the sample rows that it had. -/
def SameMsgs (St St' : Statement) : Prop :=
  St'.codes = St.codes ∧ ∀ j : Nat,
    (St'.oracles[j]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      (St.oracles[j]?).map fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)

/-- **It travels.** -/
theorem SeedIs.travels {cs : Codes} {s : OracleShape} {St St' : Statement} {o : Nat}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedIs cs s St o ρ y)
    (hs : SameMsgs St St') : SeedIs cs s St' o ρ y := by
  obtain ⟨hc, x, z, β, t, hx, h1, h2, h3, h4, h5⟩ := h
  have e := hs.2 o
  rw [hx] at e
  obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨e1, e23⟩ := Prod.mk.inj e
  obtain ⟨e2, e3⟩ := Prod.mk.inj e23
  exact ⟨hs.1.trans hc, x', z, β, t, hx', e1.trans h1, e2.trans h2, e3.trans h3, h4, h5⟩

/-- **Behind a yes of the sending's decision.** -/
theorem seedIs_behind (P : Par) (rad : Nat → Nat) (owed : Option Nat) (d d' : DState L)
    (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (hC : condPort P rad = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    ∃ y, SeedIs P.codes (shapeAt P k) d'.st (d.st.oracles.size + k.val)
      (seedAt P (bitsZ P.codes (shapeAt P k)) ρ) y := by
  have hT := cond_tie P rad hC k hk
  have h1 : 0 < P.seeds := one_le_seeds P k hk
  obtain ⟨sd, hsd, hz, hβ⟩ := hρ ⟨0, h1⟩
  obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
    d.st.oracles.size (answersIn r₂) hf k.val k.isLt
  have hk' : (shapesOf P)[k.val].answers ≠ 0 := hk
  have hx : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles[d.st.oracles.size + k.val]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val] ys') := by
    show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k.val]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  obtain ⟨t, ht⟩ : ∃ t, ys'[0]? = some t :=
    ⟨ys'[0]'(Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hk') hy), List.getElem?_eq_getElem _⟩
  have hlen : sd.1.length = P.coordinates := cutSeeds_get _ _ _ _ sd (draw_len P r₁ r₂ hfit) hsd
  have hb := bits_le_coordinates P k hk
  have e3 : seedAt P (bitsZ P.codes (shapeAt P k)) ρ =
      (fun t => pointOf (ρ ⟨0, h1⟩).1 t.val, (ρ ⟨0, h1⟩).2) := by
    unfold seedAt ownSeeds
    exact dif_pos h1
  refine ⟨readE t, hc, _, sd.1, sd.2, t, hx, ?_, by simp [wr, hk'], ?_, ?_, rfl⟩
  · unfold wr
    split <;> rfl
  · have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
        ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k.val)
          (shapesOf P)[k.val] ys' := by simp [wr, hk']
    rw [hrows]
    exact rowsOf_one _ _ _ _ _ hT.one sd t hsd ht
  · rw [e3]
    refine ⟨by rw [hlen]; exact hb, fun u => ?_, hβ⟩
    have hu : u.val < P.coordinates := Nat.lt_of_lt_of_le u.isLt hb
    show readL sd.1 u.val = pointOf (ρ ⟨0, h1⟩).1 u.val
    unfold pointOf
    rw [dif_pos hu]
    exact hz ⟨u.val, hu⟩

end VerifiableInference.Desc.K1
