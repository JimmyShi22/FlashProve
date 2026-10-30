-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyMemberBack.lean: THEOREMS. **Every word of the format that reads as a code word is the word sent of KeyMember.lean**: so the premise Sendable shuts out no encoding randomness with which a word of the format can be made.
OBJECT: Sendable | sent of KeyMember.lean. USER: none yet. LETTERS: cs · s · e.
  enc_co        the encoder of one row goes through every additive map to the base field that is linear over it (the generator is over the base field)
  row_base      one row under a code of at most 2^32 positions with room for message and tail: if every symbol of the code word lies in the base field, so does every entry of the message and of the tail
  sendable_of_up   **CodeOK → a word as sent reads as enc m r → Sendable m r**
  eq_sent          and the word is sent m r
  seedIs_map | seedIs_bare   SeedIs outlasts a map on the messages' entries that keeps shape, mark and sample rows: so the taking away of the ledgers
  exists_not_of_share | no_clash_has   where the collisions are at most a share 2^-K of the seeds, K > 0: there is a seed that is none
What is not claimed. Nothing on how a program draws its randomness: the sentence is on the format: whatever is drawn, if the word is a word of the format and a code word, then it is sent m r at a Sendable pair. Nothing on soundness or on hiding.

-/
import Johnson.RunOne.KeyMember

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1
open Johnson.RunOne.KeySendErr (qE badOwn)

/-- The second and the third coordinate of an element of the extension field. -/
def co1 : GE →+ GF := { toFun := fun y => y.c1, map_zero' := rfl, map_add' := fun _ _ => rfl }
def co2 : GE →+ GF := { toFun := fun y => y.c2, map_zero' := rfl, map_add' := fun _ _ => rfl }

theorem co1_lin (w : GF) (y : GE) : co1 (algebraMap GF GE w * y) = w * co1 y := by
  rw [← Algebra.smul_def]
  exact Code.Cubic.smul_c1 w y

theorem co2_lin (w : GF) (y : GE) : co2 (algebraMap GF GE w * y) = w * co2 y := by
  rw [← Algebra.smul_def]
  exact Code.Cubic.smul_c2 w y

theorem enc_co (π : GE →+ GF) (hπ : ∀ w y, π (algebraMap GF GE w * y) = w * π y) (C : Fmt.M1.Code) (a : Nat) (m : Fin C.l → GE) (r : Fin C.r → GE) (p : Fin (2 ^ C.a)) :
    (ldOf C a).enc (fun j => algebraMap GF GE (π (m j))) (fun q => algebraMap GF GE (π (r q))) p () = algebraMap GF GE (π ((ldOf C a).enc m r p ())) := by
  show (∑ q, genOf C p (Fin.castAdd C.l q) * algebraMap GF GE (π (r q))) + ∑ j, genOf C p (Fin.natAdd C.r j) * algebraMap GF GE (π (m j)) =
    algebraMap GF GE (π ((∑ q, genOf C p (Fin.castAdd C.l q) * r q) + ∑ j, genOf C p (Fin.natAdd C.r j) * m j))
  simp only [genOf, map_add, map_sum, hπ, map_mul]

theorem mem_of_co {y : GE} (h1 : co1 y = 0) (h2 : co2 y = 0) : y ∈ (algebraMap GF GE).range :=
  ⟨y.c0, Code.Cubic.ext rfl h1.symm h2.symm⟩

theorem co_of_mem {y : GE} (h : y ∈ (algebraMap GF GE).range) : co1 y = 0 ∧ co2 y = 0 := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- **One row: a code word over the base field has its message and its tail over the base field.** -/
theorem row_base (C : Fmt.M1.Code) (a : Nat) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) (m : Fin C.l → GE) (r : Fin C.r → GE)
    (h : ∀ p, (ldOf C a).enc m r p () ∈ (algebraMap GF GE).range) :
    (∀ j, m j ∈ (algebraMap GF GE).range) ∧ ∀ q, r q ∈ (algebraMap GF GE).range := by
  have key : ∀ π : GE →+ GF, (∀ w y, π (algebraMap GF GE w * y) = w * π y) → (∀ p, π ((ldOf C a).enc m r p ()) = 0) → (∀ j, π (m j) = 0) ∧ ∀ q, π (r q) = 0 := by
    intro π hπ h0
    have z : (ldOf C a).enc (fun j => algebraMap GF GE (π (m j))) (fun q => algebraMap GF GE (π (r q))) = 0 := by
      funext p u
      cases u
      rw [enc_co π hπ, h0 p, map_zero]
      rfl
    obtain ⟨zm, zr⟩ := (ldOf_laws C a ha hk).inj _ _ z
    exact ⟨fun j => Code.Cubic.algebraMap_injective ((congrFun zm j).trans (map_zero _).symm),
      fun q => Code.Cubic.algebraMap_injective ((congrFun zr q).trans (map_zero _).symm)⟩
  obtain ⟨a1, b1⟩ := key co1 co1_lin fun p => (co_of_mem (h p)).1
  obtain ⟨a2, b2⟩ := key co2 co2_lin fun p => (co_of_mem (h p)).2
  exact ⟨fun j => mem_of_co (a1 j) (a2 j), fun q => mem_of_co (b1 q) (b2 q)⟩

theorem upRow_mem : ∀ (b : Bool) (t : RowTy b), b = true → upRow b t ∈ (algebraMap GF GE).range
  | true, t, _ => ⟨t, rfl⟩
  | false, _, h => absurd h (by decide)

theorem upRow_inj : ∀ b : Bool, Function.Injective (upRow b)
  | true => (Code.Cubic.algebraMap_injective : Function.Injective (algebraMap GF GE))
  | false => fun _ _ h => h

variable {cs : Codes} {s : OracleShape} {e : Nat}

/-- **A word of the format that reads as a code word: its message and randomness are Sendable.** -/
theorem sendable_of_up (hC : CodeOK cs s) {f : (portOmZ cs s e).Str} {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE}
    (hf : (portOmZ cs s e).upW f = (portCode cs s).enc m r) : Sendable cs s m r := by
  intro h1
  have key : ∀ i : Fin s.mainRows, (∀ j : Fin (pMain cs s).ell, m (Sum.inl (i, j)) ∈ (algebraMap GF GE).range) ∧
      ∀ q : Fin (pMain cs s).r, r (Sum.inl (i, q)) ∈ (algebraMap GF GE).range := fun i =>
    row_base (cMain cs s) (aOf cs s) hC.a1 hC.k1 (fun j => m (Sum.inl (i, j))) (fun q => r (Sum.inl (i, q))) fun p => by
      have e1 : upRow (tabF cs s (Sum.inl p)) (f (Sum.inl p) (i, ())) = (portCode cs s).enc m r (Sum.inl p) (i, ()) :=
        congrFun (congrFun hf (Sum.inl p)) (i, ())
      have e2 : (ldOf (cMain cs s) (aOf cs s)).enc (fun j => m (Sum.inl (i, j))) (fun q => r (Sum.inl (i, q))) p () =
          (portCode cs s).enc m r (Sum.inl p) (i, ()) := rfl
      rw [e2, ← e1]
      exact upRow_mem _ _ (by simp [tabF, h1])
  exact ⟨fun x => (key x.1).1 x.2, fun q => (key q.1).2 q.2⟩

/-- **And it is the word sent.** -/
theorem eq_sent (hC : CodeOK cs s) {f : (portOmZ cs s e).Str} {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE}
    (hf : (portOmZ cs s e).upW f = (portCode cs s).enc m r) : f = sent cs s e m r := by
  have h2 := up_sent (e := e) (sendable_of_up hC hf)
  funext p x
  exact upRow_inj (tabF cs s p) ((congrFun (congrFun hf p) x).trans (congrFun (congrFun h2 p) x).symm)

/-! ## The record, as a riding part holds it -/

theorem seedIs_map (g : OnBytes.Oracle → OnBytes.Oracle) (hg : ∀ x, ((g x).shape, (g x).sampled, (g x).sampleRows) = (x.shape, x.sampled, x.sampleRows))
    {St : Statement} {o : Nat} {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedIs cs s St o ρ y) :
    SeedIs cs s { codes := St.codes, oracles := St.oracles.map g } o ρ y :=
  h.travels ⟨rfl, fun j => by
    show ((St.oracles.map g)[j]?).map _ = _
    rw [Array.getElem?_map]
    cases St.oracles[j]? with
    | none => rfl
    | some x => exact congrArg some (hg x)⟩

/-- The statement made of the codes and of the messages without their ledgers. -/
theorem seedIs_bare {St : Statement} {o : Nat} {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (h : SeedIs cs s St o ρ y) :
    SeedIs cs s { codes := St.codes, oracles := St.oracles.map fun x => { x with ledger := none } } o ρ y :=
  seedIs_map (fun x => { x with ledger := none }) (fun _ => rfl) h

/-! ## A seed that is no collision -/

theorem exists_not_of_share {D : Type} [Fintype D] [Nonempty D] (P : D → Prop) (K : Nat) (hK : 0 < K) (h : cnt P * 2 ^ K ≤ Fintype.card D) : ∃ ρ, ¬ P ρ := by
  by_contra hc
  have hc' : ∀ ρ, P ρ := fun ρ => by
    by_contra hn
    exact hc ⟨ρ, hn⟩
  have e : cnt P = Fintype.card D := by
    rw [← cnt_true (C := D)]
    exact cnt_congr fun c => ⟨fun _ => trivial, fun _ => hc' c⟩
  rw [e] at h
  have hp : 0 < Fintype.card D := Fintype.card_pos
  have h2 : 2 ^ 1 ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hK
  have h3 := Nat.mul_le_mul_left (Fintype.card D) h2
  omega

theorem no_clash_has (K : Nat) (h0 : 0 < K) (hm : meetsB cs s e = true) (hK : badOwn cs s e * 2 ^ K ≤ qE ^ bitsZ cs s * (qE - 1)) (f : (portOmZ cs s e).Str) :
    ∃ ρ : (Fin (bitsZ cs s) → GE) × GEˣ, ¬ (portOmZ cs s e).Clash f ρ :=
  exists_not_of_share _ K h0 (clash_share K hm hK f)

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.row_base
#print axioms Johnson.RunOne.KeyLetters.sendable_of_up
#print axioms Johnson.RunOne.KeyLetters.eq_sent
#print axioms Johnson.RunOne.KeyLetters.seedIs_map
#print axioms Johnson.RunOne.KeyLetters.seedIs_bare
#print axioms Johnson.RunOne.KeyLetters.no_clash_has
