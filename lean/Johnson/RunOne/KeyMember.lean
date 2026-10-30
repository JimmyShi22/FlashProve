-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyMember.lean: DEFINITIONS AND THEOREMS. **The decoder and the condition of KeyLetters.lean have a member at every honest word**: at letters for the codes, the shape and the radius.
OBJECT: decAt | Sealed | dec₂ | cond₂ of KeyLetters.lean. USER: Johnson/RunOne/KeyMemberEvery.lean calls member_one. LETTERS: cs · s · e; in the last section X · Y · stOf · f₀ · f₁ · MW · decW.
  Sendable      where the main rows are sent over the base field (mainDeg = 1), the main rows' entries of the message and of the encoding randomness lie in the base field
  sent          the code word of (m, r) as a word of the format: symbol by symbol a symbol that reads as the code word's
  up_sent       Sendable → the word sent reads as the library's code word enc m r
  wE, seedIs_has, seedIs_two   every seed and every answer is held by the record of some statement; and two messages' by one
  member_one    **Tie → Sendable → the record holds the kind's row at ρ with the sample map's own answer on m → ρ is no collision of the word's list → the message is sealed and the decoder returns m**
  not_dec_of_wrong   the control: where the record's answer is another, the decoder does not return m, at any word
  clash_share   the seeds that are collisions are at most a share 2^-K of the message's own seeds, from the library's test and one inequality on numbers
  member_two    the same of two messages and a third part: cond₂ holds and dec₂ returns the triple
  member_two_has   all premises of member_two can be met together: at the plainest letters there is a point at which cond₂ holds and dec₂ returns the triple
OVER WHAT THE DECODER's LIST RANGES. The library's list of a word f (OMsg.InList f m) is: THERE IS an encoding randomness r' such that the code word of (m, r') is within e long positions of f. The randomness stands under the ∃: a candidate is a message alone. The sample map reads the message alone too (Z.val ρ m): r enters neither the candidate nor the answer. So a word at whatever randomness its maker drew is in its own message's list, at distance 0.
WHICH CONJUNCTS ARE THE PREMISES PACKED AGAIN. Sealed is «there are ρ, y with SeedIs and ¬ Clash», and cond₂ is two of these: in member_one | member_two the first conjunct is the premises on the record and the seed, packed: no content of its own. The content is «the decoder returns m» (through up_sent) and the count (clash_share): cond₂ holds at an honest word FOR ALL SEEDS BUT THE SHARE.
What is not claimed. How a frame's strings are read as typed words (f₀, f₁). The third part's decoder. That the radii are those of a later test. That a statement as seedIs_has makes it is one that a run reaches. Nothing on soundness or on hiding.

-/
import Johnson.RunOne.KeyLettersLib
import Johnson.RunOne.KeySendErr

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1
open Johnson.RunOne.KeySendErr (qE badOwn portZ_err)

/-! ## The honest word -/

/-- Main rows that are sent over the base field hold a message and an encoding randomness over the base field. -/
def Sendable (cs : Codes) (s : OracleShape) (m : (portCode cs s).J → GE) (r : (portCode cs s).Q → GE) : Prop :=
  s.mainDeg = 1 → (∀ x : Fin s.mainRows × Fin (pMain cs s).ell, m (Sum.inl x) ∈ (algebraMap GF GE).range) ∧
    ∀ q : Fin s.mainRows × Fin (pMain cs s).r, r (Sum.inl q) ∈ (algebraMap GF GE).range

theorem upRow_onto : ∀ (b : Bool) (v : GE), (b = true → v ∈ (algebraMap GF GE).range) → ∃ t : RowTy b, upRow b t = v
  | true, _, h => by
    obtain ⟨t, ht⟩ := h rfl
    exact ⟨t, ht⟩
  | false, v, _ => ⟨v, rfl⟩

variable {cs : Codes} {s : OracleShape} {e : Nat}

/-- Each symbol of the code word is read from a symbol of the format. -/
theorem enc_in {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE} (h : Sendable cs s m r) (p : (portCode cs s).NP) (x : (portCode cs s).NS p) :
    ∃ t : RowTy (tabF cs s p), upRow (tabF cs s p) t = (portCode cs s).enc m r p x := by
  refine upRow_onto _ _ fun hb => ?_
  rcases p with p | p
  · have h1 : s.mainDeg = 1 := by simpa [tabF] using hb
    obtain ⟨hm, hr⟩ := h h1
    exact ldOf_enc_mem (cMain cs s) (aOf cs s) (fun j => m (Sum.inl ((show Fin s.mainRows × Unit from x).1, j)))
      (fun q => r (Sum.inl ((show Fin s.mainRows × Unit from x).1, q))) (fun j => hm _) (fun q => hr _) p
  · exact absurd hb (by simp [tabF])

/-- The code word of (m, r) as a word of the format. -/
def sent (cs : Codes) (s : OracleShape) (e : Nat) (m : (portCode cs s).J → GE) (r : (portCode cs s).Q → GE) : (portOmZ cs s e).Str :=
  fun p x => open Classical in
    if h : ∃ t : RowTy (tabF cs s p), upRow (tabF cs s p) t = (portCode cs s).enc m r p x then h.choose else row0 (tabF cs s p)

/-- **The word sent reads as the library's code word.** -/
theorem up_sent {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE} (h : Sendable cs s m r) :
    (portOmZ cs s e).upW (sent cs s e m r) = (portCode cs s).enc m r := by
  funext p x
  have hh := enc_in h p x
  show upRow (tabF cs s p) (sent cs s e m r p x) = _
  unfold sent
  rw [dif_pos hh]
  exact hh.choose_spec

/-! ## The record -/

/-- An element of the program that reads as x. -/
def wE (x : GE) : E := E.ofTriple (ofE x)

theorem readE_wE (x : GE) : readE (wE x) = x := by
  unfold wE
  rw [readE_ofTriple, toE_ofE]

theorem readsOne_has (cs : Codes) (s : OracleShape) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) :
    ReadsOne cs s (List.ofFn fun t => wE (ρ.1 t)) (wE (ρ.2 : GE)) ρ := by
  refine ⟨by simp, fun t => ?_, readE_wE _⟩
  unfold readL
  have : (List.ofFn fun t => wE (ρ.1 t)).getD t.val zeroE = wE (ρ.1 t) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [this, readE_wE]

/-- The message's entry in a record: marked, with just the kind's row. -/
def orc (cs : Codes) (s : OracleShape) (o : Nat) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (y : GE) : OnBytes.Oracle :=
  { shape := s, sampled := true, sampleRows := #[sampleRow (Msg.of cs s) o (List.ofFn fun t => wE (ρ.1 t)) (wE (ρ.2 : GE)) 0 (wE y)] }

theorem seedIs_of_get {St : Statement} {o : Nat} {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE} (hc : St.codes = cs) (hx : St.oracles[o]? = some (orc cs s o ρ y)) :
    SeedIs cs s St o ρ y :=
  ⟨hc, _, _, _, _, hx, rfl, rfl, rfl, readsOne_has cs s ρ, readE_wE y⟩

/-- **Every seed and every answer is held by some record.** -/
theorem seedIs_has (cs : Codes) (s : OracleShape) (o : Nat) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (y : GE) : ∃ St, SeedIs cs s St o ρ y :=
  ⟨{ codes := cs, oracles := (List.replicate o default ++ [orc cs s o ρ y]).toArray }, seedIs_of_get rfl (by simp)⟩

/-- Two messages' in one record, under the numbers 0 and 1. -/
theorem seedIs_two (cs : Codes) (s₀ s₁ : OracleShape) (ρ₀ : (Fin (bitsZ cs s₀) → GE) × GEˣ) (y₀ : GE) (ρ₁ : (Fin (bitsZ cs s₁) → GE) × GEˣ) (y₁ : GE) :
    ∃ St, SeedIs cs s₀ St 0 ρ₀ y₀ ∧ SeedIs cs s₁ St 1 ρ₁ y₁ :=
  ⟨{ codes := cs, oracles := #[orc cs s₀ 0 ρ₀ y₀, orc cs s₁ 1 ρ₁ y₁] }, seedIs_of_get rfl rfl, seedIs_of_get rfl rfl⟩

/-! ## The member -/

/-- **At an honest word, a record with the honest answer and a seed that is no collision: sealed, and the decoder returns the message.** The first conjunct packs hI and hno again; the second is the content. The answer is the sample map's on m alone: r does not enter it. -/
theorem member_one (hT : Tie cs s) {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE} (h : Sendable cs s m r) {St : Statement} {o : Nat}
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} (hI : SeedIs cs s St o ρ ((portZ cs s).val ρ m ())) (hno : ¬ (portOmZ cs s e).Clash (sent cs s e m r) ρ) :
    Sealed cs s e (sent cs s e m r) St o ∧ decAt cs s e (sent cs s e m r) St o = some m :=
  have hS : Sealed cs s e (sent cs s e m r) St o := ⟨ρ, _, hI, hno⟩
  ⟨hS, dec_of_enc hT hS hI m r (up_sent h) (funext fun _ => rfl)⟩

/-- **The control**: where the record's answer is not the sample map's on m, the decoder does not return m. -/
theorem not_dec_of_wrong (hT : Tie cs s) {m : (portCode cs s).J → GE} {St : Statement} {o : Nat} {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} {y : GE}
    (hI : SeedIs cs s St o ρ y) (hy : y ≠ (portZ cs s).val ρ m ()) (f : (portOmZ cs s e).Str) : decAt cs s e f St o ≠ some m := fun hd =>
  hy (congrFun ((cand_lib hT hI m).1 (decAt_cand hd)).2 ()).symm

/-- **The collisions' share.** The word f is FIXED and the seed ranges: a count of seeds at one word, not of pairs. It speaks of a run because the seed is drawn behind the word. A count of typed seeds: no proof of work enters. -/
theorem clash_share (K : Nat) (hm : meetsB cs s e = true) (hK : badOwn cs s e * 2 ^ K ≤ qE ^ bitsZ cs s * (qE - 1)) (f : (portOmZ cs s e).Str) :
    cnt ((portOmZ cs s e).Clash f) * 2 ^ K ≤ Fintype.card ((Fin (bitsZ cs s) → GE) × GEˣ) := by
  have c := clash_port cs s e hm f
  rw [portZ_err] at c
  have hc : Fintype.card ((Fin (bitsZ cs s) → GE) × GEˣ) = qE ^ bitsZ cs s * (qE - 1) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Cb.Ent.card_units_GE, OnBytes.Slice.card_GE]
    rfl
  rw [hc]
  exact le_trans (Nat.mul_le_mul_right _ c) hK

/-! ## Two messages and a third part -/

section two
variable {s₀ s₁ : OracleShape} {e₀ e₁ o₀ o₁ : Nat} {X Y MW : Type} {stOf : X → Statement}
  {f₀ : Y → (portOmZ cs s₀ e₀).Str} {f₁ : Y → (portOmZ cs s₁ e₁).Str} {decW : Y → Option MW}

/-- **cond₂ holds and dec₂ returns the honest triple.** cond₂ packs hI₀ | hn₀ | hI₁ | hn₁ again (at the words that hf₀ | hf₁ name); the content is dec₂'s value. -/
theorem member_two (hT₀ : Tie cs s₀) (hT₁ : Tie cs s₁) {m₀ : (portCode cs s₀).J → GE} {r₀ : (portCode cs s₀).Q → GE} {m₁ : (portCode cs s₁).J → GE} {r₁ : (portCode cs s₁).Q → GE}
    (h₀ : Sendable cs s₀ m₀ r₀) (h₁ : Sendable cs s₁ m₁ r₁) {a : X × Y} {W : MW}
    (hf₀ : f₀ a.2 = sent cs s₀ e₀ m₀ r₀) (hf₁ : f₁ a.2 = sent cs s₁ e₁ m₁ r₁) (hW : decW a.2 = some W)
    {ρ₀ : (Fin (bitsZ cs s₀) → GE) × GEˣ} {ρ₁ : (Fin (bitsZ cs s₁) → GE) × GEˣ}
    (hI₀ : SeedIs cs s₀ (stOf a.1) o₀ ρ₀ ((portZ cs s₀).val ρ₀ m₀ ())) (hI₁ : SeedIs cs s₁ (stOf a.1) o₁ ρ₁ ((portZ cs s₁).val ρ₁ m₁ ()))
    (hn₀ : ¬ (portOmZ cs s₀ e₀).Clash (sent cs s₀ e₀ m₀ r₀) ρ₀) (hn₁ : ¬ (portOmZ cs s₁ e₁).Clash (sent cs s₁ e₁ m₁ r₁) ρ₁) :
    cond₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ a ∧ dec₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW a = some (m₀, m₁, W) := by
  have a₀ := member_one (e := e₀) hT₀ h₀ hI₀ hn₀
  have a₁ := member_one (e := e₁) hT₁ h₁ hI₁ hn₁
  rw [← hf₀] at a₀
  rw [← hf₁] at a₁
  refine ⟨⟨a₀.1, a₁.1⟩, ?_⟩
  unfold dec₂
  rw [a₀.2, a₁.2, hW]
  rfl

/-- **The premises of member_two can be met together**: at the plainest letters (the riding part is the statement; the strings are the two words and the third part). -/
theorem member_two_has (hT₀ : Tie cs s₀) (hT₁ : Tie cs s₁) {m₀ : (portCode cs s₀).J → GE} {r₀ : (portCode cs s₀).Q → GE} {m₁ : (portCode cs s₁).J → GE} {r₁ : (portCode cs s₁).Q → GE}
    (h₀ : Sendable cs s₀ m₀ r₀) (h₁ : Sendable cs s₁ m₁ r₁) (W : MW)
    {ρ₀ : (Fin (bitsZ cs s₀) → GE) × GEˣ} {ρ₁ : (Fin (bitsZ cs s₁) → GE) × GEˣ}
    (hn₀ : ¬ (portOmZ cs s₀ e₀).Clash (sent cs s₀ e₀ m₀ r₀) ρ₀) (hn₁ : ¬ (portOmZ cs s₁ e₁).Clash (sent cs s₁ e₁ m₁ r₁) ρ₁) :
    ∃ a : Statement × ((portOmZ cs s₀ e₀).Str × (portOmZ cs s₁ e₁).Str × MW),
      cond₂ cs s₀ s₁ e₀ e₁ 0 1 id (fun y => y.1) (fun y => y.2.1) a ∧
        dec₂ cs s₀ s₁ e₀ e₁ 0 1 id (fun y => y.1) (fun y => y.2.1) (fun y => some y.2.2) a = some (m₀, m₁, W) := by
  obtain ⟨St, i₀, i₁⟩ := seedIs_two cs s₀ s₁ ρ₀ ((portZ cs s₀).val ρ₀ m₀ ()) ρ₁ ((portZ cs s₁).val ρ₁ m₁ ())
  exact ⟨(St, sent cs s₀ e₀ m₀ r₀, sent cs s₁ e₁ m₁ r₁, W), member_two hT₀ hT₁ h₀ h₁ rfl rfl rfl i₀ i₁ hn₀ hn₁⟩

end two

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.up_sent
#print axioms Johnson.RunOne.KeyLetters.seedIs_has
#print axioms Johnson.RunOne.KeyLetters.seedIs_two
#print axioms Johnson.RunOne.KeyLetters.member_one
#print axioms Johnson.RunOne.KeyLetters.not_dec_of_wrong
#print axioms Johnson.RunOne.KeyLetters.clash_share
#print axioms Johnson.RunOne.KeyLetters.member_two
#print axioms Johnson.RunOne.KeyLetters.member_two_has
