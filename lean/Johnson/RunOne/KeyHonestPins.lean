-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyHonestPins.lean: THEOREMS. **At an honest word, at one seat: the plain tables' promise and pin hold**: where the committed word of tenant t₀ of tree j₀, shown at every leaf, reads as the word sent of a sendable (m, r), and the record holds the honest row at any seed: hasSmp · NoColl · PIN (Johnson/Desc/Msg.lean IN THE FORM WHERE enc IS A RELATION) at the filling fillG (Johnson/Desc/Key/KeyFill.lean), its letter seedIs filled by the sending kind's SeedIs.
OBJECT: hasSmp | NoColl | PIN at fillG cs s e j₀ t₀ (seedK …). USER: Johnson/RunOne/KeyHonestStrs.lean calls honest_pins (meant beyond it: the promises of the key file's plain tables at the sampled messages' seats). LETTERS: cs · s · e · (j₀, t₀) · F · A | stOf | o (the statement in a record; the message's number) · arr | lay | decT | recOf.
  seedK           fillG's letter seedIs, filled: a ρ v ↦ ∃ y, SeedIs cs s (stOf a) o ρ y ∧ v = fun _ => y
  UniqK           fillG's premise uniq at seedK: two rows at one statement spell one sample map and one answer: a named premise of the three laws below · uniqK: IT IS PAID under Tie cs s, from forms_of_seedIs (Johnson/Desc/K1/Law/GoodSendForms.lean)
  honest_seals    hasSmp ∧ NoColl (sealed_gives at fill_seals; no_clash_sent, KeyMemberEvery.lean: at EVERY seed)
  honest_member   the message sent is a member (member_of_cand at the library's candidate)
  honest_pins     **the three together**: the third: every witness that names it is pinned
PREMISES THAT STAY: UniqK (paid by uniqK under Tie) · hlog (the told log-length is the code's) · hm (no main row, or the main code as long as the tree) · told · shown at every leaf · the word's equation · the honest row · Tie · meetsB · Sendable.
What is not claimed. THAT SUCH STRINGS EXIST (a right inverse of symsW ∘ wordOf). One tenant: off the seat fillG's enc is never. The stored table's half (PINW). That an honest run lays such strings and record. Nothing on soundness or on hiding.

-/
import Johnson.RunOne.KeyMemberEvery
import Johnson.Desc.Key.KeyFill
import Johnson.Desc.K1.Law.GoodSendForms

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1
open VerifiableInference.Desc.Key (SealReads sealed_gives)
open VerifiableInference.Desc.Key.Fill

variable (cs : Codes) (s : OracleShape) (e : Nat) {A Cells Rec XI : Type} (stOf : A → Statement) (o : Nat)

/-- fillG's letter seedIs, filled by the sending kind's. -/
def seedK (a : A) (ρ : (portOmZ cs s e).Z.D) (v : (portOmZ cs s e).Z.S → GE) : Prop :=
  ∃ y, SeedIs cs s (stOf a) o ρ y ∧ v = fun _ => y

/-- fillG's premise on its letter, at seedK: two rows at one statement spell one sample map and one answer. -/
def UniqK : Prop := ∀ a ρ v ρ' v', seedK cs s e stOf o a ρ v → seedK cs s e stOf o a ρ' v' →
    (portOmZ cs s e).Z.val ρ = (portOmZ cs s e).Z.val ρ' ∧ v = v'

/-- **It is paid**, from forms_of_seedIs. -/
theorem uniqK (hT : Tie cs s) : UniqK cs s e stOf o := by
  rintro a ρ v ρ' v' ⟨y, h, rfl⟩ ⟨y', h', rfl⟩
  obtain ⟨a1, a2⟩ := forms_of_seedIs cs s e (stOf a) o ρ y hT h
  obtain ⟨b1, b2⟩ := forms_of_seedIs cs s e (stOf a) o ρ' y' hT h'
  have hm : (portOmZ cs s e).Z.mat ρ = (portOmZ cs s e).Z.mat ρ' := Option.some.inj (a1.symm.trans b1)
  refine ⟨?_, Option.some.inj (a2.symm.trans b2)⟩
  funext u c
  unfold Sample.val
  rw [hm]

variable (j₀ t₀ : ℕ) (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → VerifiableInference.Desc.Key.Fill.Tab → VerifiableInference.Desc.Key.Fill.Tab → VerifiableInference.Desc.Key.Fill.Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : A → Option Rec) (F : FileDescription XI)

local notation "GK" => fillG cs s e j₀ t₀ (seedK cs s e stOf o) arr lay decT recOf

variable {cs s e stOf o}

theorem honest_seals (hlog : ∀ oo, F.oracleAt j₀ = some oo → oo.logLength = aOf cs s) (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s)
    (hU : UniqK cs s e stOf o) (hme : meetsB cs s e = true) {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE} (h : Sendable cs s m r)
    (a : A) (y : Strs) (hword : symsW cs s e (wordOf F y j₀ t₀) = sent cs s e m r)
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} (hI : SeedIs cs s (stOf a) o ρ ((portZ cs s).val ρ m ())) :
    hasSmp GK j₀ t₀ a = true ∧ NoColl F GK j₀ t₀ a y :=
  sealed_gives F GK (fun y' : Strs => y') _ _ _ j₀ t₀ (fill_seals cs s e j₀ t₀ _ arr lay decT recOf F (fun y' : Strs => y') hlog hm hU) a y
    ⟨ρ, fun _ => (portZ cs s).val ρ m (), ⟨_, hI, rfl⟩, by
      show ¬ (portOmZ cs s e).Clash (symsW cs s e (wordOf F y j₀ t₀)) ρ
      rw [hword]
      exact no_clash_sent (base_of_meets hme).1 (base_of_meets hme).2.1 (base_of_meets hme).2.2 h ρ⟩

theorem honest_member (hlog : ∀ oo, F.oracleAt j₀ = some oo → oo.logLength = aOf cs s) (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s)
    (hU : UniqK cs s e stOf o) {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE} (h : Sendable cs s m r)
    (a : A) (y : Strs) (oo : VerifiableInference.Desc.Oracle) (ho : F.oracleAt j₀ = some oo) (hsh : ∀ k, k < 2 ^ aOf cs s → (wordOf F y j₀ t₀ k).isSome = true)
    (hword : symsW cs s e (wordOf F y j₀ t₀) = sent cs s e m r)
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} (hI : SeedIs cs s (stOf a) o ρ ((portZ cs s).val ρ m ()))
    (z : (portOmZ cs s e).Smp) (hz : (GK).smp a j₀ t₀ = some z) : Member F GK oo j₀ t₀ y z (ofU cs s e m) :=
  member_of_cand cs s e j₀ t₀ _ arr lay decT recOf F hlog hm hU a y oo z m ρ (fun _ => (portZ cs s).val ρ m ()) ho hz ⟨_, hI, rfl⟩ hsh
    ⟨by
      rw [hword]
      refine ⟨r, ?_⟩
      show (portCode cs s).Near e ((portOmZ cs s e).upW (sent cs s e m r)) ((portCode cs s).enc m r)
      rw [up_sent h]
      unfold LdCode.Near
      simp [cnt], funext fun _ => rfl⟩

/-- **At an honest word: the promise's two parts, and the pin of every witness that names the message sent.** -/
theorem honest_pins (hlog : ∀ oo, F.oracleAt j₀ = some oo → oo.logLength = aOf cs s) (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s)
    (hU : UniqK cs s e stOf o) (hme : meetsB cs s e = true) {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE} (h : Sendable cs s m r)
    (a : A) (y : Strs) (oo : VerifiableInference.Desc.Oracle) (ho : F.oracleAt j₀ = some oo) (hsh : ∀ k, k < 2 ^ aOf cs s → (wordOf F y j₀ t₀ k).isSome = true)
    (hword : symsW cs s e (wordOf F y j₀ t₀) = sent cs s e m r)
    {ρ : (Fin (bitsZ cs s) → GE) × GEˣ} (hI : SeedIs cs s (stOf a) o ρ ((portZ cs s).val ρ m ())) :
    hasSmp GK j₀ t₀ a = true ∧ NoColl F GK j₀ t₀ a y ∧
      ∀ {Tok : Type} (w : Wit Cells Tok VerifiableInference.Desc.Key.Fill.Tab), msgOf GK w j₀ t₀ = ofU cs s e m → PIN F GK j₀ t₀ a y w := by
  obtain ⟨h1, h2⟩ := honest_seals j₀ t₀ arr lay decT recOf F hlog hm hU hme h a y hword hI
  refine ⟨h1, h2, fun w hw => ?_⟩
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 h1
  exact ⟨oo, z, ho, hz, hw ▸ honest_member j₀ t₀ arr lay decT recOf F hlog hm hU h a y oo ho hsh hword hI z hz⟩

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.uniqK
#print axioms Johnson.RunOne.KeyLetters.honest_seals
#print axioms Johnson.RunOne.KeyLetters.honest_member
#print axioms Johnson.RunOne.KeyLetters.honest_pins
