-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyHonestStrs.lean: THEOREMS. **Strings whose committed word at a seat reads as any given word of the library's exist; so the plain tables' promise and pin have a member at an honest word, AS STRINGS, at every seed.**
OBJECT: symsW (Johnson/Desc/Key/KeyFill.lean) ∘ wordOf F · j₀ t₀ (Johnson/Desc/Msg.lean, the form where enc is a relation) · hasSmp | NoColl | PIN at fillG. USER: honest_pins' two premises «shown · the word's equation» (KeyHonestPins.lean). LETTERS: cs · s · e · F · (j₀, t₀) · oo · n · o.
  degOf           the words of a main row's symbol: 1 over the base field, else 3
  syms_onto       every word f of the library's format is symsW of a word of symbols, each of the shape's numbers of raw words (from rows_onto)
  honest_strings  told · the tenant · the tenants' words add up · the tenant's two numbers are the shape's ⊢ for every f there are strings, shown at every leaf, whose word at the seat reads as f (from strs_onto)
  honest_pins_has **so, with the premises on the plan (the told log-length · hm) and Tie · meetsB · Sendable: AT EVERY SEED there are a record, strings and a witness with hasSmp · NoColl · PIN, the witness naming the message sent**
PREMISES ON THE PLAN THAT STAY, ALL ON F's SEAT: told · the tenant · the sum · the tenant's two numbers · the degree · the told log-length · hm. THAT ANY F MEETS THEM TOGETHER IS NOT SHOWN HERE: until it is, honest_pins_has shows a member under premises that are met at no shown description.
What is not claimed. More than one tenant (off the seat fillG's enc is never). The stored table's half (the strings' cells are empty; PINW). That an honest run lays such strings and record. Nothing on soundness or on hiding.

-/
import Johnson.RunOne.KeyHonestPins
import Johnson.RunOne.KeyHonestCols

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key.Fill

variable (cs : Codes) (s : OracleShape) (e : Nat)

/-- The raw words of a main row's symbol. -/
def degOf : ℕ := if (s.mainDeg == 1) = true then 1 else 3

theorem degOf_eq (h : s.mainDeg = 1 ∨ s.mainDeg = 3) : degOf s = s.mainDeg := by
  unfold degOf
  rcases h with h | h <;> rw [h] <;> rfl

open Classical in
/-- A word of symbols for a word of the library's format. -/
def symsFor (f : (portOmZ cs s e).Str) (k : ℕ) : Sym :=
  ⟨if h : k < 2 ^ (cMain cs s).a then (rows_onto (s.mainDeg == 1) s.mainRows fun i => f (.inl ⟨k, h⟩) (i, ())).choose else List.replicate (s.mainRows * degOf s) 0,
   if h : k < 2 ^ aOf cs s then (rows_onto false s.maskRows fun i => f (.inr ⟨k, h⟩) (i, ())).choose else List.replicate (s.maskRows * 3) 0⟩

theorem symsFor_len (f : (portOmZ cs s e).Str) (k : ℕ) :
    (symsFor cs s e f k).main.length = s.mainRows * degOf s ∧ (symsFor cs s e f k).mask.length = s.maskRows * 3 := by
  unfold symsFor
  constructor
  · show (dite _ _ _ : List UInt64).length = _
    split
    · exact (rows_onto (s.mainDeg == 1) s.mainRows _).choose_spec.1
    · exact List.length_replicate ..
  · show (dite _ _ _ : List UInt64).length = _
    split
    · exact (rows_onto false s.maskRows _).choose_spec.1
    · exact List.length_replicate ..

/-- **Every word of the library's format is read off a word of symbols.** -/
theorem syms_onto (f : (portOmZ cs s e).Str) : symsW cs s e (fun k => some (symsFor cs s e f k)) = f := by
  funext p
  match p with
  | .inl x =>
    funext r
    obtain ⟨i, u⟩ := r
    cases u
    show rowAt _ (symsFor cs s e f x.val).main i.val = f (.inl x) (i, ())
    unfold symsFor
    show rowAt _ (dite _ _ _ : List UInt64) i.val = _
    rw [dif_pos x.isLt]
    exact (rows_onto (s.mainDeg == 1) s.mainRows fun i => f (.inl ⟨x.val, x.isLt⟩) (i, ())).choose_spec.2 i
  | .inr x =>
    funext r
    obtain ⟨i, u⟩ := r
    cases u
    show rowAt _ (symsFor cs s e f x.val).mask i.val = f (.inr x) (i, ())
    unfold symsFor
    show rowAt _ (dite _ _ _ : List UInt64) i.val = _
    rw [dif_pos x.isLt]
    exact (rows_onto false s.maskRows fun i => f (.inr ⟨x.val, x.isLt⟩) (i, ())).choose_spec.2 i

variable {cs s e}

/-- **Strings whose word at the seat reads as a given word.** -/
theorem honest_strings {XI : Type} (F : FileDescription XI) (j₀ t₀ : ℕ) (oo : VerifiableInference.Desc.Oracle) (n : VerifiableInference.Desc.SymbolComponent)
    (ho : F.oracleAt j₀ = some oo) (hn : oo.tenants[t₀]? = some n)
    (hsum : (oo.tenants.map (·.main)).sum + (oo.tenants.map (·.mask)).sum = oo.words)
    (hmain : n.main = s.mainRows * s.mainDeg) (hmask : n.mask = s.maskRows * 3) (hdeg : s.mainDeg = 1 ∨ s.mainDeg = 3)
    (f : (portOmZ cs s e).Str) :
    ∃ y : Strs, (∀ k, (wordOf F y j₀ t₀ k).isSome = true) ∧ symsW cs s e (wordOf F y j₀ t₀) = f := by
  obtain ⟨y, hy⟩ := strs_onto F j₀ t₀ oo n ho hn hsum (symsFor cs s e f) fun k =>
    ⟨by rw [(symsFor_len cs s e f k).1, degOf_eq s hdeg, hmain], by rw [(symsFor_len cs s e f k).2, hmask]⟩
  have ew : wordOf F y j₀ t₀ = fun k => some (symsFor cs s e f k) := funext hy
  exact ⟨y, fun k => by rw [hy k]; rfl, by rw [ew]; exact syms_onto cs s e f⟩

/-- **The plain tables' promise and pin have a member at an honest word, as strings, at every seed.** -/
theorem honest_pins_has {XI : Type} (F : FileDescription XI) (j₀ t₀ : ℕ) (oo : VerifiableInference.Desc.Oracle) (n : VerifiableInference.Desc.SymbolComponent)
    (ho : F.oracleAt j₀ = some oo) (hn : oo.tenants[t₀]? = some n)
    (hsum : (oo.tenants.map (·.main)).sum + (oo.tenants.map (·.mask)).sum = oo.words)
    (hmain : n.main = s.mainRows * s.mainDeg) (hmask : n.mask = s.maskRows * 3) (hdeg : s.mainDeg = 1 ∨ s.mainDeg = 3)
    (hlog : oo.logLength = aOf cs s) (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s)
    (hT : Tie cs s) (hme : meetsB cs s e = true) {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE} (h : Sendable cs s m r)
    (o : ℕ) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) :
    ∃ (a : Statement) (y : Strs) (w : Wit Unit Unit VerifiableInference.Desc.Key.Fill.Tab),
      hasSmp (fillG cs s e j₀ t₀ (seedK cs s e (fun St : Statement => St) o) (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) fun _ => none) j₀ t₀ a = true ∧
      NoColl F (fillG cs s e j₀ t₀ (seedK cs s e (fun St : Statement => St) o) (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) fun _ => none) j₀ t₀ a y ∧
      PIN F (fillG cs s e j₀ t₀ (seedK cs s e (fun St : Statement => St) o) (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) fun _ => none) j₀ t₀ a y w ∧
      w.msg 0 = ofU cs s e m := by
  obtain ⟨a, hI⟩ := seedIs_has cs s o ρ ((portZ cs s).val ρ m ())
  obtain ⟨y, hsh, hword⟩ := honest_strings (e := e) F j₀ t₀ oo n ho hn hsum hmain hmask hdeg (sent cs s e m r)
  have hl : ∀ oo', F.oracleAt j₀ = some oo' → oo'.logLength = aOf cs s := fun oo' h' => by
    obtain rfl := Option.some.inj (h'.symm.trans ho)
    exact hlog
  obtain ⟨h1, h2, h3⟩ := honest_pins (stOf := fun St : Statement => St) (o := o) j₀ t₀ (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) (fun _ => none) F hl hm
    (uniqK cs s e _ o hT) hme h a y oo ho (fun k _ => hsh k) hword hI
  exact ⟨a, y, ⟨(), (), fun _ => ofU cs s e m, fun _ _ => ofU cs s e m⟩, h1, h2, h3 _ rfl, rfl⟩

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.syms_onto
#print axioms Johnson.RunOne.KeyLetters.honest_strings
#print axioms Johnson.RunOne.KeyLetters.honest_pins_has
