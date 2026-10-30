-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyFill.lean: A FILLING OF THE PLAIN READING (Johnson/Desc/Msg.lean, with enc a relation at the seat) BY THE LIBRARY's OWN ORACLE MESSAGE, AT ONE TENANT: seat (j₀, t₀), codes cs, shape s, radius e: Om := portOmZ cs s e.
  symsW c        a word of symbols, read as the library's word as sent: the reader wordAt (Johnson/Desc/Sound/MsgSig.lean) WITH THE WORD A LETTER: by residue (rowAt: toF | toE)
  Tab · toU | ofU  a message's two tables BY PART AND INDEX (row + 2 ^ (row bits) · place ↦ GE): the type at which the tables of joints' reader reads (at MsgT (Johnson/Desc/Sound/MsgSig.lean) no reader by part and index exists)
                 against the library's message; WellFormed m: m is 0 outside the shape's entries
  fillG          the reading: enc … m u := at the seat, m well-formed, and THERE IS a randomness r such that WHEREVER u SHOWS A SYMBOL IT READS, AT THAT LONG POSITION, AS THE CODE WORD's · rad := e · smp := some sample with seedIs, by choice ·
                 meets … m z := the library's answers of toU m at z's seed are z's
  EncAt · inList_of_far · far_of_inList   THE TWO HEARTS, WITHOUT A READING: near in Msg.lean's count ⟹ in the library's list; and back, at a word every leaf of which is shown
  local_T        «LOCAL»: where the main rows' code is as long as the tree, the long reading at x reads the word's leaf x alone
  fill_seals     THE UPPER HALF: SealReads (Johnson/Desc/Key/KeySealTie.lean) holds of fillG
  member_of_cand THE LOWER HALF's HEART: a candidate of the library's, at a word every leaf of which is shown, is a Member of fillG's list
seedIs IS A LETTER, under (uniq): one record spells one sample map and one answer. arr · lay · decT · recOf are letters that no statement here reads.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeySealTie
import Johnson.Desc.Sound.MsgSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob

variable (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e : ℕ)

/-- A word of symbols, as the library's word as sent. -/
def symsW (c : ℕ → Option Sym) : (portOmZ cs s e).Str
  | .inl x => fun r => rowAt _ (((c x.val).map (·.main)).getD []) r.1.val
  | .inr x => fun r => rowAt _ (((c x.val).map (·.mask)).getD []) r.1.val

/-- The long reading of a word of symbols. -/
def longOf (c : ℕ → Option Sym) (x : Fin (2 ^ aOf cs s)) : (portOmZ cs s e).C.Aa → GE :=
  (portOmZ cs s e).C.T ((portOmZ cs s e).upW (symsW cs s e c)) x

theorem symsW_inl (c c' : ℕ → Option Sym) (p : Fin (2 ^ (cMain cs s).a)) (h : c p.val = c' p.val) :
    symsW cs s e c (.inl p) = symsW cs s e c' (.inl p) := by
  funext r
  simp only [symsW, h]

theorem symsW_inr (c c' : ℕ → Option Sym) (p : Fin (2 ^ aOf cs s)) (h : c p.val = c' p.val) :
    symsW cs s e c (.inr p) = symsW cs s e c' (.inr p) := by
  funext r
  simp only [symsW, h]

/-- **LOCAL.** -/
theorem local_T (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s) (c c' : ℕ → Option Sym) (x : Fin (2 ^ aOf cs s)) (h : c x.val = c' x.val) :
    longOf cs s e c x = longOf cs s e c' x := by
  funext α
  match α with
  | .inl (row, ()) =>
    rcases hm with h0 | ha
    · exact (Nat.not_lt_zero _ (lt_of_lt_of_eq row.isLt h0)).elim
    · have hx : (posIn (cMain cs s) x).val = x.val := by
        show x.val % 2 ^ (cMain cs s).a = x.val
        rw [ha]
        exact Nat.mod_eq_of_lt x.isLt
      show (portOmZ cs s e).up (.inl (posIn (cMain cs s) x)) (symsW cs s e c (.inl (posIn (cMain cs s) x))) (row, ()) =
        (portOmZ cs s e).up (.inl (posIn (cMain cs s) x)) (symsW cs s e c' (.inl (posIn (cMain cs s) x))) (row, ())
      rw [symsW_inl cs s e c c' _ (by rw [hx]; exact h)]
  | .inr (row, ()) =>
    show (portOmZ cs s e).up (.inr x) (symsW cs s e c (.inr x)) (row, ()) = (portOmZ cs s e).up (.inr x) (symsW cs s e c' (.inr x)) (row, ())
    rw [symsW_inr cs s e c c' x h]

/-! ## The two counts: the library's count over long positions against Msg.lean's filtered range -/

theorem cnt_le_filter {N : ℕ} (p : Fin N → Prop) (q : ℕ → Bool) (h : ∀ x, p x → q x.val = true) :
    cnt p ≤ ((List.range N).filter q).length := by
  classical
  unfold cnt
  have hmem : ∀ x : {x : Fin N // p x}, x.1.val ∈ ((List.range N).filter q).toFinset := fun x => by
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨x.1.isLt, h x.1 x.2⟩
  have hinj : Function.Injective (fun x : {x : Fin N // p x} => (⟨x.1.val, hmem x⟩ : {k // k ∈ ((List.range N).filter q).toFinset})) := by
    intro a b hab
    exact Subtype.ext (Fin.ext (congrArg (fun z => z.1) hab))
  calc Nat.card {x : Fin N // p x} ≤ Nat.card {k // k ∈ ((List.range N).filter q).toFinset} := Nat.card_le_card_of_injective _ hinj
    _ = ((List.range N).filter q).toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ ((List.range N).filter q).length := List.toFinset_card_le _

theorem filter_le_cnt {N : ℕ} (p : Fin N → Prop) (q : ℕ → Bool) (h : ∀ x : Fin N, q x.val = true → p x) :
    ((List.range N).filter q).length ≤ cnt p := by
  classical
  unfold cnt
  have hnd : ((List.range N).filter q).Nodup := List.Nodup.filter _ List.nodup_range
  have hk : ∀ k : {k // k ∈ ((List.range N).filter q).toFinset}, k.1 < N ∧ q k.1 = true := fun k => by
    have := k.2
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at this
    exact this
  have hinj : Function.Injective (fun k : {k // k ∈ ((List.range N).filter q).toFinset} => (⟨⟨k.1, (hk k).1⟩, h _ (hk k).2⟩ : {x : Fin N // p x})) := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z => z.1.val) hab)
  calc ((List.range N).filter q).length = ((List.range N).filter q).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ = Nat.card {k // k ∈ ((List.range N).filter q).toFinset} := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Nat.card {x : Fin N // p x} := Nat.card_le_card_of_injective _ hinj

/-! ## The tables -/

/-- A message's two tables, by part and index (row + 2 ^ (row bits) · place): the type at which the tables of joints' reader reads. -/
abbrev Tab : Type := OnBytes.Part → ℕ → GE

def toU (m : Tab) : (portOmZ cs s e).Msg := fun j =>
  match (j : (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell)) with
  | .inl x => m .main (x.1.val + 2 ^ k1 s * x.2.val)
  | .inr x => m .mask (x.1.val + 2 ^ k2 s * x.2.val)

def ofU (u : (portOmZ cs s e).Msg) : Tab := fun part i =>
  match part with
  | .main => if h : i % 2 ^ k1 s < s.mainRows ∧ i / 2 ^ k1 s < (pMain cs s).ell then
      u (.inl ((⟨_, h.1⟩, ⟨_, h.2⟩) : Fin s.mainRows × Fin (pMain cs s).ell)) else 0
  | .mask => if h : i % 2 ^ k2 s < s.maskRows ∧ i / 2 ^ k2 s < (pMask cs s).ell then
      u (.inr ((⟨_, h.1⟩, ⟨_, h.2⟩) : Fin s.maskRows × Fin (pMask cs s).ell)) else 0

theorem idx_mod {R i c : ℕ} (hi : i < R) : (i + 2 ^ OnBytes.ceilLog2 R * c) % 2 ^ OnBytes.ceilLog2 R = i := by
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le hi (le_two_pow_ceilLog2 R))

theorem idx_div {R i c : ℕ} (hi : i < R) : (i + 2 ^ OnBytes.ceilLog2 R * c) / 2 ^ OnBytes.ceilLog2 R = c := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (lt_of_lt_of_le hi (le_two_pow_ceilLog2 R)), Nat.zero_add]

theorem toU_ofU (u : (portOmZ cs s e).Msg) : toU cs s e (ofU cs s e u) = u := by
  funext j
  match (j : (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell)) with
  | .inl x =>
    have h1 : (x.1.val + 2 ^ k1 s * x.2.val) % 2 ^ k1 s = x.1.val := idx_mod x.1.isLt
    have h2 : (x.1.val + 2 ^ k1 s * x.2.val) / 2 ^ k1 s = x.2.val := idx_div x.1.isLt
    show (if h : (x.1.val + 2 ^ k1 s * x.2.val) % 2 ^ k1 s < s.mainRows ∧ (x.1.val + 2 ^ k1 s * x.2.val) / 2 ^ k1 s < (pMain cs s).ell then
      u (.inl ((⟨_, h.1⟩, ⟨_, h.2⟩) : Fin s.mainRows × Fin (pMain cs s).ell)) else 0) = u (.inl x)
    rw [dif_pos ⟨by rw [h1]; exact x.1.isLt, by rw [h2]; exact x.2.isLt⟩]
    congr 2
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  | .inr x =>
    have h1 : (x.1.val + 2 ^ k2 s * x.2.val) % 2 ^ k2 s = x.1.val := idx_mod x.1.isLt
    have h2 : (x.1.val + 2 ^ k2 s * x.2.val) / 2 ^ k2 s = x.2.val := idx_div x.1.isLt
    show (if h : (x.1.val + 2 ^ k2 s * x.2.val) % 2 ^ k2 s < s.maskRows ∧ (x.1.val + 2 ^ k2 s * x.2.val) / 2 ^ k2 s < (pMask cs s).ell then
      u (.inr ((⟨_, h.1⟩, ⟨_, h.2⟩) : Fin s.maskRows × Fin (pMask cs s).ell)) else 0) = u (.inr x)
    rw [dif_pos ⟨by rw [h1]; exact x.1.isLt, by rw [h2]; exact x.2.isLt⟩]
    congr 2
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- The table is 0 outside the shape's entries. -/
def WellFormed (m : Tab) : Prop := ofU cs s e (toU cs s e m) = m

theorem wellFormed_ofU (u : (portOmZ cs s e).Msg) : WellFormed cs s e (ofU cs s e u) := by
  unfold WellFormed
  rw [toU_ofU]

theorem toU_inj {m m' : Tab} (h : WellFormed cs s e m) (h' : WellFormed cs s e m') (he : toU cs s e m = toU cs s e m') : m = m' := by
  rw [← h, ← h', he]

/-! ## The two hearts, without a reading -/

/-- u is an encoding of the table m: m is well-formed, and there is a randomness such that wherever u shows a symbol its long reading is the code word's. -/
def EncAt (m : Tab) (u : ℕ → Option Sym) : Prop :=
  WellFormed cs s e m ∧ ∃ r, ∀ x : Fin (2 ^ aOf cs s), (u x.val).isSome = true →
    longOf cs s e u x = (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc (toU cs s e m) r) x

/-- **Near in Msg.lean's count ⟹ in the library's list.** -/
theorem inList_of_far (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s) (word u : ℕ → Option Sym) (m : Tab) (h : EncAt cs s e m u)
    (hfar : far (aOf cs s) word u ≤ e) : (portOmZ cs s e).InList (symsW cs s e word) (toU cs s e m) := by
  obtain ⟨_, r, hr⟩ := h
  refine ⟨r, ?_⟩
  show cnt (fun x : Fin (2 ^ aOf cs s) => longOf cs s e word x ≠ (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc (toU cs s e m) r) x) ≤ e
  refine le_trans (cnt_le_filter _ (fun k => (word k).isNone || word k != u k) fun x hx => ?_) hfar
  by_contra hq
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isNone_eq_false_iff, bne_eq_false_iff_eq] at hq
  exact hx ((local_T cs s e hm _ _ x hq.2).trans (hr x (hq.2 ▸ hq.1)))

/-- **In the library's list, at a word every leaf of which is shown ⟹ near in Msg.lean's count.** -/
theorem far_of_inList (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s) (word : ℕ → Option Sym) (hsh : ∀ k, k < 2 ^ aOf cs s → (word k).isSome = true)
    (u₀ : (portOmZ cs s e).Msg) (h : (portOmZ cs s e).InList (symsW cs s e word) u₀) : ∃ u, EncAt cs s e (ofU cs s e u₀) u ∧ far (aOf cs s) word u ≤ e := by
  classical
  obtain ⟨r, hnear⟩ := h
  have hnear' : cnt (fun x : Fin (2 ^ aOf cs s) => longOf cs s e word x ≠ (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc u₀ r) x) ≤ e := hnear
  let u : ℕ → Option Sym := fun k => if h : k < 2 ^ aOf cs s then
    (if longOf cs s e word ⟨k, h⟩ = (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc u₀ r) ⟨k, h⟩ then word k else none) else none
  have hu1 : ∀ x : Fin (2 ^ aOf cs s), longOf cs s e word x = (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc u₀ r) x → u x.val = word x.val := fun x hx => by
    show (if h : x.val < 2 ^ aOf cs s then _ else _) = _
    rw [dif_pos x.isLt, if_pos hx]
  have hu0 : ∀ x : Fin (2 ^ aOf cs s), longOf cs s e word x ≠ (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc u₀ r) x → u x.val = none := fun x hx => by
    show (if h : x.val < 2 ^ aOf cs s then _ else _) = _
    rw [dif_pos x.isLt, if_neg hx]
  refine ⟨u, ⟨wellFormed_ofU cs s e u₀, r, fun x hx => ?_⟩, ?_⟩
  · rw [toU_ofU]
    by_cases hxx : longOf cs s e word x = (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc u₀ r) x
    · exact (local_T cs s e hm _ _ x (hu1 x hxx)).trans hxx
    · rw [hu0 x hxx] at hx
      exact nomatch hx
  · refine le_trans (filter_le_cnt (fun x : Fin (2 ^ aOf cs s) => longOf cs s e word x ≠ (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc u₀ r) x) _ fun x hq hxx => ?_) hnear'
    rw [hu1 x hxx] at hq
    have h1 := hsh x.val x.isLt
    simp only [Bool.or_eq_true, bne_self_eq_false, Bool.false_eq_true, or_false, Option.isNone_iff_eq_none] at hq
    rw [hq] at h1
    exact nomatch h1

/-! ## The reading -/

section
variable {A Cells Rec : Type} (j₀ t₀ : ℕ) (seedIs : A → (portOmZ cs s e).Z.D → ((portOmZ cs s e).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)

open Classical in
/-- **The filling at one tenant.** -/
def fillG : Reading A Cells Tab (portOmZ cs s e).Smp Rec where
  arr := arr
  lay := lay
  enc := fun _ j t m u => j = j₀ ∧ t = t₀ ∧ EncAt cs s e m u
  rad := fun _ _ _ => e
  meets := fun _ _ _ m z => (portOmZ cs s e).Z.val z.1 (toU cs s e m) = z.2
  smp := fun a j t => if j = j₀ ∧ t = t₀ then (if h : ∃ z : (portOmZ cs s e).Smp, seedIs a z.1 z.2 then some h.choose else none) else none
  decT := decT
  recOf := recOf

theorem smp_spec {a : A} {z : (portOmZ cs s e).Smp} (h : (fillG cs s e j₀ t₀ seedIs arr lay decT recOf).smp a j₀ t₀ = some z) : seedIs a z.1 z.2 := by
  classical
  simp only [fillG, and_self, if_true] at h
  split at h
  · rename_i hz
    obtain rfl := Option.some.inj h
    exact hz.choose_spec
  · exact nomatch h

variable {XI Y' : Type} (F : FileDescription XI) (str : Y' → Strs)

/-- **THE UPPER HALF: the table's list lies inside the library's.** -/
def fill_seals (hlog : ∀ o, F.oracleAt j₀ = some o → o.logLength = aOf cs s) (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s)
    (uniq : ∀ a ρ v ρ' v', seedIs a ρ v → seedIs a ρ' v' → (portOmZ cs s e).Z.val ρ = (portOmZ cs s e).Z.val ρ' ∧ v = v') :
    SealReads F (fillG cs s e j₀ t₀ seedIs arr lay decT recOf) str (fun y' => (portOmZ cs s e).InList (symsW cs s e (wordOf F (str y') j₀ t₀)))
      (portOmZ cs s e).Z.val seedIs j₀ t₀ where
  toU := toU cs s e
  has := fun a ρ y hs => by
    classical
    have hz : ∃ z : (portOmZ cs s e).Smp, seedIs a z.1 z.2 := ⟨(ρ, y), hs⟩
    simp only [hasSmp, fillG, and_self, if_true, dif_pos hz, Option.isSome_some]
  inj := fun a y' o z m m' _ _ hM hM' he => by
    obtain ⟨⟨_, ⟨_, _, hw, _⟩, _⟩, _⟩ := hM
    obtain ⟨⟨_, ⟨_, _, hw', _⟩, _⟩, _⟩ := hM'
    exact toU_inj cs s e hw hw' he
  mem := fun a y' o z m ρ y ho hz hs hM => by
    obtain ⟨⟨u, ⟨_, _, hE⟩, hfar⟩, hmeets⟩ := hM
    refine ⟨inList_of_far cs s e hm _ u m hE ?_, ?_⟩
    · have := hfar
      rw [hlog o ho] at this
      exact this
    · obtain ⟨e1, e2⟩ := uniq a ρ y z.1 z.2 hs (smp_spec cs s e j₀ t₀ seedIs arr lay decT recOf hz)
      show (portOmZ cs s e).Z.val ρ (toU cs s e m) = y
      rw [e1, e2]
      exact hmeets

/-- **THE LOWER HALF's HEART: the library's candidate, at a word every leaf of which is shown, is a member of the table's list.** -/
theorem member_of_cand (hlog : ∀ o, F.oracleAt j₀ = some o → o.logLength = aOf cs s) (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s)
    (uniq : ∀ a ρ v ρ' v', seedIs a ρ v → seedIs a ρ' v' → (portOmZ cs s e).Z.val ρ = (portOmZ cs s e).Z.val ρ' ∧ v = v')
    (a : A) (y : Strs) (o : Oracle) (z : (portOmZ cs s e).Smp) (u₀ : (portOmZ cs s e).Msg) (ρ : (portOmZ cs s e).Z.D) (v : (portOmZ cs s e).Z.S → GE)
    (ho : F.oracleAt j₀ = some o) (hz : (fillG cs s e j₀ t₀ seedIs arr lay decT recOf).smp a j₀ t₀ = some z) (hs : seedIs a ρ v)
    (hsh : ∀ k, k < 2 ^ aOf cs s → (wordOf F y j₀ t₀ k).isSome = true)
    (hc : Cb.Ood.Cand ((portOmZ cs s e).InList (symsW cs s e (wordOf F y j₀ t₀))) (portOmZ cs s e).Z.val ρ v u₀) :
    Member F (fillG cs s e j₀ t₀ seedIs arr lay decT recOf) o j₀ t₀ y z (ofU cs s e u₀) := by
  obtain ⟨hin, hval⟩ := hc
  obtain ⟨u, hE, hfar⟩ := far_of_inList cs s e hm _ hsh u₀ hin
  refine ⟨⟨u, ⟨rfl, rfl, hE⟩, ?_⟩, ?_⟩
  · show far o.logLength (wordOf F y j₀ t₀) u ≤ e
    rw [hlog o ho]
    exact hfar
  · obtain ⟨e1, e2⟩ := uniq a ρ v z.1 z.2 hs (smp_spec cs s e j₀ t₀ seedIs arr lay decT recOf hz)
    show (portOmZ cs s e).Z.val z.1 (toU cs s e (ofU cs s e u₀)) = z.2
    rw [toU_ofU, ← e1, ← e2]
    exact hval

end

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.local_T
#print axioms VerifiableInference.Desc.Key.Fill.toU_ofU
#print axioms VerifiableInference.Desc.Key.Fill.inList_of_far
#print axioms VerifiableInference.Desc.Key.Fill.far_of_inList
#print axioms VerifiableInference.Desc.Key.Fill.fill_seals
#print axioms VerifiableInference.Desc.Key.Fill.member_of_cand
