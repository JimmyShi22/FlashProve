-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/FoReads.lean: what the callers of a sub-proof's lookup hand to the three
claims on the planes of the counts, and the law under which these are the sums that the claims speak
of.

Forest.planeClaims takes two routines from its caller: bit e col and pin col give forms for the
sums, over the rows of the planes' matrix, of a weight times the matrix's entry in column col. At
the three sites that call it (the layers, attention, the head) each of these forms is one entry of
the sub-proof's vector of reads: entry t + col, where t is the first entry of one of three tables.

 - u3Val entry iU3 K3 e: entry number e of the vector of reads in a world, by the rule of uEnt: the
   vector is array iU3 of K3 columns; entry e stands in virtual row e / K3 at index e % K3.
 - ReadsAt bit pin iU3 K3 tB0 tB1 tP F c: the two routines turn neither state nor context, and
   whatever they return from (F, c) is that one entry.
 - readsAt_layer, readsAt_attention, readsAt_head: ReadsAt holds of the routines that the three
   sites write, on their bodies, in every state F and context c. K3 is the layers' own number v.K3;
   at attention and at the head it is the number of columns that F holds for array iU3 (colsOf).
   claimsPlanes_eq, att_claims_eq, claimPlanes_eq: these are the routines that the sites hand to
   Forest.planeLins (by rfl), which calls Forest.planeClaims.
 - ReadAt entry iU3 K3 t W cellAt rows n: the general clause: the n entries from entry t on are,
   column by column, the sums over a matrix's rows of a weight times the matrix's entry.
 - ReadsLaw h lm zb0 zb1 ν entry iU3 K3 tB0 tB1 tP: a proposition on a world's entries and on the
   cells ν: for each of the planes' columns the three entries are the sums under the weights
   phiB at zb0, phiB at zb1, and 2^(row mod 32). It is no identity: it is what the claims on the
   reads are to enforce. It is a hypothesis wherever it stands. readsLaw_some: some entries meet
   it, if the three tables lie one behind the other: tB0 + n ≤ tB1 and tB1 + n ≤ tP, where n is the
   number of the planes' columns. readsLaw_pins: it fixes the entries of the three tables.
 - cols_of_reads: under ReadsAt and ReadsLaw, for each of the planes' columns at which the routines
   return, the values of their forms are colsK at zb0, colsK at zb1 and pinColK.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that ReadsLaw holds of any world but the one that readsLaw_some makes.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneClaims
import OnBytes.Model.Layer
import OnBytes.Model.Attention
import OnBytes.Model.Head

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun Cb.Fo.PlaneClaims Cb.Fo.Pin

/-- Entry number e of the vector of reads. -/
def u3Val {K : Type} (entry : ℕ → ℕ → ℕ → K) (iU3 K3 e : ℕ) : K := entry iU3 (e / K3) (e % K3)

/-- The form of entry number e of the vector of reads. -/
def u3Form (iU3 K3 e : ℕ) : Aff := Aff.ent iU3 (e / K3) (e % K3)

theorem u3Form_value {K : Type} [CommRing K] (ρ : Reading K) (W : World K) (iU3 K3 e : ℕ) :
    (u3Form iU3 K3 e).value ρ W = u3Val W.entry iU3 K3 e := Aff.value_ent ρ W _ _ _

/-- The routine turns nothing, and what it returns from (F, c) is the form a. -/
def Gives (x : SubM Aff) (F : Fork) (c : Ctx) (a : Aff) : Prop :=
  Quiet x ∧ ∀ r, x F c = .ok r → r.1.1 = a

/-- The columns of array t in the state F. -/
def colsOf (F : Fork) (t : ℕ) : ℕ := ((F.trees[t]?).map (·.K)).getD 0

theorem uEnt_ok (t x : ℕ) (F : Fork) (c : Ctx) (r : (Aff × Fork) × Ctx)
    (h : uEnt t x F c = .ok r) : r = ((u3Form t (colsOf F t) x, F), c) := by
  unfold uEnt at h
  obtain ⟨G, F1, c1, h1, h2⟩ := (bind_ok _ _ F c r).1 h
  have e : ((F, F), c) = ((G, F1), c1) := Except.ok.inj h1
  cases e
  obtain ⟨_, F2, c2, h3, h4⟩ := (bind_ok _ _ _ _ r).1 h2
  obtain ⟨_, e3⟩ := (mustAs_ok _ _ _ _ _).1 h3
  cases e3
  exact (pure_ok _ _ _ r).1 h4

theorem gives_uEnt (t x : ℕ) (F : Fork) (c : Ctx) :
    Gives (uEnt t x) F c (u3Form t (colsOf F t) x) :=
  ⟨fun F' c' r h => by rw [uEnt_ok t x F' c' r h]; exact ⟨rfl, rfl⟩,
    fun r h => by rw [uEnt_ok t x F c r h]⟩

/-- A public test before a routine. -/
theorem gives_mustAs (name : String) (b : Bool) (x : SubM Aff) (F : Fork) (c : Ctx) (a : Aff)
    (hx : Gives x F c a) : Gives (do mustAs name b; x) F c a := by
  have key : ∀ F' c' r, (do mustAs name b; x : SubM Aff) F' c' = .ok r → x F' c' = .ok r := by
    intro F' c' r h
    obtain ⟨_, F2, c2, h3, h4⟩ := (bind_ok _ _ _ _ r).1 h
    obtain ⟨_, e3⟩ := (mustAs_ok _ _ _ _ _).1 h3
    cases e3
    exact h4
  exact ⟨fun F' c' r h => hx.1 F' c' r (key F' c' r h), fun r h => hx.2 r (key F c r h)⟩

/-- A form that is there or not, by public numbers alone. -/
theorem gives_get (o : Option Aff) (F : Fork) (c : Ctx) (a : Aff) (ho : ∀ b, o = some b → b = a) :
    Gives (SubM.get o) F c a := by
  have key : ∀ F' c' r, SubM.get o F' c' = .ok r → ∃ b, o = some b ∧ r = ((b, F'), c') :=
    fun F' c' r h => (get_ok o F' c' r).1 h
  refine ⟨fun F' c' r h => ?_, fun r h => ?_⟩
  · obtain ⟨b, _, rfl⟩ := key F' c' r h
    exact ⟨rfl, rfl⟩
  · obtain ⟨b, hb, rfl⟩ := key F c r h
    exact ho b hb

/-- What a caller's two routines are: one entry of the vector of reads each. -/
structure ReadsAt (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff) (iU3 K3 tB0 tB1 tP : ℕ) (F : Fork)
    (c : Ctx) : Prop where
  bit0 : ∀ col, Gives (bit 0 col) F c (u3Form iU3 K3 (tB0 + col))
  bit1 : ∀ col, Gives (bit 1 col) F c (u3Form iU3 K3 (tB1 + col))
  bitQ : ∀ e col, Quiet (bit e col)
  pin : ∀ col, Gives (pin col) F c (u3Form iU3 K3 (tP + col))

theorem got_of {x : SubM Aff} {F : Fork} {c : Ctx} {a : Aff} (hx : Gives x F c a)
    (hr : ∃ r, x F c = .ok r) : got x F c = a := by
  obtain ⟨r, h⟩ := hr
  unfold got
  rw [h]
  exact hx.2 r h

/-! ### the law of the reads -/
section
variable {K : Type} [CommRing K]

/-- The n entries of the vector of reads from entry t on are, column by column, the sums over a
matrix's rows of a weight times the matrix's entry. -/
def ReadAt (entry : ℕ → ℕ → ℕ → K) (iU3 K3 t : ℕ) (W : ℕ → K) (cellAt : ℕ → ℕ → K)
    (rows n : ℕ) : Prop :=
  ∀ col < n, u3Val entry iU3 K3 (t + col) = ∑ row ∈ Finset.range rows, W row * cellAt row col

/-- The columns of the planes' matrix. -/
def planeCols (h : FoNums.Sh) (lm : ℕ) : ℕ := h.NC * 2 ^ (h.kT + 5 - lm)

/-- The law of the reads at the three tables of the planes' matrix. -/
structure ReadsLaw (h : FoNums.Sh) (lm : ℕ) (zb0 zb1 : List K) (ν : Pl → K)
    (entry : ℕ → ℕ → ℕ → K) (iU3 K3 tB0 tB1 tP : ℕ) : Prop where
  bits0 : ReadAt entry iU3 K3 tB0 (fun r => (phiBK h lm zb0).getD r 0) (fun r c => ν (.cell r c))
    (2 ^ lm) (planeCols h lm)
  bits1 : ReadAt entry iU3 K3 tB1 (fun r => (phiBK h lm zb1).getD r 0) (fun r c => ν (.cell r c))
    (2 ^ lm) (planeCols h lm)
  count : ReadAt entry iU3 K3 tP (fun r => (2 : K) ^ (r % 32)) (fun r c => ν (.cell r c))
    (2 ^ lm) (planeCols h lm)

/-- Under the law the callers' forms have the values of which the three claims speak. -/
theorem cols_of_reads (ρ : Reading K) (W : World K) {bit : ℕ → ℕ → SubM Aff} {pin : ℕ → SubM Aff}
    {iU3 K3 tB0 tB1 tP : ℕ} {F : Fork} {c : Ctx} (R : ReadsAt bit pin iU3 K3 tB0 tB1 tP F c)
    {h : FoNums.Sh} {lm : ℕ} {zb0 zb1 : List K} {ν : Pl → K}
    (Lw : ReadsLaw h lm zb0 zb1 ν W.entry iU3 K3 tB0 tB1 tP) (col : ℕ)
    (hc : col < planeCols h lm) :
    ((∃ r, bit 0 col F c = .ok r) → (got (bit 0 col) F c).value ρ W = colsK h lm zb0 ν col) ∧
    ((∃ r, bit 1 col F c = .ok r) → (got (bit 1 col) F c).value ρ W = colsK h lm zb1 ν col) ∧
    ((∃ r, pin col F c = .ok r) → (got (pin col) F c).value ρ W = pinColK lm ν col) :=
  ⟨fun hr => by rw [got_of (R.bit0 col) hr, u3Form_value]; exact Lw.bits0 col hc,
    fun hr => by rw [got_of (R.bit1 col) hr, u3Form_value]; exact Lw.bits1 col hc,
    fun hr => by rw [got_of (R.pin col) hr, u3Form_value]; exact Lw.count col hc⟩

/-- Some world meets the law, if the three tables lie one behind the other. -/
theorem readsLaw_some (h : FoNums.Sh) (lm : ℕ) (zb0 zb1 : List K) (ν : Pl → K)
    (iU3 K3 tB0 tB1 tP : ℕ) (h01 : tB0 + planeCols h lm ≤ tB1)
    (h1P : tB1 + planeCols h lm ≤ tP) :
    ∃ entry, ReadsLaw h lm zb0 zb1 ν entry iU3 K3 tB0 tB1 tP := by
  refine ⟨fun _ r x =>
    if r * K3 + x < tB1 then colsK h lm zb0 ν (r * K3 + x - tB0)
    else if r * K3 + x < tP then colsK h lm zb1 ν (r * K3 + x - tB1)
    else pinColK lm ν (r * K3 + x - tP), ?_, ?_, ?_⟩
  · intro col hc
    unfold u3Val
    simp only [Nat.div_add_mod']
    rw [if_pos (by omega), Nat.add_sub_cancel_left]
    rfl
  · intro col hc
    unfold u3Val
    simp only [Nat.div_add_mod']
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    rfl
  · intro col hc
    unfold u3Val
    simp only [Nat.div_add_mod']
    rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
    rfl

/-- The law fixes the entries of the three tables. -/
theorem readsLaw_pins {h : FoNums.Sh} {lm : ℕ} {zb0 zb1 : List K} {ν : Pl → K}
    {e₁ e₂ : ℕ → ℕ → ℕ → K} {iU3 K3 tB0 tB1 tP : ℕ}
    (L₁ : ReadsLaw h lm zb0 zb1 ν e₁ iU3 K3 tB0 tB1 tP)
    (L₂ : ReadsLaw h lm zb0 zb1 ν e₂ iU3 K3 tB0 tB1 tP) (col : ℕ) (hc : col < planeCols h lm) :
    u3Val e₁ iU3 K3 (tB0 + col) = u3Val e₂ iU3 K3 (tB0 + col) ∧
    u3Val e₁ iU3 K3 (tB1 + col) = u3Val e₂ iU3 K3 (tB1 + col) ∧
    u3Val e₁ iU3 K3 (tP + col) = u3Val e₂ iU3 K3 (tP + col) :=
  ⟨(L₁.bits0 col hc).trans (L₂.bits0 col hc).symm, (L₁.bits1 col hc).trans (L₂.bits1 col hc).symm,
    (L₁.count col hc).trans (L₂.count col hc).symm⟩

end

/-! ### the three sites -/

/-- The layers: what claimsPlanes hands to the lookup's claims. -/
def bitLayer (v : Layer.Env) (tB0 tB1 e x : ℕ) : SubM Aff :=
  Layer.form (if x < v.y.kbm then v.U3at (if e == 0 then tB0 else tB1) x else none)
def pinLayer (v : Layer.Env) (tP x : ℕ) : SubM Aff :=
  Layer.form (if x < v.y.kbm then v.U3at tP x else none)

theorem claimsPlanes_eq (v : Layer.Env) (fo : Forest.Heard) :
    Layer.claimsPlanes v fo = (do
      let tB0 ← Layer.form (v.tabAt "b-bits-0")
      let tB1 ← Layer.form (v.tabAt "b-bits-1")
      let tP ← Layer.form (v.tabAt "b-pin")
      Forest.planeLins fo v.y.h.lmb (bitLayer v tB0 tB1) (pinLayer v tP)) := rfl

theorem U3at_some (v : Layer.Env) (t i : ℕ) (b : Aff) (h : v.U3at t i = some b) :
    b = u3Form v.iU3 v.K3 (t + i) := by
  unfold Layer.Env.U3at at h
  split at h
  · cases h
  · simp only at h
    split at h
    · exact (Option.some.inj h).symm
    · cases h

theorem gives_layer (v : Layer.Env) (t x : ℕ) (F : Fork) (c : Ctx) :
    Gives (Layer.form (if x < v.y.kbm then v.U3at t x else none)) F c
      (u3Form v.iU3 v.K3 (t + x)) :=
  gives_get _ F c _ fun b hb => by
    split at hb
    · exact U3at_some v t x b hb
    · cases hb

theorem readsAt_layer (v : Layer.Env) (tB0 tB1 tP : ℕ) (F : Fork) (c : Ctx) :
    ReadsAt (bitLayer v tB0 tB1) (pinLayer v tP) v.iU3 v.K3 tB0 tB1 tP F c where
  bit0 := fun col => gives_layer v tB0 col F c
  bit1 := fun col => gives_layer v tB1 col F c
  bitQ := fun e col => (gives_layer v (if e == 0 then tB0 else tB1) col F c).1
  pin := fun col => gives_layer v tP col F c

/-- Attention: what claims hands to the lookup's claims. -/
def bitAtt (h : Attention.Heard) (e col : ℕ) : SubM Aff :=
  Attention.u3at h (if e == 0 then h.t.tBit0 else h.t.tBit1) col
def pinAtt (h : Attention.Heard) (col : ℕ) : SubM Aff := Attention.u3at h h.t.tPin col

theorem att_claims_eq (P : Attention.Plan) (h : Attention.Heard) :
    Attention.claims P h = (do
      Forest.objects h.g
      let j ← Attention.claim3 h (Attention.Joins.empty P.NC)
      let j ← Attention.claim4 h j
      let j ← Attention.claim5 h j
      Attention.allJoined j
      Attention.paddingLaid h.S h.g
      SubM.lin (← Forest.join h.g j.kf)
      Attention.claim6 h
      Attention.claim7 h
      Attention.claim8 h
      Forest.planeLins h.g h.S.cf.lmb (bitAtt h) (pinAtt h)) := rfl

theorem gives_att (h : Attention.Heard) (t i : ℕ) (F : Fork) (c : Ctx) :
    Gives (Attention.u3at h t i) F c (u3Form h.iU3 (colsOf F h.iU3) (t + i)) :=
  gives_mustAs _ _ _ F c _ (gives_uEnt h.iU3 (t + i) F c)

theorem readsAt_attention (h : Attention.Heard) (F : Fork) (c : Ctx) :
    ReadsAt (bitAtt h) (pinAtt h) h.iU3 (colsOf F h.iU3) h.t.tBit0 h.t.tBit1 h.t.tPin F c where
  bit0 := fun col => gives_att h h.t.tBit0 col F c
  bit1 := fun col => gives_att h h.t.tBit1 col F c
  bitQ := fun e col => (gives_att h (if e == 0 then h.t.tBit0 else h.t.tBit1) col F c).1
  pin := fun col => gives_att h h.t.tPin col F c

/-- The head: what claimPlanes hands to the lookup's claims. -/
def colHead (R : Head.Run) (t x : ℕ) : SubM Aff := do
  mustAs "internal-h-table-index" (x < R.L.kb)
  Head.U3at R t x
def bitHead (R : Head.Run) (tB0 tB1 e x : ℕ) : SubM Aff := colHead R (if e == 0 then tB0 else tB1) x

theorem claimPlanes_eq (R : Head.Run) :
    Head.claimPlanes R = (do
      let tB0 ← Head.tabAt R "bH-bits-0"
      let tB1 ← Head.tabAt R "bH-bits-1"
      let tP ← Head.tabAt R "bH-pin"
      Forest.planeLins R.x.g1 R.h.lmbH (bitHead R tB0 tB1) (colHead R tP)) := rfl

theorem gives_head (R : Head.Run) (t x : ℕ) (F : Fork) (c : Ctx) :
    Gives (colHead R t x) F c (u3Form R.iU3 (colsOf F R.iU3) (t + x)) :=
  gives_mustAs _ _ _ F c _ (gives_mustAs _ _ _ F c _ (gives_uEnt R.iU3 (t + x) F c))

theorem readsAt_head (R : Head.Run) (tB0 tB1 tP : ℕ) (F : Fork) (c : Ctx) :
    ReadsAt (bitHead R tB0 tB1) (colHead R tP) R.iU3 (colsOf F R.iU3) tB0 tB1 tP F c where
  bit0 := fun col => gives_head R tB0 col F c
  bit1 := fun col => gives_head R tB1 col F c
  bitQ := fun e col => (gives_head R (if e == 0 then tB0 else tB1) col F c).1
  pin := fun col => gives_head R tP col F c

end Fo
