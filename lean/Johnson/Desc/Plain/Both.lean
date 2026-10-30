-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Both.lean: the plain form FOR A BATCH, IN TWO PARTS: what hangs on a key is paid
once, what hangs on a slot's own statement once for each slot: "εK + N · εO".

`K.LeadsB key on Q εK εO`: there are two games. `lostK k`: a property of the transcript that is a
function of the key alone: the prover has lost towards it at εK. `lostO a`: one that may read the
whole statement: lost at εO, on the statements with `on`. Where both hold and the verifier puts out
b: Q a b.
`K.LeadsBN key on Q N ε`: the same with one list of errors ε that bears εK + N · εO in each round:
the form of a block's own errors.

  `LeadsK.both` (εO = 0), `Leads.both` (εK = 0: the union bound): the two cases.
  `LeadsB.seq`, `LeadsBN.seq`: two in a row. The hand-over of the condition (hon) IS HANDED THE
    FIRST REDUCTION's OUTPUT: "K₁.out a τ = some b": so the condition behind may hold what is known
    of b for certain, of a slot's own part too. `leadsBN_cast` | `_comap` | `_front` | `_congr`:
    the moves.
  `LeadsBN.toLinkJ`: the door: the library's `LinkJ` for a batch of at most N statements with one
    key, at ε. By `jWithin_both` (Johnson/Desc/Sound/FoldSlotsProofs.lean), whose rule
    `knowB_of_lost_both` this file follows, without a witness.
Limits: those of Keyed.lean. The split (εK, εO) stands under "there is". N = 0 IS NOT MEANT: there N
  · εO is 0 whatever εO is: the law then says nothing of the part that hangs on a slot.
Nearest kin: `Piece.LostBoth`, `knowB_of_lost_both`, `jWithin_both`
(Johnson/Desc/Sound/FoldSlots*.lean): the door follows the second and calls the third; in the
library: `Err.le_refl` (Iop/State.lean:70), `Doomed.append`; `doomed_front`:
`OnBytes.Slice.doomed_cons_all` (OnBytes/Slice/LinkSound.lean), called. TWO SMALL LAWS HERE HAVE
THEIR LIKE ELSEWHERE AND STAY: `Err.times_app` is a twin of `times_app`
(Johnson/Desc/Sound/BelowOfPieces.lean): to call that one this file would import
BelowOfPieces.lean, and then `below_cast` is ambiguous in PlainWorldToy.lean, which opens both
namespaces that have one (tried). `times_zero` has its like inside the proof of `lostBothOfLostBy`
(FoldSlotsProofs.lean), under no name: it cannot be called. In `Leads.seq`,
`LeadsK.seq` (Leads.lean, Keyed.lean) and in `EachLeads`, `EachLeadsK`, `EachLeadsBN`
(FoldChain.lean, FoldChainK.lean, BothAtDesc.lean) the hand-over is NOT handed the output: so along
a row of blocks the two rules' wider hon is not yet spent.

-/
import Johnson.Desc.Plain.Moves
import OnBytes.Slice.LinkSound
import Johnson.Desc.Sound.FoldSlotsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop

theorem Err.times_app (N : ℕ) : ∀ {s t : Shape} (a : Err s) (b : Err t),
    Err.times N (Err.app a b) = Err.app (Err.times N a) (Err.times N b)
  | [], _, _, _ => rfl
  | _ :: _, _, (e, a), b => by
      show (N * e, Err.times N (Err.app a b)) = (N * e, Err.app (Err.times N a) (Err.times N b))
      rw [Err.times_app N a b]

namespace Reduction
open _root_.Prob (cnt cnt_false)
variable {A B C A' B' κ κ₂ κ₃ : Type}

/-- The plain form for a batch, in two parts. -/
def LeadsB (K : Reduction A B) (key : A → κ) (on : A → Prop) (Q : A → B → Prop)
    (εK εO : Err K.shape) : Prop :=
  ∃ (lostK : κ → Tr K.shape → Prop) (lostO : A → Tr K.shape → Prop),
    (∀ k, Doomed K.shape εK (lostK k)) ∧ (∀ a, on a → Doomed K.shape εO (lostO a)) ∧
      ∀ a τ b, on a → lostK (key a) τ → lostO a τ → K.out a τ = some b → Q a b

/-- The same at one list of errors that bears the split for N slots. -/
def LeadsBN (K : Reduction A B) (key : A → κ) (on : A → Prop) (Q : A → B → Prop) (N : ℕ)
    (ε : Err K.shape) : Prop :=
  ∃ εK εO : Err K.shape, Err.le (Err.add εK (Err.times N εO)) ε ∧ K.LeadsB key on Q εK εO

section Cases
variable {K : Reduction A B} {key : A → κ} {on : A → Prop} {Q : A → B → Prop} {ε : Err K.shape}

/-- Nothing of a slot's own. -/
theorem LeadsK.both (h : K.LeadsK key on Q ε) : K.LeadsB key on Q ε (Err.zero K.shape) :=
  ⟨fun k τ => ∀ a, key a = k → on a → ∀ b, K.out a τ = some b → Q a b, fun _ _ => True, h,
    fun _ _ => Doomed.of_forall _ _ fun _ => trivial,
    fun a _ b ha hk _ hb => hk a rfl ha b hb⟩

/-- Nothing shared: the union bound. -/
theorem Leads.both (key : A → κ) (h : K.Leads on Q ε) : K.LeadsB key on Q (Err.zero K.shape) ε :=
  ⟨fun _ _ => True, fun a τ => ∀ b, K.out a τ = some b → Q a b,
    fun _ => Doomed.of_forall _ _ fun _ => trivial, h, fun _ _ b _ _ ho hb => ho b hb⟩

end Cases

theorem times_zero (N : ℕ) : ∀ s : Shape, Err.times N (Err.zero s) = Err.zero s
  | [] => rfl
  | _ :: s => by
      show (N * 0, Err.times N (Err.zero s)) = (0, Err.zero s)
      rw [times_zero N s, Nat.mul_zero]

theorem LeadsK.bothN {K : Reduction A B} {key : A → κ} {on : A → Prop} {Q : A → B → Prop}
    {ε : Err K.shape} (h : K.LeadsK key on Q ε) (N : ℕ) : K.LeadsBN key on Q N ε :=
  ⟨ε, Err.zero K.shape, by rw [times_zero, Err.add_zero]; exact Err.le_refl ε, h.both⟩

/-- **Two in a row.** hon, the hand-over of the condition, is handed the first reduction's
output. -/
theorem LeadsB.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {key₁ : A → κ} {key₂ : B → κ₂}
    {on₁ : A → Prop} {on₂ : B → Prop} {Q₁ : A → B → Prop} {Q₂ : B → C → Prop}
    {εK₁ εO₁ : Err K₁.shape} {εK₂ εO₂ : Err K₂.shape} (h₁ : K₁.LeadsB key₁ on₁ Q₁ εK₁ εO₁)
    (h₂ : K₂.LeadsB key₂ on₂ Q₂ εK₂ εO₂)
    (hon : ∀ a τ b, on₁ a → K₁.out a τ = some b → Q₁ a b → on₂ b) (law : K₁.KeyLaw key₁ key₂) :
    (K₁.seq K₂).LeadsB key₁ on₁ (fun a c => ∃ b, Q₁ a b ∧ Q₂ b c) (Err.app εK₁ εK₂)
      (Err.app εO₁ εO₂) := by
  obtain ⟨lK₁, lO₁, dK₁, dO₁, q₁⟩ := h₁
  obtain ⟨lK₂, lO₂, dK₂, dO₂, q₂⟩ := h₂
  obtain ⟨g, lw⟩ := law
  refine ⟨fun k τ => lK₁ k (Tr.fst τ) ∧ lK₂ (g k (Tr.fst τ)) (Tr.snd (s := K₁.shape) τ),
    fun a τ => lO₁ a (Tr.fst τ) ∧
      ∀ b, K₁.out a (Tr.fst τ) = some b → on₂ b → lO₂ b (Tr.snd (s := K₁.shape) τ),
    fun k => ?_, fun a ha => ?_, fun a τ c ha hk ho hc => ?_⟩
  · refine Doomed.append K₁.shape K₂.shape _ _ _ (Doomed.mono _ _ ?_ (dK₁ k))
    intro τ₁ h1
    refine Doomed.mono _ _ ?_ (dK₂ (g k τ₁))
    intro τ₂ h2
    beta_reduce
    rw [Tr.fst_app, Tr.snd_app]
    exact ⟨h1, h2⟩
  · refine Doomed.append K₁.shape K₂.shape _ _ _ (Doomed.mono _ _ ?_ (dO₁ a ha))
    intro τ₁ h1
    cases hout : K₁.out a τ₁ with
    | none =>
      refine Doomed.of_forall _ _ fun τ₂ => ?_
      beta_reduce
      rw [Tr.fst_app, Tr.snd_app]
      exact ⟨h1, fun b hb => by rw [hout] at hb; cases hb⟩
    | some b =>
      by_cases hb2 : on₂ b
      · refine Doomed.mono _ _ ?_ (dO₂ b hb2)
        intro τ₂ h2
        beta_reduce
        rw [Tr.fst_app, Tr.snd_app]
        refine ⟨h1, fun b' hb' _ => ?_⟩
        rw [hout] at hb'
        obtain rfl := Option.some.inj hb'
        exact h2
      · refine Doomed.of_forall _ _ fun τ₂ => ?_
        beta_reduce
        rw [Tr.fst_app, Tr.snd_app]
        refine ⟨h1, fun b' hb' ho' => ?_⟩
        rw [hout] at hb'
        obtain rfl := Option.some.inj hb'
        exact absurd ho' hb2
  · obtain ⟨b, hb, hbc⟩ := Option.bind_eq_some_iff.1 hc
    have hq := q₁ a _ b ha hk.1 ho.1 hb
    have hb2 := hon a _ b ha hb hq
    refine ⟨b, hq, q₂ b _ c hb2 ?_ (ho.2 b hb hb2) hbc⟩
    rw [lw a _ b hb]
    exact hk.2

theorem LeadsBN.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {key₁ : A → κ} {key₂ : B → κ₂}
    {on₁ : A → Prop} {on₂ : B → Prop} {Q₁ : A → B → Prop} {Q₂ : B → C → Prop} {N : ℕ}
    {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape} (h₁ : K₁.LeadsBN key₁ on₁ Q₁ N ε₁)
    (h₂ : K₂.LeadsBN key₂ on₂ Q₂ N ε₂)
    (hon : ∀ a τ b, on₁ a → K₁.out a τ = some b → Q₁ a b → on₂ b) (law : K₁.KeyLaw key₁ key₂) :
    (K₁.seq K₂).LeadsBN key₁ on₁ (fun a c => ∃ b, Q₁ a b ∧ Q₂ b c) N (Err.app ε₁ ε₂) := by
  obtain ⟨a₁, b₁, l₁, k₁⟩ := h₁
  obtain ⟨a₂, b₂, l₂, k₂⟩ := h₂
  refine ⟨Err.app a₁ a₂, Err.app b₁ b₂, ?_, k₁.seq k₂ hon law⟩
  rw [Err.times_app, Err.add_app]
  exact Err.le_app l₁ l₂

/-! ## The moves -/

theorem leadsBN_cast {s t : Shape} (h : s = t) (out : A → Tr t → Option B) (key : A → κ)
    (on : A → Prop) (Q : A → B → Prop) (N : ℕ) (ε : Err s)
    (k : (⟨s, fun a τ => out a (cast (congrArg Tr h) τ)⟩ : Reduction A B).LeadsBN key on Q N ε) :
    (⟨t, out⟩ : Reduction A B).LeadsBN key on Q N (cast (congrArg Err h) ε) := by
  subst h
  exact k

theorem leadsBN_comap (K : Reduction A B) (out' : A' → Tr K.shape → Option B') (φ : A' → A)
    (key : A → κ) (on : A → Prop) (Q : A → B → Prop) (N : ℕ) (ε : Err K.shape)
    (Q' : A' → B' → Prop)
    (h : ∀ a' τ b', on (φ a') → out' a' τ = some b' →
      ∃ b, K.out (φ a') τ = some b ∧ (Q (φ a') b → Q' a' b'))
    (k : K.LeadsBN key on Q N ε) :
    (⟨K.shape, out'⟩ : Reduction A' B').LeadsBN (fun a' => key (φ a')) (fun a' => on (φ a')) Q' N
      ε := by
  obtain ⟨εK, εO, hle, lK, lO, dK, dO, q⟩ := k
  refine ⟨εK, εO, hle, lK, fun a' => lO (φ a'), dK, fun a' ha' => dO (φ a') ha',
    fun a' τ b' ha' hk ho hb' => ?_⟩
  obtain ⟨b, h1, h2⟩ := h a' τ b' ha' hb'
  exact h2 (q (φ a') τ b ha' hk ho h1)

theorem doomed_front (r : Round) (s : Shape) (ε : Err s) (lost : Tr s → Prop)
    (h : Doomed s ε lost) : Doomed (r :: s) (0, ε) (fun τ => lost τ.2.2) :=
  OnBytes.Slice.doomed_cons_all ε (fun τ => lost τ.2.2) fun _ _ => h

theorem leadsBN_front (r : Round) (K : Reduction A B) (ok : A → r.Msg → Bool) (key : A → κ)
    (on : A → Prop) (Q : A → B → Prop) (N : ℕ) (ε : Err K.shape) (k : K.LeadsBN key on Q N ε) :
    (⟨r :: K.shape, fun a τ => if ok a τ.1 then K.out a τ.2.2 else none⟩ :
      Reduction A B).LeadsBN key on Q N (0, ε) := by
  obtain ⟨εK, εO, hle, lK, lO, dK, dO, q⟩ := k
  refine ⟨(0, εK), (0, εO), ⟨by simp, hle⟩, fun x τ => lK x τ.2.2, fun a τ => lO a τ.2.2,
    fun x => doomed_front r _ _ _ (dK x), fun a ha => doomed_front r _ _ _ (dO a ha),
    fun a τ b ha hk ho hb => ?_⟩
  have hb' : (if ok a τ.1 then K.out a τ.2.2 else none) = some b := hb
  cases hok : ok a τ.1 with
  | false =>
    rw [hok] at hb'
    cases hb'
  | true =>
    rw [hok] at hb'
    exact q a _ b ha hk ho hb'

theorem leadsBN_congr (K : Reduction A B) (out' : A → Tr K.shape → Option B)
    (h : ∀ a τ, out' a τ = K.out a τ) (key : A → κ) (on : A → Prop) (Q : A → B → Prop) (N : ℕ)
    (ε : Err K.shape) (k : K.LeadsBN key on Q N ε) :
    (⟨K.shape, out'⟩ : Reduction A B).LeadsBN key on Q N ε := by
  obtain ⟨εK, εO, hle, lK, lO, dK, dO, q⟩ := k
  exact ⟨εK, εO, hle, lK, lO, dK, dO,
    fun a τ b ha hk ho hb => q a τ b ha hk ho ((h a τ).symm.trans hb)⟩

end Reduction
end Iop

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.CompileK.Joined (KnowJ)

/-- **The door: a link of a batch, at the block's own errors.** -/
theorem LeadsBN.toLinkJ {A B κ κ₂ WA WB : Type} {K : Reduction A B} {key : A → κ} {on : A → Prop}
    {Q : A → B → Prop} {N : ℕ} {ε : Err K.shape} (h : K.LeadsBN key on Q N ε) {key₂ : B → κ₂}
    {RA : A → WA → Prop} {RB : B → WB → Prop} (ext : A → Tr K.shape → WB → WA)
    (hf : ∀ a τ b w, K.out a τ = some b → (on a → Q a b) → RB b w → RA a (ext a τ w))
    (g : κ → Tr K.shape → κ₂) (law : ∀ a τ b, K.out a τ = some b → key₂ b = g (key a) τ) :
    LinkJ K (RoundSplits.const (RAnn.ofShared .sh) K.shape) N key key₂ (fun _ => True) RA RB ext ε := by
  obtain ⟨εK, εO, hle, lK, lO, dK, dO, q⟩ := h
  refine ⟨⟨fun a => (lostFam K.shape εK (lK (key a))).both (lostFam K.shape εO (lO a)),
    fun a τ b w _ hτ hb hw => ?_, fun a ha => JWithin.mono N _ _ _ hle ?_⟩, adm_of_tr g law⟩
  · obtain ⟨h1, h2⟩ := BadFam.clean_both _ _ τ hτ
    exact hf a τ b w hb
      (fun ho => q a τ b ho (lostFam_clean (dK (key a)) h1) (lostFam_clean (dO a ho) h2) hb) hw
  · by_cases hne : ∃ j aj, a j = some aj
    · obtain ⟨j₀, a₀, h₀⟩ := hne
      refine jWithin_both N K.shape εK εO (lostFam K.shape εK (lK (key a₀)))
        (fun j => ((a j).map fun aj => lostFam K.shape εO (lO aj)).getD (BadFam.empty _)) _
        (lostFam_within _ _ _) (fun j => ?_) fun j p hp => ?_
      · beta_reduce
        cases a j with
        | none => exact BadFam.empty_within _ _
        | some aj => exact lostFam_within _ _ _
      · obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
        show (lostFam K.shape εK (lK (key aj))).both (lostFam K.shape εO (lO aj)) = _
        beta_reduce
        rw [ha j j₀ aj a₀ haj h₀, haj]
        rfl
    · refine jWithin_both N K.shape εK εO (BadFam.empty _) (fun _ => BadFam.empty _) _
        (BadFam.empty_within _ _) (fun _ => BadFam.empty_within _ _) fun j p hp => ?_
      obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact absurd ⟨j, aj, haj⟩ hne

end TypedOracleCompiler.Joined

#print axioms Iop.Reduction.LeadsB.seq
#print axioms Iop.Reduction.LeadsBN.seq
#print axioms Iop.Reduction.leadsBN_front
#print axioms TypedOracleCompiler.Joined.LeadsBN.toLinkJ
