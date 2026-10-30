-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CarrySkip.lean: maps from the written rounds of a file to the rounds of a typed
protocol that has fewer rounds, and the carrying of soundness along them.

One inductive type, two functions, four theorems. `Carry` (OnBytes/Slice/Carry.lean) exists between
shapes of one length alone. A written file has rounds that a typed protocol lacks: the front round,
the joining round, the seam, a sealing round. `CarryS s s'` has a third case for them.

Main names:
  `CarryS s s'`: `nil`; `step fm fc k`: a written round is read as the next typed round: the
    prover's message by fm, the verifier's by fc, which may read the round's prover message and is
    `none` where a written message has no typed image; `skip k`: a written round that the typed
    shape lacks. The later rounds' maps k may read the round's two messages.
  `CarryS.tr`: the image of a written transcript; `none` if a verifier message has no image.
  `CarryS.Fits F ε ε'`: the error counts ε' of the written rounds bear those of the typed rounds: at
    a step e · w ≤ e', where at most w written verifier messages go to one typed message; at a
    skipped round nothing is asked (0 serves).
  `CarryS.doomed`, `sound_carryS`, `know_carryS`; `backS`, `backS_know`: as `Carry.doomed`,
    `sound_carry` (OnBytes/Slice/Carry.lean), `know_carry`, `back`, `back_know`
    (OnBytes/Flat/Transport.lean [not in this library]).

Limits: one direction. What a skipped round sends is read by no typed verifier: a test that a file's
verifier makes on it is not carried.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.Carry
import Ior.Know

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob OnBytes.Slice

/-- Maps from the written shape to a typed shape that may lack rounds. -/
inductive CarryS : Shape → Shape → Type 1
  | nil : CarryS [] []
  | step {r r' : Round} {s s' : Shape} (fm : r.Msg → r'.Msg)
      (fc : r.Msg → r.Chal → Option r'.Chal) (k : r.Msg → r.Chal → CarryS s s') :
      CarryS (r :: s) (r' :: s')
  | skip {r : Round} {s s' : Shape} (k : r.Msg → r.Chal → CarryS s s') : CarryS (r :: s) s'

namespace CarryS

/-- The image of a written transcript. -/
def tr : {s s' : Shape} → CarryS s s' → Tr s → Option (Tr s')
  | _, _, .nil, _ => some ()
  | _, _, .step fm fc k, (m, c, τ) =>
      (fc m c).bind fun c' => (tr (k m c) τ).map fun τ' => (fm m, c', τ')
  | _, _, .skip k, (m, c, τ) => tr (k m c) τ

/-- The written rounds' error counts bear the typed rounds'. -/
def Fits : {s s' : Shape} → CarryS s s' → Err s' → Err s → Prop
  | _, _, .nil, _, _ => True
  | _, _, .step (r := r) (r' := r') _ fc k, (e, ε), (e', ε') =>
      (∃ w, (∀ (m : r.Msg) (c' : r'.Chal), cnt (fun c => fc m c = some c') ≤ w) ∧ e * w ≤ e') ∧
        ∀ m c, Fits (k m c) ε ε'
  | _, _, .skip k, ε, (_, ε') => ∀ m c, Fits (k m c) ε ε'

/-- **The prover's loss is carried back.** -/
theorem doomed : ∀ {s s' : Shape} (F : CarryS s s') (ε : Err s') (ε' : Err s), F.Fits ε ε' →
    ∀ (bad : Tr s → Prop) (bad' : Tr s' → Prop), (∀ τ, F.tr τ = none → bad τ) →
    (∀ τ τ', F.tr τ = some τ' → bad' τ' → bad τ) → Doomed s' ε bad' → Doomed s ε' bad
  | _, _, .nil, _, _, _, _, _, _, h, hd => h () () rfl hd
  | _, _, .step (r := r) (r' := r') (s := s) (s' := s') fm fc k, (e, ε), (e', ε'), hF, bad, bad',
      h0, h, hd => fun m => by
      obtain ⟨⟨w, hw, hle⟩, hk⟩ := hF
      show cnt (fun c : r.Chal => ¬ Doomed s ε' (fun τ => bad (m, c, τ))) ≤ e'
      have key : ∀ c : r.Chal, ¬ Doomed s ε' (fun τ => bad (m, c, τ)) →
          ∃ c', fc m c = some c' ∧ ¬ Doomed s' ε (fun τ' => bad' (fm m, c', τ')) := by
        intro c hc
        cases hfc : fc m c with
        | none =>
          refine absurd (doomed_of_all s _ _ fun τ => h0 (m, c, τ) ?_) hc
          show (fc m c).bind _ = none
          rw [hfc]
          rfl
        | some c' =>
          refine ⟨c', rfl, fun hd' => hc ?_⟩
          refine doomed (k m c) ε ε' (hk m c) _ _ ?_ ?_ hd'
          · intro τ hτ
            refine h0 (m, c, τ) ?_
            show (fc m c).bind _ = none
            rw [hfc]
            show ((k m c).tr τ).map _ = none
            rw [hτ]
            rfl
          · intro τ τ' hτ hb
            refine h (m, c, τ) (fm m, c', τ') ?_ hb
            show (fc m c).bind _ = some _
            rw [hfc]
            show ((k m c).tr τ).map _ = some _
            rw [hτ]
            rfl
      exact ((cnt_mono key).trans
        ((cnt_some_le (fc m) (hw m) _).trans (Nat.mul_le_mul_right w (hd (fm m))))).trans hle
  | _, _, .skip (r := r) (s := s) k, ε, (e', ε'), hF, bad, bad', h0, h, hd => fun m => by
      show cnt (fun c : r.Chal => ¬ Doomed s ε' (fun τ => bad (m, c, τ))) ≤ e'
      refine le_trans (le_of_eq (cnt_false fun c hc => hc ?_)) (Nat.zero_le _)
      exact doomed (k m c) ε ε' (hF m c) _ bad' (fun τ hτ => h0 (m, c, τ) hτ)
        (fun τ τ' hτ hb => h (m, c, τ) τ' hτ hb) hd

end CarryS

/-- **Round-by-round soundness is carried to a protocol with more rounds.** -/
theorem sound_carryS {X X' : Type} {E E' : ExtSpec} (Q : InteractiveOracleProof X E) (Q' : InteractiveOracleProof X' E')
    (F : X → E.Str → CarryS Q.shape Q'.shape) (ε : Err Q'.shape) (ε' : Err Q.shape)
    (hF : ∀ x y, (F x y).Fits ε ε') (fx : X → X') (fy : E.Str → E'.Str)
    (L : X → E.Str → Prop) (L' : X' → E'.Str → Prop) (hL : ∀ x y, L' (fx x) (fy y) → L x y)
    (hacc : ∀ x y τ, Q.accept x y τ = true →
      ∃ τ', (F x y).tr τ = some τ' ∧ Q'.accept (fx x) (fy y) τ' = true)
    (h : Q'.Sound L' ε) : Q.Sound L ε' := fun x y hn =>
  CarryS.doomed (F x y) ε ε' (hF x y) (fun τ => Q.accept x y τ = false)
    (fun τ' => Q'.accept (fx x) (fy y) τ' = false)
    (fun τ hτ => by
      show Q.accept x y τ = false
      cases ha : Q.accept x y τ with
      | false => rfl
      | true =>
        obtain ⟨τ', h1, _⟩ := hacc x y τ ha
        rw [hτ] at h1
        cases h1)
    (fun τ τ' hτ hb => by
      show Q.accept x y τ = false
      have hb' : Q'.accept (fx x) (fy y) τ' = false := hb
      cases ha : Q.accept x y τ with
      | false => rfl
      | true =>
        obtain ⟨τ'', h1, h2⟩ := hacc x y τ ha
        rw [hτ] at h1
        cases h1
        rw [hb'] at h2
        cases h2)
    (h (fx x) (fy y) fun hl => hn (hL x y hl))

variable {A B WA WB A' B' WA' WB' : Type}

/-- **Round-by-round knowledge soundness is carried to a reduction with more rounds.** -/
theorem know_carryS (K : Reduction A B) (K' : Reduction A' B') (F : A → CarryS K.shape K'.shape)
    (ε : Err K'.shape) (ε' : Err K.shape) (hF : ∀ a, (F a).Fits ε ε') (fa : A → A')
    (on : A → Prop) (on' : A' → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
    (RA' : A' → WA' → Prop) (RB' : B' → WB' → Prop) (ext : A → Tr K.shape → WB → WA)
    (ext' : A' → Tr K'.shape → WB' → WA') (hon : ∀ a, on a → on' (fa a))
    (hout : ∀ a τ b w, on a → K.out a τ = some b → RB b w →
      ∃ τ' b' w', (F a).tr τ = some τ' ∧ K'.out (fa a) τ' = some b' ∧ RB' b' w' ∧
        (RA' (fa a) (ext' (fa a) τ' w') → RA a (ext a τ w)))
    (h : K'.Know on' RA' RB' ext' ε) : K.Know on RA RB ext ε' := fun a ha =>
  CarryS.doomed (F a) ε ε' (hF a)
    (fun τ => ∀ b w, K.out a τ = some b → RB b w → RA a (ext a τ w))
    (fun τ' => ∀ b' w', K'.out (fa a) τ' = some b' → RB' b' w' → RA' (fa a) (ext' (fa a) τ' w'))
    (fun τ hτ b w hb hw => by
      obtain ⟨τ', _, _, h1, _⟩ := hout a τ b w ha hb hw
      rw [hτ] at h1
      cases h1)
    (fun τ τ' hτ hbad b w hb hw => by
      obtain ⟨τ'', b', w', h1, h2, h3, h4⟩ := hout a τ b w ha hb hw
      rw [hτ] at h1
      cases h1
      exact h4 (hbad b' w' h2 h3))
    (h (fa a) (hon a ha))

/-- The typed reduction read on the written rounds. -/
def backS {s : Shape} (K' : Reduction A' B') (F : A → CarryS s K'.shape) (fa : A → A') :
    Reduction A B' where
  shape := s
  out := fun a τ => ((F a).tr τ).bind (K'.out (fa a))

/-- Its knowledge soundness, from that of the typed reduction. -/
theorem backS_know {s : Shape} (K' : Reduction A' B') (F : A → CarryS s K'.shape)
    (ε : Err K'.shape) (ε' : Err s) (hF : ∀ a, (F a).Fits ε ε') (fa : A → A') (on' : A' → Prop)
    (RA' : A' → WA' → Prop) (RB' : B' → WB' → Prop) (ext' : A' → Tr K'.shape → WB' → WA')
    (tr₀ : Tr K'.shape) (h : K'.Know on' RA' RB' ext' ε) :
    (backS K' F fa).Know (fun a => on' (fa a)) (fun a w => RA' (fa a) w) RB'
      (fun a τ w => ext' (fa a) (((F a).tr τ).getD tr₀) w) ε' :=
  know_carryS (backS K' F fa) K' F ε ε' hF fa _ on' _ RB' RA' RB' _ ext' (fun _ ha => ha)
    (fun a τ b w _ hb hw => by
      have hb' : ((F a).tr τ).bind (K'.out (fa a)) = some b := hb
      cases hτ : (F a).tr τ with
      | none =>
        rw [hτ] at hb'
        cases hb'
      | some τ' =>
        rw [hτ] at hb'
        refine ⟨τ', b, w, ?_, hb', hw, fun hr => hr⟩
        first | rfl | exact hτ) h

end OnBytes.Flat

#print axioms OnBytes.Flat.CarryS.doomed
#print axioms OnBytes.Flat.sound_carryS
#print axioms OnBytes.Flat.backS_know
