-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Pinned.lean: WHERE THE WORLD STANDS: OUTSIDE THE GAME OR INSIDE IT.

The question. The library's clauses for a block that speaks of committed messages m are "∀ m, … Know
…": m IS FIXED OUTSIDE THE GAME: the bad challenges hang on m (they are roots of polynomials made of
m). `KeepsW` (Johnson/Desc/Plain/World.lean) has "∀ w, R' b w → R a w" INSIDE the game's event. FROM
"∀ m, the prover has lost towards P m" NO "the prover has lost towards ∀ m, P m" FOLLOWS: the bad
sets' union is not bounded.

The answer. A law with the world outside the game (`∀ m, K.Leads on (Q m) ε`) composes along a chain
for each m by itself, and says nothing at the end, where the world that is meant is read off the
LAST statement, so off the transcript. What carries it inside is A PIN: the part m of the world on
which the block's bad challenges hang IS FIXED BY THE STATEMENT IN FRONT: it is what the oracles
that the statement already holds decode to (`mOf a`); and the relation behind says so of w (the pins
are among the border's items). What is sent later is no part of m; what is sent in the block's own
rounds is a prover's message of the game.

  `leads_of_pinned`: from `∀ m, K.Leads on (Q m) ε`: `K.Leads on (fun a b => Q (mOf a) a b) ε`: at
    the same errors.
  `keepsW_of_pinned`: so `KeepsW`, where R' b w gives "the part of w is mOf a" (`pin`).
  `keepsW_of_pinned_first`: the part may also be read off THE MESSAGE OF THE BLOCK's FIRST ROUND (a
    block that commits in its first round and tests behind it): that message stands before the
    round's count.
  `not_inside`: THE QUESTION's OWN POINT AS A THEOREM: a round of two challenges at which "∀ m, the
    prover has lost towards P m" holds at the error 1 and "the prover has lost towards ∀ m, P m"
    fails at it.
  `doomed_list`, `keepsW_of_listed`: where the statement in front fixes the part only up to a list
    of at most ℓ values (decoding to a list): at ℓ times the errors.
Limits: those of Leads.lean. That a border's relation holds the pins, and that `mOf` is the one
decoder of the top's extractor, is the table of joints' matter.

Nearest kin in the library. `Doomed.and` (Iop/Compose.lean), of which `doomed_list` is the fold over
a list.


-/
import Johnson.Desc.Plain.World
import Ior.BatchSeq
import Ior.Draw

set_option autoImplicit false

namespace Iop
namespace Reduction
variable {A B W Mm : Type}

/-- The world's part is read off the statement in front: the law with it outside the game is a
law. -/
theorem leads_of_pinned {K : Reduction A B} {on : A → Prop} {Q : Mm → A → B → Prop}
    {ε : Err K.shape} (mOf : A → Mm) (h : ∀ m, K.Leads on (Q m) ε) :
    K.Leads on (fun a b => Q (mOf a) a b) ε := fun a ha => h (mOf a) a ha

/-- **From the world outside the game to the world inside, by a pin.** -/
theorem keepsW_of_pinned {K : Reduction A B} {on : A → Prop} {on' : B → Prop} {R : A → W → Prop}
    {R' : B → W → Prop} {ε : Err K.shape} (part : W → Mm) (mOf : A → Mm)
    (h : ∀ m, K.Leads on (fun a b => on' b ∧ ∀ w, part w = m → R' b w → R a w) ε)
    (pin : ∀ a τ b w, on a → K.out a τ = some b → R' b w → part w = mOf a) :
    K.KeepsW on on' R R' ε :=
  Leads.conseq (leads_of_pinned mOf h) (fun _ h => h) fun a τ b ha hb hq =>
    ⟨hq.1, fun w hw => hq.2 w (pin a τ b w ha hb hw) hw⟩

/-- **The part read off the statement in front and the message of the block's first round.** -/
theorem keepsW_of_pinned_first {r : Round} {s : Shape} (out : A → Tr (r :: s) → Option B)
    {on : A → Prop} {on' : B → Prop} {R : A → W → Prop} {R' : B → W → Prop} {ε : Err (r :: s)}
    (part : W → Mm) (mOf : A → r.Msg → Mm)
    (h : ∀ m, (⟨r :: s, out⟩ : Reduction A B).Leads on
      (fun a b => on' b ∧ ∀ w, part w = m → R' b w → R a w) ε)
    (pin : ∀ a (τ : Tr (r :: s)) b w, on a → out a τ = some b → R' b w → part w = mOf a τ.1) :
    (⟨r :: s, out⟩ : Reduction A B).KeepsW on on' R R' ε := by
  intro a ha msg
  have hm := h (mOf a msg) a ha msg
  refine le_trans (Prob.cnt_mono ?_) hm
  intro c hc hd
  refine hc (Doomed.mono _ _ ?_ hd)
  intro τ' hτ b hb
  exact ⟨(hτ b hb).1, fun w hw => (hτ b hb).2 w (pin a (msg, c, τ') b w ha hb hw) hw⟩

/-- **The world cannot be carried inside for nothing**: one round, two challenges: towards "the
drawn value is not m" the prover has lost at the error 1, for each m; towards "for every m the drawn
value is not m" it has not. -/
theorem not_inside :
    (∀ m : Bool, Doomed [IOR.drawRound Bool] ((1, ()) : ℕ × Unit) (fun τ => IOR.drawn τ ≠ m)) ∧
      ¬ Doomed [IOR.drawRound Bool] ((1, ()) : ℕ × Unit)
        (fun τ => ∀ m : Bool, IOR.drawn τ ≠ m) := by
  refine ⟨fun m _ => le_trans (Prob.cnt_mono fun c hc => not_not.mp hc)
    (le_of_eq (Prob.cnt_eq_const m)), fun h => ?_⟩
  have h1 := h ((), ())
  have h2 : Prob.cnt (fun _ : Bool => True) ≤ 1 :=
    le_trans (Prob.cnt_mono fun c _ hd => (show ∀ m : Bool, c ≠ m from hd) c rfl) h1
  have h3 : Prob.cnt (fun _ : Bool => True) = 2 := by
    rw [Prob.cnt_true]
    rfl
  omega

/-- Towards finitely many properties at once: the errors once for each. -/
theorem doomed_list {s : Shape} {ε : Err s} {P : Mm → Tr s → Prop} :
    ∀ l : List Mm, (∀ m ∈ l, Doomed s ε (P m)) →
      Doomed s (Err.times l.length ε) (fun τ => ∀ m ∈ l, P m τ)
  | [], _ => Doomed.of_forall _ _ fun _ _ hm => nomatch hm
  | m :: l, h => by
      have h1 := h m List.mem_cons_self
      have h2 := doomed_list l fun m' hm' => h m' (List.mem_cons_of_mem _ hm')
      have h3 := Doomed.and s h1 h2
      have e : ∀ {t : Shape} (δ : Err t) (n : ℕ),
          Err.le (Err.add δ (Err.times n δ)) (Err.times (n + 1) δ) := by
        intro t
        induction t with
        | nil => exact fun _ _ => trivial
        | cons r t ih =>
          rintro ⟨d, δ⟩ n
          exact ⟨by show d + n * d ≤ (n + 1) * d; rw [Nat.succ_mul]; omega, ih δ n⟩
      refine Doomed.mono _ _ ?_ (Doomed.mono_err _ (e ε l.length) h3)
      intro τ hτ m' hm'
      rcases List.mem_cons.1 hm' with rfl | hm''
      · exact hτ.1
      · exact hτ.2 m' hm''

/-- **The same where the statement in front fixes the part up to a list of at most ℓ values.** -/
theorem keepsW_of_listed {K : Reduction A B} {on : A → Prop} {on' : B → Prop} {R : A → W → Prop}
    {R' : B → W → Prop} {ε : Err K.shape} (part : W → Mm) (msOf : A → List Mm) (ℓ : ℕ)
    (hℓ : ∀ a, on a → (msOf a).length = ℓ)
    (h : ∀ m, K.Leads on (fun a b => on' b ∧ ∀ w, part w = m → R' b w → R a w) ε)
    (ne : ∀ a, on a → msOf a ≠ [])
    (pin : ∀ a τ b w, on a → K.out a τ = some b → R' b w → part w ∈ msOf a) :
    K.KeepsW on on' R R' (Err.times ℓ ε) := by
  intro a ha
  have hd := doomed_list (P := fun m τ => ∀ b, K.out a τ = some b →
    on' b ∧ ∀ w, part w = m → R' b w → R a w) (msOf a) fun m _ => h m a ha
  rw [hℓ a ha] at hd
  refine Doomed.mono _ _ ?_ hd
  intro τ hτ b hb
  obtain ⟨m₀, hm₀⟩ := List.exists_mem_of_ne_nil _ (ne a ha)
  exact ⟨(hτ m₀ hm₀ b hb).1, fun w hw => (hτ _ (pin a τ b w ha hb hw) b hb).2 w rfl hw⟩

end Reduction
end Iop

#print axioms Iop.Reduction.keepsW_of_pinned
#print axioms Iop.Reduction.keepsW_of_pinned_first
#print axioms Iop.Reduction.not_inside
#print axioms Iop.Reduction.doomed_list
#print axioms Iop.Reduction.keepsW_of_listed
