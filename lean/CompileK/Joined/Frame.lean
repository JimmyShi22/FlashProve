-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Joined/Frame.lean: the finer count for three joined chains, where the second chain's tail
reads and turns the shared part of a statement alone: its three premises on the tail follow from one
ordinary soundness clause of the tail on shared parts, and two local laws.

A second form of the compiler's verifier side, beside the library's own. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


CompileK/Joined/ExtractKnow.lean has the finer count (`sndBKT_of_four`): the second chain is cut
into a head, whose errors count once for each of the N slots, and a tail, whose errors count once.
For the tail it asks, in the place of the clause `Know`: the game that the prover has lost is a
function of a key of the statement (`lost₂`); on a transcript of that game each slot's backward step
holds (`back₂`); the statements of all slots behind the head have one key (`OneKey`). Here these
three are had where a statement behind the head has a shared part (its key), and the tail is a
reduction K' on shared parts that is carried to whole statements.

Main names:
  `onKey K' key glue`: the reduction K' on keys, carried to statements: it runs K' on the key of the
    statement and lays the output of K' back into the statement.
  `extKey`: its extractor, from that of K'.
  `lost_onKey`, `back_onKey`: `lost₂` and `back₂` for it, from `Know` of K'.
  `ShV`, `shView`: what all slots see alike of a transcript of shared rounds: the shared parts of
    the prover's messages and the verifier's messages. `shView_slot`: they do see it alike.
  `oneKey_of_laws`: `OneKey`, from two laws: what the first chain hands on has a shared part that is
    a function of the external string (`law₁`); the key behind the head is a function of that and of
    the shared view of the head's transcript (`lawJ`).
  `sndBKT_of_frame`, `sndBKT_of_frame_late`: the finer count from these.

What is asked of the relations (`split`, `join`), at what K' yields from the key alone: a witness of
what the tail hands on holds a witness of the shared part that K' hands on; and with a witness of
the key it makes a witness of the statement before the tail.

Where a record, or a public part of the instance, belongs to the shared part: `law₁` makes the first
chain's shared part a function of the external string alone. So such a thing comes in as a parameter
of K₁ (a session has one record in all slots: the rule is used record by record), not through the
instance. `lawJ` reads the key off the shared view: so
what the tail works on must stand in the shared parts of the head's messages or follow from its
verifier messages; it cannot be computed from the slots' own claims.

Beside the library: Ior/KnowBRules.lean has the frame rule in a batch for an IOR
(`knowB_shared_beside`: a block on what the slots share, run once, beside what each slot carries:
the errors once). This file is a sister of it over `Reduction` and `KnowJ`, with the key and the
laying back as letters; it is no new idea. `KnowJ` at an IOR's reduction is the library's `KnowB`
(CompileK/Joined/BatchMid.lean).

Limits: nothing here shows that a real file's second chain has this form.
This list charges the head's two rounds whole N times. The second of them is the round in which the
shared point is drawn. In the library that round's error for a batch has two terms (`errPtB`,
Cb/Ld/LdLinB.lean): one for the fold of the stored table, counted once, and one for a slot's own
claim at the point, counted N times. By a count made outside Lean from the planner's printed
numbers at the default setting (not checked here) the programs' plan does the same, and the first
term fills the bound of 2^-128 to within about a bit: so this list's bound is not met there with 64
slots. In the form with links (OnBytes/TypedOracleCompiler/Joined/MidLinks.lean) the rule adds no factor: it takes
the batch link's own list. That this list is small is still owed there.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Joined.ExtractKnow

set_option autoImplicit false

namespace CompileK.Joined
open Iop Prob

/-! ## A reduction on keys, carried to statements -/

section OnKey
variable {AJ A₂ κ κ' WJ W₂ Wκ Wκ' : Type} (K' : Reduction κ κ') (key : AJ → κ)
  (glue : AJ → κ' → A₂)

/-- K' on the key of a statement; its output is laid back into the statement. -/
@[reducible] def onKey : Reduction AJ A₂ :=
  ⟨K'.shape, fun a τ => (K'.out (key a) τ).map (glue a)⟩

variable (e' : κ → Tr K'.shape → Wκ' → Wκ) (p : W₂ → Wκ') (mk : AJ → W₂ → Wκ → WJ)

/-- the extractor of `onKey`: of the witness behind the tail take the shared part's, run the
extractor of K' on it, and make the witness before the tail -/
def extKey (a : AJ) (τ : Tr K'.shape) (w : W₂) : WJ := mk a w (e' (key a) τ (p w))

variable {K' key glue e' p mk} {on' : κ → Prop} {onJ : AJ → Prop} {Rκ : κ → Wκ → Prop}
  {Rκ' : κ' → Wκ' → Prop} {RJ : AJ → WJ → Prop} {R₂ : A₂ → W₂ → Prop} {ε₂ : Err K'.shape}

/-- the game that the prover has lost in the tail: the goal of `Know` of K', a function of the
key -/
def lostKey (K' : Reduction κ κ') (e' : κ → Tr K'.shape → Wκ' → Wκ) (Rκ : κ → Wκ → Prop)
    (Rκ' : κ' → Wκ' → Prop) (k : κ) (τ : Tr K'.shape) : Prop :=
  ∀ b w, K'.out k τ = some b → Rκ' b w → Rκ k (e' k τ w)

theorem lost_onKey (know : K'.Know on' Rκ Rκ' e' ε₂) (hon : ∀ a, onJ a → on' (key a)) (a : AJ)
    (ha : onJ a) : Doomed (onKey K' key glue).shape ε₂ (lostKey K' e' Rκ Rκ' (key a)) :=
  know (key a) (hon a ha)

theorem back_onKey
    (split : ∀ a τ k' w, K'.out (key a) τ = some k' → R₂ (glue a k') w → Rκ' k' (p w))
    (join : ∀ a τ k' w wk, onJ a → K'.out (key a) τ = some k' → R₂ (glue a k') w →
      Rκ (key a) wk → RJ a (mk a w wk)) (a : AJ)
    (τ : Tr K'.shape) (b : A₂) (w : W₂) (ha : onJ a) (hl : lostKey K' e' Rκ Rκ' (key a) τ)
    (hb : (onKey K' key glue).out a τ = some b) (hw : R₂ b w) :
    RJ a (extKey K' key e' p mk a τ w) := by
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.1 hb
  exact join a τ k' w _ ha hk' hw (hl k' (p w) hk' (split a τ k' w hk' hw))

end OnKey

/-! ## What all slots see alike of shared rounds -/

/-- the shared parts of the prover's messages, and the verifier's messages -/
def ShV : (s : Shape) → RoundSplits s → Type
  | [], _ => Unit
  | r :: s, (a, A) => a.M0 × r.Chal × ShV s A

/-- the shared view of a local transcript -/
def shView : (s : Shape) → (A : RoundSplits s) → Tr s → ShV s A
  | [], _, _ => ()
  | _ :: s, (a, A), (m, c, τ) => ((a.split m).1, c, shView s A τ)

theorem kind_slot_sh {N : ℕ} {C : Type} :
    ∀ (k : Kind), k = .sh → ∀ (v : k.All N C) (j j' : Fin N), k.slot v j = k.slot v j' := by
  rintro _ rfl v j j'
  rfl

/-- In shared rounds all slots have the same shared view. -/
theorem shView_slot {N : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s), RoundSplits.AllKind .sh A → ∀ (τ : BTr N s A) (j j' : Fin N),
      shView s A (τ.slot j) = shView s A (τ.slot j')
  | [], _, _, _, _, _ => rfl
  | r :: s, (a, A), h, (m, v, τ), j, j' => by
    show ((a.split (a.join m.1 (m.2 j))).1, a.kind.slot v j, shView s A (τ.slot j)) =
      ((a.split (a.join m.1 (m.2 j'))).1, a.kind.slot v j', shView s A (τ.slot j'))
    rw [shView_slot s A h.2 τ j j', kind_slot_sh a.kind h.1 v j j']
    simp [RAnn.join]

/-! ## One key -/

section One
variable {Y : Type} {E : ExtSpec} {A₁ AJ κ κ₁ : Type} (N : ℕ) (K₁ : Reduction (Y × E.Str) A₁)
  (KJ : Reduction A₁ AJ) (An₁ : RoundSplits K₁.shape) (AnJ : RoundSplits KJ.shape)

/-- **`OneKey` from two local laws.** -/
theorem oneKey_of_laws (shJ : RoundSplits.AllKind .sh AnJ) (key : AJ → κ) (key₁ : A₁ → κ₁)
    (f₁ : E.Str → κ₁) (fJ : κ₁ → ShV KJ.shape AnJ → κ)
    (law₁ : ∀ a τ b, K₁.out a τ = some b → key₁ b = f₁ a.2)
    (lawJ : ∀ b τ c, KJ.out b τ = some c → key c = fJ (key₁ b) (shView KJ.shape AnJ τ)) :
    OneKey N K₁ KJ An₁ AnJ key := by
  intro a₀ hS τ₁ τJ j j' c c' hc hc'
  obtain ⟨b, hb, hbc⟩ := Option.bind_eq_some_iff.1 hc
  obtain ⟨b', hb', hbc'⟩ := Option.bind_eq_some_iff.1 hc'
  obtain ⟨a, ha, hab⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨a', ha', hab'⟩ := Option.bind_eq_some_iff.1 hb'
  rw [lawJ b _ c hbc, lawJ b' _ c' hbc', law₁ a _ b hab, law₁ a' _ b' hab', hS j j' a a' ha ha',
    shView_slot KJ.shape AnJ shJ τJ j j']

end One

/-! ## The finer count -/

section Frame
variable {Y W₀ : Type} {E : ExtSpec} {A₁ AJ A₂ W₁ WJ W₂ κ κ' κ₁ Wκ Wκ' : Type}
  (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y) (K₁ : Reduction (Y × E.Str) A₁)
  (KJ : Reduction A₁ AJ) (K' : Reduction κ κ') (key : AJ → κ) (glue : AJ → κ' → A₂)
  (K₃ : Reduction A₂ Unit) (An₁ : RoundSplits K₁.shape) (AnJ : RoundSplits KJ.shape) (An₃ : RoundSplits K₃.shape)
  (lo₁ : AllKind .lo K₁.shape An₁) (shJ : AllKind .sh KJ.shape AnJ)
  (lo₃ : AllKind .lo K₃.shape An₃) {on₀ : Y × E.Str → Prop} {on₁ : A₁ → Prop} {onJ : AJ → Prop}
  {on' : κ → Prop} {on₂ : A₂ → Prop} {R₀ : Y × E.Str → W₀ → Prop} {R₁ : A₁ → W₁ → Prop}
  {RJ : AJ → WJ → Prop} {Rκ : κ → Wκ → Prop} {Rκ' : κ' → Wκ' → Prop} {R₂ : A₂ → W₂ → Prop}
  {e₁ : Y × E.Str → Tr K₁.shape → W₁ → W₀} {eJ : A₁ → Tr KJ.shape → WJ → W₁}
  (e' : κ → Tr K'.shape → Wκ' → Wκ) (p : W₂ → Wκ') (mk : AJ → W₂ → Wκ → WJ)
  {e₃ : A₂ → Tr K₃.shape → Unit → W₂} {ε₁ : Err K₁.shape} {εJ : Err KJ.shape}
  {ε₂ : Err K'.shape} {ε₃ : Err K₃.shape} (d₀ : W₀) (d₁ : W₁) (dJ : WJ)

include lo₁ shJ lo₃ in
/-- **Three chains in a row, the finer count, where the tail acts on the shared part alone**, at
late = none. For the tail one ordinary clause is asked: `Know` of K' on keys. -/
theorem sndBKT_of_frame (know₁ : K₁.Know on₀ R₀ R₁ e₁ ε₁) (knowJ : KJ.Know on₁ R₁ RJ eJ εJ)
    (know' : K'.Know on' Rκ Rκ' e' ε₂) (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (handsJ : ∀ a τ b, on₁ a → KJ.out a τ = some b → onJ b)
    (handsκ : ∀ a, onJ a → on' (key a))
    (hands₂ : ∀ a τ b, onJ a → (onKey K' key glue).out a τ = some b → on₂ b)
    (split : ∀ a τ k' w, K'.out (key a) τ = some k' → R₂ (glue a k') w → Rκ' k' (p w))
    (join : ∀ a τ k' w wk, onJ a → K'.out (key a) τ = some k' → R₂ (glue a k') w →
      Rκ (key a) wk → RJ a (mk a w wk))
    (key₁ : A₁ → κ₁) (f₁ : E.Str → κ₁) (fJ : κ₁ → ShV KJ.shape AnJ → κ)
    (law₁ : ∀ a τ b, K₁.out a τ = some b → key₁ b = f₁ a.2)
    (lawJ : ∀ b τ c, KJ.out b τ = some c → key c = fJ (key₁ b) (shView KJ.shape AnJ τ))
    (hs : Q.loc.shape = (K₁.seq (KJ.seq ((onKey K' key glue).seq K₃))).shape)
    (ha : HEq Q.ann
      (RoundSplits.app An₁ (RoundSplits.app AnJ (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) K'.shape) An₃))))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (KJ.seq ((onKey K' key glue).seq K₃))).out (early x, y)
        (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early none (fun x y w => on₀ (early x, y) → R₀ (early x, y) w)
      (fun x y τ => Reduction.extSeq K₁ (KJ.seq ((onKey K' key glue).seq K₃)) e₁
        (Reduction.extSeq KJ ((onKey K' key glue).seq K₃) eJ
          (Reduction.extSeq (onKey K' key glue) K₃ (extKey K' key e' p mk) e₃ dJ) d₁) d₀
        (early x, y) (cast (congrArg Tr hs) τ) ())
      (cast (congrArg Err hs.symm)
        (Err.app ε₁ (Err.app (Err.times N εJ) (Err.app ε₂ ε₃)))) :=
  sndBKT_of_four Q N early K₁ KJ (onKey K' key glue) K₃ An₁ AnJ An₃ lo₁ shJ lo₃ d₀ d₁ dJ know₁
    knowJ key (lostKey K' e' Rκ Rκ') (lost_onKey know' handsκ) (back_onKey split join) know₃
    hands₁ handsJ hands₂ (oneKey_of_laws N K₁ KJ An₁ AnJ shJ key key₁ f₁ fJ law₁ lawJ) hs ha hacc

include lo₁ shJ lo₃ in
/-- **The same with a part of the instance fixed in round n of the first chain.** -/
theorem sndBKT_of_frame_late (n : ℕ) (idem : ∀ x, early (early x) = early x)
    (inFirst : n ≤ K₁.shape.length) (h0 : 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (know₁ : KnowLate K₁ on₀ R₀ R₁ e₁ ε₁ early n) (knowJ : KJ.Know on₁ R₁ RJ eJ εJ)
    (know' : K'.Know on' Rκ Rκ' e' ε₂) (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (handsJ : ∀ a τ b, on₁ a → KJ.out a τ = some b → onJ b)
    (handsκ : ∀ a, onJ a → on' (key a))
    (hands₂ : ∀ a τ b, onJ a → (onKey K' key glue).out a τ = some b → on₂ b)
    (split : ∀ a τ k' w, K'.out (key a) τ = some k' → R₂ (glue a k') w → Rκ' k' (p w))
    (join : ∀ a τ k' w wk, onJ a → K'.out (key a) τ = some k' → R₂ (glue a k') w →
      Rκ (key a) wk → RJ a (mk a w wk))
    (key₁ : A₁ → κ₁) (f₁ : E.Str → κ₁) (fJ : κ₁ → ShV KJ.shape AnJ → κ)
    (law₁ : ∀ a τ b, K₁.out a τ = some b → key₁ b = f₁ a.2)
    (lawJ : ∀ b τ c, KJ.out b τ = some c → key c = fJ (key₁ b) (shView KJ.shape AnJ τ))
    (hs : Q.loc.shape = (K₁.seq (KJ.seq ((onKey K' key glue).seq K₃))).shape)
    (ha : HEq Q.ann
      (RoundSplits.app An₁ (RoundSplits.app AnJ (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) K'.shape) An₃))))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (KJ.seq ((onKey K' key glue).seq K₃))).out (x, y)
        (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early (some n) (fun x y w => on₀ (x, y) → R₀ (x, y) w)
      (fun x y τ => Reduction.extSeq K₁ (KJ.seq ((onKey K' key glue).seq K₃)) e₁
        (Reduction.extSeq KJ ((onKey K' key glue).seq K₃) eJ
          (Reduction.extSeq (onKey K' key glue) K₃ (extKey K' key e' p mk) e₃ dJ) d₁) d₀
        (x, y) (cast (congrArg Tr hs) τ) ())
      (cast (congrArg Err hs.symm)
        (Err.app ε₁ (Err.app (Err.times N εJ) (Err.app ε₂ ε₃)))) :=
  sndBKT_of_four_late Q N early K₁ KJ (onKey K' key glue) K₃ An₁ AnJ An₃ lo₁ shJ lo₃ d₀ d₁ dJ n
    idem inFirst h0 know₁ knowJ key (lostKey K' e' Rκ Rκ') (lost_onKey know' handsκ)
    (back_onKey split join) know₃ hands₁ handsJ hands₂
    (oneKey_of_laws N K₁ KJ An₁ AnJ shJ key key₁ f₁ fJ law₁ lawJ) hs ha hacc

end Frame

end CompileK.Joined
