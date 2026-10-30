-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/StrMade.lean: the code switch: THE TYPED OPEN WORD's STRING, MADE OFF
THE ORACLES: so that ShowsCols.lean's StrIs, a premise of the switch's law (TiePaid.lean's
FrontAt.strIs), is a THEOREM at that string.

StrIs asks of a string of the folded complex with kept slots: at EVERY position q at which the front
reads something off the oracles (K2Hears/LongOne.lean's longFront), drawn or not, the string's long
symbol at q has, at the coordinate α, longFront's entry number coord α, read in the field. The
complex's words stand on the group's own positions, the two mask rows' too (OnBytes/Slice/
LinkAt.lean's ldRep: «a word that is no code word may have different symbols at two positions that
are equal modulo C's length»). So ANY family of long symbols is some word's.
  wordOf     the word of the complex that has the given long symbols
  posIn_self a position of the group is its own place in the main code
  T_wordOf   its long symbol at x, at α, is the given one: the complex's transformation has a right
             inverse
  strMade    THE STRING: wordOf of «longFront's entry number coord α at q, read in the field; 0
             where longFront has nothing»: a function of the place's numbers, the record in front,
             its front, the oracles orc and the numbering coord
  strIs_made StrIs at strMade: NO PREMISE
  strOpen    the string off a statement in front (record, oracles): strMade at the front that the
             text makes of the record, at the frame's own numbering coordOf
  strIs_open FrontAt's clause strIs at strOpen, to its letter: its one premise is FrontOn's own
             binder «frontAt p a.1 = some fx»
LIMITS. orc is a letter: a family of words by a tree's key and a position. strMade READS THE RECORD
(its book and number of roots; the front's shapes, target and carried rows' layout), not the oracles
alone: a reading of the oracles alone wants these from the plan. Where longFront has nothing the
string is 0 there: nothing is said of that case. THAT THIS STRING IS THE ONE OF WHICH THE PROMISE IN
FRONT SPEAKS (near a code word; the held slots decode) IS NOT SAID: that is what stands in front of
the switch (CarryOf.lean), and whoever closes the block in front owes it AT THIS STRING. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.ShowsCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

section
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K]

/-- The word of the folded complex with kept slots that has the given long symbols. -/
def wordOf (g : s.Ps → (s.cKept K).Aa → GE) : (s.cKept K).Word := fun p =>
  match p with
  | .inl p => fun x => g p (.inl (x.1, ()))
  | .inr (.inl p) => fun _ => g p (.inr (.inl ()))
  | .inr (.inr p) => fun _ => g p (.inr (.inr ()))

theorem posIn_self (x : s.Ps) : posIn s.C x = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- **The complex's transformation has a right inverse.** -/
theorem T_wordOf (g : s.Ps → (s.cKept K).Aa → GE) (x : s.Ps) (α : (s.cKept K).Aa) :
    (s.cKept K).T (wordOf s K g) x α = g x α := by
  rcases α with ⟨κ, u⟩ | u | u
  · show g (posIn s.C x) (.inl (κ, ())) = g x (.inl (κ, u))
    rw [posIn_self]
  · rfl
  · rfl

end

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

/-- **The typed open word's string, made off the oracles.** -/
noncomputable def strMade (p : K2.P2) (s : VerifiableInference.Desc.First.S)
    (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64) (coord : (LocK).C.Aa → ℕ) :
    (LocK).C.ext.Str :=
  wordOf R.s R.Kp fun q α =>
    readE (((K2.longFront p s fx orc q.val).getD #[]).getD (coord α) OnBytes.zeroE)

/-- **StrIs at the string made.** -/
theorem strIs_made (p : K2.P2) (s : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front)
    (orc : ℕ → ℕ → List UInt64) (coord : (LocK).C.Aa → ℕ) :
    StrIs R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p s fx orc coord
      (strMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p s fx orc coord) := by
  intro q seg h α
  show (R.s.cKept R.Kp).T (wordOf R.s R.Kp _) q α = _
  rw [T_wordOf, h]
  rfl

/-- **The open word's string off a statement in front**: strMade at the front that the text makes of
the record, at the oracles' reading orcs and at the frame's own numbering of the coordinates; the
zero word where the text makes no front. -/
noncomputable def strOpen {Yt : Type} (p : K2.P2) (W₀ : OnBytes.SwitchFrame) (mem row : R.Kp → ℕ)
    (orcs : VerifiableInference.Desc.First.S × Yt → ℕ → ℕ → List UInt64)
    (a : VerifiableInference.Desc.First.S × Yt) : (LocK).C.ext.Str :=
  match K2.frontAt p a.1 with
  | some fx => strMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p a.1 fx (orcs a)
      (coordOf R.s R.Kp W₀ fx.f.rows mem row)
  | none => wordOf R.s R.Kp fun _ _ => 0

/-- **FrontAt's clause strIs at that string**: to the letter of TiePaid.lean's FrontAt.strIs. -/
theorem strIs_open {Yt : Type} (p : K2.P2) (W₀ : OnBytes.SwitchFrame) (mem row : R.Kp → ℕ)
    (orcs : VerifiableInference.Desc.First.S × Yt → ℕ → ℕ → List UInt64)
    (a : VerifiableInference.Desc.First.S × Yt) {fx : _root_.Tw.K2.Front}
    (hx : K2.frontAt p a.1 = some fx) :
    StrIs R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p a.1 fx (orcs a)
      (coordOf R.s R.Kp W₀ fx.f.rows mem row)
      (strOpen R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p W₀ mem row orcs a) := by
  unfold strOpen
  rw [hx]
  exact strIs_made R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p a.1 fx (orcs a) _

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.strIs_open
#print axioms VerifiableInference.Desc.First.K2Hands.T_wordOf
#print axioms VerifiableInference.Desc.First.K2Hands.strIs_made
