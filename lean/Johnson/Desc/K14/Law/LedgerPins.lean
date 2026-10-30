-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerPins.lean: THE PINS OF o_u AND o_omega AT THE LEDGER OF A PROOF FILE's
SHARED CHAIN, AT THE TABLE's FILES' OWN FILLING (meaningSigS: a pin is pinJT: the committed word
decodes, with the sample that the record holds, to the witness's typed message;
Johnson/Desc/Sound/BordersSharedFill.lean, MeaningSig.lean): they pay three premises of "LIN zeta"'s
clause (Johnson/Desc/K14/Law/LedgerZeta.lean): hdet, hback, hid.

  rgOf mem rd w   THE WORDS THAT THE ROWS READ OF A WITNESS, by the plan's numbers of the messages
                  in the chain's own statement: at the number o the member mem o's TYPED message
                  (msgsOf), read by a letter rd; 0 where the plan names no member. It shows nothing
                  of the witness but typed messages: so what a pin fixes fixes the words.
  agreeOn_of_pinJT   two witnesses pinned at one seat, at one record and strings, have the same
                  words at the number of the member that sits there: by pinAt_one.
  pins7_det       **hdet**, where the promise gives that the numbers noted for o_u and o_omega are
                  the plan's.
  pins7_back      **hback**, where the two records hold the same samples and the two messages' trees
                  were sent in front of the block (SentBefore): by pin_rides
                  (Johnson/Desc/Sound/LedgerRides.lean).
  lays7, ext7_id  **hid**: at the table's files' extractor extS the table lays nothing at block 7.
What is not claimed. PREMISES LEFT: hnum (the filling's shape 7: K14's law's files) · hsm (the
letter smp₂ reads nothing that "LIN zeta" turns: the table's files' filling of smp₂) · SentBefore
at the two messages (four comparisons of numbers each: the plan's and the tiling's). mem and rd
are letters: no member is shown. Nothing on soundness.

-/
import Johnson.Desc.Sound.LedgerRides
import Johnson.Desc.K14.Law.LedgerZeta

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

section
variable (cs : OnBytes.Codes) {A Xi Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {K : Type} [Zero K] (mem : ℕ → Option Mem)
  (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → K)

/-- **The words that the rows read of a witness**, by the plan's numbers. -/
def rgOf (w : Wit Cells Tok MsgT) : Words K := fun o part i =>
  match mem o with
  | some x => rd x (msgsOf cs x.1.l x.1.seat arr w x.2) part i
  | none => 0

/-- Two witnesses pinned at one seat have the same words at the number of the member there. -/
theorem agreeOn_of_pinJT (ms : List Mem) (j t : ℕ) (a : A) (y : Strs)
    (w w' : Wit Cells Tok MsgT) (o : ℕ) (x : Mem) (hm : mem o = some x) (hx : x ∈ ms)
    (hs : SitsAt x j t) (h : pinJT cs G arr smp ms j t a y w)
    (h' : pinJT cs G arr smp ms j t a y w') :
    AgreeOn o (rgOf cs arr mem rd w) (rgOf cs arr mem rd w') := by
  intro i
  unfold rgOf
  simp only [hm]
  rw [pinAt_one cs G arr smp x a y w w' (h.2 x hx hs) (h'.2 x hx hs)]

end

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
  (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- **hdet of "LIN zeta"'s clause, at the table's files' pins.** nU, nO: the plan's numbers of o_u
and o_omega in the chain's own statement; xU, xO: the members that the plan names there. -/
theorem pins7_det (mem : ℕ → Option Mem)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE) (nU nO : ℕ) (xU xO : Mem)
    (hU : mem nU = some xU) (hO : mem nO = some xO) (mU : xU ∈ ms) (mO : xO ∈ ms)
    (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
    (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
    (hnum : ∀ x, onQ₂ N Pm Oc split p l 7 x →
      x.1.2.loc.oU.oracle = nU ∧ x.1.2.loc.oOmega = nO) :
    ∀ x w w', onQ₂ N Pm Oc split p l 7 x →
      Pins7 N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l 7 ((actQ N p l 7).2 x) w →
      Pins7 N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l 7 ((actQ N p l 7).2 x) w' →
      AgreeOn x.1.2.loc.oOmega (rgOf cs arr mem rd w) (rgOf cs arr mem rd w') ∧
        AgreeOn x.1.2.loc.oU.oracle (rgOf cs arr mem rd w) (rgOf cs arr mem rd w') := by
  intro x w w' hx h h'
  obtain ⟨eU, eO⟩ := hnum x hx
  rw [eU, eO]
  exact ⟨agreeOn_of_pinJT cs G arr smp₂ mem rd ms _ _ _ _ w w' nO xO hO mO sO h.2 h'.2,
    agreeOn_of_pinJT cs G arr smp₂ mem rd ms _ _ _ _ w w' nU xU hU mU sU h.1 h'.1⟩

/-- **hback of "LIN zeta"'s clause, at the table's files' pins.** -/
theorem pins7_back (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hsm : ∀ a τ b, onQ₂ N Pm Oc split p l 7 a → x.ior.red.out a τ = some b →
      ∀ z ∈ ms, smp₂ a.1.2 z.1 z.2 = smp₂ b.1.2 z.1 z.2)
    (hU : SentBefore N p l 7 x .oU) (hO : SentBefore N p l 7 x .oOmega) :
    ∀ a τ b w, onQ₂ N Pm Oc split p l 7 a → x.ior.red.out a τ = some b →
      Pins7 N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l 8 ((actQ N p l 8).2 b) w →
      Pins7 N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l 7 ((actQ N p l 7).2 a) w :=
  fun a τ b w ha hout h =>
    ⟨pin_rides cs G arr smp₂ ms decT₂ N Mg p l 7 x .oU hU a b τ hout (hsm a τ b ha hout) w h.1,
      pin_rides cs G arr smp₂ ms decT₂ N Mg p l 7 x .oOmega hO a b τ hout (hsm a τ b ha hout) w
        h.2⟩

/-- The table lays nothing at block 7. -/
theorem lays7 : laysAtS split 7 = [] := by cases split <;> rfl

/-- **hid of "LIN zeta"'s clause, at the table's files' extractor.** -/
theorem ext7_id (c₀ : Cells) (s : St) (y : Strs) (w : Wit Cells Tok MsgT) :
    extS cs G arr smp₂ ms decT₂ c₀ N split 7 s y w = w :=
  extS_id cs G arr smp₂ ms decT₂ c₀ N split 7 (lays7 split) s y w

end Desc.K14.Law
