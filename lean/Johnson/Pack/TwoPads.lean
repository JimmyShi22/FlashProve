-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/TwoPads.lean: an honest word of a shape of the programs decodes to its message; and one
message can be sent twice with two pads, so that both words decode, each to its own table.

The programs send a message that is kept across a code switch once more, with a fresh pad: the two
copies are equal off the pad's places (`padP`, Johnson/Pack/PortZ.lean) and differ there. A
statement that pins each copy by the library's decoder with a sample (`OMsg.dec`, Cb/Ld/LdSig.lean)
must be met by such a pair. Here the decodings are shown, at the oracle message of every shape
(`portOmZ`), at every radius and at all seeds, for every message that can be sent. The decoder is
not evaluated: the library's `sig_dec_enc` (Cb/Ld/LdSig.lean; proved in Cb/Ld/LdSigProofs.lean) says
that decoding undoes encoding under the code's laws and distance 1; `port_laws` and `port_dist`
(Johnson/Pack/Port.lean) give these from comparisons of numbers; `ldOf_enc_mem`
(Johnson/Pack/PortF.lean) says that an encoding of data over the base field is over the base
field. Definitions, statements and proofs.
Main names:
  `Sendable cs s e w`: where the main rows are sent over the base field, the entries of their
    messages and tails lie in it.
  `sent_of`: the encoding of such a w is the reading of a word as sent.
  `dec_sent`: that word decodes, at every seed, with the message's answers there, to the message.
  `pbase_one`: what laws and distance 1 ask follows from `CodeOK` alone.
  `msgOfTab cs s t`, `dec_tab`, `sig_dec_tab`: the message of a shape out of a plain table (mask row
    or main row, row, place); `dec_sent` at it, with the tail 0; the same at a member of a
    sending's signature (`sigOf`, Johnson/Pack/PortF.lean). For a message that is sent in two
    sendings this is called once for each, at two tables that are equal off the pads.
  `two_pads`: at one shape: any message that can be sent, and the same with 1 added at a place of
    the pad: both are sent, both decode, they are equal off the pad and differ at that place.
  `pad_exists`: a shape without a mask row has a place of the pad.
Near kin: Johnson/Top/Fam/BattShortInhabited.lean has, for any oracle message whose format reaches
every word, that an encoding is near itself and has no collision below the distance.
Limits: nothing on collisions: beyond unique decoding a word's list may hold more than one message,
and that no two of them have one answer at a seed is not said. Nothing on strings of a file, on
trees, on seats or on a run of the programs. Nothing on soundness or on hiding.

-/
import Johnson.Pack.Check
import Cb.Ld.LdSigProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open OnBytes.Slice Cb

variable (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e : ℕ)

/-- A symbol that may be sent: over the base field where the row is. -/
theorem upRow_onto (b : Bool) (y : GE) (h : b = true → y ∈ (algebraMap GF GE).range) :
    ∃ z : RowTy b, upRow b z = y := by
  cases b with
  | true => obtain ⟨z, hz⟩ := h rfl; exact ⟨z, hz⟩
  | false => exact ⟨y, rfl⟩

/-- A message with its tail that can be sent: where the main rows are over the base field, their
entries are. -/
def Sendable (w : (portOmZ cs s e).Wit) : Prop :=
  s.mainDeg = 1 → (∀ x, w.1 (.inl x) ∈ (algebraMap GF GE).range) ∧
    ∀ x, w.2 (.inl x) ∈ (algebraMap GF GE).range

/-- Its encoding is the reading of a word as sent. -/
theorem sent_of (w : (portOmZ cs s e).Wit) (h : Sendable cs s e w) :
    ∃ f : (portOmZ cs s e).Str, (portOmZ cs s e).upW f = (portCode cs s).enc w.1 w.2 := by
  have key : ∀ (p : (portCode cs s).NP) (x : (portCode cs s).NS p),
      ∃ z : RowTy (tabF cs s p), upRow (tabF cs s p) z = (portCode cs s).enc w.1 w.2 p x := by
    intro p x
    refine upRow_onto _ _ fun hb => ?_
    rcases p with p | p
    · have h1 : s.mainDeg = 1 := by
        have hb' : (s.mainDeg == 1) = true := hb
        exact beq_iff_eq.1 hb'
      exact ldOf_enc_mem (cMain cs s) (aOf cs s) _ _ (fun j => (h h1).1 (x.1, j))
        (fun q => (h h1).2 (x.1, q)) p
    · cases hb
  choose f hf using key
  exact ⟨f, funext fun p => funext fun x => hf p x⟩

/-- **An honest word decodes to its message**, at every seed and every radius. -/
theorem dec_sent (g : PBase cs s 1) (w : (portOmZ cs s e).Wit) (h : Sendable cs s e w) :
    ∃ f : (portOmZ cs s e).Str, (portOmZ cs s e).upW f = (portCode cs s).enc w.1 w.2 ∧
      ∀ ρ : (portOmZ cs s e).Z.D,
        (portOmZ cs s e).dec f (ρ, (portOmZ cs s e).Z.val ρ w.1) = some w.1 := by
  obtain ⟨f, hf⟩ := sent_of cs s e w h
  exact ⟨f, hf, fun ρ => sig_dec_enc GE (portOmZ cs s e) (port_laws cs s g.ok)
    (port_dist cs s g.ok 1 g.d1 g.d2) f w ρ hf⟩

theorem distAt_pos (C : Fmt.M1.Code) (a : ℕ) : 1 ≤ distAt C a :=
  Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.succ_pos _)

/-- What laws and distance 1 ask, from the conditions on the two codes' numbers. -/
theorem pbase_one (h : CodeOK cs s) : PBase cs s 1 :=
  ⟨h, Or.inr (distAt_pos _ _), Or.inr (distAt_pos _ _)⟩

/-- The message of a shape out of a plain table: mask row (true) or main row, row, place. -/
def msgOfTab (t : Bool → ℕ → ℕ → GE) : (portCode cs s).J → GE
  | .inl q => t false q.1.val q.2.val
  | .inr q => t true q.1.val q.2.val

/-- **A plain table, sent with the tail 0, decodes to itself.** -/
theorem dec_tab (h : CodeOK cs s) (t : Bool → ℕ → ℕ → GE)
    (ht : s.mainDeg = 1 → ∀ r p, t false r p ∈ (algebraMap GF GE).range) :
    ∃ f : (portOmZ cs s e).Str,
      (portOmZ cs s e).upW f = (portCode cs s).enc (msgOfTab cs s t) (fun _ => 0) ∧
      ∀ ρ : (portOmZ cs s e).Z.D,
        (portOmZ cs s e).dec f (ρ, (portOmZ cs s e).Z.val ρ (msgOfTab cs s t)) =
          some (msgOfTab cs s t) :=
  dec_sent cs s e (pbase_one cs s h) (msgOfTab cs s t, fun _ => 0)
    fun h1 => ⟨fun x => ht h1 x.1.val x.2.val, fun _ => Subring.zero_mem _⟩

/-- The same at a member of a sending's signature. -/
theorem sig_dec_tab (l : List (OnBytes.OracleShape × ℕ)) (i : Fin l.length)
    (h : CodeOK cs (l.get i).1) (t : Bool → ℕ → ℕ → GE)
    (ht : (l.get i).1.mainDeg = 1 → ∀ r p, t false r p ∈ (algebraMap GF GE).range) :
    ∃ f : ((sigOf cs l).om i).Str,
      ((sigOf cs l).om i).upW f =
        ((sigOf cs l).om i).C.enc (msgOfTab cs (l.get i).1 t) (fun _ => 0) ∧
      ∀ ρ : ((sigOf cs l).om i).Z.D,
        ((sigOf cs l).om i).dec f (ρ, ((sigOf cs l).om i).Z.val ρ (msgOfTab cs (l.get i).1 t)) =
          some (msgOfTab cs (l.get i).1 t) :=
  dec_tab cs (l.get i).1 (l.get i).2 h t ht

/-- **One message, sent twice with two pads**: any message that can be sent, and the same with 1
added at a place of the pad. -/
theorem two_pads (h : CodeOK cs s) (w : (portOmZ cs s e).Wit) (hw : Sendable cs s e w)
    (j₀ : (portCode cs s).J) (h₀ : padP cs s j₀) :
    ∃ (m' : (portOmZ cs s e).Msg) (f f' : (portOmZ cs s e).Str),
      (∀ j, ¬ padP cs s j → w.1 j = m' j) ∧ w.1 j₀ ≠ m' j₀ ∧
      (portOmZ cs s e).upW f = (portCode cs s).enc w.1 w.2 ∧
      (portOmZ cs s e).upW f' = (portCode cs s).enc m' w.2 ∧
      (∀ ρ, (portOmZ cs s e).dec f (ρ, (portOmZ cs s e).Z.val ρ w.1) = some w.1) ∧
      ∀ ρ, (portOmZ cs s e).dec f' (ρ, (portOmZ cs s e).Z.val ρ m') = some m' := by
  have s1 : Sendable cs s e (fun j => if j = j₀ then w.1 j + 1 else w.1 j, w.2) :=
    fun h1 => ⟨fun x => by
      show (if Sum.inl x = j₀ then w.1 (.inl x) + 1 else w.1 (.inl x)) ∈ _
      split_ifs
      · exact Subring.add_mem _ ((hw h1).1 x) (Subring.one_mem _)
      · exact (hw h1).1 x, (hw h1).2⟩
  obtain ⟨f, e1, hf⟩ := dec_sent cs s e (pbase_one cs s h) w hw
  obtain ⟨f', e2, hf'⟩ := dec_sent cs s e (pbase_one cs s h) _ s1
  refine ⟨_, f, f', fun j hj => ?_, ?_, e1, e2, hf, hf'⟩
  · have hne : j ≠ j₀ := fun k => hj (k ▸ h₀)
    exact (if_neg hne).symm
  · show w.1 j₀ ≠ if j₀ = j₀ then w.1 j₀ + 1 else w.1 j₀
    rw [if_pos rfl]
    intro k
    exact one_ne_zero (add_left_cancel (k.symm.trans (add_zero _).symm))

/-- A shape without a mask row has a place of the pad: the last place of its last main row. -/
theorem pad_exists (h0 : s.maskRows = 0) (h1 : 0 < s.mainRows) (h2 : 0 < (pMain cs s).ell) :
    ∃ j₀, padP cs s j₀ := by
  have hl : (cMain cs s).l = (pMain cs s).ell := rfl
  refine ⟨.inl (⟨s.mainRows - 1, by omega⟩, ⟨(pMain cs s).ell - 1, by omega⟩), h0, ?_, ?_⟩
  · show s.mainRows - 1 + 1 = s.mainRows
    omega
  · show (pMain cs s).ell ≤ (pMain cs s).ell - 1 + eachZ s
    unfold eachZ
    split <;> omega

end Johnson.Pack

#print axioms Johnson.Pack.sent_of
#print axioms Johnson.Pack.dec_sent
#print axioms Johnson.Pack.pbase_one
#print axioms Johnson.Pack.dec_tab
#print axioms Johnson.Pack.sig_dec_tab
#print axioms Johnson.Pack.two_pads
#print axioms Johnson.Pack.pad_exists
