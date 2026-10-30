-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyExact.lean: theorems about the toy example of
Honest/Law/ToyRow.lean and about two sides of Honest/FrameToy.lean: the fields `fits` and `exact` of
`Good` (Honest/Side.lean) at these sides, at the parameters that Honest/Law/ToyRow.lean supplies;
and, list by list, what coins the book gives, what is played, what is read and what is decided. They
speak of these files' own made-up objects alone. None is one of the library's goals.

  1  `members_…`, `onePos_elim`   each side's `Member`s, written out
  2  `colAt`, `ansAt`, `eAt`, `tellAt`, `play_…`, `shows_…`, `tells_…`   what a part shows, and what
     its simulator outputs, as an equation in the coins: whatever the state of the run, at every
     challenge and position; by `play_one` and `play_two` (Honest/Law/ToyPlay.lean)
  3  `exact_…`   part by part
  4  `By_spent`, `Bz_spent`, `cut_u`, `fresh_own`   the one pair of owner and spender
  5  `look_…`, `send_…`, `tell_…`, `carry_…`   fields, side by side, as `Good` has them
  6  `roundsFit_cons`, `lend_…`, `play_…`, `reads_tell`, `tell_decide`   the lists of parts

Limits.
  * A toy example.
  * The conditions of `Good` on the run of a whole list of parts are not in this file.
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `look_exact`, `send_exact`, `tell_exact`, `carry_exact`,
    `zSide₂_exact`, `look_fresh`, `fresh_unspent`. The statements of item 5 have every hypothesis of
    the field of `Good` that they prove.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyRow
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw
import Johnson.Desc.ProofFile.Honest.Law.ToyPlay
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription OpenedColumn itemOf roundsFit drawsMarkedNonzeroHaveNonzeroWords need)
open VerifiableInference.Desc.BlockToy (St look send₃ ask tree tree₃ drawT sendS openA sendR orc)
open OnBytes.Slice (toF toE ofF ofE)
open Prob

/-! ## 1 The `Member`s -/

theorem members_look : zSide.members = [zU₀, zU₁] := rfl
theorem members_send : ySide₂.members = [yU₂] := rfl
theorem members_tell : ySide₃.members = [yU₃] := rfl
theorem members_carry : ySide₄.members = [yU₄] := rfl
theorem members_zSide₂ : zSide₂.members = [zU₂] := rfl

theorem onePos_elim {asks : List (List (List Nat))} (h : onePos asks = true) :
    ∃ p, asks = [[[p]]] := by
  unfold onePos at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-! ## 2 What a part shows, as an equation in the coins -/

/-- One round that shows one column of one word. -/
def colAt (p : Nat) (y : Cb.Gl.F) : Option (List Shown) := some [⟨[], [[(p, [ofF y])]]⟩]
/-- One round that shows one answer. -/
def ansAt (y : Cb.Gl.F) : Option (List Shown) := some [⟨[.answer (ofF y, 0, 0)], []⟩]
/-- One round that shows one element. -/
def eAt (y : Cb.Gl.F) : Option (List Shown) := some [⟨[.e (ofF y, 0, 0)], []⟩]
/-- A round that shows nothing, and one that shows one element. -/
def tellAt (y : Cb.Gl.F) : Option (List Shown) := some [⟨[], []⟩, ⟨[.e (ofF y, 0, 0)], []⟩]

/-- The owner's round, played. -/
theorem play_own (c : Cs ⟨2, 0⟩) (sp ca : Unit) (m : Mid L₀ Nat) (R : Fmt.Drawn) : ∃ m',
    play (zU₀.part.steps zSide.block.name ⟨zSide.block.place, zU₀.number⟩ zU₀.rounds
        (Face.shared.sees m.st.input) (c, sp, ca)) [R] [] m =
      .ok ([⟨"look", pLook, 0, true, [], [some ⟨3, 1, fun p _ => toF (m.st.input.w₀.a p) +
        c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩ + c.f ⟨1, by decide⟩⟩], R⟩], m') :=
  ⟨_, play_one (z := ⟨[], [⟨3, 1, fun p _ => toF (m.st.input.w₀.a p) + c.f ⟨0, by decide⟩ +
    c.f ⟨1, by decide⟩ + c.f ⟨1, by decide⟩⟩]⟩) (fun _ _ => rfl) (fun _ _ => rfl) rfl
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)⟩

theorem shows_own (c : Cs ⟨2, 0⟩) (sp ca : Unit) (m : Mid L₀ Nat) (R : Fmt.Drawn) (p : Nat) :
    zSide.shows .shared zU₀ (c, sp, ca) m [R] [[[p]]] =
      colAt p (toF (m.st.input.w₀.a p) + c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩ +
        c.f ⟨1, by decide⟩) := by
  obtain ⟨m', h⟩ := play_own c sp ca m R
  unfold Side.shows
  rw [h]
  rfl

theorem tells_own (c : Cs ⟨1, 0⟩) (w : L₀) (front : Before) (ds : List Fmt.Drawn) (p : Nat) :
    zU₀.tells .shared c w front ds [[[p]]] = colAt p (c.f ⟨0, by decide⟩) := rfl

/-- The spender's round, played. -/
theorem play_spend (c : Cs ⟨0, 0⟩) (sp : Cs ⟨1, 0⟩ × Unit) (ca : Unit) (m : Mid L₀ Nat)
    (R : Fmt.Drawn) : ∃ m',
    play (zU₁.part.steps zSide.block.name ⟨zSide.block.place, zU₁.number⟩ zU₁.rounds
        (Face.shared.sees m.st.input) (c, sp, ca)) [R] [] m =
      .ok ([⟨"look", pLook, 1, true, [.answer (ofF (toF m.st.input.w₀.ans + sp.1.f ⟨0, by decide⟩),
        ofF (toF 0), ofF (toF 0))], [], R⟩], m') :=
  ⟨_, play_one (z := ⟨[.answer ⟨toF m.st.input.w₀.ans + sp.1.f ⟨0, by decide⟩, toF 0, toF 0⟩], []⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)⟩

theorem shows_spend (c : Cs ⟨0, 0⟩) (sp : Cs ⟨1, 0⟩ × Unit) (ca : Unit) (m : Mid L₀ Nat)
    (R : Fmt.Drawn) (asks : List (List (List Nat))) :
    zSide.shows .shared zU₁ (c, sp, ca) m [R] asks =
      ansAt (toF m.st.input.w₀.ans + sp.1.f ⟨0, by decide⟩) := by
  obtain ⟨m', h⟩ := play_spend c sp ca m R
  unfold Side.shows
  rw [h, ofF_toF_zero]
  rfl

theorem tells_spend (c : Cs ⟨1, 0⟩) (w : L₀) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    zU₁.tells .shared c w front ds asks = ansAt (c.f ⟨0, by decide⟩) := rfl

/-- The second owner's round, played. -/
theorem play_send (c : Cs ⟨1, 0⟩) (sp ca : Unit) (m : Mid L Nat) (R : Fmt.Drawn) : ∃ m',
    play (yU₂.part.steps ySide₂.block.name ⟨ySide₂.block.place, yU₂.number⟩ yU₂.rounds
        (Face.own.sees m.st.input) (c, sp, ca)) [R] [] m =
      .ok ([⟨"send", pSend, 0, true, [], [some ⟨2, 1, fun p _ => toF (m.st.input.trace.b p) +
        c.f ⟨0, by decide⟩⟩], R⟩], m') :=
  ⟨_, play_one (z := ⟨[], [⟨2, 1, fun p _ => toF (m.st.input.trace.b p) + c.f ⟨0, by decide⟩⟩]⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)⟩

theorem shows_send (c : Cs ⟨1, 0⟩) (sp ca : Unit) (m : Mid L Nat) (R : Fmt.Drawn) (p : Nat) :
    ySide₂.shows .own yU₂ (c, sp, ca) m [R] [[[p]]] =
      colAt p (toF (m.st.input.trace.b p) + c.f ⟨0, by decide⟩) := by
  obtain ⟨m', h⟩ := play_send c sp ca m R
  unfold Side.shows
  rw [h]
  rfl

theorem tells_send (c : Cs ⟨1, 0⟩) (w : L) (front : Before) (ds : List Fmt.Drawn) (p : Nat) :
    yU₂.tells .own c w front ds [[[p]]] = colAt p (c.f ⟨0, by decide⟩) := rfl

/-- What the carrier says: the trace's last word, its own coin r, three times u and four times t. -/
def carryVal (m : Mid L Nat) (c : Cs ⟨1, 0⟩) (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) : Cb.Gl.F :=
  toF m.st.input.trace.last + c.f ⟨0, by decide⟩ +
    (ca.1.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩) +
    (ca.2.1.f ⟨0, by decide⟩ + ca.2.1.f ⟨0, by decide⟩ + ca.2.1.f ⟨0, by decide⟩ +
      ca.2.1.f ⟨0, by decide⟩)

/-- The carrier's round, played. -/
theorem play_carry (c : Cs ⟨1, 0⟩) (sp : Unit) (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) (m : Mid L Nat)
    (R : Fmt.Drawn) : ∃ m',
    play (yU₄.part.steps ySide₄.block.name ⟨ySide₄.block.place, yU₄.number⟩ yU₄.rounds
        (Face.own.sees m.st.input) (c, sp, ca)) [R] [] m =
      .ok ([⟨"ask", pAsk, 0, true, [.e (ofF (carryVal m c ca), ofF (toF 0), ofF (toF 0))], [], R⟩],
        m') :=
  ⟨_, play_one (z := ⟨[.e ⟨carryVal m c ca, toF 0, toF 0⟩], []⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)⟩

theorem shows_carry (c : Cs ⟨1, 0⟩) (sp : Unit) (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) (m : Mid L Nat)
    (R : Fmt.Drawn) (asks : List (List (List Nat))) :
    ySide₄.shows .own yU₄ (c, sp, ca) m [R] asks = eAt (carryVal m c ca) := by
  obtain ⟨m', h⟩ := play_carry c sp ca m R
  unfold Side.shows
  rw [h, ofF_toF_zero]
  rfl

/-- The same at the side of Honest/FrameToy.lean, whose sub-protocol is `BlockToy.ask`. -/
theorem shows_zCarry (c : Cs ⟨1, 0⟩) (sp : Unit) (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit)
    (m : Mid L Nat) (R : Fmt.Drawn) (asks : List (List (List Nat))) :
    zSide₂.shows .own zU₂ (c, sp, ca) m [R] asks = ySide₄.shows .own yU₄ (c, sp, ca) m [R] asks :=
  rfl

theorem tells_carry (c : Cs ⟨1, 0⟩) (w : L) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    yU₄.tells .own c w front ds asks = eAt (c.f ⟨0, by decide⟩) := rfl

/-- The two rounds of `yTell` as played, where the word w is said. -/
def tellPlayed (w : UInt64) (R₀ R₁ : Fmt.Drawn) : List Played :=
  [⟨"tell", pTell, 0, true, [], [], R₀⟩, ⟨"tell", pTell, 0, true, [.e (w, 0, 0)], [], R₁⟩]

/-- The first round of `yTell`, as the `Step` that `play` is given. -/
def tS₀ (m : Mid L Nat) : Step L Nat :=
  ⟨"tell", sTell, { entry := drawT, opens := [(tree₃, .own 0)] }, [], yTell.bad,
    fun f o => (Face.own.sees m.st.input).bind fun w => yTell.hid w f o, 0, false,
    some ⟨fun _ _ _ => .ok ⟨[], []⟩, fun s => s.own⟩⟩

/-- Its second round, with the carried coin v put in. -/
def tS₁ (m : Mid L Nat) (v : Cb.Gl.F) : Step L Nat :=
  ⟨"tell", sTell, { entry := { name := "CS", msg := 24 } }, [], yTell.bad,
    fun f o => (Face.own.sees m.st.input).bind fun w => yTell.hid w f o, 1, true,
    some ⟨fun _ _ s => .ok ⟨[.e ⟨toF (s.input.trace.b (posOf (s.heard.getLast?.getD d0))) + v,
      toF 0, toF 0⟩], []⟩, fun s => s.own⟩⟩

/-- The two rounds, played. -/
theorem play_tS (m : Mid L Nat) (v : Cb.Gl.F) (R₀ R₁ : Fmt.Drawn) : ∃ m' : Mid L Nat,
    play [tS₀ m, tS₁ m v] [R₀, R₁] [] m =
      .ok (tellPlayed (ofF (toF (m.st.input.trace.b (posOf R₀)) + v)) R₀ R₁, m') ∧
    m'.st.input = m.st.input := by
  have hl : (m.st.heard ++ [R₀]).getLast? = some R₀ := by simp
  have h := play_two (s₀ := tS₀ m) (s₁ := tS₁ m v) (m := m) (d₀ := R₀) (d₁ := R₁)
    (z₀ := ⟨[], []⟩) (z₁ := ⟨[.e ⟨toF (m.st.input.trace.b (posOf R₀)) + v, toF 0, toF 0⟩], []⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
    (by
      show Except.ok (⟨[.e ⟨toF (m.st.input.trace.b
        (posOf ((m.st.heard ++ [R₀]).getLast?.getD d0))) + v, toF 0, toF 0⟩], []⟩ : Sending) = _
      simp only [hl, Option.getD_some]) (by with_unfolding_all rfl)
  have he : [playedOf (tS₀ m) ⟨[], []⟩ R₀, playedOf (tS₁ m v)
        ⟨[.e ⟨toF (m.st.input.trace.b (posOf R₀)) + v, toF 0, toF 0⟩], []⟩ R₁] =
      tellPlayed (ofF (toF (m.st.input.trace.b (posOf R₀)) + v)) R₀ R₁ := by
    show [(⟨"tell", pTell, 0, true, [], [], R₀⟩ : Played), ⟨"tell", pTell, 0, true,
      [.e (ofF (toF (m.st.input.trace.b (posOf R₀)) + v), ofF (toF 0), ofF (toF 0))], [], R₁⟩] = _
    rw [ofF_toF_zero]
    rfl
  rw [he] at h
  exact ⟨_, h, rfl⟩

/-- The two rounds of `yTell`, played: as a part by itself. -/
theorem play_tellPart (c : Cs ⟨0, 0⟩) (sp : Unit) (ca : Cs ⟨1, 0⟩ × Unit) (m : Mid L Nat)
    (R₀ R₁ : Fmt.Drawn) : ∃ m' : Mid L Nat,
    play (yU₃.part.steps ySide₃.block.name ⟨ySide₃.block.place, yU₃.number⟩ yU₃.rounds
        (Face.own.sees m.st.input) (c, sp, ca)) [R₀, R₁] [] m =
      .ok (tellPlayed (ofF (toF (m.st.input.trace.b (posOf R₀)) + ca.1.f ⟨0, by decide⟩)) R₀ R₁,
        m') ∧ m'.st.input = m.st.input :=
  play_tS m (ca.1.f ⟨0, by decide⟩) R₀ R₁

theorem shows_tell (c : Cs ⟨0, 0⟩) (sp : Unit) (ca : Cs ⟨1, 0⟩ × Unit) (m : Mid L Nat)
    (R₀ R₁ : Fmt.Drawn) (asks : List (List (List Nat))) :
    ySide₃.shows .own yU₃ (c, sp, ca) m [R₀, R₁] asks =
      tellAt (toF (m.st.input.trace.b (posOf R₀)) + ca.1.f ⟨0, by decide⟩) := by
  obtain ⟨m', h, -⟩ := play_tellPart c sp ca m R₀ R₁
  unfold Side.shows
  rw [h]
  rfl

/-- What `Before.holds` asks at the rounds of `yTell`, where the first challenge draws the one
position x. -/
theorem holds_tell (front : Before) (ft : Nat) (el : List Fmt.Ext) (x : Nat) (tr : List Int)
    (dg : Option ByteArray) (R₁ : Fmt.Drawn) :
    front.holds 2 ft (yU₃.rounds.map (·.1)) [⟨el, [x], tr, dg⟩, R₁] =
      ((match front.treeCols 2 0 with
        | some cols => cols.any fun c => c.1 == x % 2 ^ 2
        | none => true) && true) := rfl

/-! ## 3 `exact`, part by part -/

theorem exact_own (ca : Unit) (m : Mid L₀ Nat) (front : Before) (R : Fmt.Drawn) (p : Nat) :
    (unif (Cs zU₀.part.takes × CsAll zU₀.part.spends)).map
        (fun c => zSide.shows .shared zU₀ (c.1, c.2, ca) m [R] [[[p]]]) =
      (unif (Cs zU₀.sim.takes)).map fun c =>
        zU₀.tells .shared c m.st.input front [R] [[[p]]] := by
  refine Eq.trans (map_unif_fst_equiv (Cs.eq2u.trans (shear (toF (m.st.input.w₀.a p))))
    (colAt p) _ fun c => shows_own c.1 c.2 ca m R p) (Eq.symm ?_)
  exact map_unif_by_equiv Cs.eq1 (colAt p) _ fun c => tells_own c m.st.input front [R] p

theorem exact_spend (ca : Unit) (m : Mid L₀ Nat) (front : Before) (R : Fmt.Drawn)
    (asks : List (List (List Nat))) :
    (unif (Cs zU₁.part.takes × CsAll zU₁.part.spends)).map
        (fun c => zSide.shows .shared zU₁ (c.1, c.2, ca) m [R] asks) =
      (unif (Cs zU₁.sim.takes)).map fun c => zU₁.tells .shared c m.st.input front [R] asks := by
  refine Eq.trans (map_unif_by_equiv (Cs.eq01u.trans (Equiv.addLeft (toF m.st.input.w₀.ans)))
    ansAt _ fun c => shows_spend c.1 c.2 ca m R asks) (Eq.symm ?_)
  exact map_unif_by_equiv Cs.eq1 ansAt _ fun c => tells_spend c m.st.input front [R] asks

theorem exact_send (ca : Unit) (m : Mid L Nat) (front : Before) (R : Fmt.Drawn) (p : Nat) :
    (unif (Cs yU₂.part.takes × CsAll yU₂.part.spends)).map
        (fun c => ySide₂.shows .own yU₂ (c.1, c.2, ca) m [R] [[[p]]]) =
      (unif (Cs yU₂.sim.takes)).map fun c => yU₂.tells .own c m.st.input front [R] [[[p]]] := by
  refine Eq.trans (map_unif_by_equiv (Cs.eq1u.trans (Equiv.addLeft (toF (m.st.input.trace.b p))))
    (colAt p) _ fun c => shows_send c.1 c.2 ca m R p) (Eq.symm ?_)
  exact map_unif_by_equiv Cs.eq1 (colAt p) _ fun c => tells_send c m.st.input front [R] p

theorem exact_carry (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) (m : Mid L Nat) (front : Before)
    (R : Fmt.Drawn) (asks : List (List (List Nat))) :
    (unif (Cs yU₄.part.takes × CsAll yU₄.part.spends)).map
        (fun c => ySide₄.shows .own yU₄ (c.1, c.2, ca) m [R] asks) =
      (unif (Cs yU₄.sim.takes)).map fun c => yU₄.tells .own c m.st.input front [R] asks := by
  refine Eq.trans (map_unif_by_equiv
    (Cs.eq1u.trans ((Equiv.addLeft (toF m.st.input.trace.last)).trans
      ((Equiv.addRight (ca.1.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩ +
          ca.1.f ⟨0, by decide⟩)).trans
        (Equiv.addRight (ca.2.1.f ⟨0, by decide⟩ + ca.2.1.f ⟨0, by decide⟩ +
          ca.2.1.f ⟨0, by decide⟩ + ca.2.1.f ⟨0, by decide⟩)))))
    eAt _ fun c => shows_carry c.1 c.2 ca m R asks) (Eq.symm ?_)
  exact map_unif_by_equiv Cs.eq1 eAt _ fun c => tells_carry c m.st.input front [R] asks

/-- `yTell`: both distributions are point masses. -/
theorem exact_tell (ca : Cs ⟨1, 0⟩ × Unit) (m : Mid L Nat) (front : Before) (ft : Nat)
    (R₀ R₁ : Fmt.Drawn) (asks : List (List (List Nat)))
    (hOn : onTell (ca.1.f ⟨0, by decide⟩) m.st.input.trace.b front = true)
    (h₀ : R₀.poss.length = 1)
    (hh : front.holds 2 ft (yU₃.rounds.map (·.1)) [R₀, R₁] = true) :
    (unif (Cs yU₃.part.takes × CsAll yU₃.part.spends)).map
        (fun c => ySide₃.shows .own yU₃ (c.1, c.2, ca) m [R₀, R₁] asks) =
      (unif (Cs yU₃.sim.takes)).map fun c =>
        yU₃.tells .own c m.st.input front [R₀, R₁] asks := by
  obtain ⟨el, ps, tr, dg⟩ := R₀
  obtain ⟨x, hx⟩ := one_of_length (l := ps) h₀
  subst hx
  rw [holds_tell] at hh
  cases hc : front.treeCols 2 0 with
  | none =>
    unfold onTell at hOn
    rw [hc] at hOn
    have hOn' : false = true := hOn
    cases hOn'
  | some cols =>
    unfold onTell at hOn
    rw [hc] at hOn hh
    have hAll : cols.all (fun c =>
        c.2 == [ofF (toF (m.st.input.trace.b c.1) + ca.1.f ⟨0, by decide⟩)]) = true := hOn
    have hAny : cols.any (fun c => c.1 == x % 2 ^ 2) = true := (Bool.and_eq_true_iff.1 hh).1
    cases hf : cols.find? (fun c => c.1 == x % 2 ^ 2) with
    | none =>
      obtain ⟨c₀, hm, hp⟩ := List.any_eq_true.1 hAny
      exact absurd hp (List.find?_eq_none.1 hf c₀ hm)
    | some c₀ =>
      have hb : (c₀.1 == x % 2 ^ 2) = true :=
        List.find?_some (p := fun c : Nat × List UInt64 => c.1 == x % 2 ^ 2) hf
      have h1 : c₀.1 = x % 2 ^ 2 := eq_of_beq hb
      have h2 : c₀.2 = [ofF (toF (m.st.input.trace.b c₀.1) + ca.1.f ⟨0, by decide⟩)] :=
        eq_of_beq (List.all_eq_true.1 hAll c₀ (List.mem_of_find?_eq_some hf))
      refine map_unif_point
        (tellAt (toF (m.st.input.trace.b (x % 2 ^ 2)) + ca.1.f ⟨0, by decide⟩)) _ _
        (fun c => shows_tell c.1 c.2 ca m ⟨el, [x], tr, dg⟩ R₁ asks) (fun c => ?_)
      show ((front.treeCols 2 0).bind fun cols =>
        (cols.find? fun c => c.1 == x % 2 ^ 2).map fun c =>
          [(⟨[], []⟩ : Shown), ⟨[.e (c.2.headD 0, 0, 0)], []⟩]) = _
      rw [hc]
      show ((cols.find? fun c => c.1 == x % 2 ^ 2).map fun c =>
          [(⟨[], []⟩ : Shown), ⟨[.e (c.2.headD 0, 0, 0)], []⟩]) = _
      rw [hf]
      show some [(⟨[], []⟩ : Shown), ⟨[.e (c₀.2.headD 0, 0, 0)], []⟩] = _
      rw [h2, h1]
      rfl

/-! ## 4 `fresh` at the one pair of owner and spender -/

/-- The one entry of either book that spends. -/
def eU : Ahead := ⟨"u to the spender", zO, ⟨1, 0⟩, ⟨1, 0⟩, zP, true⟩

theorem By_spent : ∀ e ∈ By.ahead, e.once = true → e.owner = zO ∧ e.spender = zP := by decide
theorem Bz_spent : ∀ e ∈ Bz.ahead, e.once = true → e.owner = zO ∧ e.spender = zP := by decide

/-- The block that the entry cuts from the owner's two coins is the second coin. -/
theorem cut_u (c : Cs ⟨2, 0⟩) : c.cut ⟨1, 0⟩ ⟨1, 0⟩ = some (Cs.one (c.f ⟨1, by decide⟩)) := by
  unfold Cs.cut
  split
  · congr 1
    exact Cs.ext'
      (fun i => congrArg c.f (Fin.ext (by
        have h : i.1 < 1 := i.2
        show 1 + i.1 = 1
        omega)))
      (fun i => i.elim0)
  · rename_i h
    exact absurd ⟨by decide, by decide⟩ h

theorem cutAll_u (c : Cs ⟨2, 0⟩) :
    cutAll c [eU] =
      (some (Cs.one (c.f ⟨1, by decide⟩), ()) : Option (CsAll ([eU].map Ahead.named))) := by
  show ((c.cut ⟨1, 0⟩ ⟨1, 0⟩).bind fun x => (cutAll c []).map fun y => (x, y)) = _
  rw [cut_u]
  rfl

/-- What the three components of `fresh` are, as functions of the column's element y and the spent
coin u. -/
def freshAt (p : Nat) (x : Cb.Gl.F × Cb.Gl.F) :
    Option (CsAll ([eU].map Ahead.named)) × Option (List Shown) ×
      Option (CsAll (([] : List Ahead).map Ahead.named)) :=
  (some (Cs.one x.2, ()), colAt p x.1, some ())

/-- The owner's condition for its spender: (u, the column at p, nothing) over (t, u), and the same
with u drawn afresh. -/
theorem fresh_own (es ks : List Ahead) (hes : es = [eU]) (hks : ks = []) (sp ca : Unit)
    (m : Mid L₀ Nat) (R : Fmt.Drawn) (p : Nat) :
    (unif (Cs zU₀.part.takes)).map (fun c =>
        (cutAll c es, zSide.shows .shared zU₀ (c, sp, ca) m [R] [[[p]]], cutAll c ks)) =
      (unif (CsAll (es.map Ahead.named) × Cs zU₀.part.takes)).map fun a =>
        (some a.1, zSide.shows .shared zU₀ (a.2, sp, ca) m [R] [[[p]]], cutAll a.2 ks) := by
  subst hes
  subst hks
  refine Eq.trans (map_unif_by_equiv (Cs.eq2.trans (shear (toF (m.st.input.w₀.a p))))
    (freshAt p) _ fun c => ?_) (Eq.symm ?_)
  · exact Prod.ext (cutAll_u c) (Prod.ext (shows_own c sp ca m R p) rfl)
  · exact map_unif_fst_equiv
      ((Equiv.prodCongr Cs.eq1u (Cs.eq2.trans (shear (toF (m.st.input.w₀.a p))))).trans rot)
      (freshAt p) _ fun a => Prod.ext (congrArg some (Cs.eq1u.left_inv a.1).symm)
        (Prod.ext (shows_own a.2 sp ca m R p) rfl)

/-! ## 5 The three fields, side by side -/

theorem look_fits : zSide.fits = true := rfl
theorem send_fits : ySide₂.fits = true := rfl
theorem tell_fits : ySide₃.fits = true := rfl
theorem carry_fits : ySide₄.fits = true := rfl
theorem zSide₂_fits : zSide₂.fits = true := rfl

theorem look_exact : ∀ u ∈ zSide.members, ∀ ca m front ds asks, onAny u ca m front →
    m.seen = front.seen → drawsFit (u.rounds.map (·.1)) ds = true → budOne u.number ds asks →
    front.holds 1 0 (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (Face.shared.sees m.st.input) m.loc ds ≠ some .hid →
    (unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => zSide.shows .shared u (c.1, c.2, ca) m ds asks) =
      (unif (Cs u.sim.takes)).map fun c => u.tells .shared c m.st.input front ds asks := by
  intro u hu
  rw [members_look] at hu
  rcases List.mem_pair.1 hu with rfl | rfl
  · intro ca m front ds asks _ _ hd hb _ _
    have hd' : drawsFit [{ entry := sendS }] ds = true := hd
    obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
    obtain ⟨p, rfl⟩ := onePos_elim (hb rfl)
    exact exact_own ca m front R p
  · intro ca m front ds asks _ _ hd _ _ _
    have hd' : drawsFit [{ entry := openA, opens := [(tree, .own 0)] }] ds = true := hd
    obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
    exact exact_spend ca m front R asks

theorem send_exact (ft : Nat) : ∀ u ∈ ySide₂.members, ∀ ca m front ds asks, onAny u ca m front →
    m.seen = front.seen → drawsFit (u.rounds.map (·.1)) ds = true → budOne u.number ds asks →
    front.holds 2 ft (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
    (unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => ySide₂.shows .own u (c.1, c.2, ca) m ds asks) =
      (unif (Cs u.sim.takes)).map fun c => u.tells .own c m.st.input front ds asks := by
  intro u hu
  rw [members_send] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd hb _ _
  have hd' : drawsFit [{ entry := { name := "CS", msg := 32, roots := 1 } }] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  obtain ⟨p, rfl⟩ := onePos_elim (hb rfl)
  exact exact_send ca m front R p

theorem tell_exact (ft : Nat) : ∀ u ∈ ySide₃.members, ∀ ca m front ds asks,
    onTeller u ca m front →
    m.seen = front.seen → drawsFit (u.rounds.map (·.1)) ds = true → budAny u.number ds asks →
    front.holds 2 ft (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
    (unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => ySide₃.shows .own u (c.1, c.2, ca) m ds asks) =
      (unif (Cs u.sim.takes)).map fun c => u.tells .own c m.st.input front ds asks := by
  intro u hu
  rw [members_tell] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks hOn _ hd _ hh _
  have hd' : drawsFit [{ entry := drawT, opens := [(tree₃, .own 0)] },
      { entry := { name := "CS", msg := 24 } }] ds = true := hd
  obtain ⟨R₀, R₁, rfl, h₀, -⟩ := drawsFit_two hd'
  have hl : R₀.poss.length = 1 := by
    simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h₀
    exact h₀.1.1.1.1.1.1.2
  exact exact_tell ca m front ft R₀ R₁ asks hOn hl hh

theorem carry_exact (ft : Nat) : ∀ u ∈ ySide₄.members, ∀ ca m front ds asks, onAny u ca m front →
    m.seen = front.seen → drawsFit (u.rounds.map (·.1)) ds = true → budAny u.number ds asks →
    front.holds 2 ft (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
    (unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => ySide₄.shows .own u (c.1, c.2, ca) m ds asks) =
      (unif (Cs u.sim.takes)).map fun c => u.tells .own c m.st.input front ds asks := by
  intro u hu
  rw [members_carry] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd _ _ _
  have hd' : drawsFit [{ entry := { name := "CS", msg := 24 } }] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  exact exact_carry ca m front R asks

theorem zSide₂_exact (ft : Nat) : ∀ u ∈ zSide₂.members, ∀ ca m front ds asks,
    onAny u ca m front →
    m.seen = front.seen → drawsFit (u.rounds.map (·.1)) ds = true → budAny u.number ds asks →
    front.holds 2 ft (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
    (unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => zSide₂.shows .own u (c.1, c.2, ca) m ds asks) =
      (unif (Cs u.sim.takes)).map fun c => u.tells .own c m.st.input front ds asks := by
  intro u hu
  rw [members_zSide₂] at hu
  obtain rfl := List.mem_singleton.1 hu
  intro ca m front ds asks _ _ hd _ _ _
  have hd' : drawsFit [{ entry := { name := "CS", msg := 24 } }] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  exact Eq.trans (congrArg (fun φ => PMF.map φ _)
    (funext fun c => shows_zCarry c.1 c.2 ca m R asks)) (exact_carry ca m front R asks)

/-- `fresh` at the side of `look`, at a book whose one spending entry is `eU` and at an order in
which nothing else of the owner's is given to the spender or to a part before it. -/
theorem look_fresh (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ e ∈ Bk.ahead, e.once = true → e.owner = zO ∧ e.spender = zP)
    (hS : Bk.spentBy zO zP = [eU]) (hK : Bk.knownBy ord zO zP = []) :
    ∀ u ∈ zSide.members, ∀ (p : Addr) sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → budOne u.number ds asks →
    u.part.stopAt (Face.shared.sees m.st.input) m.loc ds ≠ some .hid →
    (unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨zSide.block.place, u.number⟩ p),
          zSide.shows .shared u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨zSide.block.place, u.number⟩ p))) =
      (unif (CsAll ((Bk.spentBy ⟨zSide.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, zSide.shows .shared u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨zSide.block.place, u.number⟩ p)) := by
  intro u hu
  rw [members_look] at hu
  rcases List.mem_pair.1 hu with rfl | rfl
  · intro p sp ca m ds asks hd hb _
    have hd' : drawsFit [{ entry := sendS }] ds = true := hd
    obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
    obtain ⟨q, rfl⟩ := onePos_elim (hb rfl)
    by_cases hp : p = zP
    · subst hp
      exact fresh_own _ _ hS hK sp ca m R q
    · exact fresh_of_nil _ (spentBy_nil Bk zO p fun e he ho _ hs =>
        hp (hs.symm.trans (hB e he ho).2)) _ _
  · intro p sp ca m ds asks _ _ _
    exact fresh_of_nil _ (spentBy_nil Bk zP p fun e he ho hw _ =>
      absurd ((hB e he ho).1.symm.trans hw) (by decide)) _ _

/-- `fresh` at a side of whose parts' coins the book lets nobody spend any. -/
theorem fresh_unspent {S Cl V W X Pb : Type} (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (h : ∀ e ∈ Bk.ahead, e.once = true → e.owner.place ≠ σ.block.place) :
    ∀ u ∈ σ.members, ∀ (p : Addr) sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p)) := by
  intro u _ p sp ca m ds asks _ _ _
  exact fresh_of_nil _ (spentBy_nil Bk _ p fun e he ho hw _ =>
    h e he ho (congrArg Addr.place hw)) _ _

theorem By_spent_place : ∀ e ∈ By.ahead, e.once = true → e.owner.place = pLook := by decide
theorem Bz_spent_place : ∀ e ∈ Bz.ahead, e.once = true → e.owner.place = pLook := by decide

/-! ## 6 The lists of parts: what coins the book gives, what is played, what is read, what is
decided -/

/-- A round whose challenge its entry can draw, and whose items are those that the entry cuts,
passes `roundsFit`. -/
theorem roundsFit_cons {d : Fmt.DeclaredRound} {R : Fmt.Drawn} {v : List Fmt.ItemValue}
    {ds : List Fmt.DeclaredRound} {rs : List Fmt.RoundView}
    (hv : (v.map itemOf == d.items.filter (· != .root)) = true) (h : drawFit d R = true) :
    roundsFit (d :: ds) (⟨v, R⟩ :: rs) = roundsFit ds rs := by
  simp only [drawFit, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, -⟩ := h
  have h6' : drawsMarkedNonzeroHaveNonzeroWords d ⟨v, R⟩ = true := h6
  simp only [roundsFit, hv, h1, h2, h3, h4, h5, h6', Bool.true_and]

/-- The number of positions that a challenge holds which a round's entry can draw. -/
theorem poss_of_drawFit {d : Fmt.DeclaredRound} {R : Fmt.Drawn} (h : drawFit d R = true) :
    R.poss.length = d.entry.poss := by
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.2

/-! ### The owner's and the spender's list -/

/-- What a book gives the list at `look`: the owner's two coins, which are the run's own; to the
spender none of its own and one block. -/
def LendsLook (Bk : ProverCoinCounts) : Prop :=
  ∀ k : Coins Bk, ∃ (c₀ : Cs ⟨2, 0⟩) (e₀ : Cs ⟨0, 0⟩) (cu : Cs ⟨1, 0⟩),
    lendRow Bk (Bk.rowsOf 1) (k.look 1) zSide.block.place zSide.half.parts 0 =
      .ok ((c₀, (), ()), ((e₀, (cu, ()), ()), ())) ∧
    c₀.f ⟨0, by decide⟩ = coinAt k 1 zO 0 ∧ c₀.f ⟨1, by decide⟩ = coinAt k 1 zO 1

theorem lendsLook_By : LendsLook By := fun _ => ⟨_, _, _, rfl, rfl, rfl⟩
theorem lendsLook_Bz : LendsLook Bz := fun _ => ⟨_, _, _, rfl, rfl, rfl⟩

/-- The list's two rounds, played. -/
theorem play_look (c₀ : Cs ⟨2, 0⟩) (e₀ : Cs ⟨0, 0⟩) (cu : Cs ⟨1, 0⟩) (m : Mid L₀ Nat)
    (R₀ R₁ : Fmt.Drawn) : ∃ m' : Mid L₀ Nat,
    play (zSide.half.steps zSide.block (Face.shared.sees m.st.input)
        ((c₀, (), ()), ((e₀, (cu, ()), ()), ()))) [R₀, R₁] [] m =
      .ok ([⟨"look", pLook, 0, true, [], [some ⟨3, 1, fun p _ => toF (m.st.input.w₀.a p) +
          c₀.f ⟨0, by decide⟩ + c₀.f ⟨1, by decide⟩ + c₀.f ⟨1, by decide⟩⟩], R₀⟩,
        ⟨"look", pLook, 1, true, [.answer (ofF (toF m.st.input.w₀.ans + cu.f ⟨0, by decide⟩),
          ofF (toF 0), ofF (toF 0))], [], R₁⟩], m') ∧ m'.st.input = m.st.input := by
  have h := play_two (m := m) (d₀ := R₀) (d₁ := R₁)
    (s₀ := ⟨"look", zO, { entry := sendS }, [orc (3, 1) true], zOwn.bad,
      fun f o => (Face.shared.sees m.st.input).bind fun w => zOwn.hid w f o, 0, true,
      some ⟨fun _ _ s => .ok ⟨[], [⟨3, 1, fun p _ => toF (s.input.w₀.a p) + c₀.f ⟨0, by decide⟩ +
        c₀.f ⟨1, by decide⟩ + c₀.f ⟨1, by decide⟩⟩]⟩, fun _ => 7⟩⟩)
    (s₁ := ⟨"look", zP, { entry := openA, opens := [(tree, .own 0)] }, [], zSpend.bad,
      fun f o => (Face.shared.sees m.st.input).bind fun w => zSpend.hid w f o, 0, true,
      some ⟨fun _ _ s => .ok ⟨[.answer ⟨toF s.input.w₀.ans + cu.f ⟨0, by decide⟩, toF 0, toF 0⟩],
        []⟩, fun s => s.own⟩⟩)
    (z₀ := ⟨[], [⟨3, 1, fun p _ => toF (m.st.input.w₀.a p) + c₀.f ⟨0, by decide⟩ +
      c₀.f ⟨1, by decide⟩ + c₀.f ⟨1, by decide⟩⟩]⟩)
    (z₁ := ⟨[.answer ⟨toF m.st.input.w₀.ans + cu.f ⟨0, by decide⟩, toF 0, toF 0⟩], []⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  exact ⟨_, h, rfl⟩

/-! ### The second owner's list -/

theorem lend_send (k : Coins By) : ∃ c₀ : Cs ⟨1, 0⟩,
    lendRow By (By.rowsOf 2) (k.look 2) ySide₂.block.place ySide₂.half.parts 0 =
      .ok ((c₀, (), ()), ()) ∧ c₀.f ⟨0, by decide⟩ = coinAt k 2 sSend 0 :=
  ⟨_, rfl, rfl⟩

theorem play_sendRow (c₀ : Cs ⟨1, 0⟩) (m : Mid L Nat) (R : Fmt.Drawn) : ∃ m' : Mid L Nat,
    play (ySide₂.half.steps ySide₂.block (Face.own.sees m.st.input) ((c₀, (), ()), ())) [R] [] m =
      .ok ([⟨"send", pSend, 0, true, [], [some ⟨2, 1, fun p _ => toF (m.st.input.trace.b p) +
        c₀.f ⟨0, by decide⟩⟩], R⟩], m') ∧ m'.st.input = m.st.input := by
  have h := play_one (m := m) (d := R)
    (s := ⟨"send", sSend, { entry := { name := "CS", msg := 32, roots := 1 } }, [orc (2, 1)],
      ySend.bad, fun f o => (Face.own.sees m.st.input).bind fun w => ySend.hid w f o, 0, true,
      some ⟨fun _ _ s => .ok ⟨[], [⟨2, 1, fun p _ => toF (s.input.trace.b p) +
        c₀.f ⟨0, by decide⟩⟩]⟩, fun s => s.own⟩⟩)
    (z := ⟨[], [⟨2, 1, fun p _ => toF (m.st.input.trace.b p) + c₀.f ⟨0, by decide⟩⟩]⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)
  exact ⟨_, h, rfl⟩

/-! ### The carrier's list, at either sub-protocol -/

/-- The carrier's round, as the `Step` that `play` is given. -/
def cS (m : Mid L Nat) (c : Cs ⟨1, 0⟩) (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit) : Step L Nat :=
  ⟨"ask", sAsk, { entry := { name := "CS", msg := 24 } }, [], zCarry.bad,
    fun f o => (Face.own.sees m.st.input).bind fun w => zCarry.hid w f o, 0, true,
    some ⟨fun _ _ s => .ok ⟨[.e ⟨toF s.input.trace.last + c.f ⟨0, by decide⟩ +
      (ca.1.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩ + ca.1.f ⟨0, by decide⟩) +
      (ca.2.1.f ⟨0, by decide⟩ + ca.2.1.f ⟨0, by decide⟩ + ca.2.1.f ⟨0, by decide⟩ +
        ca.2.1.f ⟨0, by decide⟩), toF 0, toF 0⟩], []⟩, fun s => s.own⟩⟩

theorem play_cS (m : Mid L Nat) (c : Cs ⟨1, 0⟩) (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit)
    (R : Fmt.Drawn) : ∃ m' : Mid L Nat, play [cS m c ca] [R] [] m =
      .ok ([⟨"ask", pAsk, 0, true, [.e (ofF (carryVal m c ca), ofF (toF 0), ofF (toF 0))], [], R⟩],
        m') :=
  ⟨_, play_one (z := ⟨[.e ⟨carryVal m c ca, toF 0, toF 0⟩], []⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl (by with_unfolding_all rfl)
    (by with_unfolding_all rfl)⟩

theorem lend_carry (k : Coins By) : ∃ (c : Cs ⟨1, 0⟩) (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit),
    lendRow By (By.rowsOf 2) (k.look 2) ySide₄.block.place ySide₄.half.parts 0 =
      .ok ((c, (), ca), ()) := ⟨_, _, rfl⟩
theorem lend_zCarry (k : Coins Bz) : ∃ (c : Cs ⟨1, 0⟩) (ca : Cs ⟨1, 0⟩ × Cs ⟨1, 0⟩ × Unit),
    lendRow Bz (Bz.rowsOf 2) (k.look 2) zSide₂.block.place zSide₂.half.parts 0 =
      .ok ((c, (), ca), ()) := ⟨_, _, rfl⟩

/-! ### The list of `yTell` -/

/-- What the book gives `yTell`: no coin of its own, and as carried the second owner's coin. -/
theorem lend_tell (k : Coins By) : ∃ (c₀ : Cs ⟨0, 0⟩) (cv : Cs ⟨1, 0⟩),
    lendRow By (By.rowsOf 2) (k.look 2) ySide₃.block.place ySide₃.half.parts 0 =
      .ok ((c₀, (), (cv, ())), ()) ∧ cv.f ⟨0, by decide⟩ = coinAt k 2 sSend 0 :=
  ⟨_, _, rfl, rfl⟩

/-- The two rounds of `yTell`, played: as a list of parts. -/
theorem play_tell (c₀ : Cs ⟨0, 0⟩) (cv : Cs ⟨1, 0⟩) (m : Mid L Nat) (R₀ R₁ : Fmt.Drawn) :
    ∃ m' : Mid L Nat,
      play (ySide₃.half.steps ySide₃.block (Face.own.sees m.st.input) ((c₀, (), (cv, ())), ()))
          [R₀, R₁] [] m =
        .ok (tellPlayed (ofF (toF (m.st.input.trace.b (posOf R₀)) + cv.f ⟨0, by decide⟩)) R₀ R₁,
          m') ∧ m'.st.input = m.st.input :=
  play_tS m (cv.f ⟨0, by decide⟩) R₀ R₁

/-- What the rounds of `yTell` read, where the chain has sent one tree before them. -/
theorem reads_tell (st : Nat → Nat → Option (List UInt64))
    (tre : Fmt.TreeSource → Option (Place × Table)) (ps : List Played) (ft : Nat)
    (el : List Fmt.Ext) (x : Nat) (tr : List Int) (dg : Option ByteArray) (R₁ : Fmt.Drawn) :
    readsOf 2 ft (Env.add ⟨st, tre, 1⟩ ps).stored (Env.add ⟨st, tre, 1⟩ ps).tree tellB.rounds
        [⟨el, [x], tr, dg⟩, R₁] =
      [⟨tree₃.tree - ft, x % 2 ^ 2, none, some (2, 0), (tre (.own 0)).map (·.1),
        (tre (.own 0)).map (·.2.col (x % 2 ^ 2)), 1⟩] := rfl

/-- The decision of `tellB` where the word said is the column's. -/
theorem tell_decide (s : St) (r₀ r₁ : Fmt.Drawn) (p : Nat) (w : UInt64) :
    tellB.decide s [⟨[], r₀⟩, ⟨[.e (w, 0, 0)], r₁⟩] [[(p, [w])]] = .ok s := by
  show (need "tell.the-word" ((w, (0 : UInt64), (0 : UInt64)) == (w, 0, 0))).map (fun _ => s) =
    .ok s
  rw [beq_self_eq_true]
  rfl

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.members_look
#print axioms ProofFile.Honest.Toy.members_send
#print axioms ProofFile.Honest.Toy.members_tell
#print axioms ProofFile.Honest.Toy.members_carry
#print axioms ProofFile.Honest.Toy.members_zSide₂
#print axioms ProofFile.Honest.Toy.onePos_elim
#print axioms ProofFile.Honest.Toy.play_own
#print axioms ProofFile.Honest.Toy.shows_own
#print axioms ProofFile.Honest.Toy.tells_own
#print axioms ProofFile.Honest.Toy.play_spend
#print axioms ProofFile.Honest.Toy.shows_spend
#print axioms ProofFile.Honest.Toy.tells_spend
#print axioms ProofFile.Honest.Toy.play_send
#print axioms ProofFile.Honest.Toy.shows_send
#print axioms ProofFile.Honest.Toy.tells_send
#print axioms ProofFile.Honest.Toy.play_carry
#print axioms ProofFile.Honest.Toy.shows_carry
#print axioms ProofFile.Honest.Toy.shows_zCarry
#print axioms ProofFile.Honest.Toy.tells_carry
#print axioms ProofFile.Honest.Toy.play_tS
#print axioms ProofFile.Honest.Toy.play_tellPart
#print axioms ProofFile.Honest.Toy.shows_tell
#print axioms ProofFile.Honest.Toy.holds_tell
#print axioms ProofFile.Honest.Toy.exact_own
#print axioms ProofFile.Honest.Toy.exact_spend
#print axioms ProofFile.Honest.Toy.exact_send
#print axioms ProofFile.Honest.Toy.exact_carry
#print axioms ProofFile.Honest.Toy.exact_tell
#print axioms ProofFile.Honest.Toy.By_spent
#print axioms ProofFile.Honest.Toy.Bz_spent
#print axioms ProofFile.Honest.Toy.cut_u
#print axioms ProofFile.Honest.Toy.cutAll_u
#print axioms ProofFile.Honest.Toy.fresh_own
#print axioms ProofFile.Honest.Toy.look_fits
#print axioms ProofFile.Honest.Toy.send_fits
#print axioms ProofFile.Honest.Toy.tell_fits
#print axioms ProofFile.Honest.Toy.carry_fits
#print axioms ProofFile.Honest.Toy.zSide₂_fits
#print axioms ProofFile.Honest.Toy.look_exact
#print axioms ProofFile.Honest.Toy.send_exact
#print axioms ProofFile.Honest.Toy.tell_exact
#print axioms ProofFile.Honest.Toy.carry_exact
#print axioms ProofFile.Honest.Toy.zSide₂_exact
#print axioms ProofFile.Honest.Toy.look_fresh
#print axioms ProofFile.Honest.Toy.fresh_unspent
#print axioms ProofFile.Honest.Toy.By_spent_place
#print axioms ProofFile.Honest.Toy.Bz_spent_place
#print axioms ProofFile.Honest.Toy.roundsFit_cons
#print axioms ProofFile.Honest.Toy.poss_of_drawFit
#print axioms ProofFile.Honest.Toy.lendsLook_By
#print axioms ProofFile.Honest.Toy.lendsLook_Bz
#print axioms ProofFile.Honest.Toy.play_look
#print axioms ProofFile.Honest.Toy.lend_send
#print axioms ProofFile.Honest.Toy.play_sendRow
#print axioms ProofFile.Honest.Toy.play_cS
#print axioms ProofFile.Honest.Toy.lend_carry
#print axioms ProofFile.Honest.Toy.lend_zCarry
#print axioms ProofFile.Honest.Toy.lend_tell
#print axioms ProofFile.Honest.Toy.play_tell
#print axioms ProofFile.Honest.Toy.reads_tell
#print axioms ProofFile.Honest.Toy.tell_decide
