-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/XkAtHead.lean: FOR "THE FORM BEHIND" AT K9's THREE MEMBERS, WITH NO LETTER OF K9's
LEFT: under the library's head h and l < 25, AT WHATEVER BLOCK blk STANDS AT THE MEMBER's NUMBER IN THE FIRST CHAIN's
FLAT LIST: nine statements: at the batching (14 l + nAt l + 2), "the one equation" (14 l + nAt l + 4 + 0) and "the
segment is shut" (14 l + nAt l + 4 + 2): no mark behind a yes of blk's step · XK at the public test `EW` behind, from
XK there in front and no mark in front · `samplesHeld` behind, from `samplesHeld` in front. No thread, no prover, no
string is in this file. Statements and proofs ON THE VERIFIER's TEXT; no goal is stated.
  `seats_at_head`   under h, l < 25: K9's two seats at one link Lk and one p, with the number of hearing members
      `IM.nAt l`: `seated_at_head` (Honest/K9/AtHead.lean) and `close_at_head` (Honest/K9/CloseKeeps.lean) joined:
      both name the chain's link at l; `seated_at_head` hands "if l = 24 then 9 else 7": `IM.nAt l`'s text, by
      unfolding. Called by the nine and by Honest/K9/KeepsAtPlace.lean
  `mark_bat_at`, `mark_eq_at`, `mark_shut_at` · **`xk_bat_at`**, **`xk_eq_at`**, **`xk_shut_at`** · `samples_bat_at`,
      `samples_eq_at`, `samples_shut_at`   the nine: Honest/K9/XkBat.lean's, XkClose.lean's and XkSamples.lean's at
      these seats. FOR A CALLER: the numbers stand in the library's forms (`close0_Pt`'s + 4 + 0, `close2_E`'s + 4 +
      2): whoever writes a border otherwise owes that equation · ft stands BEFORE base z | N Mg hH z here, behind them
      in those three files · "hb" is the block's line here, base's own premise there (here: hbase)
AT "THE ONE EQUATION" `xk_eq_at` KEEPS THE TWO NAMED PREMISES AT THE STATE IN FRONT (hg · hne:
Honest/K9/XkClose.lean's head says what they are); Honest/K9/XkEqReach.lean pays both from the library's raw "reached"
at that border, with no mark and XK in front for hne (`xk_eq_reach`; at the frame's thread, from its stand:
`xk_eq_thr`). At the two other members no premise ON THE STATE stays beside what stands in front. ON THE LETTERS:
hbase (base answers alike at any two states; by our reader's reading the library's `mgBase.pub` does: false
everywhere) at the three on XK; hH (`Mg.held` is the library's `smpHeld`; its `mgAll_held` says so of the composed
meaning by rfl) at the three on `samplesHeld`; N and Mg are free there. No mark in front is asked, as the frame's pen
from the yes and no mark behind: kept for the caller's ease.
WHAT IS NOT CLAIMED. That a yes is there. XK or `samplesHeld` at any state. hg, hne at any state. pubP. The step from
the frame's letters to `EW` and back (Honest/K9/XkFront.lean has it for XK under four equations; for `samplesHeld`'s
open set the caller turns `IM.linksW`, `IM.placesW` by the last two: no lemma of ours). No member: `xk_eq_at` is
called by Honest/K9/XkEqReach.lean, `seats_at_head` also by KeepsAtPlace.lean; the eight others by no line. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.XkSamples
import Johnson.Desc.ProofFile.Honest.K9.AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open LPFK9.HandsAt (EW)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- K9's two seats at one link. -/
theorem seats_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) :
    ∃ Lk p w Q bE bS, SeatedFree cF Zp l (IM.nAt l) Lk p w ∧ SeatedClose cF Zp l Lk p Q bE bS := by
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h l hl
  obtain ⟨Lk', p', Q, bE, bS, H⟩ := close_at_head h l hl
  obtain rfl : Lk = Lk' := Option.some.inj (Sd.link.symm.trans H.link)
  obtain rfl : p = p' := Option.some.inj (Sd.numbers.symm.trans H.numbers)
  exact ⟨Lk, p, w, Q, bE, bS, Sd, H⟩

section
variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl} (ft : ℕ)
  {s s' : S}
include h hl

/-- No mark behind the batching's yes. -/
theorem mark_bat_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk) (hy : IM.Yes ft blk s s') :
    s'.failed = none := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, -⟩ := seats_at_head h hl
  obtain rfl := Option.some.inj (hb.symm.trans Sd.batching)
  exact mark_behind_bat Sd ft hy

/-- No mark behind the yes of "the one equation". -/
theorem mark_eq_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk) (hy : IM.Yes ft blk s s') :
    s'.failed = none := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atE
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  exact mark_behind_eq H ft hy

/-- No mark behind the yes of "the segment is shut". -/
theorem mark_shut_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some blk) (hy : IM.Yes ft blk s s') :
    s'.failed = none := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atS
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  exact mark_behind_shut H ft hy

variable {P : Type} (base : First.Pub → P × S → Bool) (z : P)
  (hbase : ∀ q (s s' : S), base q (z, s') = base q (z, s))
include hbase

/-- **XK behind the batching's yes.** -/
theorem xk_bat_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk) (hy : IM.Yes ft blk s s')
    (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 2) s = true) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 2 + 1) s' = true := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, -⟩ := seats_at_head h hl
  obtain rfl := Option.some.inj (hb.symm.trans Sd.batching)
  exact xk_behind_bat h hl Sd base z hbase ft hy h0 hx

/-- **XK behind the yes of "the one equation"**, under the two named premises at the state in front. -/
theorem xk_eq_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk) (hy : IM.Yes ft blk s s')
    (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 0) s = true)
    (hg : ∀ a, Desc.K9.atS.get? s = some a → (P5J.At.N Zp cF).groupAt l = a.L.check.group)
    (hne : LinkJoin.OwnNotIndex s) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 0 + 1) s' = true := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atE
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  exact xk_behind_eq h hl H base z hbase ft hy h0 hx hg hne

/-- **XK behind the yes of "the segment is shut".** -/
theorem xk_shut_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some blk) (hy : IM.Yes ft blk s s')
    (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 2) s = true) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (EW h.𝔇.pubD base z) (14 * l + IM.nAt l + 4 + 2 + 1) s' = true := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atS
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  exact xk_behind_shut h hl H base z hbase ft hy h0 hx

end

section
variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl} (ft : ℕ)
  {s s' : S} {P W : Type} (N : Numbers) (Mg : Meaning P W)
  (hH : Mg.held = fun j t (a : P × S) => smpHeld a.2.st a.2.book j t) (z : P)
include h hl hH

/-- `samplesHeld` behind the batching's yes. -/
theorem samples_bat_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk) (hy : IM.Yes ft blk s s')
    (hs : samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 2)) (z, s) = true) :
    samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 2 + 1)) (z, s') = true := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, -⟩ := seats_at_head h hl
  obtain rfl := Option.some.inj (hb.symm.trans Sd.batching)
  exact samples_behind_bat h hl Sd N Mg hH z ft hy hs

/-- `samplesHeld` behind the yes of "the one equation". -/
theorem samples_eq_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk) (hy : IM.Yes ft blk s s')
    (hs : samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 0)) (z, s) = true) :
    samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 0 + 1)) (z, s') = true := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atE
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  exact samples_behind_eq hl H N Mg hH z ft hy hs

/-- `samplesHeld` behind the yes of "the segment is shut". -/
theorem samples_shut_at (hb : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some blk) (hy : IM.Yes ft blk s s')
    (hs : samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 2)) (z, s) = true) :
    samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 2 + 1)) (z, s') = true := by
  obtain ⟨Lk, p, w, Q, bE, bS, Sd, H⟩ := seats_at_head h hl
  have e := H.atS
  rw [Sd.hears] at e
  obtain rfl := Option.some.inj (hb.symm.trans e)
  exact samples_behind_shut hl H N Mg hH z ft hy hs

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.seats_at_head
#print axioms ProofFile.Honest.K9.mark_bat_at
#print axioms ProofFile.Honest.K9.mark_eq_at
#print axioms ProofFile.Honest.K9.mark_shut_at
#print axioms ProofFile.Honest.K9.xk_bat_at
#print axioms ProofFile.Honest.K9.xk_eq_at
#print axioms ProofFile.Honest.K9.xk_shut_at
#print axioms ProofFile.Honest.K9.samples_bat_at
#print axioms ProofFile.Honest.K9.samples_eq_at
#print axioms ProofFile.Honest.K9.samples_shut_at
