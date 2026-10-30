-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerZetaAt.lean: "LIN zeta" AT THE LEDGER OF A PROOF FILE's SHARED CHAIN, AT
THE TABLE's FILES' OWN FILLING of the pins, of the promise's three clauses on a message and of the
extractor (meaningSigS, promSigS, extS: Johnson/Desc/Sound/BordersSharedFill.lean), and at the words
rgOf (Johnson/Desc/K14/Law/LedgerPins.lean). Of zeta_clause's ten premises
(Johnson/Desc/K14/Law/LedgerZeta.lean) FOUR ARE PAID HERE (hid, hback, hdet, and of hprom and frames
all that speaks of a message's pin or promise). A JOINING.

  sub7, nl7       the table at border 8 promises "no collision" of no message of which it does not
                  at border 7, and not yet "nothing is left": by evaluation.
  openSh_iff, open7_pin   which shared items are open at a border: the computed list; the two pins
                  are open at border 7.
  zeta_at_sig     **the clause at block 7, at that filling.**
WHAT IS LEFT, AND WHOSE. By make: hz (LedgerWrap.lean) · hd · he. NUMBERS of the plan and tiling:
SentBefore at each message whose pin is open (hB, hB'). THE TABLE's FILES' LETTER smp₂, and the
test "the record holds the sample": they read no z_fd (hsm, hh). THE FILLING (K14's law's files):
hOm · hFold · hnum (the numbers noted for o_u and o_omega are the plan's) · hshape (shape 7 gives
shape 8 whatever z_fd is laid) · hother (the rows as they lie ride back). THE STORED TABLE's PROMISE
reads the cells and no z_fd (htab). The plan's mem, and that its two members sit at the table's
tenants.
What is not claimed. NO MEMBER: no letters are shown at which what is left holds together. No
soundness of a verifier.

-/
import Johnson.Desc.Sound.GlueSecondProofs
import Johnson.Desc.K14.Law.LedgerPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription smpHeld)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

/-- At border 8 the table promises "no collision" of no message of which it does not at 7. -/
theorem sub7 (split : Bool) (m : Msg2) (h : PromS.noColl m ∈ promsAt split 8) :
    PromS.noColl m ∈ promsAt split 7 := by
  revert h
  cases split <;> cases m <;> decide

/-- At border 8 it does not yet promise that nothing is left. -/
theorem nl7 (split : Bool) : PromS.nothingLeft ∉ promsAt split 8 := by
  cases split <;> decide

/-- Which shared items are open at border k: the computed list. (Kin: the table's files'
openShL_iff, Johnson/Desc/Sound/PointTie.lean: the same two lines; that file's imports are not all
among what this file can import: WHEN IT IS, THIS ONE GOES.) -/
theorem openSh_iff (split : Bool) (k : ℕ) (i : ItemS) :
    openSh split k i ↔ i ∈ openL (insLSh split) (outsLSh split) startLSh k := by
  show openAfter (insSh split) (outsSh split) startSh k i ↔ _
  rw [insSh_eq, outsSh_eq, startSh_eq, openIsList ItemS (insLSh split) (outsLSh split) startLSh]

/-- The pins of o_u and o_omega are open at border 7. -/
theorem open7_pin (split : Bool) (m : Msg2) (h : m = .oU ∨ m = .oOmega) :
    openSh split 7 (.pin m) := by
  refine (openSh_iff split 7 _).2 ?_
  rcases h with rfl | rfl <;> cases split <;> decide

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells)
  (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook)
  (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
  (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- **"LIN zeta" at the ledger, at the table's files' filling.** -/
theorem zeta_at_sig (S : LinShape) (mem : ℕ → Option Mem)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE) (nU nO : ℕ) (xU xO : Mem)
    (hU : mem nU = some xU) (hO : mem nO = some xO) (mU : xU ∈ ms) (mO : xO ∈ ms)
    (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
    (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
    (b : Block (P₁ × St) Cl) (base : ℕ) (d : RDT)
    (ex : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (er : Err (uLT (ckP .two) [d])) {ns a0 : ℕ} (hd : SendsDraws (toRD d) ns S.kRow 0 a0) (e : ℕ)
    (he : S.kRow * Fintype.card GE ^ (S.kRow - 1) ≤ e)
    (hz : ∀ t rs gs t', b.decide t rs gs = .ok t' → linZeta t.2 rs = some t'.2)
    (hB : ∀ m, PromS.noColl m ∈ promsAt split 8 → SentBefore N p l 7
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) m)
    (hB' : ∀ m, openSh split 7 (.pin m) → SentBefore N p l 7
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) m)
    (hsm : ∀ (s : St) z, smp₂ { s with loc := { s.loc with zFd := z } } = smp₂ s)
    (hOm : ∀ x w, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l 7 x →
      OmegaCol OnBytes.Model.Reading.gl S x.1.2 (rgOf cs arr mem rd w) → Mg.omU x.1.2 w)
    (hFold : ∀ (y : (P₁ × St) × Fr.E.Str) w,
      promQ N (promSigS cs G smp₂ ms stOf bookOf Pm) split p l 8 ((actQ N p l 8).2 y) →
      Mg.row .fold y.1.2 w → FoldAt OnBytes.Model.Reading.gl S y.1.2 (rgOf cs arr mem rd w))
    (hnum : ∀ x, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l 7 x →
      x.1.2.loc.oU.oracle = nU ∧ x.1.2.loc.oOmega = nO)
    (hshape : ∀ (s : St) z, Pm.shape 7 s = true →
      Pm.shape 8 { s with loc := { s.loc with zFd := z } } = true)
    (htab : ∀ (s : St) z y y', y'.cell = y.cell → Pm.tablePromise s y →
      Pm.tablePromise { s with loc := { s.loc with zFd := z } } y')
    (hother : ∀ x τ y w i, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l 7 x →
      (⟨b, base, [d], [], ex, er⟩ :
        Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)).ior.red.out x τ = some y →
      openSh split 7 i → ¬ insSh split 7 i → (∀ m, i ≠ .pin m) →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i 8 ((actQ N p l 8).2 y) w →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i 7 ((actQ N p l 7).2 x) w) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ Mg) (promSigS cs G smp₂ ms stOf bookOf Pm) Oc
      split p l
      (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N split k v.1 (strsOfAct Fr v) w) 7
      (⟨b, base, [d], [], ex, er⟩ : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      ((vecMaps d S.kRow).err ((e, ()) : ℕ × Unit)) := by
  have inv : ∀ x τ y, (⟨b, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)).ior.red.out x τ = some y →
      ∃ z, y.1.2 = { x.1.2 with loc := { x.1.2.loc with zFd := z } } := by
    intro x τ y hout
    obtain ⟨_, gs, hdd⟩ := piece_yes (⟨b, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) x τ y hout
    have k7 := hz _ _ _ _ hdd
    obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k7
    rw [hr] at k7
    exact ⟨_, linZeta_inv x.1.2 y.1.2 r7 k7⟩
  have hsm' : ∀ x τ y, (⟨b, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)).ior.red.out x τ = some y →
      smp₂ y.1.2 = smp₂ x.1.2 := by
    intro x τ y hout
    obtain ⟨z, e7⟩ := inv x τ y hout
    rw [e7]
    exact hsm _ z
  refine zeta_clause N (meaningSigS cs G arr smp₂ ms decT₂ Mg)
    (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l _ S (rgOf cs arr mem rd) b base d ex er hd e
    he hz (fun v w => ext7_id cs G arr smp₂ ms decT₂ N split c₀ v.1 (strsOfAct Fr v) w) hOm hFold
    ?_ ?_ (pins7_det cs G arr smp₂ ms decT₂ N Mg (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l
      mem rd nU nO xU xO hU hO mU mO sU sO hnum) ?_
  · intro x τ y hx hout
    obtain ⟨z, e7⟩ := inv x τ y hout
    refine prom_rides cs G smp₂ ms stOf bookOf N Pm p l split 7 (⟨b, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (sub7 split) (nl7 split) hB x y
      τ hout (fun q _ => by rw [hsm' x τ y hout]) ?_ ?_
      hx.1
    · intro h
      rw [e7]
      exact htab _ z _ _ (cells_stay N p l 7 (⟨b, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) x y τ hout).symm h
    · intro h
      rw [e7]
      exact hshape _ z h
  · exact pins7_back cs G arr smp₂ ms decT₂ N Mg (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l
      (⟨b, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      (fun x τ y _ hout q _ => by rw [hsm' x τ y hout])
      (hB' .oU (open7_pin split _ (Or.inl rfl))) (hB' .oOmega (open7_pin split _ (Or.inr rfl)))
  · intro x τ y w i hx hout _ ho hi hm
    exact frames_of_pins cs G arr smp₂ ms decT₂ N Mg p l split 7 (⟨b, base, [d], [], ex, er⟩ :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
      (onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l 7) hB'
      (fun x τ y _ hout q _ => by rw [hsm' x τ y hout]) hother x τ y w i hx hout ho hi hm

end Desc.K14.Law
