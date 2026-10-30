-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSplitFilled.lean: THE JOININGS AND "SPLIT" AT THE LEDGER OF A PROOF
FILE's SHARED CHAIN (blocks 6 and 8; two codes), AT THE TABLE's FILES' FILLING OF THE PINS, THE
PROMISE AND THE EXTRACTOR (Johnson/Desc/Sound/BordersSharedFill.lean) AND WITH THIS KIND's LETTERS
FILLED as
Johnson/Desc/K14/Law/ShapesSend.lean fills them: row (fold) := FoldAt · row (fold_u) := the one row
number cU on G_u · row (fold_omega) := the one row number cO on G_omega · shape 6, 7, 8 := shapeO at
the counts cU, cO · shape 9 := shapeO at cU + 1, cO + 1. JOININGS: by split_core
(Johnson/Desc/K14/Law/ShapesOmega.lean), the tools of Johnson/Desc/Sound/LedgerRides.lean and
clause_of_own | empty_clause.

  sub6, nl6, sub8, nl8, lays6, lays8   the table, evaluated at the two blocks.
  open8_pin       o_sp's pin is open at border 8.
  joins_filled    **the clause at block 6.**
  split_filled    **the clause at block 8.**
WHAT IS LEFT, AND WHOSE. By make: hj | hb (the wrap). Numbers of the plan and the tiling: hB, hB'.
THE TABLE's FILES' LETTERS: a yes of the block leaves the samples (hsm) and the stored table's
promise (htab). hother: the shared items that are no pins and that the
row does not name ride back (the rows as they lie: rowsU_back; the samples' rows:
the sending kind's files). The equations of letters: rfl where the letters are so filled.
What is not claimed. NO MEMBER: no letters and statement are shown at which all premises hold
together. A block that refuses all meets the clause. Nothing at one code. No soundness of a
verifier.

-/
import Johnson.Desc.K14.Law.LedgerZetaFilled
import Johnson.Desc.K14.Law.LedgerSplit
import Johnson.Desc.K14.Law.LedgerJoins

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription smpHeld)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

theorem sub6 (split : Bool) (m : Msg2) (h : PromS.noColl m ∈ promsAt split 7) :
    PromS.noColl m ∈ promsAt split 6 := by
  revert h
  cases split <;> cases m <;> decide

theorem nl6 (split : Bool) : PromS.nothingLeft ∉ promsAt split 7 := by cases split <;> decide

theorem sub8 (m : Msg2) (h : PromS.noColl m ∈ promsAt true 9) :
    PromS.noColl m ∈ promsAt true 8 := by
  revert h
  cases m <;> decide

theorem nl8 : PromS.nothingLeft ∉ promsAt true 9 := by decide

theorem lays6 (split : Bool) : laysAtS split 6 = [] := by cases split <;> rfl

theorem lays8 : laysAtS true 8 = [] := rfl

/-- o_sp's pin is open at border 8. -/
theorem open8_pin : openSh true 8 (.pin .oSp) := (openSh_iff true 8 _).2 (by decide)

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells)
  (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook)
  (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
  (Oc : P₁ → Strs → Prop)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- **The joinings at the ledger, the letters filled.** -/
theorem joins_filled (split : Bool) (P : Par) (nU nO cU cO : ℕ)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (ε : Err (uLT (ckP .two) x.ds))
    (hj : ∀ t rs gs t', x.b.decide t rs gs = .ok t' → joins P t.2 rs = some t'.2)
    (hB : ∀ m, PromS.noColl m ∈ promsAt split 7 → SentBefore N p l 6 x m)
    (hB' : ∀ m, openSh split 6 (.pin m) → SentBefore N p l 6 x m)
    (hsm : ∀ a τ b, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l 6 a →
      x.ior.red.out a τ = some b → smp₂ b.1.2 = smp₂ a.1.2)
    (htab : ∀ a τ b, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l 6 a →
      x.ior.red.out a τ = some b →
      Pm.tablePromise a.1.2 (strsOfAct Fr ((actQ N p l 6).2 a)) →
      Pm.tablePromise b.1.2 (strsOfAct Fr ((actQ N p l 7).2 b)))
    (hother : ∀ a τ b w i, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l 6 a →
      x.ior.red.out a τ = some b → openSh split 6 i → ¬ insSh split 6 i → (∀ m, i ≠ .pin m) →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i 7 ((actQ N p l 7).2 b) w →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i 6 ((actQ N p l 6).2 a) w)
    (hS6 : Pm.shape 6 = shapeO P nU nO cU cO) (hS7 : Pm.shape 7 = shapeO P nU nO cU cO) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ Mg) (promSigS cs G smp₂ ms stOf bookOf Pm) Oc
      split p l
      (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N split k v.1 (strsOfAct Fr v) w) 6 x ε := by
  refine joins_clause N (meaningSigS cs G arr smp₂ ms decT₂ Mg)
    (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l _ x ε
    (fun v w => extS_id cs G arr smp₂ ms decT₂ c₀ N split 6 (lays6 split) v.1 (strsOfAct Fr v) w)
    ?_ ?_
  · intro a τ b ha hout
    refine prom_rides cs G smp₂ ms stOf bookOf N Pm p l split 6 x (sub6 split) (nl6 split) hB a b τ
      hout (fun q _ => by rw [hsm a τ b ha hout]) (htab a τ b ha hout) ?_ ha.1
    intro h
    obtain ⟨_, gs, hd⟩ := piece_yes x a τ b hout
    rw [hS6] at h
    rw [hS7]
    exact shapeO_joins P nU nO cU cO a.1.2 b.1.2 _ (hj _ _ _ _ hd) h
  · intro a τ b w i ha hout ho hm
    exact frames_of_pins cs G arr smp₂ ms decT₂ N Mg p l split 6 x
      (onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc split p l 6) hB'
      (fun a τ b ha hout q _ => by rw [hsm a τ b ha hout]) hother a τ b w i ha hout ho
      (ins6 split i) hm

/-- **"SPLIT" at the ledger, the letters filled.** -/
theorem split_filled (P : Par) (rg : Wit Cells Tok MsgT → Words GE) (nU nO cU cO : ℕ)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (ε : Err (uLT (ckP .two) x.ds))
    (hb : ∀ t rs gs t', x.b.decide t rs gs = .ok t' → split P t.2 rs = some t'.2)
    (hB : ∀ m, PromS.noColl m ∈ promsAt true 9 → SentBefore N p l 8 x m)
    (hB' : ∀ m, openSh true 8 (.pin m) → SentBefore N p l 8 x m)
    (hsm : ∀ a τ b, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 8 a →
      x.ior.red.out a τ = some b → smp₂ b.1.2 = smp₂ a.1.2)
    (htab : ∀ a τ b, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 8 a →
      x.ior.red.out a τ = some b →
      Pm.tablePromise a.1.2 (strsOfAct Fr ((actQ N p l 8).2 a)) →
      Pm.tablePromise b.1.2 (strsOfAct Fr ((actQ N p l 9).2 b)))
    (hother : ∀ a τ b w i, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 8 a →
      x.ior.red.out a τ = some b → openSh true 8 i → ¬ insSh true 8 i → (∀ m, i ≠ .pin m) →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i 9 ((actQ N p l 9).2 b) w →
      muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l i 8 ((actQ N p l 8).2 a) w)
    (hrF : Mg.row .fold = fun s w => FoldAt OnBytes.Model.Reading.gl P.S s (rg w))
    (hrU : Mg.row .foldU = fun s w => RowsU OnBytes.Model.Reading.gl cU 1 s (rg w))
    (hrO : Mg.row .foldOmega = fun s w => RowsO OnBytes.Model.Reading.gl cO 1 s (rg w))
    (hS8 : Pm.shape 8 = shapeO P nU nO cU cO)
    (hS9 : Pm.shape 9 = shapeO P nU nO (cU + 1) (cO + 1)) :
    ClauseAt N (meaningSigS cs G arr smp₂ ms decT₂ Mg) (promSigS cs G smp₂ ms stOf bookOf Pm) Oc
      true p l
      (fun k v w => extS cs G arr smp₂ ms decT₂ c₀ N true k v.1 (strsOfAct Fr v) w) 8 x ε := by
  have hid : ∀ (v : (actQ N p l 8).1) (w : Wit Cells Tok MsgT),
      extS cs G arr smp₂ ms decT₂ c₀ N true 8 v.1 (strsOfAct Fr v) w = w := fun v w =>
    extS_id cs G arr smp₂ ms decT₂ c₀ N true 8 lays8 v.1 (strsOfAct Fr v) w
  have hsh : ∀ a, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 8 a →
      shapeO P nU nO cU cO a.1.2 = true := by
    intro a ha
    have h1 : Pm.shape 8 a.1.2 = true := ha.1 (.shape 8) (by simp [promsAt])
    rw [hS8] at h1
    exact h1
  have hprom : ∀ a τ b, onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 8 a →
      x.ior.red.out a τ = some b →
      promQ N (promSigS cs G smp₂ ms stOf bookOf Pm) true p l 9 ((actQ N p l 9).2 b) := by
    intro a τ b ha hout
    refine prom_rides cs G smp₂ ms stOf bookOf N Pm p l true 8 x sub8 nl8 hB a b τ hout
      (fun q _ => by rw [hsm a τ b ha hout]) (htab a τ b ha hout) ?_ ha.1
    intro _
    obtain ⟨_, gs, hd⟩ := piece_yes x a τ b hout
    have k8 := hb _ _ _ _ hd
    have hS := ((shapeO_iff P nU nO cU cO a.1.2).1 (hsh a ha)).2.2.2.2.2
    obtain ⟨r8, hr⟩ := split_one _ _ _ _ hS k8
    rw [hr] at k8
    rw [hS9]
    exact shapeO_split P nU nO cU cO a.1.2 b.1.2 r8 k8 (hsh a ha)
  refine clause_of_own N (meaningSigS cs G arr smp₂ ms decT₂ Mg)
    (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l _ 8 x ε ?_ ?_
  · refine goodIn_conseq _ _ _ _ _ _ _
      (split_core OnBytes.Model.Reading.gl rg (Prod.snd : P₁ × St → St)
        ({ x with
          ext := fun a _ w => extS cs G arr smp₂ ms decT₂ c₀ N true 8 ((actQ N p l 8).2 a).1
            (strsOfAct Fr ((actQ N p l 8).2 a)) w
          err := ε } : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) P hb
        (fun a _ w => hid _ w) (onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 8)
        (fun b => promQ N (promSigS cs G smp₂ ms stOf bookOf Pm) true p l 9 ((actQ N p l 9).2 b))
        (fun a w => muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin .oSp) 8
          ((actQ N p l 8).2 a) w)
        (fun b w => muQ N (meaningSigS cs G arr smp₂ ms decT₂ Mg) p l (.pin .oSp) 9
          ((actQ N p l 9).2 b) w)
        (fun a ha => by
          obtain ⟨h1, h2, h3⟩ := seated_of_shapeO P nU nO cU cO a.1.2 (hsh a ha)
          exact onSplit_of_seated (F := Fr) P (a.1.2, a.2) h3 _ h1 h2)
        cU cO
        (fun a ha => ((shapeU_iff P nU cU a.1.2).1
          ((shapeO_iff P nU nO cU cO a.1.2).1 (hsh a ha)).1).2.2.2)
        (fun a ha => ((shapeO_iff P nU nO cU cO a.1.2).1 (hsh a ha)).2.2.2.2.1) hprom
        (fun a τ b w ha hout h => pin_rides cs G arr smp₂ ms decT₂ N Mg p l 8 x .oSp
          (hB' .oSp open8_pin) a b τ hout (fun q _ => by rw [hsm a τ b ha hout]) w h)) ?_ ?_
    · intro b w _ h
      have h1 : Mg.row .foldU b.1.2 w := h _ ((outs8 _).2 (Or.inl rfl))
      have h2 : Mg.row .foldOmega b.1.2 w := h _ ((outs8 _).2 (Or.inr (Or.inl rfl)))
      rw [hrU] at h1
      rw [hrO] at h2
      exact ⟨h _ ((outs8 _).2 (Or.inr (Or.inr rfl))), h1, h2⟩
    · intro a w _ h i hi
      rcases (ins8 i).1 hi with rfl | rfl
      · show Mg.row .fold a.1.2 w
        rw [hrF]
        exact h.2
      · exact h.1
  · intro a τ b w i ha hout _ ho hi hm
    rw [hid]
    exact frames_of_pins cs G arr smp₂ ms decT₂ N Mg p l true 8 x
      (onQ₂ N (promSigS cs G smp₂ ms stOf bookOf Pm) Oc true p l 8) hB'
      (fun a τ b ha hout q _ => by rw [hsm a τ b ha hout]) hother a τ b w i ha hout ho hi hm

end Desc.K14.Law
