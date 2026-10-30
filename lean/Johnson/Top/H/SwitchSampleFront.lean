-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchSampleFront.lean: the clause "sample" of the record `FrontAt`
(Johnson/Top/H0/K2Hands/TiePaid.lean), at the caller of the kept messages, from
`sample_clause_held` (Johnson/Top/H/SwitchSampleAt.lean): the last call.

`FrontAt` holds what the join of the code switch's typed chain to its written text asks of the
statement in front: sixteen clauses, all premises there. Its last clause, "sample", asks of every
held old sample: a kept member's record in the frame, a stored sample row, the member's slots, the
typed answer as the row's target, and the typed sample row, carried to the open word's entries, as
the vector of the stored row's form. `sample_clause_held` ends at a statement of that shape, typed
beside the record, not against it. Here that end fills the record's own field: so that the two
shapes are one is held by Lean. Statements and proofs; no new reasoning.
Main names (namespace `VerifiableInference.Desc.First.K2Hands`, the record's own):
  `front_sample_held`: the clause, in `FrontAt`'s own words, at R := the group's rows with the kept
    members, Hd := `heldPort`, the two maps of names `iJ`, `iQ` of a frame W with `Fit`, aOf := a
    held message's member's number, iOf := 0 (one answer), the statement and the new messages'
    numbers of a front fx: from `sample_clause_held`'s seven premises at St := fx.st.
  `frontAt_of_rest`: `FrontAt` there, from its other fifteen clauses, word for word, and these
    seven: so Lean holds `front_sample_held`'s end against the record's own field.
Limits: the other fifteen clauses stay premises. The seven are those of SwitchSampleAt.lean: among
them that a kept message has one answer, and that its stored sample row is the program's row at a
seed that the typed sample reads: shown at no run (at the written records of the two examples, at
values made there of the record: `sample_member_full`, `sample_member_small`,
Johnson/G/SwitchSampleMember.lean). No member of `FrontAt` is named. Nothing on soundness.

-/
import Johnson.Top.H.SwitchSampleAt
import Johnson.Top.H0.K2Hands.TiePaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch

variable (cs : Codes) (l : List (OracleShape × ℕ)) (mem : Fin l.length → Prop)
  [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (l.get a.1).1.mainRows ≠ 0) (h0 : ∀ a, kp a → (l.get a.1).1.maskRows = 0)
  (kq : Fin l.length → Prop) (num : {a // kp a} → ℕ)
  [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsPort cs l mem s e oM oZ hM hZ).G.C.J)
  (Z : Evader GE ((rowsPort cs l mem s e oM oZ hM hZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs l).sub kq).Msg × Wp))
  (cs' : Codes) (l' : List (OracleShape × ℕ)) (W : SwitchFrame) (plOf : {a // kp a} → KeptPlace)
  (Ft : Fit cs' l' s W (slotNum cs l mem s e oM oZ hM hZ kp num)
    (slotRow cs l mem s e oM oZ hM hZ kp) (slotPl cs l mem s e oM oZ hM hZ kp plOf))
  (t : ℕ)
  (w₀ : ((heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "hP" => heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq
set_option quotPrecheck false in
local notation:max "aK " k:max => (⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩ : {a // kp a})
set_option quotPrecheck false in
local notation "jW" => iJ s W (slotNum cs l mem s e oM oZ hM hZ kp num)
  (slotRow cs l mem s e oM oZ hM hZ kp) (slotPl cs l mem s e oM oZ hM hZ kp plOf) cs' l' Ft.nameJ
set_option quotPrecheck false in
local notation "qW" => iQ s W (slotNum cs l mem s e oM oZ hM hZ kp num)
  (slotRow cs l mem s e oM oZ hM hZ kp) cs' l' Ft.nameQ
set_option quotPrecheck false in
local notation "locK" => (closeSel (hP) Sb sl Z A₀ cs' l' (jW) (qW) t w₀).loc

/-- **The clause "sample" of `FrontAt` at the caller of the kept messages.** -/
theorem front_sample_held (fx : _root_.Tw.K2.Front) (xc : (locK).Xc × (locK).hd.Smp)
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (hmem : ∀ a, W.kept[num a]? = some (plOf a))
    (hrb : ∀ a : {a // kp a}, (plOf a).rowBits = k1 (l.get a.1.1).1)
    (hSl : ∀ a, Slots s ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp cs' l' W
      (fun i => fx.st.oracles.size + i)
      (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp) (num a)
      (plOf a))
    (ha : ∀ a : {a // kp a}, (l.get a.1.1).1.answers = 1)
    (hc : ∀ a : {a // kp a}, CaseE (l.get a.1.1).1 ∨ CaseF (l.get a.1.1).1)
    (hst : ∀ k : {a // (hP).cl a}, ∃ (seed : SampleSeed) (row : OnBytes.Row) (y : E) (β : GEˣ),
      Send.form cs (l.get k.1.1).1 (plOf (aK k)).old seed 0 = some row ∧
      (samplesOf fx.st (plOf (aK k)))[0]? = some { row with target := y } ∧
      bitsZ cs (l.get k.1.1).1 ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      (xc.2 k).1 = (readP (bitsZ cs (l.get k.1.1).1) seed.z, β) ∧ (xc.2 k).2 () = readE y) :
    ∀ ks : Σ k, ((locK).hd.o k).Z.S, ∃ (k : KeptPlace) (smp : OnBytes.Row),
      W.kept[num (aK ks.1)]? = some k ∧ (samplesOf fx.st k)[0]? = some smp ∧
        Slots s ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp cs' l' W
          (fun i => fx.st.oracles.size + i) (slotNum cs l mem s e oM oZ hM hZ kp num)
          (slotRow cs l mem s e oM oZ hM hZ kp) (num (aK ks.1)) k ∧
        (xc.2 ks.1).2 ks.2 = readE smp.target ∧
        pushTo ((locK).hd.sJ ks.1) (((locK).hd.o ks.1).Z.mat (xc.2 ks.1).1 ks.2) =
          slotVec s ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp
            (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
            (num (aK ks.1)) k.rowBits (formOn smp) :=
  sample_clause_held cs l mem s e oM oZ hM hZ kp h1 h0 kq num Sb sl Z A₀ cs' l' W plOf Ft t w₀
    fx.st (fun i => fx.st.oracles.size + i) xc.2 inj hmem hrb hSl ha hc hst

set_option quotPrecheck false in
local notation "RK" => (rowsPort cs l mem s e oM oZ hM hZ).keep kp

/-- **`FrontAt` at the caller of the kept messages, from its other fifteen clauses and the seven
premises on the old samples.** -/
theorem frontAt_of_rest (p : K2.P2) (sR : Rec) (orc : ℕ → ℕ → List UInt64)
    (fx : _root_.Tw.K2.Front) (xc : (locK).Xc × (locK).hd.Smp) (str : (locK).C.ext.Str)
    (frameIs : K2.frameAt fx = some W) (z32 : W.zk.logN ≤ 32)
    (twoOld : ∀ (a a' : ℕ) (k k' : KeptPlace), W.kept[a]? = some k → W.kept[a']? = some k' →
      k.old = k'.old → a = a')
    (codes : fx.st.codes = cs') (keptPos : K2.KeptPos fx.T)
    (keptRows : fx.f.rows.keptRows = (W.kept.map (·.rows)).sum)
    (ell : ∀ (a : ℕ) (k : KeptPlace), W.kept[a]? = some k →
      (fx.st.codes.base.getD (fx.st.oracles.getD k.old default).shape.code default).ell =
        W.code.ell)
    (first : ∃ g0 : 0 < l'.length, (l'.get ⟨0, g0⟩).1 = fx.T.shape)
    (next : ∀ i (hi : i < fx.T.kept.size), ∃ h : 1 + i < l'.length,
      (l'.get ⟨1 + i, h⟩).1 = fx.T.kept[i].shape)
    (mainVars : ∀ v ∈ fx.f.rows.c.tensors, v.vars = W.code.logEll)
    (d0 : (fx.f.rows.d.getD 0 #[]).size ≤ W.zk.ell)
    (d1 : (fx.f.rows.d.getD 1 #[]).size ≤ W.zk.ell)
    (strIs : StrIs (RK) (hP) Sb sl Z A₀ cs' l' (jW) (qW) t w₀ p sR fx orc
      (coordOf (RK).s (RK).Kp W fx.f.rows (slotNum cs l mem s e oM oZ hM hZ kp num)
        (slotRow cs l mem s e oM oZ hM hZ kp)) str)
    (target : xc.1.1 = readE fx.f.rows.target)
    (vector : xc.1.2 = vecOf (RK).s (RK).Kp fx.f.rows (slotRow cs l mem s e oM oZ hM hZ kp)
      (slotPl cs l mem s e oM oZ hM hZ kp plOf))
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (hmem : ∀ a, W.kept[num a]? = some (plOf a))
    (hrb : ∀ a : {a // kp a}, (plOf a).rowBits = k1 (l.get a.1.1).1)
    (hSl : ∀ a, Slots s ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp cs' l' W
      (fun i => fx.st.oracles.size + i)
      (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp) (num a)
      (plOf a))
    (ha : ∀ a : {a // kp a}, (l.get a.1.1).1.answers = 1)
    (hc : ∀ a : {a // kp a}, CaseE (l.get a.1.1).1 ∨ CaseF (l.get a.1.1).1)
    (hst : ∀ k : {a // (hP).cl a}, ∃ (seed : SampleSeed) (row : OnBytes.Row) (y : E) (β : GEˣ),
      Send.form cs (l.get k.1.1).1 (plOf (aK k)).old seed 0 = some row ∧
      (samplesOf fx.st (plOf (aK k)))[0]? = some { row with target := y } ∧
      bitsZ cs (l.get k.1.1).1 ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      (xc.2 k).1 = (readP (bitsZ cs (l.get k.1.1).1) seed.z, β) ∧ (xc.2 k).2 () = readE y) :
    FrontAt (RK) (hP) Sb sl Z A₀ cs' l' (jW) (qW) t w₀ W p
      (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
      (slotPl cs l mem s e oM oZ hM hZ kp plOf) (fun k => num (aK k)) (fun _ _ => 0) sR orc xc str
      fx :=
  ⟨frameIs, z32, twoOld, codes, keptPos, keptRows, ell, first, next, mainVars, d0, d1, strIs,
    target, vector,
    front_sample_held cs l mem s e oM oZ hM hZ kp h1 h0 kq num Sb sl Z A₀ cs' l' W plOf Ft t w₀ fx
      xc inj hmem hrb hSl ha hc hst⟩

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.front_sample_held
#print axioms VerifiableInference.Desc.First.K2Hands.frontAt_of_rest
