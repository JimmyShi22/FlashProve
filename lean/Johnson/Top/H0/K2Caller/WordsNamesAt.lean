-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/WordsNamesAt.lean: the code switch (the kind K2): THE PREMISES hF AND h0 OF
`rowsHoldT_of_says` (Johnson/Top/H0/K2Caller/RowsSay.lean), IN ITS OWN BINDERS, at the words
`wordsFirst` (Johnson/Desc/Sound/WordsAt.lean) of the state behind and at inside := `Inside`
(Johnson/Top/H0/K2Hands/HandsOn.lean); and that theorem called with the two laid in. Theorems with
their proofs, over WordsNames.lean.

Main names:
  `newNumbers_atSwitch`: `NewNumbers` from the structure `AtSwitch`
    (Johnson/Top/H0/K2Hands/Paid.lean) and the two facts on numbers that `six_paid`
    (Johnson/Top/H0/K2Hands/AtYes.lean) makes where the kind's text accepts.
  `words_zero_atSwitch`: h0 from `AtSwitch`, these two facts, `ShapesAt` and `CodesFit`.
  `check_codes`, `codesFit_atSwitch`: `CodesFit` at g and at the messages that take the kept
    members, where the program's test on the target and the test on the codes' lengths pass.
  `words_at_accept`: hF AND h0 WHERE THE KIND's OWN TEXT ACCEPTS: from `AtYes`, `AtSwitch`,
    `ShapesAt`, `KeptPos` and the test on the codes' lengths.
  `hF_at`, `h0_at`: the two premises to the letter.
  `rowsHoldT_of_words`: `rowsHoldT_of_says` with hF and h0 paid: hm and hrow stay.
Limits. `AtSwitch`, `ShapesAt` (to be shown by `yes_new_shape`,
Johnson/Top/H0/Tw/K2C/NewAtYes.lean, and `K2.yes_codes`, Johnson/Top/H0/Tw/K2C/KeepsWhole.lean),
`KeptPos`, the test on the lengths (asked of the first chain's codes by `pubBy`,
Johnson/Desc/ProofFile/Pub.lean, and `startOk`, Johnson/Desc/First/State.lean), hm and hrow are
premises: nobody shows them here. Nothing on
soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WordsNames
import Johnson.Top.H0.K2Caller.RowsSay
import Johnson.Top.H0.K2Hands.AtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open OnBytes.Means (Words Says wordsOn)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.First.K2Hands

/-! ## 1 From the structure AtSwitch -/

section
variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : ℕ} {anew : Array ℕ}
  {W : SwitchFrame} {l : List (OracleShape × ℕ)} {s : Sg} {Kp : Type} [Fintype Kp]
  [DecidableEq Kp] {mem row : Kp → ℕ} {pl : Kp → KeptPlace} {n0 : ℕ}

omit [Fintype Kp] [DecidableEq Kp] in
/-- **g and the messages that take the kept members are messages of the new sending.** hg, hk: what
`six_paid` makes where the kind's text accepts. -/
theorem newNumbers_atSwitch {ids : ℕ → ℕ} (A : AtSwitch S old T g anew W l s Kp mem row pl ids)
    (hg : W.g = n0) (hk : ∀ (a : ℕ) (k : KeptPlace), W.kept[a]? = some k → k.anew = n0 + (1 + a)) :
    NewNumbers l n0 W where
  g := by
    obtain ⟨g0, -⟩ := A.first
    exact ⟨⟨0, g0⟩, hg⟩
  kept := fun k hk' => by
    obtain ⟨a, ha⟩ := List.getElem?_of_mem hk'
    obtain ⟨hi, -⟩ := kept_rec S old T g anew W A.frame a k ha
    have h2 : a < T.kept.size := by
      rw [(check_facts A.check).2.2.2.2.2.2.1]
      exact hi
    obtain ⟨h, -⟩ := A.next a h2
    exact ⟨⟨1 + a, h⟩, hk a k ha⟩

/-- **(h0) from the structure AtSwitch.** S: the statement in which the rows are made; st: the
statement at which the words are read (behind the switch: it has S's tables). -/
theorem words_zero_atSwitch {K : Type} [CommRing K]
    (A : AtSwitch S old T g anew W l s Kp mem row pl (fun i => n0 + i)) (hg : W.g = n0)
    (hk : ∀ (a : ℕ) (k : KeptPlace), W.kept[a]? = some k → k.anew = n0 + (1 + a))
    {st : Statement} (N : ShapesAt S.codes l n0 st) (C : CodesFit S.codes l (Taken l n0 W))
    (Tb : ℕ → Bool → ℕ → ℕ → K) :
    ∀ x ∈ tabAll st, ¬ Inside s W pl x.1 x.2.1 x.2.2 → wordsOn st Tb x.1 x.2.1 x.2.2 = 0 :=
  words_zero_outside N C (newNumbers_atSwitch A hg hk) (paid_names A) (paid_namesK A) A.slots
    (paid_slots A) Tb

end

/-! ## 2 Where the kind's own text accepts -/

section
open VerifiableInference.Desc.First.K2
open _root_.Tw.K2 (switchNotices)

/-- Where the program's test on the target passes: what that says of the codes of g's shape and of
the shapes that take the kept members. -/
theorem check_codes {S : Statement} {old : SingleRows} {T : SwitchTarget}
    (h : switchTargetCheck S old T = true) :
    T.shape.code < S.codes.base.size ∧
      (0 < T.shape.maskRows → T.shape.maskCode < S.codes.mask.size) ∧
      ∀ a (ha : a < T.kept.size),
        T.kept[a].shape.maskRows = 0 ∧ T.kept[a].shape.code < S.codes.base.size := by
  have hks := (check_facts h).2.2.2.2.2.2.1
  unfold switchTargetCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hcode⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hb⟩, _⟩, _⟩, _⟩, _⟩,
    hall⟩ := h
  refine ⟨hcode, fun hp => ?_, fun a ha => ?_⟩
  · cases hp' : T.rest.part with
    | mask =>
      rw [hp'] at hb
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      exact hb.1.1.1.1
    | main =>
      rw [hp'] at hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      have h0 := hb.1.1.1
      omega
  · rw [Array.all_eq_true] at hall
    have hz : a < ((switchKept old).zip T.kept).size := by
      rw [Array.size_zip]
      omega
    have hi := hall a hz
    rw [Array.getElem_zip] at hi
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
    exact ⟨hi.1.1.1.1.1.1.2, hi.1.1.1.1.1.2⟩

/-- **`CodesFit` at g and at the messages that take the kept members**, from the structure
AtSwitch (its clause "check": the program's test on the target passes), the two facts on numbers,
and the test on the codes' lengths. -/
theorem codesFit_atSwitch {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : ℕ}
    {anew : Array ℕ} {W : SwitchFrame} {l : List (OracleShape × ℕ)} {s : Sg} {Kp : Type}
    {mem row : Kp → ℕ} {pl : Kp → KeptPlace} {ids : ℕ → ℕ} {n0 : ℕ}
    (A : AtSwitch S old T g anew W l s Kp mem row pl ids) (hg : W.g = n0)
    (hk : ∀ (a : ℕ) (k : KeptPlace), W.kept[a]? = some k → k.anew = n0 + (1 + a))
    (hL : S.codes.lengthsOk = true) : CodesFit S.codes l (Taken l n0 W) := by
  obtain ⟨hcode, gmask, kept⟩ := check_codes A.check
  have shapeOf : ∀ i : Fin l.length, Taken l n0 W i → (l.get i).1 = T.shape ∨
      ∃ a, ∃ ha : a < T.kept.size, (l.get i).1 = T.kept[a].shape := by
    rintro ⟨i, hi⟩ (h | ⟨k, hk', h⟩)
    · obtain ⟨g0, e⟩ := A.first
      have h' : n0 + i = W.g := h
      obtain rfl : i = 0 := by omega
      exact Or.inl e
    · obtain ⟨a, ha⟩ := List.getElem?_of_mem hk'
      obtain ⟨hi', -⟩ := kept_rec S old T g anew W A.frame a k ha
      have h2 : a < T.kept.size := by
        rw [(check_facts A.check).2.2.2.2.2.2.1]
        exact hi'
      obtain ⟨h3, e⟩ := A.next a h2
      have h' : n0 + i = k.anew := h
      rw [hk a k ha] at h'
      obtain rfl : i = 1 + a := by omega
      exact Or.inr ⟨a, h2, e⟩
  refine ⟨hL, fun i hi _ => ?_, fun i hi hp => ?_⟩
  · rcases shapeOf i hi with e | ⟨a, ha, e⟩
    · rw [e]
      exact hcode
    · rw [e]
      exact (kept a ha).2
  · rcases shapeOf i hi with e | ⟨a, ha, e⟩
    · rw [e] at hp ⊢
      exact gmask hp
    · rw [e, (kept a ha).1] at hp
      exact absurd hp (Nat.lt_irrefl 0)

/-- **(hF) AND (h0) WHERE THE KIND's OWN TEXT ACCEPTS**: from all that this gives (`AtYes`,
Johnson/Top/H0/K2Hears/Whole.lean), the structure `AtSwitch` there, `ShapesAt` behind, `KeptPos`,
and the test on the codes' lengths. -/
theorem words_at_accept {K : Type} [CommRing K] {p : K2.P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c) {W : SwitchFrame}
    {l : List (OracleShape × ℕ)} {sg : Sg} {Kp : Type} [Fintype Kp] [DecidableEq Kp]
    {mem row : Kp → ℕ} {pl : Kp → KeptPlace}
    (A : AtSwitch S3 fx.f.rows fx.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + fx.T.kept.size)) W l
      sg Kp mem row pl (fun i => fx.st.oracles.size + i))
    (N : ShapesAt S3.codes l fx.st.oracles.size s'.st)
    (hp : K2.KeptPos fx.T) (hL : fx.st.codes.lengthsOk = true) (Tb : ℕ → Bool → ℕ → ℕ → K) :
    (∀ n, nameOf S3.codes l (fun i => fx.st.oracles.size + i) n ∈ tabAll s'.st) ∧
      ∀ x ∈ tabAll s'.st, ¬ Inside sg W pl x.1 x.2.1 x.2.2 →
        wordsOn s'.st Tb x.1 x.2.1 x.2.2 = 0 := by
  obtain ⟨-, -, hg, hk⟩ := K2.six_paid Y1.sent Y1.same (K2.keptOld_of Y1.check hp) Y1.check A.frame
  have hc3 : S3.codes = fx.st.codes := Y1.same.codes.trans Y1.sent.codes
  exact ⟨fun n => name_in_tables N n, words_zero_atSwitch A hg hk N
    (codesFit_atSwitch A hg hk (by rw [hc3]; exact hL)) Tb⟩

end

/-! ## 3 In the binders of rowsHoldT_of_says -/

section
variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) (p : K2.P2)

/-- **hF, to the letter.** -/
theorem hF_at (s s' : Rec)
    (hN : ∀ fx, K2.frontAt p s = some fx → ShapesAt cs l fx.st.oracles.size s'.st) :
    ∀ fx, K2.frontAt p s = some fx →
      ∀ n, nameOf cs l (fun i => fx.st.oracles.size + i) n ∈ tabAll s'.st :=
  fun fx h n => name_in_tables (hN fx h) n

/-- What h0 takes at the front fx. -/
structure ZeroAsks (W : SwitchFrame) (mem row : R.Kp → ℕ) (pl : R.Kp → KeptPlace) (n0 : ℕ)
    (st : Statement) : Prop where
  shapes : ShapesAt cs l n0 st
  codes : CodesFit cs l (Taken l n0 W)
  numbers : NewNumbers l n0 W
  names : ∃ aMain aM0 aT0 aM1 aT1,
    Names R.s R.Kp cs l iJ iQ W (fun i => n0 + i) aMain aM0 aT0 aM1 aT1
  namesK : ∃ aKept, NamesK R.s R.Kp cs l iJ iQ W (fun i => n0 + i) mem row pl aKept
  slots : ∀ a k, W.kept[a]? = some k → Slots R.s R.Kp cs l W (fun i => n0 + i) mem row a k

omit [Nonempty R.G.P] in
/-- **h0, to the letter**: at m := the words that the witness w gives through the statement and the
book behind, and inside := `Inside R.s W pl`. -/
theorem h0_at (s' : Rec) {W : SwitchFrame} {mem row : R.Kp → ℕ} {pl : R.Kp → KeptPlace} {n0 : ℕ}
    (Q : ZeroAsks R cs l iJ iQ W mem row pl n0 s'.st) (A : SlotsAll R.Kp W mem row pl)
    {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
    (w : Wit Cells Tok MsgT) :
    ∀ x ∈ tabAll s'.st, ¬ Inside R.s W pl x.1 x.2.1 x.2.2 →
      wordsFirst arr s'.st s'.book w x.1 x.2.1 x.2.2 = 0 := by
  obtain ⟨aMain, aM0, aT0, aM1, aT1, D⟩ := Q.names
  obtain ⟨aKept, DK⟩ := Q.namesK
  exact words_zero_first Q.shapes Q.codes Q.numbers D DK A Q.slots arr s'.book w

/-- **`rowsHoldT_of_says` WITH hF AND h0 PAID**: at the words that the witness gives through the
statement and the book behind. hm and hrow are its own, to the letter. -/
theorem rowsHoldT_of_words (s s' : Rec) (u : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Msg)
    {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (w : Wit Cells Tok MsgT) {W : SwitchFrame}
    {mem row : R.Kp → ℕ} {pl : R.Kp → KeptPlace}
    (hm : ∀ fx, K2.frontAt p s = some fx → ∀ n : (sigOf cs l).Ent,
      (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.ents u
          (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n) =
        wordsFirst arr s'.st s'.book w (fx.st.oracles.size + (entAt cs l n).1) (entAt cs l n).2.1
          (entAt cs l n).2.2)
    (hrow : ∀ fx, K2.frontAt p s = some fx → ∀ G0 G', fx.st.groups[fx.f.group]? = some G0 →
      s'.st.groups[fx.f.group]? = some G' → ∀ r ∈ G'.rows.toList.drop G0.rows.size,
        Says rdE s'.st r (wordsFirst arr s'.st s'.book w) ∧
          OnlyAt cs l (fun i => fx.st.oracles.size + i) (Inside R.s W pl) r)
    (Q : ∀ fx, K2.frontAt p s = some fx →
      ZeroAsks R cs l iJ iQ W mem row pl fx.st.oracles.size s'.st)
    (A : SlotsAll R.Kp W mem row pl) :
    RowsHoldT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p s s' u := by
  cases hf : K2.frontAt p s with
  | none =>
    intro fx hfx
    rw [hf] at hfx
    cases hfx
  | some fx0 =>
    exact rowsHoldT_of_says R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p s s' u
      (wordsFirst arr s'.st s'.book w) hm hrow
      (hF_at cs l p s s' fun fx h => (Q fx h).shapes)
      (h0_at R cs l iJ iQ s' (Q fx0 hf) A arr w)

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.newNumbers_atSwitch
#print axioms VerifiableInference.Desc.First.K2Caller.words_zero_atSwitch
#print axioms VerifiableInference.Desc.First.K2Caller.check_codes
#print axioms VerifiableInference.Desc.First.K2Caller.codesFit_atSwitch
#print axioms VerifiableInference.Desc.First.K2Caller.words_at_accept
#print axioms VerifiableInference.Desc.First.K2Caller.hF_at
#print axioms VerifiableInference.Desc.First.K2Caller.h0_at
#print axioms VerifiableInference.Desc.First.K2Caller.rowsHoldT_of_words
