-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/FitAt.lean: a value of the test on a file's chain queries
(OnBytes/K/Arm/FileInj.lean, `FitJ`) at the data that OnBytes/Maker/Page/Fill.lean lays (`fillJ`),
and that the laws `LawsJ` hold there, if the data of the three silent rounds meet laws of their own.

Definitions that compute where the read-back does, statements and proofs. OnBytes/K/Arm/FileInj.lean
shows that a file's calls are one to one among the typed chain queries that pass a test, under laws
on the file's data; test and laws are letters there. Here they are laid for `fillJ`.

Main names:
  `rootsFit D i rt`: as many roots as the typed round i has items "root"; false where no written
    round stands at i.
  `fitRow`: the plain part is read as the typed round i's, its nonce is below 2^64, the roots fit.
  `frontAt`, `joinAt`, `seamAt`: the plain part is read as the front round's, the joining round's,
    the seam's message, and that message passes a test that is a letter.
  `slotAt`: the plain part is the joining round's part of a slot.
  `fitAt`: the value of `FitJ`.
  `SilentLaws S fF fJ f3`: what is asked of the silent rounds' data.
  `kindsAndWorkBelow256 D`: every written round's kind's number and bits of work are below 256.
  `laws_fill`: `LawsJ (fillJ ..) (fitAt ..) K`.
Premises of `laws_fill`: `SilentLaws`; the test `kindsAndWorkBelow256`; K + 1 < 2^49; the read-back is one to one
where it reads (hrd).
Under "there is" stand, in the tools `fitRow_row`, `frontAt_front`, `joinAt_join`, `seamAt_seam`,
`partAt_some`: what `partAt` or `rd` gives at z, each fixed by its equation.

What is not claimed. That a verifier's queries pass the tests: OnBytes/Maker/Page/FitPass.lean has a
file's own. That data of silent rounds meet `SilentLaws`: OnBytes/Maker/Page/FitSilent.lean. Nothing
on strings, on any hash, on soundness.


-/
import OnBytes.Maker.Page.InjParts
import OnBytes.K.Arm.FileInj

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Joined Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open TypedOracleCompiler.Run.PQ (toRoots)
open OnBytes.K.Arm.FileInj (FitJ LawsJ)

/-- As many roots as the typed round i has items "root"; false where no written round stands at
i. -/
def rootsFit (D : WholeD) (i : ℕ) (rt : List (Dig 256)) : Bool :=
  match rdAt D i with
  | some d => (toRoots d.items rt).isSome
  | none => false

/-- Every written round's kind's number and bits of work are below 256. -/
def kindsAndWorkBelow256 (D : WholeD) : Bool :=
  (D.ds₁ ++ D.ds₂ ++ D.ds₃).all fun d => decide (d.kind.num < 256) && decide (d.entry.work < 256)

theorem rdAt_mem {D : WholeD} {i : ℕ} {d : RDT} (h : rdAt D i = some d) :
    d ∈ D.ds₁ ++ D.ds₂ ++ D.ds₃ := by
  unfold rdAt at h
  split_ifs at h
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? h))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_of_getElem? h))
  · exact List.mem_append_right _ (List.mem_of_getElem? h)

theorem small_at {D : WholeD} (h : kindsAndWorkBelow256 D = true) (i : ℕ) :
    kindAt D i < 256 ∧ workAt D i < 256 := by
  unfold kindAt workAt
  cases hr : rdAt D i with
  | none => exact ⟨by decide, by decide⟩
  | some d =>
    have a := List.all_eq_true.1 h d (rdAt_mem hr)
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at a
    exact a

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3)
  (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))

/-- **The test at a written round.** -/
def fitRow (i : ℕ) (rt : List (Dig 256)) (z : PBt L t) : Bool :=
  match partAt C D tF tJ t3 rd z with
  | .row i' _ n => decide (i' = i) && decide (n < 2 ^ 64) && rootsFit D i rt
  | _ => false

/-- At the first chain's first query. -/
def frontAt (fF : List (Dig 256) → Option X → TF → Bool) (cms : List (Dig 256)) (x : Option X)
    (z : PBt L t) : Bool :=
  match partAt C D tF tJ t3 rd z with
  | .front p => fF cms x p
  | _ => false

/-- At the second chain's first query. -/
def joinAt (fJ : List (Dig 256) → TJ → Bool) (cms : List (Dig 256)) (z : PBt L t) : Bool :=
  match partAt C D tF tJ t3 rd z with
  | .join p => fJ cms p
  | _ => false

/-- At the third chain's first query. -/
def seamAt (f3 : T3 → Bool) (z : PBt L t) : Bool :=
  match partAt C D tF tJ t3 rd z with
  | .seam p => f3 p
  | _ => false

/-- At the slot's query. -/
def slotAt (z : PBt L t) : Bool :=
  match rd z with
  | some w => isSlot C D tF tJ t3 w
  | none => false

/-- **The value of the test.** -/
def fitAt (fF : List (Dig 256) → Option X → TF → Bool) (fJ : List (Dig 256) → TJ → Bool)
    (f3 : T3 → Bool) : FitJ L t where
  row := fitRow C D tF tJ t3 rd
  front := frontAt C D tF tJ t3 rd fF
  join := joinAt C D tF tJ t3 rd fJ
  seam := seamAt C D tF tJ t3 rd f3
  slot := slotAt C D tF tJ t3 rd

/-! ## Tools -/

theorem fitRow_row {i : ℕ} {rt : List (Dig 256)} {z : PBt L t}
    (h : fitRow C D tF tJ t3 rd i rt z = true) :
    ∃ m n, partAt C D tF tJ t3 rd z = .row i m n ∧ n < 2 ^ 64 ∧ rootsFit D i rt = true := by
  unfold fitRow at h
  split at h
  next i' m n hp =>
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, h2⟩, h3⟩ := h
    exact ⟨m, n, hp, h2, h3⟩
  next => cases h

theorem frontAt_front {fF : List (Dig 256) → Option X → TF → Bool} {cms : List (Dig 256)}
    {x : Option X} {z : PBt L t} (h : frontAt C D tF tJ t3 rd fF cms x z = true) :
    ∃ p, partAt C D tF tJ t3 rd z = .front p ∧ fF cms x p = true := by
  unfold frontAt at h
  split at h
  next p hp => exact ⟨p, hp, h⟩
  next => cases h

theorem joinAt_join {fJ : List (Dig 256) → TJ → Bool} {cms : List (Dig 256)} {z : PBt L t}
    (h : joinAt C D tF tJ t3 rd fJ cms z = true) :
    ∃ p, partAt C D tF tJ t3 rd z = .join p ∧ fJ cms p = true := by
  unfold joinAt at h
  split at h
  next p hp => exact ⟨p, hp, h⟩
  next => cases h

theorem seamAt_seam {f3 : T3 → Bool} {z : PBt L t} (h : seamAt C D tF tJ t3 rd f3 z = true) :
    ∃ p, partAt C D tF tJ t3 rd z = .seam p ∧ f3 p = true := by
  unfold seamAt at h
  split at h
  next p hp => exact ⟨p, hp, h⟩
  next => cases h

theorem partAt_some {z : PBt L t} {P : PartJ TF TJ T3} (h : partAt C D tF tJ t3 rd z = P)
    (hn : P ≠ .nothing) : ∃ w, rd z = some w ∧ partOf C D tF tJ t3 w = P := by
  unfold partAt at h
  cases hr : rd z with
  | none =>
    rw [hr] at h
    exact absurd h.symm hn
  | some w =>
    rw [hr] at h
    exact ⟨w, rfl, h⟩

variable (S : SilentJ X TF TJ T3)

theorem fillAt_msg {z : PBt L t} {i : ℕ} {m : List ByteArray → ByteArray} {n : ℕ}
    (hp : partAt C D tF tJ t3 rd z = .row i m n) (rts : List ByteArray) :
    (fillJ C D tF tJ t3 rd S).msg i rts z = m rts := by
  show (match partAt C D tF tJ t3 rd z with
    | .row i' m _ => if i' = i then m rts else ByteArray.empty
    | _ => ByteArray.empty) = _
  rw [hp]
  exact if_pos rfl

theorem fillAt_nonce {z : PBt L t} {i : ℕ} {m : List ByteArray → ByteArray} {n : ℕ}
    (hp : partAt C D tF tJ t3 rd z = .row i m n) : (fillJ C D tF tJ t3 rd S).nonce i z = n := by
  show (match partAt C D tF tJ t3 rd z with
    | .row i' _ n => if i' = i then n else 0
    | _ => 0) = _
  rw [hp]
  exact if_pos rfl

theorem fillAt_stm₁ {z : PBt L t} {p : TF} (hp : partAt C D tF tJ t3 rd z = .front p)
    (cms : List (Dig 256)) (x : Option X) :
    (fillJ C D tF tJ t3 rd S).stm₁ cms x z = S.stm₁ cms x p := by
  show (match partAt C D tF tJ t3 rd z with
    | .front p => S.stm₁ cms x p
    | _ => ByteArray.empty) = _
  rw [hp]

theorem fillAt_stm₂ {z : PBt L t} {p : TJ} (hp : partAt C D tF tJ t3 rd z = .join p)
    (cms : List (Dig 256)) (r : Bits) :
    (fillJ C D tF tJ t3 rd S).stm₂ cms r z = S.stm₂ cms r p := by
  show (match partAt C D tF tJ t3 rd z with
    | .join p => S.stm₂ cms r p
    | _ => ByteArray.empty) = _
  rw [hp]

theorem fillAt_run₂ {z : PBt L t} {p : TJ} (hp : partAt C D tF tJ t3 rd z = .join p) :
    (fillJ C D tF tJ t3 rd S).run₂ z = S.run₂ p := by
  show (match partAt C D tF tJ t3 rd z with
    | .join p => S.run₂ p
    | _ => []) = _
  rw [hp]

theorem fillAt_stm₃ {z : PBt L t} {p : T3} (hp : partAt C D tF tJ t3 rd z = .seam p)
    (a c : Bits) : (fillJ C D tF tJ t3 rd S).stm₃ a c z = S.stm₃ a c p := by
  show (match partAt C D tF tJ t3 rd z with
    | .seam p => S.stm₃ a c p
    | _ => ByteArray.empty) = _
  rw [hp]

theorem fillAt_run₃ {z : PBt L t} {p : T3} (hp : partAt C D tF tJ t3 rd z = .seam p) :
    (fillJ C D tF tJ t3 rd S).run₃ z = S.run₃ p := by
  show (match partAt C D tF tJ t3 rd z with
    | .seam p => S.run₃ p
    | _ => []) = _
  rw [hp]

/-! ## The laws -/

/-- **What is asked of the silent rounds' data.** fF, fJ, f3: the tests on the three messages. -/
structure SilentLaws (fF : List (Dig 256) → Option X → TF → Bool)
    (fJ : List (Dig 256) → TJ → Bool) (f3 : T3 → Bool) : Prop where
  l12 : S.lab₁ ≠ S.lab₂
  l13 : S.lab₁ ≠ S.lab₃
  l23 : S.lab₂ ≠ S.lab₃
  run₂ : ∀ p, whole (S.run₂ p) = true
  run₃ : ∀ p, whole (S.run₃ p) = true
  first₁ : ∀ (cms cms' : List (Dig 256)) (x x' : Option X) (p p' : TF), fF cms x p = true →
    fF cms' x' p' = true → S.stm₁ cms x p = S.stm₁ cms' x' p' → cms = cms' ∧ x = x' ∧ p = p'
  first₂ : ∀ (cms cms' : List (Dig 256)) (r r' : Bits) (p p' : TJ), fJ cms p = true →
    fJ cms' p' = true → r.length = 256 → r'.length = 256 → S.stm₂ cms r p = S.stm₂ cms' r' p' →
    S.run₂ p = S.run₂ p' → cms = cms' ∧ r = r' ∧ p = p'
  first₃ : ∀ (a a' c c' : Bits) (p p' : T3), f3 p = true → f3 p' = true → a.length = 256 →
    a'.length = 256 → c.length = 256 → c'.length = 256 → S.stm₃ a c p = S.stm₃ a' c' p' →
    S.run₃ p = S.run₃ p' → a = a' ∧ c = c' ∧ p = p'

variable (hrd : ∀ z z' w, rd z = some w → rd z' = some w → z = z')
include hrd

/-- Two plain parts that are read as one part P other than `nothing` are the same, if one plain part
alone of the file's rounds is read as P (hw). -/
theorem partAt_inj {z z' : PBt L t} {w : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann}
    (P : PartJ TF TJ T3) (hn : P ≠ .nothing) (h : partAt C D tF tJ t3 rd z = P)
    (h' : partAt C D tF tJ t3 rd z' = P)
    (hw : ∀ v, partOf C D tF tJ t3 v = P → v = w) : z = z' := by
  obtain ⟨v, hv, e⟩ := partAt_some C D tF tJ t3 rd h hn
  obtain ⟨v', hv', e'⟩ := partAt_some C D tF tJ t3 rd h' hn
  rw [hw v e] at hv
  rw [hw v' e'] at hv'
  exact hrd z z' w hv hv'

/-- **A written round.** -/
theorem fill_row_inj (i : ℕ) (rt rt' : List (Dig 256)) (z z' : PBt L t)
    (h : fitRow C D tF tJ t3 rd i rt z = true) (h' : fitRow C D tF tJ t3 rd i rt' z' = true)
    (em : (fillJ C D tF tJ t3 rd S).msg i (rt.map digToBytes) z =
      (fillJ C D tF tJ t3 rd S).msg i (rt'.map digToBytes) z')
    (en : (fillJ C D tF tJ t3 rd S).nonce i z = (fillJ C D tF tJ t3 rd S).nonce i z') :
    rt = rt' ∧ z = z' := by
  obtain ⟨m, n, hp, -, hf⟩ := fitRow_row C D tF tJ t3 rd h
  obtain ⟨m', n', hp', -, hf'⟩ := fitRow_row C D tF tJ t3 rd h'
  rw [fillAt_msg C D tF tJ t3 rd S hp, fillAt_msg C D tF tJ t3 rd S hp'] at em
  rw [fillAt_nonce C D tF tJ t3 rd S hp, fillAt_nonce C D tF tJ t3 rd S hp'] at en
  obtain ⟨v, hv, e⟩ := partAt_some C D tF tJ t3 rd hp (fun c => by cases c)
  obtain ⟨v', hv', e'⟩ := partAt_some C D tF tJ t3 rd hp' (fun c => by cases c)
  obtain ⟨a, b⟩ := partOf_row_inj C D tF tJ t3 rt rt' v v' i m m' n n' e e'
    (fun d hd => by
      unfold rootsFit at hf hf'
      rw [hd] at hf hf'
      exact ⟨hf, hf'⟩) em en
  rw [b] at hv
  exact ⟨a, hrd z z' v' hv hv'⟩

/-- **The laws at the data that `fillJ` lays.** -/
theorem laws_fill {fF : List (Dig 256) → Option X → TF → Bool} {fJ : List (Dig 256) → TJ → Bool}
    {f3 : T3 → Bool} (hS : SilentLaws S fF fJ f3) (hD : kindsAndWorkBelow256 D = true) (K : ℕ)
    (hK : K + 1 < 2 ^ 49) :
    LawsJ (fillJ C D tF tJ t3 rd S) (fitAt C D tF tJ t3 rd fF fJ f3) K where
  l12 := hS.l12
  l13 := hS.l13
  l23 := hS.l23
  word := fun i b hb => by
    obtain ⟨a1, a2⟩ := small_at hD i
    show (kwcTo (kindAt D i) (workAt D i) (b / 2)).isSome = true
    unfold kwcTo
    rw [if_pos ⟨a1, a2, by omega⟩]
    rfl
  nonce := fun i rt p h => by
    obtain ⟨m, n, hp, hn, -⟩ := fitRow_row C D tF tJ t3 rd h
    rw [fillAt_nonce C D tF tJ t3 rd S hp]
    exact hn
  row := fun i rt rt' p p' h h' em en => fill_row_inj C D tF tJ t3 rd S hrd i rt rt' p p' h h' em en
  run₂ := fun p => by
    show whole (match partAt C D tF tJ t3 rd p with
      | .join p => S.run₂ p
      | _ => []) = true
    split
    · exact hS.run₂ _
    · rfl
  run₃ := fun p => by
    show whole (match partAt C D tF tJ t3 rd p with
      | .seam p => S.run₃ p
      | _ => []) = true
    split
    · exact hS.run₃ _
    · rfl
  first₁ := fun cms cms' x x' z z' h h' e => by
    obtain ⟨p, hp, f⟩ := frontAt_front C D tF tJ t3 rd h
    obtain ⟨p', hp', f'⟩ := frontAt_front C D tF tJ t3 rd h'
    rw [fillAt_stm₁ C D tF tJ t3 rd S hp, fillAt_stm₁ C D tF tJ t3 rd S hp'] at e
    obtain ⟨a, b, c⟩ := hS.first₁ cms cms' x x' p p' f f' e
    rw [← c] at hp'
    exact ⟨a, b, partAt_inj C D tF tJ t3 rd hrd (.front p) (fun c => by cases c) hp hp'
      (fun v hv => partOf_front_eq C D tF tJ t3 v p hv)⟩
  first₂ := fun cms cms' r r' z z' h h' l l' e er => by
    obtain ⟨p, hp, f⟩ := joinAt_join C D tF tJ t3 rd h
    obtain ⟨p', hp', f'⟩ := joinAt_join C D tF tJ t3 rd h'
    rw [fillAt_stm₂ C D tF tJ t3 rd S hp, fillAt_stm₂ C D tF tJ t3 rd S hp'] at e
    rw [fillAt_run₂ C D tF tJ t3 rd S hp, fillAt_run₂ C D tF tJ t3 rd S hp'] at er
    obtain ⟨a, b, c⟩ := hS.first₂ cms cms' r r' p p' f f' l l' e er
    rw [← c] at hp'
    exact ⟨a, b, partAt_inj C D tF tJ t3 rd hrd (.join p) (fun c => by cases c) hp hp'
      (fun v hv => partOf_join_eq C D tF tJ t3 v p hv)⟩
  first₃ := fun a a' c c' z z' h h' l1 l2 l3 l4 e er => by
    obtain ⟨p, hp, f⟩ := seamAt_seam C D tF tJ t3 rd h
    obtain ⟨p', hp', f'⟩ := seamAt_seam C D tF tJ t3 rd h'
    rw [fillAt_stm₃ C D tF tJ t3 rd S hp, fillAt_stm₃ C D tF tJ t3 rd S hp'] at e
    rw [fillAt_run₃ C D tF tJ t3 rd S hp, fillAt_run₃ C D tF tJ t3 rd S hp'] at er
    obtain ⟨u, v, w⟩ := hS.first₃ a a' c c' p p' f f' l1 l2 l3 l4 e er
    rw [← w] at hp'
    exact ⟨u, v, partAt_inj C D tF tJ t3 rd hrd (.seam p) (fun c => by cases c) hp hp'
      (fun v hv => partOf_seam_eq C D tF tJ t3 v p hv)⟩
  slot := fun z z' h h' => by
    have g : ∀ y : PBt L t, slotAt C D tF tJ t3 rd y = true →
        rd y = some (in₂ C D tF tJ t3 (.inl (.inr ()))) := by
      intro y hy
      unfold slotAt at hy
      cases hr : rd y with
      | none =>
        rw [hr] at hy
        cases hy
      | some w =>
        rw [hr] at hy
        rw [isSlot_eq C D tF tJ t3 w hy]
    exact hrd z z' _ (g z h) (g z' h')

end

end OnBytes.Maker.Page
