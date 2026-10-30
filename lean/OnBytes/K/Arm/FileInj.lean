-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/FileInj.lean: on the chain queries of one file that fit, the format's call is one to
one.

OnBytes/Maker/Page/Frame.lean gives, for a typed chain query of a file with three joined chains and
a block of its answer, the call that the format hashes there (`fbCallJ`), and for the query of the
slot value its call (`gCallJ`). These functions test no lengths, and they do not read every field of
a query, so two queries can have one call. Here a test `fitFb` | `fitG` on a query is written, which
computes where its data compute, and laws `LawsJ` on the file's data are named, in letters, under
which two fitting queries with one call are one query, with one block.
What is proved is the frame: from one call, the same number, label, index, block, chain value,
nonce and lengths, and so the same typed round. That a round's message and the three statements tell
their typed content is asked: the laws `row`, `first₁`, `first₂`, `first₃` are themselves one-to-one
premises on the data's own spellings, and `slot` asks that at most one plain part passes the test.
So this file is a reduction to these.
For proofs only; the program does not import this file.

1. What the file contains.
    `FitJ L t`: the data of the test, five tests on what a query holds in typed form: at a written
      round its roots with its plain part; at the first chain's first query the outer roots, the
      instance and the plain part; at the second chain's the outer roots and the plain part; at the
      third chain's the plain part; at the slot's query the plain part.
    `fitPart`, `callIn`, `fitFb`, `fitG`: the tests. A chain value, a run's value, a request root
      and a seal have 256 bits; the queries of the three silent rounds (each chain's first) and the
      slot's hold no root; the call lies in the domain of the format's hash (`Fmt.hDom`).
    `LawsJ F Φ K`: the laws: the three labels differ; the word for kind, work and a call's number is
      written; a nonce is below 2 ^ 64; the later chains' run values are whole bytes; and the five
      premises named above.

2. What is checked when the file compiles. The proofs.

3. Theorems.
    `fbCallJ_inj`: two fitting chain queries and blocks with one call are one.
    `gCallJ_inj`: two fitting queries of the slot value with one call are one.
    `fb_g_apart`: a chain query's call is no call of the slot value.

4. What is not claimed.
   That the laws hold of any file's data at a test that lets a verifier's queries through. A test
   that says no everywhere meets every law but `l12`, `l13`, `l23`, `word`, `run₂` and `run₃`, which
   speak of the file's data alone; then no query fits, and the three theorems say nothing. So the
   laws are worth what the test lets through. That a call's string is one to one:
   OnBytes/K/Arm/StrInj.lean. That the queries which a verifier asks fit. Nothing on leaves,
   vertices or the request tree. Nothing on any hash. Nothing on soundness.
   The law `first₁` asks that the first chain's statement tells the instance. Where the statement
   holds the instance through digests, as a proof file's holds its request, `first₁` cannot hold at
   a test that lets the first query of every instance through: OnBytes/K/Arm/ProofGlue.lean says
   what follows.
   A chain query of the format f2 that holds an instance fits at no data of the test: `fitPart` says
   no, and `fbCallJ` gives it no call. So where an interface names a written round of the first or
   the third chain in its field `late`, the query of that round of a verifier that hands its chains
   an instance does not fit. That `late` names no such round is not shown here.
   The law `row` asks that a round's message tells all the roots that a fitting query holds. Where
   the test lets through more roots than the round's message spells, `row` fails: so it cannot hold
   together with the premise that a verifier's queries of such a round fit.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.CallInj

set_option autoImplicit false

namespace OnBytes.K.Arm.FileInj

open OnBytes.Maker.Page TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag}

/-- The data of the test on a file's chain queries. -/
structure FitJ (L : BatchProtocolWithLeafBody I X) (t : Tag) where
  /-- at the written round i: the roots and the plain part -/
  row : ℕ → List (Dig 256) → PBt L t → Bool
  /-- at the first chain's first query: the outer roots, the instance, the plain part -/
  front : List (Dig 256) → Option X → PBt L t → Bool
  /-- at the second chain's first query: the outer roots, the plain part -/
  join : List (Dig 256) → PBt L t → Bool
  /-- at the third chain's first query: the plain part -/
  seam : PBt L t → Bool
  /-- at the slot's query: the plain part -/
  slot : PBt L t → Bool

/-- What a chain query holds fits its head's form. -/
def fitPart (Φ : FitJ L t) (i : ℕ) (rt : List (Dig 256)) (p : PBt L t) : Head 256 X → Bool
  | .f1 cms x salt => rt.isEmpty && Φ.front cms x p && salt.length == 256
  | .f2 none ρ => ρ.length == 256 && Φ.row i rt p
  | .f2 (some _) _ => false
  | .f4 cms r => rt.isEmpty && Φ.join cms p && r.length == 256
  | .f5 ρ => ρ.length == 256 && Φ.row i rt p
  | .f3 a c => rt.isEmpty && Φ.seam p && a.length == 256 && c.length == 256

/-- The call lies in the domain of the format's hash. -/
def callIn (c : Fmt.OQ) : Bool := Fmt.hDom c.number c.tree c.index c.start c.bytes

/-- **The test on a chain query and a block.** -/
def fitFb (Φ : FitJ L t) (F : FileJ L t) (K : ℕ) (q : FbIn 256 L t) (j : Fin (K + 1)) : Bool :=
  fitPart Φ q.round q.rt q.plain q.head && (fbCallJ F K q j).any callIn

/-- **The test on a query of the slot value.** -/
def fitG (Φ : FitJ L t) (F : FileJ L t) (q : JoiningRoundQuery 256 L t) : Bool :=
  q.ρ.length == 256 && q.rt.isEmpty && Φ.slot q.plain && (gCallJ F q).any callIn

/-- **The laws on a file's data.** -/
structure LawsJ (F : FileJ L t) (Φ : FitJ L t) (K : ℕ) : Prop where
  /-- the three labels differ -/
  l12 : F.lab₁ ≠ F.lab₂
  l13 : F.lab₁ ≠ F.lab₃
  l23 : F.lab₂ ≠ F.lab₃
  /-- the word for kind, work and a call's number is written at every block -/
  word : ∀ i b, b ≤ K + 1 → (kwcTo (F.kind i) (F.work i) (b / 2)).isSome = true
  /-- a fitting round's nonce is a word of eight bytes -/
  nonce : ∀ i rt p, Φ.row i rt p = true → F.nonce i p < 2 ^ 64
  /-- a written round: the message's bytes and the nonce tell the roots and the plain part -/
  row : ∀ i (rt rt' : List (Dig 256)) (p p' : PBt L t), Φ.row i rt p = true →
    Φ.row i rt' p' = true → F.msg i (rt.map digToBytes) p = F.msg i (rt'.map digToBytes) p' →
    F.nonce i p = F.nonce i p' → rt = rt' ∧ p = p'
  /-- the later chains' run values are whole bytes -/
  run₂ : ∀ p, whole (F.run₂ p) = true
  run₃ : ∀ p, whole (F.run₃ p) = true
  /-- the first chain's statement tells the outer roots, the instance and the plain part -/
  first₁ : ∀ (cms cms' : List (Dig 256)) (x x' : Option X) (p p' : PBt L t),
    Φ.front cms x p = true → Φ.front cms' x' p' = true → F.stm₁ cms x p = F.stm₁ cms' x' p' →
    cms = cms' ∧ x = x' ∧ p = p'
  /-- the second chain's statement and run value -/
  first₂ : ∀ (cms cms' : List (Dig 256)) (r r' : Bits) (p p' : PBt L t), Φ.join cms p = true →
    Φ.join cms' p' = true → r.length = 256 → r'.length = 256 →
    F.stm₂ cms r p = F.stm₂ cms' r' p' → F.run₂ p = F.run₂ p' → cms = cms' ∧ r = r' ∧ p = p'
  /-- the third chain's statement and run value -/
  first₃ : ∀ (a a' c c' : Bits) (p p' : PBt L t), Φ.seam p = true → Φ.seam p' = true →
    a.length = 256 → a'.length = 256 → c.length = 256 → c'.length = 256 →
    F.stm₃ a c p = F.stm₃ a' c' p' → F.run₃ p = F.run₃ p' → a = a' ∧ c = c' ∧ p = p'
  /-- at most one plain part fits the slot's query -/
  slot : ∀ p p', Φ.slot p = true → Φ.slot p' = true → p = p'

/-! ## Tools -/

theorem whole_256 {l : List Bool} (h : l.length = 256) : whole l = true := by
  unfold whole
  rw [h]
  rfl

theorem blockNo_le (w K : ℕ) (j : Fin (K + 1)) : blockNo w K j ≤ K + 1 := by
  have := j.isLt
  unfold blockNo
  split_ifs <;> omega

theorem callIn_size {c : Fmt.OQ} (h : callIn c = true) : c.bytes.size < 2 ^ 64 := by
  unfold callIn Fmt.hDom at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨_, h5⟩, _⟩, _⟩, _⟩ := h
  omega

theorem size_firstBytes (pd st : ByteArray) (salt : Bits) :
    st.size ≤ (firstBytes pd st salt).size := by
  unfold firstBytes
  simp only [ByteArray.size_append]
  omega

/-- The statement of a first call in the domain is short enough. -/
theorem first_size {lab : ℕ} {pd st : ByteArray} {run : Bits}
    (h : callIn (firstCall lab pd st run) = true) : st.size < 2 ^ 64 := by
  have s : (firstBytes pd st run).size < 2 ^ 64 := callIn_size h
  have := size_firstBytes pd st run
  omega

theorem row_first {lab idx kind work nonce ow K lab' : ℕ} {ρ run : Bits} {msg pd st : ByteArray}
    {j : Fin (K + 1)}
    (e : rowCall lab idx ρ msg kind work nonce ow K j = firstCall lab' pd st run) : False :=
  rowCall_ne_firstCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ e

theorem nil_of_isEmpty {α : Type} {l : List α} (h : l.isEmpty = true) : l = [] :=
  List.isEmpty_iff.1 h

/-- A written round, at one typed round and one order of the blocks. -/
theorem row_core {F : FileJ L t} {Φ : FitJ L t} {K : ℕ} (h : LawsJ F Φ K)
    {i lab lab' idx idx' ow : ℕ} {ρ ρ' : Bits} {rt rt' : List (Dig 256)} {p p' : PBt L t}
    {j j' : Fin (K + 1)}
    (hρ : ρ.length = 256) (hρ' : ρ'.length = 256) (hr : Φ.row i rt p = true)
    (hr' : Φ.row i rt' p' = true)
    (e : rowCall lab idx ρ (F.msg i (rt.map digToBytes) p) (F.kind i) (F.work i) (F.nonce i p) ow K
        j =
      rowCall lab' idx' ρ' (F.msg i (rt'.map digToBytes) p') (F.kind i) (F.work i) (F.nonce i p') ow
        K j') : ρ = ρ' ∧ rt = rt' ∧ p = p' ∧ j = j' := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.word i _ (blockNo_le ow K j))
  obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 (h.word i _ (blockNo_le ow K j'))
  obtain ⟨_, _, e3, e4, e5, e6⟩ := rowCall_inj (whole_256 hρ) (whole_256 hρ') hv hv'
    (h.nonce i rt p hr) (h.nonce i rt' p' hr') e
  obtain ⟨r1, r2⟩ := h.row i rt rt' p p' hr hr' e4 e5
  exact ⟨e3, r1, r2, e6⟩

/-! ## The forms of a call -/

section Forms
variable {F : FileJ L t} {K : ℕ} {i : ℕ} {rt : List (Dig 256)} {p : PBt L t} {j : Fin (K + 1)}
  {c : Fmt.OQ}

theorem call_f1 {cms : List (Dig 256)} {x : Option X} {salt : Bits}
    (h : fbCallJ F K ⟨i, .f1 cms x salt, rt, p⟩ j = some c) :
    i = 0 ∧ j.val = K ∧ c = firstCall F.lab₁ F.pd₁ (F.stm₁ cms x p) salt := by
  have h' : (if i = 0 ∧ j.val = K then some (firstCall F.lab₁ F.pd₁ (F.stm₁ cms x p) salt)
    else none) = some c := h
  split_ifs at h' with hc
  exact ⟨hc.1, hc.2, (Option.some.inj h').symm⟩

theorem call_f4 {cms : List (Dig 256)} {r : Bits}
    (h : fbCallJ F K ⟨i, .f4 cms r, rt, p⟩ j = some c) :
    i = F.J ∧ j.val = K ∧ c = firstCall F.lab₂ F.pd₂ (F.stm₂ cms r p) (F.run₂ p) := by
  have h' : (if i = F.J ∧ j.val = K then
    some (firstCall F.lab₂ F.pd₂ (F.stm₂ cms r p) (F.run₂ p)) else none) = some c := h
  split_ifs at h' with hc
  exact ⟨hc.1, hc.2, (Option.some.inj h').symm⟩

theorem call_f3 {a b : Bits} (h : fbCallJ F K ⟨i, .f3 a b, rt, p⟩ j = some c) :
    i = F.J3 ∧ j.val = K ∧ c = firstCall F.lab₃ F.pd₃ (F.stm₃ a b p) (F.run₃ p) := by
  have h' : (if i = F.J3 ∧ j.val = K then
    some (firstCall F.lab₃ F.pd₃ (F.stm₃ a b p) (F.run₃ p)) else none) = some c := h
  split_ifs at h' with hc
  exact ⟨hc.1, hc.2, (Option.some.inj h').symm⟩

/-- A written round of the first or the third chain. -/
theorem call_f2 {ρ : Bits} (h : fbCallJ F K ⟨i, .f2 none ρ, rt, p⟩ j = some c) :
    (1 ≤ i ∧ i ≤ F.n₁ ∧ c = rowCall F.lab₁ i ρ (F.msg i (rt.map digToBytes) p) (F.kind i)
        (F.work i) (F.nonce i p) (F.work i) K j) ∨
      (F.J3 + 1 ≤ i ∧ i ≤ F.J3 + F.n₃ ∧ c = rowCall F.lab₃ (i - F.J3) ρ
        (F.msg i (rt.map digToBytes) p) (F.kind i) (F.work i) (F.nonce i p) (F.work i) K j) := by
  have h' : (if 1 ≤ i ∧ i ≤ F.n₁ then
      some (rowCall F.lab₁ i ρ (F.msg i (rt.map digToBytes) p) (F.kind i) (F.work i) (F.nonce i p)
        (F.work i) K j)
    else if F.J3 + 1 ≤ i ∧ i ≤ F.J3 + F.n₃ then
      some (rowCall F.lab₃ (i - F.J3) ρ (F.msg i (rt.map digToBytes) p) (F.kind i) (F.work i)
        (F.nonce i p) (F.work i) K j)
    else none) = some c := h
  split_ifs at h' with h1 h2
  · exact .inl ⟨h1.1, h1.2, (Option.some.inj h').symm⟩
  · exact .inr ⟨h2.1, h2.2, (Option.some.inj h').symm⟩

/-- A written round of the second chain. -/
theorem call_f5 {ρ : Bits} (h : fbCallJ F K ⟨i, .f5 ρ, rt, p⟩ j = some c) :
    F.J + 1 ≤ i ∧ i ≤ F.J + F.n₂ ∧ c = rowCall F.lab₂ (i - F.J) ρ (F.msg i (rt.map digToBytes) p)
      (F.kind i) (F.work i) (F.nonce i p) (if i = F.J + F.n₂ then 1 else F.work i) K j := by
  have h' : (if F.J + 1 ≤ i ∧ i ≤ F.J + F.n₂ then
      some (rowCall F.lab₂ (i - F.J) ρ (F.msg i (rt.map digToBytes) p) (F.kind i) (F.work i)
        (F.nonce i p) (if i = F.J + F.n₂ then 1 else F.work i) K j)
    else none) = some c := h
  by_cases h1 : F.J + 1 ≤ i ∧ i ≤ F.J + F.n₂
  · rw [if_pos h1] at h'
    exact ⟨h1.1, h1.2, (Option.some.inj h').symm⟩
  · rw [if_neg h1] at h'
    cases h'

end Forms

/-- **What a fitting chain query's call is**: a written round's, with the chain's label, the index
in the chain and the order of the blocks; or a chain's first. -/
inductive Form (F : FileJ L t) (Φ : FitJ L t) (K : ℕ) (q : FbIn 256 L t) (j : Fin (K + 1))
    (c : Fmt.OQ) : Prop
  | row (n lab idx ow : ℕ) (ρ : Bits) (hn : n = 1 ∨ n = 2 ∨ n = 3)
      (hlab : (n = 1 → lab = F.lab₁ ∧ q.round = idx ∧ ow = F.work q.round ∧ q.head = .f2 none ρ) ∧
        (n = 2 → lab = F.lab₂ ∧ q.round = F.J + idx ∧
          ow = (if q.round = F.J + F.n₂ then 1 else F.work q.round) ∧ q.head = .f5 ρ) ∧
        (n = 3 → lab = F.lab₃ ∧ q.round = F.J3 + idx ∧ ow = F.work q.round ∧ q.head = .f2 none ρ))
      (hρ : ρ.length = 256) (hr : Φ.row q.round q.rt q.plain = true)
      (hc : c = rowCall lab idx ρ (F.msg q.round (q.rt.map digToBytes) q.plain) (F.kind q.round)
        (F.work q.round) (F.nonce q.round q.plain) ow K j) : Form F Φ K q j c
  | first₁ (cms : List (Dig 256)) (x : Option X) (salt : Bits)
      (hq : q = ⟨0, .f1 cms x salt, [], q.plain⟩) (hj : j.val = K)
      (hf : Φ.front cms x q.plain = true) (hs : salt.length = 256)
      (hc : c = firstCall F.lab₁ F.pd₁ (F.stm₁ cms x q.plain) salt) : Form F Φ K q j c
  | first₂ (cms : List (Dig 256)) (r : Bits) (hq : q = ⟨F.J, .f4 cms r, [], q.plain⟩)
      (hj : j.val = K) (hf : Φ.join cms q.plain = true) (hs : r.length = 256)
      (hc : c = firstCall F.lab₂ F.pd₂ (F.stm₂ cms r q.plain) (F.run₂ q.plain)) : Form F Φ K q j c
  | first₃ (a b : Bits) (hq : q = ⟨F.J3, .f3 a b, [], q.plain⟩) (hj : j.val = K)
      (hf : Φ.seam q.plain = true) (ha : a.length = 256) (hb : b.length = 256)
      (hc : c = firstCall F.lab₃ F.pd₃ (F.stm₃ a b q.plain) (F.run₃ q.plain)) : Form F Φ K q j c

theorem form_of {F : FileJ L t} {Φ : FitJ L t} {K : ℕ} {q : FbIn 256 L t} {j : Fin (K + 1)}
    {c : Fmt.OQ} (hf : fitFb Φ F K q j = true) (hc : fbCallJ F K q j = some c) :
    Form F Φ K q j c := by
  obtain ⟨i, hd, rt, p⟩ := q
  have hp : fitPart Φ i rt p hd = true := (Bool.and_eq_true_iff.1 hf).1
  cases hd with
  | f1 cms x salt =>
    obtain ⟨h1, h2, h3⟩ := call_f1 hc
    simp only [fitPart, Bool.and_eq_true, beq_iff_eq] at hp
    subst h1
    rw [nil_of_isEmpty hp.1.1]
    exact .first₁ cms x salt rfl h2 hp.1.2 hp.2 h3
  | f2 xl ρ =>
    cases xl with
    | some x => cases hp
    | none =>
      simp only [fitPart, Bool.and_eq_true, beq_iff_eq] at hp
      rcases call_f2 hc with ⟨_, _, h3⟩ | ⟨h1, _, h3⟩
      · exact .row 1 F.lab₁ i (F.work i) ρ (.inl rfl)
          ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun e => by omega, fun e => by omega⟩ hp.1 hp.2 h3
      · exact .row 3 F.lab₃ (i - F.J3) (F.work i) ρ (.inr (.inr rfl))
          ⟨fun e => by omega, fun e => by omega,
            fun _ => ⟨rfl, by show i = F.J3 + (i - F.J3); omega, rfl, rfl⟩⟩ hp.1 hp.2 h3
  | f3 a b =>
    obtain ⟨h1, h2, h3⟩ := call_f3 hc
    simp only [fitPart, Bool.and_eq_true, beq_iff_eq] at hp
    subst h1
    rw [nil_of_isEmpty hp.1.1.1]
    exact .first₃ a b rfl h2 hp.1.1.2 hp.1.2 hp.2 h3
  | f4 cms r =>
    obtain ⟨h1, h2, h3⟩ := call_f4 hc
    simp only [fitPart, Bool.and_eq_true, beq_iff_eq] at hp
    subst h1
    rw [nil_of_isEmpty hp.1.1]
    exact .first₂ cms r rfl h2 hp.1.2 hp.2 h3
  | f5 ρ =>
    obtain ⟨h1, _, h3⟩ := call_f5 hc
    simp only [fitPart, Bool.and_eq_true, beq_iff_eq] at hp
    exact .row 2 F.lab₂ (i - F.J) (if i = F.J + F.n₂ then 1 else F.work i) ρ (.inr (.inl rfl))
      ⟨fun e => by omega, fun _ => ⟨rfl, by show i = F.J + (i - F.J); omega, rfl, rfl⟩,
        fun e => by omega⟩ hp.1 hp.2 h3

/-! ## One to one -/

section Main
variable {F : FileJ L t} {Φ : FitJ L t} {K : ℕ}

/-- Two written rounds' queries at one typed round, one order of the blocks and one form of head. -/
theorem row_diag (h : LawsJ F Φ K) (mk : Bits → Head 256 X) {i i' lab lab' idx idx' ow ow' : ℕ}
    {hd hd' : Head 256 X} {ρ ρ' : Bits} {rt rt' : List (Dig 256)} {p p' : PBt L t}
    {j j' : Fin (K + 1)} (hi : i = i') (ho : ow = ow') (hh : hd = mk ρ) (hh' : hd' = mk ρ')
    (hρ : ρ.length = 256) (hρ' : ρ'.length = 256) (hr : Φ.row i rt p = true)
    (hr' : Φ.row i' rt' p' = true)
    (e : rowCall lab idx ρ (F.msg i (rt.map digToBytes) p) (F.kind i) (F.work i) (F.nonce i p) ow K
        j =
      rowCall lab' idx' ρ' (F.msg i' (rt'.map digToBytes) p') (F.kind i') (F.work i')
        (F.nonce i' p') ow' K j') :
    (⟨i, hd, rt, p⟩ : FbIn 256 L t) = ⟨i', hd', rt', p'⟩ ∧ j = j' := by
  subst hi ho hh hh'
  obtain ⟨a, b, c, d⟩ := row_core h hρ hρ' hr hr' e
  subst a b c d
  exact ⟨rfl, rfl⟩

theorem callIn_of {q : FbIn 256 L t} {j : Fin (K + 1)} {c : Fmt.OQ}
    (hf : fitFb Φ F K q j = true) (hc : fbCallJ F K q j = some c) : callIn c = true := by
  have h := (Bool.and_eq_true_iff.1 hf).2
  rw [hc] at h
  exact h

/-- **Two fitting chain queries and blocks with one call are one.** -/
theorem fbCallJ_inj (h : LawsJ F Φ K) {q q' : FbIn 256 L t} {j j' : Fin (K + 1)} {c : Fmt.OQ}
    (hf : fitFb Φ F K q j = true) (hf' : fitFb Φ F K q' j' = true)
    (hc : fbCallJ F K q j = some c) (hc' : fbCallJ F K q' j' = some c) : q = q' ∧ j = j' := by
  have din := callIn_of hf hc
  have A := form_of hf hc
  have A' := form_of hf' hc'
  obtain ⟨i, hd, rt, p⟩ := q
  obtain ⟨i', hd', rt', p'⟩ := q'
  cases A with
  | row n lab idx ow ρ hn hl hρ hr e =>
    cases A' with
    | row n' lab' idx' ow' ρ' hn' hl' hρ' hr' e' =>
      have ee := e.symm.trans e'
      obtain ⟨p1, p2⟩ := rowCall_place ee
      rcases hn with rfl | rfl | rfl <;> rcases hn' with rfl | rfl | rfl
      · obtain ⟨_, a2, a3, a4⟩ := hl.1 rfl
        obtain ⟨_, b2, b3, b4⟩ := hl'.1 rfl
        have hi : i = i' := a2.trans (p2.trans b2.symm)
        exact row_diag h (fun ρ => .f2 none ρ) hi (by rw [a3, b3]; exact congrArg F.work hi) a4 b4
          hρ hρ' hr hr' ee
      · exact absurd ((hl.1 rfl).1.symm.trans (p1.trans (hl'.2.1 rfl).1)) h.l12
      · exact absurd ((hl.1 rfl).1.symm.trans (p1.trans (hl'.2.2 rfl).1)) h.l13
      · exact absurd ((hl'.1 rfl).1.symm.trans (p1.symm.trans (hl.2.1 rfl).1)) h.l12
      · obtain ⟨_, a2, a3, a4⟩ := hl.2.1 rfl
        obtain ⟨_, b2, b3, b4⟩ := hl'.2.1 rfl
        have hi : i = i' := a2.trans ((congrArg (F.J + ·) p2).trans b2.symm)
        exact row_diag h (fun ρ => .f5 ρ) hi (by rw [a3, b3]; subst hi; rfl) a4 b4 hρ hρ' hr hr' ee
      · exact absurd ((hl.2.1 rfl).1.symm.trans (p1.trans (hl'.2.2 rfl).1)) h.l23
      · exact absurd ((hl'.1 rfl).1.symm.trans (p1.symm.trans (hl.2.2 rfl).1)) h.l13
      · exact absurd ((hl'.2.1 rfl).1.symm.trans (p1.symm.trans (hl.2.2 rfl).1)) h.l23
      · obtain ⟨_, a2, a3, a4⟩ := hl.2.2 rfl
        obtain ⟨_, b2, b3, b4⟩ := hl'.2.2 rfl
        have hi : i = i' := a2.trans ((congrArg (F.J3 + ·) p2).trans b2.symm)
        exact row_diag h (fun ρ => .f2 none ρ) hi (by rw [a3, b3]; exact congrArg F.work hi) a4 b4
          hρ hρ' hr hr' ee
    | first₁ _ _ _ _ _ _ _ e' => exact (row_first (e.symm.trans e')).elim
    | first₂ _ _ _ _ _ _ e' => exact (row_first (e.symm.trans e')).elim
    | first₃ _ _ _ _ _ _ _ e' => exact (row_first (e.symm.trans e')).elim
  | first₁ cms x salt hq hj hfr hs e =>
    cases A' with
    | row _ _ _ _ _ _ _ _ _ e' => exact (row_first (e'.symm.trans e)).elim
    | first₁ cms' x' salt' hq' hj' hfr' hs' e' =>
      obtain ⟨_, _, s1, s2⟩ := firstCall_inj rfl (first_size (e ▸ din)) (first_size (e' ▸ din))
        (whole_256 hs) (whole_256 hs') (e.symm.trans e')
      obtain ⟨a, b, d⟩ := h.first₁ cms cms' x x' _ _ hfr hfr' s1
      have d' : p = p' := d
      rw [hq, hq']
      subst a b s2 d'
      exact ⟨rfl, Fin.ext (hj.trans hj'.symm)⟩
    | first₂ _ _ _ _ _ _ e' =>
      exact absurd (congrArg Fmt.OQ.index (e.symm.trans e')) h.l12
    | first₃ _ _ _ _ _ _ _ e' =>
      exact absurd (congrArg Fmt.OQ.index (e.symm.trans e')) h.l13
  | first₂ cms r hq hj hfr hs e =>
    cases A' with
    | row _ _ _ _ _ _ _ _ _ e' => exact (row_first (e'.symm.trans e)).elim
    | first₁ _ _ _ _ _ _ _ e' =>
      exact absurd (congrArg Fmt.OQ.index (e'.symm.trans e)) h.l12
    | first₂ cms' r' hq' hj' hfr' hs' e' =>
      obtain ⟨_, _, s1, s2⟩ := firstCall_inj rfl (first_size (e ▸ din)) (first_size (e' ▸ din))
        (h.run₂ _) (h.run₂ _) (e.symm.trans e')
      obtain ⟨a, b, d⟩ := h.first₂ cms cms' r r' _ _ hfr hfr' hs hs' s1 s2
      have d' : p = p' := d
      rw [hq, hq']
      subst a b d'
      exact ⟨rfl, Fin.ext (hj.trans hj'.symm)⟩
    | first₃ _ _ _ _ _ _ _ e' =>
      exact absurd (congrArg Fmt.OQ.index (e.symm.trans e')) h.l23
  | first₃ a b hq hj hfr ha hb e =>
    cases A' with
    | row _ _ _ _ _ _ _ _ _ e' => exact (row_first (e'.symm.trans e)).elim
    | first₁ _ _ _ _ _ _ _ e' =>
      exact absurd (congrArg Fmt.OQ.index (e'.symm.trans e)) h.l13
    | first₂ _ _ _ _ _ _ e' =>
      exact absurd (congrArg Fmt.OQ.index (e'.symm.trans e)) h.l23
    | first₃ a' b' hq' hj' hfr' ha' hb' e' =>
      obtain ⟨_, _, s1, s2⟩ := firstCall_inj rfl (first_size (e ▸ din)) (first_size (e' ▸ din))
        (h.run₃ _) (h.run₃ _) (e.symm.trans e')
      obtain ⟨u, v, d⟩ := h.first₃ a a' b b' _ _ hfr hfr' ha ha' hb hb' s1 s2
      have d' : p = p' := d
      rw [hq, hq']
      subst u v d'
      exact ⟨rfl, Fin.ext (hj.trans hj'.symm)⟩

/-- What the slot's call is. -/
theorem call_g {q : JoiningRoundQuery 256 L t} {c : Fmt.OQ} (h : gCallJ F q = some c) :
    q.round = F.J ∧ c.tree = F.lab₁ ∧ c.index = F.J ∧ c.start = bitsToBytes q.ρ ∧
      c.number = (rowCall 0 0 [] ByteArray.empty 0 0 0 0 0 0).number := by
  unfold gCallJ at h
  split_ifs at h with h1
  rw [← Option.some.inj h]
  exact ⟨h1, rfl, rfl, rfl, rfl⟩

/-- **Two fitting queries of the slot value with one call are one.** -/
theorem gCallJ_inj (h : LawsJ F Φ K) {q q' : JoiningRoundQuery 256 L t} {c : Fmt.OQ}
    (hf : fitG Φ F q = true) (hf' : fitG Φ F q' = true) (hc : gCallJ F q = some c)
    (hc' : gCallJ F q' = some c) : q = q' := by
  obtain ⟨a1, _, _, a4, _⟩ := call_g hc
  obtain ⟨b1, _, _, b4, _⟩ := call_g hc'
  simp only [fitG, Bool.and_eq_true, beq_iff_eq] at hf hf'
  obtain ⟨i, ρ, rt, p⟩ := q
  obtain ⟨i', ρ', rt', p'⟩ := q'
  have e1 : i = i' := a1.trans b1.symm
  have e2 : ρ = ρ' := bitsToBytes_inj (whole_256 hf.1.1.1) (whole_256 hf'.1.1.1) (a4.symm.trans b4)
  have e3 : rt = rt' := (nil_of_isEmpty hf.1.1.2).trans (nil_of_isEmpty hf'.1.1.2).symm
  have e4 : p = p' := h.slot p p' hf.1.2 hf'.1.2
  subst e1 e2 e3 e4
  rfl

/-- **A fitting chain query's call is no call of the slot value.** -/
theorem fb_g_apart (h : LawsJ F Φ K) {q : FbIn 256 L t} {j : Fin (K + 1)} {q' : JoiningRoundQuery 256 L t}
    {c : Fmt.OQ} (hf : fitFb Φ F K q j = true) (hc : fbCallJ F K q j = some c)
    (hc' : gCallJ F q' = some c) : False := by
  obtain ⟨_, g2, g3, _, g5⟩ := call_g hc'
  obtain ⟨i, hd, rt, p⟩ := q
  cases hd with
  | f1 cms x salt =>
    obtain ⟨_, _, e⟩ := call_f1 hc
    rw [e] at g5
    exact absurd g5 (by simp [rowCall, firstCall])
  | f2 xl ρ =>
    cases xl with
    | some x => cases hc
    | none =>
      rcases call_f2 hc with ⟨_, h2, e⟩ | ⟨_, _, e⟩
      · rw [e] at g3
        have g3' : i = F.J := g3
        unfold FileJ.J at g3'
        omega
      · rw [e] at g2
        exact absurd (g2 : F.lab₃ = F.lab₁).symm h.l13
  | f3 a b =>
    obtain ⟨_, _, e⟩ := call_f3 hc
    rw [e] at g5
    exact absurd g5 (by simp [rowCall, firstCall])
  | f4 cms r =>
    obtain ⟨_, _, e⟩ := call_f4 hc
    rw [e] at g5
    exact absurd g5 (by simp [rowCall, firstCall])
  | f5 ρ =>
    obtain ⟨_, _, e⟩ := call_f5 hc
    rw [e] at g2
    exact absurd (g2 : F.lab₂ = F.lab₁).symm h.l12

end Main

end OnBytes.K.Arm.FileInj
