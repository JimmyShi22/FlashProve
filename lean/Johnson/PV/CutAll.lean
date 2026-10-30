-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/CutAll.lean: one cut, and so one encoding, for the key file's and the proof file's typed
  queries, at one interface, after the manner of OnBytes/K/Arm/KeyCut.lean, ProofCut.lean,
  KeyInj.lean and ProofInj.lean, at letters.

`cutKey` and `cutProof` are cut out of one page of all three files (`PageJ`) at one interface. They
  write alike at leaves, vertices, the request tree and the seeds' queries; the first adds the key
  file's rows (tag test), the second the proof file's (tag onl). Here both sets of rows stand in one
  function `cutBoth`. It is one to one where it writes, under `KeyLaws`, `ProofLaws` and one further
  premise: no label of the key file's three is a label of the proof file's three.
Letters: the interface, the number of blocks, the page, the four tests of fitness, `back`.
Limits: the entry file's chain queries are not given (the page's field `link`: a spelling taken as
  it is). That any premise holds at any data is not shown. The page's cfg and pd₁ .. pd₃ are
  letters: the format makes them by the hash itself, and nothing here cures that. Nothing on any
  hash. Nothing on soundness.

-/
import OnBytes.K.Arm.ProofInj
import OnBytes.Params.Chains
import Rom.ExitDown

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open TypedOracleCompiler.Run.Apart
open OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type}

/-- The data: the page, and both files' tests of fitness. -/
structure BothCut (L : BatchProtocolWithLeafBody I X) (K : ℕ) where
  P : PageJ L K
  fitFbK : FbIn 256 L .test × Fin (K + 1) → Bool
  fitGK : JoiningRoundQuery 256 L .test → Bool
  fitFbP : FbIn 256 L .onl × Fin (K + 1) → Bool
  fitGP : JoiningRoundQuery 256 L .onl → Bool

variable {L : BatchProtocolWithLeafBody I X} {K : ℕ} (C : BothCut L K)

/-- Its two parts. -/
def BothCut.key : KeyCut L K := ⟨C.P, C.fitFbK, C.fitGK⟩
def BothCut.proof : ProofCut L K := ⟨C.P, C.fitFbP, C.fitGP⟩

/-- **The call of a real point**, at the rows of both files and of the request tree. -/
def rowBoth : RealPts 256 K L → Option Fmt.OQ
  | .inr (.inr (.inr (.inr (.inl ⟨.test, x⟩)))) => rowKey C.key (.inr (.inr (.inr (.inr (.inl
      ⟨.test, x⟩)))))
  | .inr (.inr (.inr (.inr (.inr ⟨.test, q⟩)))) => rowKey C.key (.inr (.inr (.inr (.inr (.inr
      ⟨.test, q⟩)))))
  | a => rowProof C.proof a

/-- **The strings of both files' parts.** -/
def cutBoth (a : RealPts 256 K L) : Option (List Bool) :=
  match takenProof C.proof a with
  | some s => some s
  | none => (rowBoth C a).bind bitsOf

/-- The spellings that are taken as they are, are the same three in both parts. -/
theorem taken_same (a : RealPts 256 K L) : takenKey C.key a = takenProof C.proof a := by
  rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · cases t <;> rfl
  · cases t <;> rfl

/-- A row's call is the key file's part's or the proof file's part's. -/
theorem rowBoth_cases (a : RealPts 256 K L) (c : Fmt.OQ) (h : rowBoth C a = some c) :
    rowKey C.key a = some c ∨ rowProof C.proof a = some c := by
  rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
  · exact Or.inr h
  · exact Or.inr h
  · exact Or.inr h
  · exact Or.inr h
  · cases t
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
  · cases t
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h

/-- What either part's rows give, these rows give. -/
theorem rowBoth_key (a : RealPts 256 K L) (c : Fmt.OQ) (h : rowKey C.key a = some c) :
    rowBoth C a = some c := by
  rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
  · cases h
  · cases h
  · exact h
  · exact h
  · cases t
    · exact h
    · cases h
    · cases h
  · cases t
    · exact h
    · cases h
    · cases h

theorem rowBoth_proof (a : RealPts 256 K L) (c : Fmt.OQ) (h : rowProof C.proof a = some c) :
    rowBoth C a = some c := by
  rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
  · cases h
  · cases h
  · exact h
  · exact h
  · cases t
    · cases h
    · cases h
    · exact h
  · cases t
    · cases h
    · cases h
    · exact h

/-- No label of the key file's three chains is a label of the proof file's three. -/
def LabelsApart : Prop :=
  ∀ l, (l = C.P.key.lab₁ ∨ l = C.P.key.lab₂ ∨ l = C.P.key.lab₃) →
    (l = C.P.proof.lab₁ ∨ l = C.P.proof.lab₂ ∨ l = C.P.proof.lab₃) → False

/-- **A call of the key file's rows that is a call of the proof file's rows is the request tree's,
at
one point.** -/
theorem row_cross (hl : LabelsApart C)
    (hP : ∀ a b c, rowProof C.proof a = some c → rowProof C.proof b = some c → a = b)
    (a b : RealPts 256 K L) (c : Fmt.OQ) (ha : rowKey C.key a = some c)
    (hb : rowProof C.proof b = some c) : a = b := by
  obtain ⟨-, d2, d3, d4, d5⟩ := numbers_differ
  have d6 : nFirst ≠ nRow := by decide
  rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
  · cases ha
  · cases ha
  · exact hP _ b c ha hb
  · exact hP _ b c ha hb
  · exfalso
    cases t
    · have ka := row_call C.key _ c ha
      have h' : (if C.fitFbK x = true then fbCallJ C.P.key K x.1 x.2 else none) = some c := ha
      by_cases f : C.fitFbK x = true
      · rw [if_pos f] at h'
        rcases fb_place _ _ _ _ h' with ⟨n, i⟩ | ⟨n, i⟩ <;>
          rcases rowP_call C.proof b c hb with m | m | ⟨m, j⟩ | ⟨m, j⟩
        · exact d2 (m.symm.trans n)
        · exact d4 (m.symm.trans n)
        · exact hl _ i j
        · exact d6 (n.symm.trans m)
        · exact d3 (m.symm.trans n)
        · exact d5 (m.symm.trans n)
        · exact d6 (m.symm.trans n)
        · exact hl _ i j
      · rw [if_neg f] at h'
        cases h'
    · cases ha
    · cases ha
  · exfalso
    cases t
    · have h' : (if C.fitGK q = true then gCallJ C.P.key q else none) = some c := ha
      by_cases f : C.fitGK q = true
      · rw [if_pos f] at h'
        obtain ⟨n, i⟩ := g_place _ _ _ h'
        rcases rowP_call C.proof b c hb with m | m | ⟨m, j⟩ | ⟨m, j⟩
        · exact d3 (m.symm.trans n)
        · exact d5 (m.symm.trans n)
        · exact d6 (m.symm.trans n)
        · exact hl _ (Or.inl i) j
      · rw [if_neg f] at h'
        cases h'
    · cases ha
    · cases ha

/-- **What is asked**: both parts' laws, and that the two files' labels differ. -/
structure BothLaws : Prop where
  key : KeyLaws C.key
  proof : ProofLaws C.proof
  apart : LabelsApart C

variable {C}

theorem BothLaws.rowK (H : BothLaws C) :
    ∀ a b c, rowKey C.key a = some c → rowKey C.key b = some c → a = b :=
  rowKey_inj C.key (fun q q' c => rleaf_inj _ _ q q' c) (fun q q' c => rnode_inj _ q q' c)
    H.key.fb H.key.g H.key.fbg

theorem BothLaws.rowP (H : BothLaws C) :
    ∀ a b c, rowProof C.proof a = some c → rowProof C.proof b = some c → a = b :=
  rowProof_inj C.proof (fun q q' c => rleaf_inj _ _ q q' c) (fun q q' c => rnode_inj _ q q' c)
    H.proof.fb H.proof.g H.proof.fbg

/-- The rows' calls are one to one. -/
theorem BothLaws.row (H : BothLaws C) :
    ∀ a b c, rowBoth C a = some c → rowBoth C b = some c → a = b := by
  intro a b c ha hb
  rcases rowBoth_cases C a c ha with ha | ha <;> rcases rowBoth_cases C b c hb with hb | hb
  · exact H.rowK a b c ha hb
  · exact row_cross C H.apart H.rowP a b c ha hb
  · exact (row_cross C H.apart H.rowP b a c hb ha).symm
  · exact H.rowP a b c ha hb

/-- No string of a spelling is the string of a row's call. -/
theorem BothLaws.takenRow (H : BothLaws C) :
    ∀ a b s c, takenProof C.proof a = some s → rowBoth C b = some c → bitsOf c ≠ some s := by
  intro a b s c ha hb
  rcases rowBoth_cases C b c hb with hb | hb
  · exact taken_rows C.key H.key.taken H.key.cfg H.key.lab1 H.key.lab2 H.key.lab3 a b s c
      ((taken_same C a).trans ha) hb
  · exact takenP_rows C.proof H.proof.taken H.proof.cfg H.proof.lab1 H.proof.lab2 H.proof.lab3
      a b s c ha hb

/-- **ONE TO ONE WHERE IT WRITES.** -/
theorem cutBoth_one (H : BothLaws C) :
    ∀ a b s, cutBoth C a = some s → cutBoth C b = some s → a = b := by
  intro a b s ha hb
  unfold cutBoth at ha hb
  cases ta : takenProof C.proof a with
  | some u =>
    rw [ta] at ha
    obtain rfl : u = s := Option.some.inj ha
    cases tb : takenProof C.proof b with
    | some v =>
      rw [tb] at hb
      obtain rfl : v = u := Option.some.inj hb
      exact takenP_inj C.proof H.proof.taken H.proof.cfg a b v ta tb
    | none =>
      rw [tb] at hb
      obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 hb
      exact absurd hs (H.takenRow a b u c ta hc)
  | none =>
    rw [ta] at ha
    obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 ha
    cases tb : takenProof C.proof b with
    | some v =>
      rw [tb] at hb
      obtain rfl : v = s := Option.some.inj hb
      exact absurd hs (H.takenRow b a v c tb hc)
    | none =>
      rw [tb] at hb
      obtain ⟨c', hc', hs'⟩ := Option.bind_eq_some_iff.1 hb
      obtain rfl := bitsOf_inj c c' s hs hs'
      exact H.row a b c hc hc'

/-- **It writes what the key file's cut writes, and what the proof file's cut writes.** -/
theorem cutBoth_key (a : RealPts 256 K L) (s : List Bool) (h : cutKey C.key a = some s) :
    cutBoth C a = some s := by
  unfold cutKey at h
  unfold cutBoth
  rw [taken_same C a] at h
  cases ta : takenProof C.proof a with
  | some u => rw [ta] at h; exact h
  | none =>
    rw [ta] at h
    obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 h
    exact Option.bind_eq_some_iff.2 ⟨c, rowBoth_key C a c hc, hs⟩

theorem cutBoth_proof (a : RealPts 256 K L) (s : List Bool) (h : cutProof C.proof a = some s) :
    cutBoth C a = some s := by
  unfold cutProof at h
  unfold cutBoth
  cases ta : takenProof C.proof a with
  | some u => rw [ta] at h; exact h
  | none =>
    rw [ta] at h
    obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 h
    exact Option.bind_eq_some_iff.2 ⟨c, rowBoth_proof C a c hc, hs⟩

/-- And nothing else. -/
theorem cutBoth_cases (a : RealPts 256 K L) (s : List Bool) (h : cutBoth C a = some s) :
    cutKey C.key a = some s ∨ cutProof C.proof a = some s := by
  unfold cutBoth at h
  cases ta : takenProof C.proof a with
  | some u =>
    rw [ta] at h
    refine Or.inr ?_
    unfold cutProof
    rw [ta]
    exact h
  | none =>
    rw [ta] at h
    obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 h
    rcases rowBoth_cases C a c hc with hc | hc
    · refine Or.inl ?_
      unfold cutKey
      rw [taken_same C a, ta]
      exact Option.bind_eq_some_iff.2 ⟨c, hc, hs⟩
    · refine Or.inr ?_
      unfold cutProof
      rw [ta]
      exact Option.bind_eq_some_iff.2 ⟨c, hc, hs⟩

/-- Its strings begin with no byte other than 0 and 1. -/
theorem cutBoth_hd (H : BothLaws C) (a : RealPts 256 K L) (s : List Bool)
    (h : cutBoth C a = some s) (e : UInt8) (h0 : e ≠ 0) (h1 : e ≠ 1) : ¬ bitsOfByte e <+: s := by
  rcases cutBoth_cases a s h with h | h
  · exact cutKey_hd C.key H.key.taken a s h e h0 h1
  · exact cutProof_hd C.proof H.proof.taken a s h e h0 h1

/-- **ONE ENCODING OF ALL TYPED ORACLES THAT WRITES THE KEY FILE's PART AS `cutKey` DOES AND THE
PROOF
FILE's PART AS `cutProof` DOES**; every other typed point by `back`, behind an escape. -/
noncomputable def mBoth (H : BothLaws C) (back : StrCode (AllPts 256 K L)) :
    OracleCoding (typedOracleFamily 256 K L) 256 :=
  PageOf.implOf (cutBoth C) (cutBoth_one H) (cutBoth_hd H) back

/-! ## The entry file's chain queries beside them: all three files -/

variable (C)

/-- l is a label of one of the two files' six chains. -/
def IsLab (l : ℕ) : Prop :=
  (l = C.P.key.lab₁ ∨ l = C.P.key.lab₂ ∨ l = C.P.key.lab₃) ∨
    (l = C.P.proof.lab₁ ∨ l = C.P.proof.lab₂ ∨ l = C.P.proof.lab₃)

/-- What a row's call says: its number, and for the chains' rows where a label stands. -/
theorem rowBoth_call (a : RealPts 256 K L) (c : Fmt.OQ) (h : rowBoth C a = some c) :
    c.number = nRLeaf ∨ c.number = nRNode ∨ (c.number = nFirst ∧ IsLab C c.index) ∨
      (c.number = nRow ∧ IsLab C c.tree) := by
  rcases rowBoth_cases C a c h with h | h
  · rcases row_call C.key a c h with k | k | ⟨k, i⟩ | ⟨k, i⟩
    · exact Or.inl k
    · exact Or.inr (Or.inl k)
    · exact Or.inr (Or.inr (Or.inl ⟨k, Or.inl i⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k, Or.inl i⟩))
  · rcases rowP_call C.proof a c h with k | k | ⟨k, i⟩ | ⟨k, i⟩
    · exact Or.inl k
    · exact Or.inr (Or.inl k)
    · exact Or.inr (Or.inr (Or.inl ⟨k, Or.inr i⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨k, Or.inr i⟩))

/-- **What is asked of the page's spelling of the entry file's chain queries**: it is one to one;
its
strings have the form of a first call or of a row's call under one label lL, which fits its place
and
is neither the seeds' nor one of the six. -/
structure LinkLaws (lL : ℕ) : Prop where
  inj : ∀ x x' s, C.P.link x = some s → C.P.link x' = some s → x = x'
  is : ∀ x s, C.P.link x = some s → Is160 lL s ∨ Is162 lL s
  lt : lL < 2 ^ 48
  neS : lL ≠ Fmt.recordLabel
  ne : ∀ l, IsLab C l → l ≠ lL

/-- **The strings of all three files' parts.** -/
def cutAll : RealPts 256 K L → Option (List Bool)
  | .inr (.inr (.inr (.inr (.inl ⟨.link, x⟩)))) => C.P.link x
  | a => cutBoth C a

variable {C}

/-- Away from the entry file's chain queries it is `cutBoth`; there `cutBoth` writes nothing. -/
theorem cutBoth_link (x : FbIn 256 L .link × Fin (K + 1)) :
    cutBoth C (.inr (.inr (.inr (.inr (.inl ⟨.link, x⟩))))) = none := rfl

theorem cutAll_both (a : RealPts 256 K L) (s : List Bool) (h : cutBoth C a = some s) :
    cutAll C a = some s := by
  rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
  · exact h
  · exact h
  · exact h
  · exact h
  · cases t
    · exact h
    · cases h
    · exact h
  · exact h

theorem cutAll_link (x : FbIn 256 L .link × Fin (K + 1)) :
    cutAll C (.inr (.inr (.inr (.inr (.inl ⟨.link, x⟩))))) = C.P.link x := rfl

theorem cutAll_cases (a : RealPts 256 K L) (s : List Bool) (h : cutAll C a = some s) :
    cutBoth C a = some s ∨
      ∃ x, a = .inr (.inr (.inr (.inr (.inl ⟨.link, x⟩)))) ∧ C.P.link x = some s := by
  rcases a with q | q | q | q | ⟨t, x⟩ | ⟨t, q⟩
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inl h
  · cases t
    · exact Or.inl h
    · exact Or.inr ⟨x, rfl, h⟩
    · exact Or.inl h
  · exact Or.inl h

/-- **No string of the entry file's spelling is written by `cutBoth`.** -/
theorem link_apart (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL)
    (x : FbIn 256 L .link × Fin (K + 1)) (b : RealPts 256 K L) (s : List Bool)
    (hx : C.P.link x = some s) : cutBoth C b ≠ some s := by
  obtain ⟨-, -, n3, n4, n5, n6, n7, n8, -, -, -, -, -, -, m7⟩ := numbers_differ2
  obtain ⟨-, d2, d3, d4, d5⟩ := numbers_differ
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := mem_nums
  intro hb
  -- what the entry file's string is
  have kx : (No s nFirst ∧ Is160 lL s) ∨ (No s nRow ∧ Is162 lL s) := by
    rcases G.is x s hx with g | g
    · exact Or.inl ⟨tag_160 _ s g, g⟩
    · exact Or.inr ⟨tag_162 _ s g, g⟩
  unfold cutBoth at hb
  cases tb : takenProof C.proof b with
  | some u =>
    rw [tb] at hb
    obtain rfl : u = s := Option.some.inj hb
    rcases takenP_call C.proof H.proof.taken H.proof.cfg b u tb with
        ⟨q, -, -, k1 | k1⟩ | ⟨q, -, -, k1⟩ | ⟨y, -, -, ⟨k1, i1⟩ | ⟨k1, i1⟩⟩ <;>
      rcases kx with ⟨k2, i2⟩ | ⟨k2, i2⟩
    · exact n3 (no_inj u _ _ e3 e1 k1 k2)
    · exact n4 (no_inj u _ _ e3 e2 k1 k2)
    · exact n5 (no_inj u _ _ e6 e1 k1 k2)
    · exact n6 (no_inj u _ _ e6 e2 k1 k2)
    · exact n7 (no_inj u _ _ e4 e1 k1 k2)
    · exact n8 (no_inj u _ _ e4 e2 k1 k2)
    · exact no_160_160 lL _ G.lt recordLabel_lt G.neS u i2 i1
    · exact m7 (no_inj u _ _ e1 e2 k1 k2)
    · exact m7 (no_inj u _ _ e1 e2 k2 k1)
    · exact no_162_162 lL _ G.lt recordLabel_lt G.neS u i2 i1
  | none =>
    rw [tb] at hb
    obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 hb
    have kc := bitsOf_no c s hs
    rcases rowBoth_call C b c hc with k | k | ⟨k, i⟩ | ⟨k, i⟩ <;> rw [k] at kc <;>
      rcases kx with ⟨k2, i2⟩ | ⟨k2, i2⟩
    · exact d2 (no_inj s _ _ e5 e1 kc k2)
    · exact d3 (no_inj s _ _ e5 e2 kc k2)
    · exact d4 (no_inj s _ _ e7 e1 kc k2)
    · exact d5 (no_inj s _ _ e7 e2 kc k2)
    · exact G.ne _ i (first_label c s hs lL G.lt i2)
    · exact m7 (no_inj s _ _ e1 e2 kc k2)
    · exact m7 (no_inj s _ _ e1 e2 k2 kc)
    · exact G.ne _ i (row_label c s hs k lL G.lt i2)

/-- **ALL THREE FILES: ONE TO ONE WHERE IT WRITES.** -/
theorem cutAll_one (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL) :
    ∀ a b s, cutAll C a = some s → cutAll C b = some s → a = b := by
  intro a b s ha hb
  rcases cutAll_cases a s ha with ha | ⟨x, rfl, ha⟩ <;>
    rcases cutAll_cases b s hb with hb | ⟨y, rfl, hb⟩
  · exact cutBoth_one H a b s ha hb
  · exact absurd ha (link_apart H G y a s hb)
  · exact absurd hb (link_apart H G x b s ha)
  · rw [G.inj x y s ha hb]

/-- Its strings begin with no byte other than 0 and 1. -/
theorem cutAll_hd (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL) (a : RealPts 256 K L)
    (s : List Bool) (h : cutAll C a = some s) (e : UInt8) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    ¬ bitsOfByte e <+: s := by
  rcases cutAll_cases a s h with h | ⟨x, -, h⟩
  · exact cutBoth_hd H a s h e h0 h1
  · rcases G.is x s h with g | g
    · exact g.2.2 e h0
    · exact g.2 e h0 h1

/-- **ONE ENCODING OF ALL TYPED ORACLES FOR ALL THREE FILES**: it writes the key file's part as
`cutKey`
does, the proof file's as `cutProof` does, the entry file's chain queries as the page's spelling
does;
every other typed point by `back`, behind an escape. -/
noncomputable def mAll (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL)
    (back : StrCode (AllPts 256 K L)) : OracleCoding (typedOracleFamily 256 K L) 256 :=
  PageOf.implOf (cutAll C) (cutAll_one H G) (cutAll_hd H G) back

/-- It writes what each of the three writes. -/
theorem cutAll_key (a : RealPts 256 K L) (s : List Bool) (h : cutKey C.key a = some s) :
    cutAll C a = some s := cutAll_both a s (cutBoth_key a s h)
theorem cutAll_proof (a : RealPts 256 K L) (s : List Bool) (h : cutProof C.proof a = some s) :
    cutAll C a = some s := cutAll_both a s (cutBoth_proof a s h)

/-! ## «spare»: which strings are points of the spare oracle, written as themselves -/

/-- Every string that it writes has the tag of one of the format's seven numbers of typed queries.
-/
theorem cutAll_no (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL) (a : RealPts 256 K L)
    (s : List Bool) (h : cutAll C a = some s) : ∃ n ∈ fmtNums, No s n := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := mem_nums
  rcases cutAll_cases a s h with h | ⟨x, -, h⟩
  · unfold cutBoth at h
    cases ta : takenProof C.proof a with
    | some u =>
      rw [ta] at h
      obtain rfl : u = s := Option.some.inj h
      rcases takenP_call C.proof H.proof.taken H.proof.cfg a u ta with
        ⟨q, -, -, k | k⟩ | ⟨q, -, -, k⟩ | ⟨y, -, -, ⟨k, -⟩ | ⟨k, -⟩⟩
      · exact ⟨_, e3, k⟩
      · exact ⟨_, e6, k⟩
      · exact ⟨_, e4, k⟩
      · exact ⟨_, e1, k⟩
      · exact ⟨_, e2, k⟩
    | none =>
      rw [ta] at h
      obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 h
      have kc := bitsOf_no c s hs
      rcases rowBoth_call C a c hc with k | k | ⟨k, -⟩ | ⟨k, -⟩ <;> rw [k] at kc
      · exact ⟨_, e5, kc⟩
      · exact ⟨_, e7, kc⟩
      · exact ⟨_, e1, kc⟩
      · exact ⟨_, e2, kc⟩
  · rcases G.is x s h with g | g
    · exact ⟨_, e1, tag_160 _ s g⟩
    · exact ⟨_, e2, tag_162 _ s g⟩

/-- **A string with none of the seven tags and neither escape in front is a point of the spare
oracle,
written as itself.** -/
theorem mAll_spare (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL) (back : StrCode (AllPts 256 K L))
    (s : List Bool) (hs : ∀ n ∈ fmtNums, ¬ No s n) (h2 : ¬ bitsOfByte 2 <+: s)
    (h3 : ¬ bitsOfByte 3 <+: s) (j : Fin 1) : (mAll H G back).code .other s j = s :=
  PageG.implG_other' (PageOf.pageOf (cutAll C) (cutAll_one H G) (cutAll_hd H G) back) s j
    (fun a h => by
      obtain ⟨n, hn, k⟩ := cutAll_no H G a s h
      exact hs n hn k) h2 h3

/-- **So is every string whose first byte is none of 0, 1, 2, 3.** -/
theorem mAll_spare_byte (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL)
    (back : StrCode (AllPts 256 K L)) (e : UInt8) (r : List Bool) (h0 : e ≠ 0) (h1 : e ≠ 1)
    (h2 : e ≠ 2) (h3 : e ≠ 3) (j : Fin 1) :
    (mAll H G back).code .other (bitsOfByte e ++ r) j = bitsOfByte e ++ r :=
  PageG.implG_other' (PageOf.pageOf (cutAll C) (cutAll_one H G) (cutAll_hd H G) back) _ j
    (fun a h => cutAll_hd H G a _ h e h0 h1 ⟨r, rfl⟩)
    (byte_prefix 2 e (Ne.symm h2) r) (byte_prefix 3 e (Ne.symm h3) r)

/-- The format's three numbers of calls that no typed query makes: the two digests of parameters and
configuration, a run's value, the commitment ID. -/
def pubNums : List ℕ := [169, 172, 179]

theorem pub_tags : ∀ n ∈ pubNums, ∀ m ∈ fmtNums, (Wd n).take 16 ≠ (Wd m).take 16 := by
  decide +kernel

/-- **«spare» at the format's calls under 169, 172 and 179**: the string of such a call, at the half
0
or 1 and a start of 32 bytes, is a point of the spare oracle, written as itself. -/
theorem mAll_call (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL) (back : StrCode (AllPts 256 K L))
    (n : ℕ) (hn : n ∈ pubNums) (half : UInt8) (hh : half = 0 ∨ half = 1) (tree index : ℕ)
    (start bytes : ByteArray) (hs : start.size = 32) (j : Fin 1) :
    (mAll H G back).code .other (bytesToBits (Fmt.oStr half n tree index start bytes)) j =
      bytesToBits (Fmt.oStr half n tree index start bytes) := by
  have e := oStr_bits half n tree index start bytes
  refine mAll_spare H G back _ (fun m hm k => ?_) ?_ ?_ j
  · rw [e] at k
    have k' : No (hdr half n tree index start ++ bytesToBits bytes) n :=
      tag_of_lw1 n tree _ (lw_hdr half n tree index start hs _).1
    exact pub_tags n hn m hm (k'.symm.trans k)
  · rw [e]
    exact hdr_not_prefix 2 half (by rcases hh with rfl | rfl <;> decide) n tree index start _
  · rw [e]
    exact hdr_not_prefix 3 half (by rcases hh with rfl | rfl <;> decide) n tree index start _

/-- In the words of the premise «spare»: the point that such a string codes lies at the spare
oracle. -/
theorem mAll_isOther (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL) (back : StrCode (AllPts 256 K L))
    (s : List Bool) (h : (mAll H G back).code .other s (0 : Fin 1) = s) :
    ((mAll H G back).dec s).1 = TypedOracleCompiler.Compile.Batch.OracleName.other := by
  have e := (mAll H G back).dec_code .other s (0 : Fin 1)
  rw [h] at e
  rw [e]

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.cutBoth_one
#print axioms OnBytes.K.Arm.link_apart
#print axioms OnBytes.K.Arm.cutAll_one
#print axioms OnBytes.K.Arm.mAll
#print axioms OnBytes.K.Arm.mAll_call
#print axioms OnBytes.K.Arm.mAll_spare_byte
#print axioms OnBytes.K.Arm.mAll_isOther
-- the format's own numerals: the nine and the seven inequalities, evaluated
example : ∀ l ∈ [OnBytes.Params.labelOneTime, OnBytes.Params.labelShared,
    OnBytes.Params.labelSecond],
    l ∉ [OnBytes.Params.labelFirst, OnBytes.Params.labelSharedProof,
        OnBytes.Params.labelSecondProof] := by
  decide
example : ∀ l ∈ [OnBytes.Params.labelOneTime, OnBytes.Params.labelShared,
    OnBytes.Params.labelSecond,
    OnBytes.Params.labelFirst, OnBytes.Params.labelSharedProof, OnBytes.Params.labelSecondProof,
    Fmt.recordLabel], l ≠ OnBytes.Params.labelLink ∧ l < 2 ^ 48 := by
  decide
