-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinkSib.lean: the link of a stored table with a record, over pairs of records, at the
shape of the written link `LinkX`.

The written link of OnBytes/TypedOracleCompiler/Slice/EntryX.lean (`LinkX D dec`) has instances "both tables'
answers as lists of triples of words; both tables' seeds", and its external strings have 2 ^ D.a
symbols, D.a being computed from a description. The link of a configuration with a record
(`DecR.configurationOfStoredTable`, OnBytes/Slice/ConfOf.lean) has pairs of records as instances and 2 ^ T.a symbols. At
the sizes in use the two depths are equal by a theorem; `rfl` does not show it to the elaborator, so
the two types of external strings are not one to it. So the protocol is said here over letters: a
kit C, rounds' data ds, a depth a, stored openings xs.

Main names:
  `linkSkeletonOfRoundData`, `linkProtocolOfRoundData`: skeleton and protocol over letters; `psxw_at`, `linkW_at`: at a description's
    own letters they are `PSXE D dec` and `LinkX D dec`, by unfolding.
  `trAns`, `anT_trAns`: typed answers as a list of triples of words, in the order of the program's
    key; read back they are the typed answers.
  `recX`: the instance made of two records; `keys_recX`: the two keys written of it are the keys
    written of the two records.
  `linkSib`: `linkProtocolOfRoundData` at the decision "dec at `recX`".
  `linkSib_fix`: at a pair of records it reads and accepts as `linkProtocolOfRoundData` at dec does at `recX` of the
    pair, by unfolding.
  `linkSib_local`: its verifier is local.
  `conf_lang`: the language of four clauses gives the language of which the link's soundness in
    the compiled verifier speaks.
  `SoundAt`, `linkSib_sound`: soundness instance by instance at a description whose four letters
    are C, ds, T.a, xs gives soundness of `linkSib` for that language, with the same bound.

Limits: no probability is computed here; the hypothesis of `linkSib_sound` is shown elsewhere
(OnBytes/TypedOracleCompiler/Slice/EntryRow13JohFull.lean, EntryRow13JohSmall.lean). This is said under the
hypotheses that stand in the statement itself, which this comment does not list; it is no claim that
they hold. Nothing on an honest prover.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryXJudge
import OnBytes.TypedOracleCompiler.Slice.EntryPS
import OnBytes.TypedOracleCompiler.Slice.EntryData
import OnBytes.TypedOracleCompiler.Slice.KeysOfX
import OnBytes.Slice.ConfOf
import OnBytes.Slice.BlkProxGp

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat
open OnBytes.Slice TypedOracleCompiler.Slice TypedOracleCompiler.Run TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD skeletonOverBothExternalStrings SOf psofX_local)
open _root_.Run.PQ (View SgX CK XO)
open scoped ENNReal

/-! ## The protocol over letters -/

section
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)

/-- The written link with an instance, as a skeleton, over letters. -/
@[reducible] def linkSkeletonOfRoundData : Twin.PS X (twoExternalStrings (2 ^ a) SgX) where
  S := SOf C ds
  blinded := (skeletonOverBothExternalStrings C ds a xs fun _ => true).blinded
  extReads := fun _ ρ => (skeletonOverBothExternalStrings C ds a xs fun _ => true).extReads () ρ
  reads := fun _ ρ π => (skeletonOverBothExternalStrings C ds a xs fun _ => true).reads () ρ π
  accept := fun x y τ => (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ
  ann := _root_.Run.Twin.allLo (SOf C ds)

/-- The protocol. -/
abbrev linkProtocolOfRoundData : InteractiveOracleProof X (twoExternalStrings (2 ^ a) SgX) := (linkSkeletonOfRoundData C ds a xs dec).up.loc

/-- The verifier is local. -/
theorem linkW_local : (linkProtocolOfRoundData C ds a xs dec).IsLocal :=
  fun x y y' τ τ' hρ hp he hr => psofX_local C ds a xs (dec x) () y y' τ τ' hρ hp he hr

end

/-- At a description's own letters the skeleton is `PSXE`. -/
theorem psxw_at {X : Type} (D : XD) (dec : X → View → Bool) :
    PSXE D dec = linkSkeletonOfRoundData D.C D.ds D.a D.xs dec := rfl

/-- At a description's own letters the protocol is `LinkX`. -/
theorem linkW_at {X : Type} (D : XD) (dec : X → View → Bool) :
    LinkX D dec = linkProtocolOfRoundData D.C D.ds D.a D.xs dec := rfl

/-! ## The instance made of two records -/

section
variable {v lg s : ℕ}

/-- Typed answers as a list of triples of words: entry r * s + i is the answer of the row with the
number r under seed i. -/
def trAns (a : (Fin v → Bool) × Fin s → GE) : AnsT :=
  List.ofFn fun n : Fin (2 ^ v * s) =>
    ofE (a (vtx v (n.val / s), ⟨n.val % s, Nat.mod_lt _ (pos_of_place n)⟩))

/-- Read back they are the typed answers. -/
theorem anT_trAns (a : (Fin v → Bool) × Fin s → GE) : anT v s (trAns a) = a := by
  funext x
  obtain ⟨r, i⟩ := x
  have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hlt : Sz.rowNo r * s + i.val < 2 ^ v * s := by
    have h1 : Sz.rowNo r + 1 ≤ 2 ^ v := rowNo_lt r
    calc Sz.rowNo r * s + i.val < Sz.rowNo r * s + s := Nat.add_lt_add_left i.isLt _
      _ = (Sz.rowNo r + 1) * s := by ring
      _ ≤ 2 ^ v * s := Nat.mul_le_mul_right _ h1
  have hd : (Sz.rowNo r * s + i.val) / s = Sz.rowNo r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  have hm : (Sz.rowNo r * s + i.val) % s = i.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  unfold anT trAns
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt), List.getElem_ofFn, toE_ofE]
  congr 1
  exact Prod.ext (by show vtx v _ = r; rw [hd, ProxRun.vtx_rowNo]) (Fin.ext hm)

/-- The instance made of two records. -/
def recX (rr : RecP NZ v lg s × RecP NZ v lg s) : XE AnsT lg s :=
  ((trAns rr.1.2, trAns rr.2.2), (rr.1.1, rr.2.1))

/-- The two keys written of it are the keys written of the two records. -/
theorem keys_recX (rr : RecP NZ v lg s × RecP NZ v lg s) :
    keysOfX v lg s (anT v s) (recX rr) =
      (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) := by
  unfold keysOfX recX
  simp only [anT_trAns]

end

/-! ## The link over pairs of records -/

section
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {v lg s : ℕ}
  (dec : XE AnsT lg s → View → Bool)

/-- The link over pairs of records, at the shape of `LinkX`. -/
abbrev linkSib : InteractiveOracleProof (RecP NZ v lg s × RecP NZ v lg s) (twoExternalStrings (2 ^ a) SgX) :=
  linkProtocolOfRoundData C ds a xs fun rr => dec (recX rr)

/-- At a pair of records it accepts as the link with instances does at the instance made of the
pair; what both read does not hang on the instance. -/
theorem linkSib_fix (rr : RecP NZ v lg s × RecP NZ v lg s) :
    (linkSib C ds a xs dec).accept rr = (linkProtocolOfRoundData C ds a xs dec).accept (recX rr) ∧
      (linkSib C ds a xs dec).reads rr = (linkProtocolOfRoundData C ds a xs dec).reads (recX rr) ∧
      (linkSib C ds a xs dec).extReads rr = (linkProtocolOfRoundData C ds a xs dec).extReads (recX rr) ∧
      (linkSib (v := v) C ds a xs dec).shape = (linkProtocolOfRoundData C ds a xs dec).shape :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Its verifier is local. -/
theorem linkSib_local : (linkSib (v := v) C ds a xs dec).IsLocal := linkW_local C ds a xs _

end

/-! ## Soundness -/

section
variable {D : DecR} {X : Type} (A : D.Claims X) (R : D.RelationsAndEncoding A)

open Classical in
/-- The language of four clauses gives the language of which the link's soundness in the compiled
verifier speaks. -/
theorem conf_lang (r : D.Rec × D.Rec)
    (y : (Fin (2 ^ D.T.a) → SgX) × (Fin (2 ^ D.T.a) → SgX))
    (hL : D.dcd y.1 r.1 = none ∨ D.coll y.1 r.1.1 ∨ D.coll y.2 r.2.1 ∨
      ∃ u₀ u₁, D.dcd y.1 r.1 = some u₀ ∧ D.dcd y.2 r.2 = some u₁ ∧ D.Agree u₁ u₀) :
    (DecR.configurationOfStoredTable A R).D y.1 r.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 r.2.1 ∨
      (DecR.configurationOfStoredTable A R).D y.2 r.2 = (DecR.configurationOfStoredTable A R).D y.1 r.1 := by
  by_cases c0 : D.coll y.1 r.1.1
  · exact Or.inl (by rw [DecR.conf_D, if_pos c0])
  by_cases c1 : D.coll y.2 r.2.1
  · exact Or.inr (Or.inl c1)
  rcases hL with h | h | h | ⟨u₀, u₁, h0, h1, hA⟩
  · exact Or.inl (by rw [DecR.conf_D, if_neg c0, h]; rfl)
  · exact absurd h c0
  · exact absurd h c1
  · refine Or.inr (Or.inr ?_)
    rw [DecR.conf_D, DecR.conf_D, if_neg c0, if_neg c1, h0, h1]
    exact DecR.conf_held A R u₁ u₀ hA

end

section
variable (T : Fmt.M1.Code) (v eM lg s : ℕ) (dec : XE AnsT lg s → View → Bool) (κ : ℝ≥0∞)

/-- Soundness instance by instance, over letters: one list of counts, below κ, with which at every
instance the written link at that instance's decision is sound for the entry's language of a typed
world. -/
def SoundAt (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) : Prop :=
  ∃ ε : Err (linkProtocolOfRoundData C ds a xs fun _ : Unit => fun _ => true).shape,
    (∀ x : XE AnsT lg s, (linkProtocolOfRoundData C ds a xs fun _ : Unit => dec x).Sound
      (fun _ y => DecR.LgE (D := decRec T v eM lg s) (Equiv.refl _) (anT v s) id (x.1.1, x.2.1)
        (x.1.2, x.2.2) y.1 y.2) ε) ∧ Err.Below ε κ

/-- At a description's own letters it is the statement of soundness record by record. -/
theorem soundAt_at (D : XD)
    (h : ∃ ε : Err (Link0 D fun _ => true).shape,
      (∀ x, (Link0 D (dec x)).Sound (fun _ => lgEX T v eM lg s D (anT v s) x) ε) ∧
        Err.Below ε κ) : SoundAt T v eM lg s dec κ D.C D.ds D.a D.xs := h

/-- `linkSib` is sound for the language of the compiled verifier's link, with the same bound. This
is said under the hypotheses that stand in the statement itself, which this comment does not list;
it is no claim that they hold. -/
theorem linkSib_sound {X : Type} (A : (decRec T v eM lg s).Claims X)
    (R : (decRec T v eM lg s).RelationsAndEncoding A) (C : CK) (ds : List PQ.RD) (xs : List XO)
    (h : SoundAt T v eM lg s dec κ C ds T.a xs) :
    ∃ ε : Err (linkSib (v := v) C ds T.a xs dec).shape,
      (linkSib (v := v) C ds T.a xs dec).Sound
        (fun rr y => (DecR.configurationOfStoredTable A R).D y.1 rr.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 rr.2.1 ∨
          (DecR.configurationOfStoredTable A R).D y.2 rr.2 = (DecR.configurationOfStoredTable A R).D y.1 rr.1) ε ∧ Err.Below ε κ := by
  obtain ⟨ε, hS, hB⟩ := h
  refine ⟨ε, fun rr y hn => hS (recX rr) () y fun hl => hn ?_, hB⟩
  have h4 := (DecR.lgE_iff (D := decRec T v eM lg s) (Equiv.refl _) (anT v s) id rfl
    ((recX rr).1.1, (recX rr).2.1) ((recX rr).1.2, (recX rr).2.2) y.1 y.2).1 hl
  have e0 : anT v s (recX rr).1.1 = rr.1.2 := anT_trAns _
  have e1 : anT v s (recX rr).1.2 = rr.2.2 := anT_trAns _
  simp only [e0, e1] at h4
  exact conf_lang A R rr y h4

end

end OnBytes.Flat
