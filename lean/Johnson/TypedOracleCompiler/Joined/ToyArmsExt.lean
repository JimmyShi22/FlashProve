-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/ToyArmsExt.lean: a test of `three_arms` (Johnson/TypedOracleCompiler/RecCompile/ThreeArms.lean)
with more weight than Johnson/TypedOracleCompiler/Joined/ToyArms.lean. `three_arms` is one bound for three checks
run in one experiment, one each for the key file, the entry file and the proof file; each check is
the test of a record's seed (for the entry file: of both records' seeds) followed by the compiled
verifier of that file's protocol. Here every hypothesis of it but the two bounds on the committer's
and the prover's queries (hC, hP) is proved, and the theorem is applied with these two alone left
(`toy_three_arms_ext`), at a small interface with records whose encoded index all three protocols
read (`reads_word_T`, `reads_word_B`, `reads_word_L`), a link with a round, one wire record and
three codings that differ. Three controls (`not_oktaX`, `not_oklaX`, `not_okbaX`): each bundle of
conditions on the wire record fails where a word's place in its tree is spoilt.

A test of a theorem's premises. Nothing on any program.


The encoded index is a word of two bits under a tree of depth 1. The index is one bit. A record is a
seed of one bit and an answer. Word and record decode to the answer if the seed is no collision seed
and the word's first bit is the answer, and to nothing else. The key's file and the proof's file are
three joined hash chains each, with the rounds of OnBytes/TypedOracleCompiler/Joined/ToyFile.lean; the key's
verifier reads the word at place 0, the proof's at place 1. The link has one round, in which the
prover sends two trees and the verifier draws a block; its verifier reads both words at place 0 and
the prover's string at the drawn place.

Limits: a test of one thing alone: that the premises of `three_arms` can be met together. IT SHOWS
NOTHING ON THE NUMBER: hash values have one bit, so each term of the bound is at least 1
(`one_le_term`, Johnson/TypedOracleCompiler/Joined/ToyArms.lean). All errors of the three protocols are 0: each
verifier decides its language outright, and what it reads of the prover's strings adds nothing to
soundness. Every type of witnesses is Unit. The conditions on the wires are shown at one wire
record. The second and the third coding are the first with two strings swapped, by their definitions
(no theorem counts where they differ); none is the programs'; they are made by a choice principle.
The test on the number of the stored copy always says yes; a table's name holds its root alone. The
three checks are the lax ones (`armTL`, `armL`, `armBL`): the strict ones are not applied here. It
is not shown that any of the three checks accepts anything.

Terms: lean/GLOSSARY.md.
-/
import Johnson.TypedOracleCompiler.Joined.ToyArms
import OnBytes.TypedOracleCompiler.Joined.CodePerm

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.Toy
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (KnowLate)
open scoped ENNReal

/-! ## Words, tests, the decoder -/

/-- a word: two bits -/
abbrev Wd : Type := Fin 2 → Bool

/-- the key's test: the seed is no collision seed, and the word's first bit is the answer -/
def gT (r : Rec0) (y : Wd) : Bool := !(r.1 0 0) && (y 0 == r.2)

/-- the proof's test: the instance's first bit is the answer, its second bit is true, and the word's
second bit is the answer -/
def gB (a : Y2 × Rec0) (y : Wd) : Bool := (a.1.1 == a.2.2) && a.1.2 && (y 1 == a.2.2)

/-- the decoder reads the word and its record -/
def decX (y : Wd) (r : Rec0) : Option Bool := if gT r y then some r.2 else none

theorem gT_congr (r : Rec0) {y y' : Wd} (h : y 0 = y' 0) : gT r y = gT r y' := by
  unfold gT
  rw [h]

theorem gB_congr (a : Y2 × Rec0) {y y' : Wd} (h : y 1 = y' 1) : gB a y = gB a y' := by
  unfold gB
  rw [h]

theorem decX_congr (r : Rec0) {y y' : Wd} (h : y 0 = y' 0) : decX y r = decX y' r := by
  unfold decX
  rw [gT_congr r h]

theorem decX_of_coll {y : Wd} {r : Rec0} (h : coll0 r.1) : decX y r = none := by
  have h' : r.1 0 0 = true := h
  unfold decX gT
  rw [h']
  rfl

/-! ## A file of three chains with a test on statement and word -/

section File
variable {A : Type} (g : A → Wd → Bool) (er : Finset (Fin 2))

/-- The file's verifier: the test, and chain 1's string holds true at both places. -/
@[reducible] def Dg : Desc G A (oneExternalString 2 Bool) where
  blinded := fun _ => false
  extReads := fun _ _ => er
  reads := fun _ ρ _ => {p₁ ρ, p₃ ρ}
  accept := fun a y τ =>
    g a y && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)

theorem isLocalg (hg : ∀ a (y y' : Wd), (∀ p ∈ er, y p = y' p) → g a y = g a y') :
    (Dg g er).proto.IsLocal := by
  intro a y y' τ τ' hρ _ hy hr
  have h1 : str₁ τ (bit (G.rho₁ τ.rho).1) = str₁ τ' (bit (G.rho₁ τ.rho).1) :=
    hr _ (Finset.mem_insert_self _ _)
  have h3 : str₁ τ (bit (G.rho₃ τ.rho).1) = str₁ τ' (bit (G.rho₃ τ.rho).1) :=
    hr _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  show (g a y && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)) =
    (g a y' && str₁ τ' (bit (G.rho₁ τ'.rho).1) && str₁ τ' (bit (G.rho₃ τ'.rho).1))
  rw [h1, h3, hρ, hg a y y' hy]

/-- The three chains' descriptions of the file, made of its verifier's tests. -/
@[reducible] def Cg : Links G (A × (oneExternalString 2 Bool).Str) where
  A₁ := Fin 2 → Bool
  A₂ := Fin 2 → Bool
  W₀ := Unit
  W₁ := Unit
  W₂ := Unit
  out₁ := fun a τ => if g a.1 a.2 && sOf τ (bit (bOf₁ τ)) then some (sOf τ) else none
  out₂ := fun o _ => some o
  out₃ := fun o τ => if o (bit (bOf₃ τ)) then some () else none
  on₀ := fun _ => True
  on₁ := fun _ => True
  on₂ := fun _ => True
  R₀ := fun a _ => g a.1 a.2 = true
  R₁ := fun _ _ => True
  R₂ := fun _ _ => True
  e₁ := fun _ _ _ => ()
  e₂ := fun _ _ _ => ()
  e₃ := fun _ _ _ => ()
  ε₁ := err0 _
  ε₂ := err0 _
  ε₃ := err0 _
  d₀ := ()
  d₁ := ()

theorem knowsg : (Cg g).Knows where
  know₁ := fun a _ => Doomed.of_forall _ _ fun τ b _ h _ => by
    have h' : (if (g a.1 a.2 && sOf τ (bit (bOf₁ τ))) = true then some (sOf τ) else none) =
        some b := h
    by_cases hc : (g a.1 a.2 && sOf τ (bit (bOf₁ τ))) = true
    · exact (Bool.and_eq_true_iff.1 hc).1
    · rw [if_neg hc] at h'
      cases h'
  know₂ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  know₃ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

theorem knowsLateg (e : A → A) : (Cg g).KnowsLate e 1 where
  know₁ := fun _ y => JDoomed.of_forall _ _ _ fun φ τ _ b _ h _ => by
    have h' : (if (g φ.1 y && sOf τ (bit (bOf₁ τ))) = true then some (sOf τ) else none) =
        some b := h
    by_cases hc : (g φ.1 y && sOf τ (bit (bOf₁ τ))) = true
    · exact (Bool.and_eq_true_iff.1 hc).1
    · rw [if_neg hc] at h'
      cases h'
  know₂ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  know₃ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

/-- No chain of the description rejects exactly where the file's verifier accepts. -/
theorem isSome_allg_iff (a : A) (y : (oneExternalString 2 Bool).Str) (τ : Tr G.sh) :
    ((Cg g).all.out (a, y) τ).isSome = true ↔ (Dg g er).accept a y τ = true := by
  show ((if (g a y && str₁ τ (bit (G.rho₁ τ.rho).1)) = true then some (str₁ τ) else none).bind
      fun b => (some b).bind fun c =>
        if c (bit (G.rho₃ τ.rho).1) = true then some () else none).isSome = true ↔
    (g a y && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)) = true
  cases hp : (g a y && str₁ τ (bit (G.rho₁ τ.rho).1)) <;>
    cases hq : str₁ τ (bit (G.rho₃ τ.rho).1) <;> simp [hq]

theorem decidesg (a : A) (y : (oneExternalString 2 Bool).Str) (τ : Tr G.sh)
    (h : (Dg g er).accept a y τ = true) : ((Cg g).all.out (a, y) τ).isSome = true :=
  (isSome_allg_iff g er a y τ).2 h

/-- The language of the file: the test. -/
theorem lgg_iff (a : A) (y : (oneExternalString 2 Bool).Str) : (Cg g).Lg id a y ↔ g a y = true :=
  ⟨fun h => (h trivial).elim fun _ hw => hw, fun h _ => ⟨(), h⟩⟩

/-- What the file's verifier accepts passes the test. -/
theorem g_of_accept {a : A} {y : (oneExternalString 2 Bool).Str} {τ : Tr G.sh}
    (h : (Dg g er).accept a y τ = true) : g a y = true := by
  have h' : (g a y && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)) = true := h
  exact (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').1).1

end File

/-- the key's file; the proof's file -/
abbrev DTX : Desc G Rec0 (oneExternalString 2 Bool) := Dg gT {0}
abbrev DBX : Desc G (Y2 × Rec0) (oneExternalString 2 Bool) := Dg gB {1}

theorem isLocalTX : DTX.proto.IsLocal :=
  isLocalg gT {0} fun r _ _ h => gT_congr r (h 0 (Finset.mem_singleton_self _))

theorem isLocalBX : DBX.proto.IsLocal :=
  isLocalg gB {1} fun a _ _ h => gB_congr a (h 1 (Finset.mem_singleton_self _))

/-! ## The link: one round -/

/-- the language of the link -/
def linkLgX (rr : Rec0 × Rec0) (y : Wd × Wd) : Prop :=
  decX y.1 rr.1 = none ∨ coll0 rr.2.1 ∨ decX y.2 rr.2 = decX y.1 rr.1

instance (rr : Rec0 × Rec0) (y : Wd × Wd) : Decidable (linkLgX rr y) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The link: the prover sends two bits and one more bit, the verifier draws a block; it accepts its
language where the prover's string holds true at the drawn place. -/
@[reducible] def pLkX : InteractiveOracleProof (Rec0 × Rec0) (twoExternalStrings 2 Bool) where
  shape := [rB]
  blinded := fun _ => false
  extReads := fun _ _ => {.inl 0, .inr 0}
  reads := fun _ ρ _ => {.inl (.inl (bit ρ.1))}
  accept := fun rr y τ => decide (linkLgX rr y) && τ.1.1.1 (bit τ.2.1)

theorem linkLgX_congr (rr : Rec0 × Rec0) {y y' : Wd × Wd} (h1 : y.1 0 = y'.1 0)
    (h2 : y.2 0 = y'.2 0) : linkLgX rr y ↔ linkLgX rr y' := by
  unfold linkLgX
  rw [decX_congr rr.1 h1, decX_congr rr.2 h2]

theorem isLocalLkX : pLkX.IsLocal := by
  intro rr y y' τ τ' hρ _ hy hr
  have e1 : y.1 0 = y'.1 0 := hy (.inl 0) (Finset.mem_insert_self _ _)
  have e2 : y.2 0 = y'.2 0 :=
    hy (.inr 0) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hc : τ.2.1 = τ'.2.1 := congrArg Prod.fst hρ
  have h1 : τ.1.1.1 (bit τ.2.1) = τ'.1.1.1 (bit τ.2.1) := hr _ (Finset.mem_singleton_self _)
  show (decide (linkLgX rr y) && τ.1.1.1 (bit τ.2.1)) =
    (decide (linkLgX rr y') && τ'.1.1.1 (bit τ'.2.1))
  rw [h1, hc, decide_eq_decide.2 (linkLgX_congr rr e1 e2)]

/-! ## The interface with records -/

@[reducible] def LRX : HolographicProtocol Bool Y2 where
  wordLength := 2
  Symbol := Bool
  EncodingRandomness := Unit
  encodeIndex := fun i _ _ => i
  OutOfDomainSeed := Seed0
  OutOfDomainAnswer := Bool
  honestOutOfDomainAnswer := fun i _ _ => i
  hasCollisionAt := fun _ s => coll0 s
  decodeIndex := decX
  offline := DTX.proto
  link := pLkX
  maxBatchSize := 2
  onlineBatch := DBX.batch
  honestOfflineProver := _root_.Run.dummyH DTX.proto fun _ _ => false
  honestLinkProver := _root_.Run.dummyH pLkX fun _ => (fun _ => false, fun _ => false)
  honestOnlineBatchProver := _root_.Run.dummyB DBX.batch fun _ _ => false
  early := early
  late := some 1

/-- the annotation of the link's round: local -/
abbrev aLX : RoundSplits LRX.link.shape := RoundSplits.allLocal [rB]

theorem sndLX : LRX.link.Sound
    (fun rr y => LRX.decodeIndex y.1 rr.1 = none ∨ LRX.hasCollisionAt y.2 rr.2.1 ∨
      LRX.decodeIndex y.2 rr.2 = LRX.decodeIndex y.1 rr.1) (err0 [rB]) :=
  fun rr y h => Doomed.of_forall _ _ fun τ => by
    show (decide (linkLgX rr y) && τ.1.1.1 (bit τ.2.1)) = false
    rw [decide_eq_false (p := linkLgX rr y) h]
    rfl

theorem noneCollX (y : Wd) (rec : LRX.Rec) (h : LRX.hasCollisionAt y rec.1) : LRX.decodeIndex y rec = none :=
  decX_of_coll h

theorem rcdX (y : Wd) : cnt (fun s => LRX.hasCollisionAt y s) ≤ 1 :=
  cnt_le_one fun a b ha hb => funext fun i => funext fun j => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact (show a 0 0 = true from ha).trans (show b 0 0 = true from hb).symm

theorem tieTX (rec : LRX.Rec) (y : (oneExternalString 2 Bool).Str) (h : (Cg gT).Lg id rec y) :
    LRX.hasCollisionAt y rec.1 ∨ LRX.decodeIndex y rec ≠ none := by
  refine Or.inr ?_
  show decX y rec ≠ none
  unfold decX
  rw [if_pos ((lgg_iff gT rec y).1 h)]
  exact Option.some_ne_none _

theorem tieBX (x : Y2) (rec : LRX.Rec) (y : (oneExternalString 2 Bool).Str) (τ : Tr G.sh)
    (h : DBX.accept (x, rec) y τ = true) : LRX.relB Rn rec x y () := by
  have hb : ((x.1 == rec.2) && x.2 && (y 1 == rec.2)) = true := g_of_accept gB {1} h
  have h2 := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hb).1
  cases hc : gT rec y with
  | false => exact Or.inl (if_neg (by rw [hc]; exact Bool.false_ne_true))
  | true => exact Or.inr ⟨rec.2, if_pos hc, beq_iff_eq.1 h2.1, h2.2⟩

theorem soundAtX : LRX.SoundAtR Rn (fun _ _ _ => ()) 1 (Cg gT).err (err0 [rB])
    ((Cg gB).errN LRX.maxBatchSize) :=
  soundAtR_of_files_late LRX DTX DBX (CT := Cg gT) (CB := Cg gB) Rn (fun _ _ _ => ()) 1 (err0 [rB])
    rfl rfl 1 rfl noneCollX rcdX sndLX (knowsg gT) (decidesg gT {0}) tieTX laws
    (knowsLateg gB fun a : Y2 × Rec0 => (early a.1, a.2))
    (fun x r y τ h => decidesg gB {1} (x, r) y τ h)
    early_idem Nat.one_pos (Nat.le_refl 1) fun x rec y τ h _ => tieBX x rec y τ h

/-! ## The wire records -/

instance decOL : DecidableEq (OPos [rB]) :=
  inferInstanceAs (DecidableEq ((Fin 2 ⊕ Unit) ⊕ Empty))

/-- the body of a leaf: a symbol of a file's string, of the link's string, or of a word -/
abbrev BdX : Type := (Σ p : OPos G.sh, OSym G.sh p) ⊕ (Σ p : OPos [rB], OSym [rB] p) ⊕ Bool

def prjGX (p : OPos G.sh) : BdX → Option (OSym G.sh p)
  | .inl z => if h : z.1 = p then some (h ▸ z.2) else none
  | _ => none

def prjLX (p : OPos [rB]) : BdX → Option (OSym [rB] p)
  | .inr (.inl z) => if h : z.1 = p then some (h ▸ z.2) else none
  | _ => none

def prjEX : BdX → Option Bool
  | .inr (.inr b) => some b
  | _ => none

/-- the wire record of one word: place p of the word is leaf p of tree 0, of depth 1 -/
def we1X : WireE (oneExternalString 2 Bool) where
  all := [0, 1]
  which := fun _ => 0
  leaf := fun p => p.val
  depth := 1
  build := fun f p => (f p).getD false
  dec := inferInstanceAs (DecidableEq (Fin 2))

theorem we1X_ok : we1X.OK :=
  ⟨by decide, fun p => by
    show p ∈ [(0 : Fin 2), 1]
    fin_cases p <;> simp, fun f p a h => by
    show (f p).getD false = a
    rw [h]
    rfl⟩

/-- the wire record of two words: the first under tree 0, the further under tree 1 -/
def we2X : WireE (twoExternalStrings 2 Bool) where
  all := [.inl 0, .inl 1, .inr 0, .inr 1]
  which := fun p => p.elim (fun _ => 0) fun _ => 1
  leaf := fun p => p.elim (fun q => q.val) fun q => q.val
  depth := 1
  build := fun f => (fun p => (f (.inl p)).getD false, fun p => (f (.inr p)).getD false)
  dec := inferInstanceAs (DecidableEq (Fin 2 ⊕ Fin 2))

theorem we2X_ok : we2X.OK :=
  ⟨by decide, fun p => by
    show p ∈ [(Sum.inl 0 : Fin 2 ⊕ Fin 2), .inl 1, .inr 0, .inr 1]
    rcases p with p | p <;> fin_cases p <;> simp, fun f p a h => by
    rcases p with p | p
    · show (f (.inl p)).getD false = a
      rw [h]
      rfl
    · show (f (.inr p)).getD false = a
      rw [h]
      rfl⟩

/-- The wire record of the whole: blocks of one bit, one block a query; the trees over the words
have depth 1; at most three openings. -/
@[reducible] def WRX : QueryLayout 1 (typedOracleCarrier LRX BdX G.ann aLX) where
  K := 1
  T := ⟨V.sh, we1X, decO, 3, 1⟩
  Lk := ⟨(wA₁, ()), we2X, decOL, 3, 1⟩
  B := ⟨V.sh, we1X, decO, 3, 1⟩
  depth := 1
  depthReq := 1
  depthReqT := 0
  depthReqL := 0
  embE := fun b => .inr (.inr b)
  prjE := prjEX
  embT := fun p a => .inl ⟨p, a⟩
  prjT := prjGX
  embL := fun p a => .inr (.inl ⟨p, a⟩)
  prjL := prjLX
  embB := fun p a => .inl ⟨p, a⟩
  prjB := prjGX

theorem card_readsX (ρ : Rho G.sh) (q : Fin 2) :
    (({p₁ ρ, p₃ ρ} : Finset (OPos G.sh))).card + ({q} : Finset (Fin 2)).card ≤ 3 := by
  rw [Finset.card_singleton]
  exact Nat.add_le_add_right Finset.card_le_two 1

theorem card_readsLX (p : OPos [rB]) :
    (({p} : Finset (OPos [rB]))).card + ({.inl 0, .inr 0} : Finset (Fin 2 ⊕ Fin 2)).card ≤ 3 := by
  rw [Finset.card_singleton]
  exact Nat.add_le_add_left Finset.card_le_two 1

theorem okgTX : (wTC WRX).OKG :=
  ⟨V.sh_okg V_okg, we1X_ok, fun _ ρ _ => card_readsX ρ 0, V.sh_depthLe V_depthLe⟩

theorem okgLX : (wLC WRX).OKG :=
  ⟨⟨wA₁_okg, trivial⟩, we2X_ok, fun _ _ _ => card_readsLX _, ⟨⟨le_nil 1, le_one_zero⟩, trivial⟩⟩

theorem okgBX : (wBC WRX).OKG :=
  ⟨V.sh_okg V_okg, we1X_ok, fun _ ρ _ => card_readsX ρ 1, V.sh_depthLe V_depthLe⟩

theorem oktaX : OKTA WRX :=
  ⟨okgTX, we1X_ok, fun _ => rfl, fun _ _ => dif_pos rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem oklaX : OKLA WRX :=
  ⟨okgLX, we1X_ok, fun _ => rfl, fun _ _ => dif_pos rfl, rfl,
    ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩⟩

theorem okbaX : OKBA WRX :=
  ⟨okgBX, we1X_ok, fun _ => rfl, fun _ _ => dif_pos rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl⟩

/-! ### controls: each bundle fails where a word's place in its tree is spoilt -/

/-- a word's wire record that puts both places on leaf 0 -/
def we1Bad : WireE (oneExternalString 2 Bool) := { we1X with leaf := fun _ => 0 }

/-- two words' wire record that puts both words under tree 0 -/
def we2Bad : WireE (twoExternalStrings 2 Bool) := { we2X with which := fun _ => 0 }

def WRXbadT : QueryLayout 1 (typedOracleCarrier LRX BdX G.ann aLX) := { WRX with T := ⟨V.sh, we1Bad, decO, 3, 1⟩ }
def WRXbadL : QueryLayout 1 (typedOracleCarrier LRX BdX G.ann aLX) :=
  { WRX with Lk := ⟨(wA₁, ()), we2Bad, decOL, 3, 1⟩ }
def WRXbadB : QueryLayout 1 (typedOracleCarrier LRX BdX G.ann aLX) := { WRX with B := ⟨V.sh, we1Bad, decO, 3, 1⟩ }

theorem not_oktaX : ¬ OKTA WRXbadT := fun h => absurd (h.extT (1 : Fin 2)).2 (by decide)

theorem not_oklaX : ¬ OKLA WRXbadL := fun h => absurd (h.extL.2 (0 : Fin 2)).1 (by decide)

theorem not_okbaX : ¬ OKBA WRXbadB := fun h => absurd (h.extB (1 : Fin 2)).2 (by decide)

/-! ### each verifier's verdict turns with the word -/

/-- a record with a seed that is no collision seed, and the answer true -/
def recT : Rec0 := (fun _ _ => false, true)

theorem reads_word_T :
    DTX.accept recT (fun _ => true) (trOf (fun _ => true) fun _ _ => false) = true ∧
      DTX.accept recT (fun _ => false) (trOf (fun _ => true) fun _ _ => false) = false :=
  ⟨rfl, rfl⟩

theorem reads_word_B :
    DBX.accept ((true, true), recT) (fun _ => true) (trOf (fun _ => true) fun _ _ => false) = true ∧
      DBX.accept ((true, true), recT) (fun _ => false) (trOf (fun _ => true) fun _ _ => false) =
        false :=
  ⟨rfl, rfl⟩

/-- a transcript of the link: the string of ones, the block of zeros -/
def trLk : Tr [rB] := (((fun _ => true, false), ()), fun _ _ => false, ())

theorem reads_word_L :
    pLkX.accept (recT, recT) (fun _ => true, fun _ => true) trLk = true ∧
      pLkX.accept (recT, recT) (fun _ => true, fun _ => false) trLk = false :=
  ⟨by decide, by decide⟩

/-! ## The seeds, the answers, a coding -/

@[reducible] def SRX : OutOfDomainSampleQueryLayout 1 WRX.K LRX BdX G.ann aLX where
  t := .onl
  cfg := []
  shape := []
  pl0 := .inl (.inr ())
  pl1 := .inl (.inr ())
  seed := id
  code := fun r => [r.1 0, fun _ => r.2]
  num := fun _ _ => true
  decS := inferInstance

theorem hSdX : SRX.Law (1 / 2) := fun y => by
  have h := (pr_unif_le_iff_cnt_le (fun s : Seed0 => coll0 s) 1).2 (rcdX y)
  rw [card_seed0] at h
  simpa using h

def cAX : LRX.OutOfDomainAnswer → List (Dig 1) := fun b => [fun _ => b]

theorem ansOKX : AnsOK (L := LRX) cAX :=
  ⟨fun _ _ h => congrFun (List.cons.inj h).1 0, fun _ _ => rfl⟩

/-- positions, symbols and plain parts of the link's round are countable -/
theorem ctbL : CtbS [rB] aLX :=
  ⟨⟨inferInstanceAs (Countable (Fin 2 ⊕ Unit)), fun _ => inferInstanceAs (Countable Bool),
    inferInstanceAs (Countable Unit), inferInstanceAs (Countable Unit)⟩, trivial⟩

/-- the carrier of the typed oracles -/
abbrev CX : BatchProtocolWithLeafBody Empty LRX.XC := typedOracleCarrier LRX BdX G.ann aLX

theorem ctbAllX (t : Tag) : CtbS (shapeOf CX t) (annOf CX t) := by
  cases t
  · exact ctbG
  · exact ctbL
  · exact ctbG

theorem countable_realX : Countable (RealPts 1 WRX.K CX) ∧ Countable (GhostPts 1 WRX.K CX) :=
  haveI : Countable (_root_.Compile.SymAny G.sh) := _root_.Compile.Batch.countable_symAny _ _ ctbG
  haveI : Countable (_root_.Compile.SymAny [rB]) := _root_.Compile.Batch.countable_symAny _ _ ctbL
  countable_pts 1 WRX.K CX (inferInstanceAs (Countable (Option Y2 × Rec0 × Rec0)))
    (inferInstanceAs (Countable
      (_root_.Compile.SymAny G.sh ⊕ _root_.Compile.SymAny [rB] ⊕ Bool))) ctbAllX

/-- a code of strings of the points of the scheme's own oracles; of the analysis's further names -/
def cX : StrCode (RealPts 1 WRX.K CX) :=
  haveI := countable_realX.1
  StrCode.ofCountable _

def cGX : StrCode (GhostPts 1 WRX.K CX) :=
  haveI := countable_realX.2
  StrCode.ofCountable _

/-- the point of a Fiat-Shamir query of the session's tag, with the number of a hash block -/
def fbP (q : FbIn 1 CX .onl) (j : Fin 2) : RealPts 1 WRX.K CX :=
  .inr (.inr (.inr (.inr (.inl ⟨.onl, q, j⟩))))

theorem fbP_inj {q q' : FbIn 1 CX .onl} {j j' : Fin 2} (h : fbP q j = fbP q' j') : q = q' := by
  simp only [fbP, Sum.inr.injEq, Sum.inl.injEq, Sigma.mk.injEq, heq_eq_eq, true_and,
    Prod.mk.injEq] at h
  exact h.1

/-- three Fiat-Shamir queries of the kind with which each of the three checks begins (`outOfDomainSeedIs`): the
first seed query at two roots; a second seed query -/
def q0 : FbIn 1 CX .onl := seedQ0 WRX SRX fun _ => false
def q1 : FbIn 1 CX .onl := seedQ0 WRX SRX fun _ => true
def q2 : FbIn 1 CX .onl := seedQ1 WRX SRX []

theorem q0_ne_q1 : q0 ≠ q1 := fun h =>
  Bool.noConfusion (congrFun (seedQ0_inj (W := WRX) (S := SRX) h) 0)

theorem q0_ne_q2 : q0 ≠ q2 := fun h => absurd (congrArg FbIn.round h) (by decide)

theorem q1_ne_q2 : q1 ≠ q2 := fun h => absurd (congrArg FbIn.round h) (by decide)

open Classical in
/-- the coding in which the strings of the first hash blocks of two Fiat-Shamir queries are swapped
-/
def mSw (q q' : FbIn 1 CX .onl) : OracleCoding (typedOracleFamily 1 WRX.K CX) 1 :=
  implOf 1 WRX.K CX (permCode cX (Equiv.swap (fbP q 0) (fbP q' 0))) cGX

/-- Three codings, one for each check: the key file's, the entry file's and the proof file's -/
def mX : OracleCoding (typedOracleFamily 1 WRX.K CX) 1 := implOf 1 WRX.K CX cX cGX
def mX1 : OracleCoding (typedOracleFamily 1 WRX.K CX) 1 := mSw q0 q1
def mX2 : OracleCoding (typedOracleFamily 1 WRX.K CX) 1 := mSw q0 q2

/-- They agree on the leaf and node oracles. -/
theorem sameTrees_sw (q q' : FbIn 1 CX .onl) : SameTrees WRX mX (mSw q q') := by
  classical
  refine ⟨fun x _ _ => ?_, fun x _ _ => ?_, fun _ => rfl, fun _ => rfl⟩
  · show true :: cX.put (.inl x) = true :: cX.put (Equiv.swap (fbP q 0) (fbP q' 0) (.inl x))
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [fbP]) (by simp [fbP])]
  · show true :: cX.put (.inr (.inl x)) =
      true :: cX.put (Equiv.swap (fbP q 0) (fbP q' 0) (.inr (.inl x)))
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [fbP]) (by simp [fbP])]

/-- the first hash block of a Fiat-Shamir answer -/
def j0 : Fin 2 := 0

/-- how the swapped coding writes the first of the two queries -/
theorem code_sw (q q' : FbIn 1 CX .onl) :
    (mSw q q').code (OracleName.fb .onl) q j0 = true :: cX.put (fbP q' 0) := by
  classical
  show true :: cX.put (Equiv.swap (fbP q 0) (fbP q' 0) (fbP q 0)) = _
  rw [Equiv.swap_apply_left]

/-- **The three codings differ, pair by pair**: they write the first seed query at one root, which
a check asks where it is handed that root, as three strings. -/
theorem codings_differ :
    mX.code (OracleName.fb .onl) q0 j0 ≠ mX1.code (OracleName.fb .onl) q0 j0 ∧
      mX.code (OracleName.fb .onl) q0 j0 ≠ mX2.code (OracleName.fb .onl) q0 j0 ∧
      mX1.code (OracleName.fb .onl) q0 j0 ≠ mX2.code (OracleName.fb .onl) q0 j0 := by
  have e0 : mX.code (OracleName.fb .onl) q0 j0 = true :: cX.put (fbP q0 0) := rfl
  have e1 : mX1.code (OracleName.fb .onl) q0 j0 = true :: cX.put (fbP q1 0) := code_sw q0 q1
  have e2 : mX2.code (OracleName.fb .onl) q0 j0 = true :: cX.put (fbP q2 0) := code_sw q0 q2
  rw [e0, e1, e2]
  exact ⟨fun h => q0_ne_q1 (fbP_inj (put_inj cX (List.cons.inj h).2)),
    fun h => q0_ne_q2 (fbP_inj (put_inj cX (List.cons.inj h).2)),
    fun h => q1_ne_q2 (fbP_inj (put_inj cX (List.cons.inj h).2))⟩

/-- **Every hypothesis of `three_arms` but hC and hP is met at an interface whose three protocols
read the encoded index, at one wire record and three codings that differ**: the theorem applied with
hC and hP alone left: for every committer and every prover with bounded queries. -/
theorem toy_three_arms_ext {St : Type} (Ct : OComp (rom 1) ((Dig 1 × LRX.Rec) × St))
    (Pt : St → OComp (rom 1) (OutP3 1 LRX G.ann aLX)) (tC tP : ℕ) (hC : Ct.QueryBound tC)
    (hP : ∀ st, (Pt st).QueryBound tP) :
    Rom.Pr (exp3A WRX (armTL WRX SRX cAX) (armL WRX SRX cAX) (armBL WRX SRX cAX recT) mX mX1 mX2
          Ct Pt)
        (fun _ => {x | x.2.2.1 = true ∧ x.2.2.2.1 = true ∧ x.2.2.2.2 = true ∧
          ¬ ∃ i, LRX.decodeIndex (extEnc WRX (singleTr mX x.1.2) x.1.1.1.1) x.1.1.1.2 = some i ∧
            ∃ w, Rn i x.2.1.1.2.2.1 w}) ≤
      ((((tC + tP + 1 + tVT WRX) * (1 + 2) : ℕ) : ℝ≥0∞) * (1 / 2) +
        2 * (((tC + tP + 1 + tVT WRX) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 1) +
      (((((tC + tP + 1 + tVL WRX) * (1 + 4) : ℕ) : ℝ≥0∞) * (1 / 2) +
        2 * (((tC + tP + 1 + tVL WRX) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 1) +
      ((((tC + tP + tVB WRX) * (1 + 2) : ℕ) : ℝ≥0∞) * (1 / 2) +
        2 * (((tC + tP + tVB WRX) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 1)) :=
  three_arms Rn (fun _ _ _ => ()) soundAtX.sndT (isLocal_of_eq LRX.offline rfl isLocalTX)
    (coherent_of_test DTX laws LRX.offline rfl G.ann HEq.rfl) oktaX (below_err0 _ G.sh)
    (isArmT_armTL WRX SRX cAX) soundAtX.sndL isLocalLkX
    (Iop.BatchOne.BAnn.allLocal_coherent [rB]) oklaX
    (below_err0 _ [rB]) (isArm_armL WRX SRX cAX) (headSeeds_armL SRX cAX) soundAtX.sndB
    (isLocal_of_eq LRX.onlineBatch.loc (congrArg BatchInteractiveOracleProof.loc rfl) isLocalBX)
    (coherent_of_bat DBX laws LRX.onlineBatch rfl) okbaX (below_err0 _ G.sh)
    (isArmB_armBL WRX SRX cAX recT) (headSeedB_armBL SRX cAX recT) ansOKX hSdX Nat.one_pos mX mX1
    mX2 (sameTrees_sw _ _) (sameTrees_sw _ _) Ct Pt tC tP hC hP

end TypedOracleCompiler.Joined.Toy
