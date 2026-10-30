-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/ToyOwes.lean: a test: AT THE SMALL WHOLE FILE OF
Johnson/Prover/Print/ToyRun.lean ALL PREMISES OF whole_prints (OnBytes/Prover/Print/Owed.lean) ARE
MET TOGETHER, at the compiled prover's own value: so that theorem bites somewhere.

Main names.
  coins_toy    CoinsPrint at the toy's byte coins.
  okg_toy, fewJ_toy, few0_toy   the wire record's laws and the two counts, at the toy's kit.
  GoodF, GoodW, chkC, chkX   the clauses of WholeOwes in forms that Lean can decide: the fronts ·
    the plain parts' words · the opened columns over all positions · the outer tree at all places.
  good_F, good_W, good_C, good_X   the prover returns a value, and the four hold of it: by
    evaluation in Lean's kernel.
  bad_X, bad_word   the tests can say no.
  owes_of_good WholeOwes from the four.
  bites        whole_prints' conclusion at that value: Printable, Canon, the run values not zero.

Limits: a test at one family of oracle functions, one strategy, a toy kit of verifier's messages.
Nothing at the letters of the full size: GoodOwes and RunsOwe (Johnson/Prover/Print/) have no member
here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.ToyRun
import OnBytes.Prover.Print.Owed
import OnBytes.Maker.WireLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Print.ToyRun

open _root_.Run _root_.Run.PQ Compile.Joined Rom
open _root_.Compile (Tag Opening pathOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃ FewJ Few0)
open OnBytes.Maker OnBytes.Maker.Carrier
open OnBytes.Prover OnBytes.Prover.Print

/-! ## The coins, the wire record -/

theorem size_pattern (n a b : ℕ) : (_root_.Fmt.pattern n a b).size = n := by
  unfold _root_.Fmt.pattern
  exact Array.size_ofFn

theorem coins_toy : CoinsPrint (bc r1) 2 sB where
  fit :=
    { run1 := size_pattern _ _ _, run2 := size_pattern _ _ _, run3 := size_pattern _ _ _
      leaf := fun _ _ _ _ => size_pattern _ _ _
      place := by decide
      slotPath := rfl
      slotSalt := size_pattern _ _ _ }
  salt64 := by decide
  ok1 := by decide +kernel
  ok2 := by decide +kernel
  ok3 := by decide +kernel

theorem nb_le (k : _root_.Fmt.Kind) : nb k ≤ 1 := by cases k <;> decide

theorem chalUnif_toy (ds : List RDT) : ChalUnifT Ct 1 chal ds := fun d _ =>
  map_firstBlocks_unif (Dig 256) (fun _ => false) (nb d.kind) 1 (nb_le d.kind)

theorem drawnFits_toy (ds : List RDT) : DrawnFitsT Ct ds := fun d _ c => by
  show ((List.range d.entry.poss).map _).length ≤ d.entry.poss
  rw [List.length_map, List.length_range]

theorem okg_toy : wq.OKG :=
  wqWhole_okg Ct 1 chal D tF tJ t3 sil rn (chalUnif_toy _) (chalUnif_toy _) (chalUnif_toy _)
    (by decide) (by decide) (by decide) (drawnFits_toy _) (drawnFits_toy _) (drawnFits_toy _)

theorem fewJ_toy : FewJ Q.loc.shape Q.ann wq.sh := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> decide

theorem few0_toy : Few0 Q.loc.shape Q.ann wq.sh := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> decide

/-! ## WholeOwes' clauses, in a form that Lean decides -/

instance (x : UInt64) : Decidable (Carrier.okF x) :=
  inferInstanceAs (Decidable (x.toNat < _root_.Fmt.Fld.two.p))
instance (e : _root_.Fmt.Ext) : Decidable (Carrier.okE e) :=
  inferInstanceAs (Decidable (e.1.toNat < _root_.Fmt.Fld.two.p ∧
    e.2.1.toNat < _root_.Fmt.Fld.two.p ∧ e.2.2.toNat < _root_.Fmt.Fld.two.p))

instance decCanonI : (l : List _root_.Fmt.Item) → (x : PlainOf l) → Decidable (CanonI l x)
  | [], _ => isTrue trivial
  | .root :: l, x => decCanonI l x
  | .f :: l, (x : UInt64 × PlainOf l) =>
    haveI := decCanonI l x.2
    inferInstanceAs (Decidable (Carrier.okF x.1 ∧ CanonI l x.2))
  | .word :: l, (x : UInt64 × PlainOf l) => decCanonI l x.2
  | .e :: l, (x : _root_.Fmt.Ext × PlainOf l) =>
    haveI := decCanonI l x.2
    inferInstanceAs (Decidable (Carrier.okE x.1 ∧ CanonI l x.2))
  | .answer :: l, (x : _root_.Fmt.Ext × PlainOf l) =>
    haveI := decCanonI l x.2
    inferInstanceAs (Decidable (Carrier.okE x.1 ∧ CanonI l x.2))

instance decWordsP : (ds : List RDT) → (pl : Plains (uLT Ct ds)) → Decidable (WordsP Ct ds pl)
  | [], _ => isTrue trivial
  | d :: ds, (pl, r) =>
    haveI := decWordsP ds r
    inferInstanceAs (Decidable (CanonI d.items
      (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl) ∧ WordsP Ct ds r))

/-- all positions of the three stretches -/
def allA : List (OPos (uLT Ct D.ds₁)) :=
  [.inl (.inl ⟨0, by decide⟩), .inl (.inl ⟨1, by decide⟩), .inl (.inr (.inl ⟨0, by decide⟩))]
def allB : List (OPos (uLT Ct D.ds₂)) := [.inl (.inl ⟨0, by decide⟩), .inl (.inl ⟨1, by decide⟩)]
def allC : List (OPos (uLT Ct D.ds₃)) := [.inl (.inl ⟨0, by decide⟩), .inl (.inl ⟨1, by decide⟩)]

theorem memA : ∀ q : OPos (uLT Ct D.ds₁), q ∈ allA
  | .inl (.inl ⟨0, _⟩) => List.mem_cons_self
  | .inl (.inl ⟨1, _⟩) => List.mem_cons_of_mem _ List.mem_cons_self
  | .inl (.inl ⟨n + 2, h⟩) => absurd (show n + 2 < 2 from h) (by omega)
  | .inl (.inr (.inl ⟨0, _⟩)) =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | .inl (.inr (.inl ⟨n + 1, h⟩)) => absurd (show n + 1 < 1 from h) (by omega)
  | .inl (.inr (.inr e)) => nomatch e
  | .inr e => nomatch e

theorem memB : ∀ q : OPos (uLT Ct D.ds₂), q ∈ allB
  | .inl (.inl ⟨0, _⟩) => List.mem_cons_self
  | .inl (.inl ⟨1, _⟩) => List.mem_cons_of_mem _ List.mem_cons_self
  | .inl (.inl ⟨n + 2, h⟩) => absurd (show n + 2 < 2 from h) (by omega)
  | .inl (.inr e) => nomatch e
  | .inr e => nomatch e

theorem memC : ∀ q : OPos (uLT Ct D.ds₃), q ∈ allC
  | .inl (.inl ⟨0, _⟩) => List.mem_cons_self
  | .inl (.inl ⟨1, _⟩) => List.mem_cons_of_mem _ List.mem_cons_self
  | .inl (.inl ⟨n + 2, h⟩) => absurd (show n + 2 < 2 from h) (by omega)
  | .inl (.inr e) => nomatch e
  | .inr e => nomatch e

/-- an opened column's words, or none -/
def col₁ (π : Prf) (q : OPos (uLT Ct D.ds₁)) : List UInt64 :=
  match op₁ Ct D tF tJ t3 sil rn π q with
  | some op => colOfSym Ct D.ds₁ q op.sym
  | none => []
def col₂ (π : Prf) (q : OPos (uLT Ct D.ds₂)) : List UInt64 :=
  match op₂ Ct D tF tJ t3 sil rn π q with
  | some op => colOfSym Ct D.ds₂ q op.sym
  | none => []
def col₃ (π : Prf) (q : OPos (uLT Ct D.ds₃)) : List UInt64 :=
  match op₃ Ct D tF tJ t3 sil rn π q with
  | some op => colOfSym Ct D.ds₃ q op.sym
  | none => []

/-- WholeOwes' clauses, in four parts. -/
abbrev GoodF (z : Prf × Tr Q.loc.shape) : Prop :=
  (pls₂ (wholeDesc Ct D tF tJ t3 sil rn) z.1).1.run = r2 ∧
    (pls₃ (wholeDesc Ct D tF tJ t3 sil rn) z.1).1 = r3 ∧
    (pls₂ (wholeDesc Ct D tF tJ t3 sil rn) z.1).1.answers =
      (pls₁ (wholeDesc Ct D tF tJ t3 sil rn) z.1).1.answers ∧
    (∀ e ∈ (pls₁ (wholeDesc Ct D tF tJ t3 sil rn) z.1).1.answers, Carrier.okE e.triple) ∧
    (pls₁ (wholeDesc Ct D tF tJ t3 sil rn) z.1).1.answers.length < 2 ^ 64 ∧
    (pls₁ (wholeDesc Ct D tF tJ t3 sil rn) z.1).1.copy < 2 ^ 64

abbrev GoodW (z : Prf × Tr Q.loc.shape) : Prop :=
  WordsP Ct D.ds₁ (pls₁ (wholeDesc Ct D tF tJ t3 sil rn) z.1).2 ∧
    WordsP Ct D.ds₂ (pls₂ (wholeDesc Ct D tF tJ t3 sil rn) z.1).2 ∧
    WordsP Ct D.ds₃ (pls₃ (wholeDesc Ct D tF tJ t3 sil rn) z.1).2

/-- a word below the prime, as a test -/
def okFb (w : UInt64) : Bool := decide (w.toNat < _root_.Fmt.Fld.two.p)

theorem okF_of {w : UInt64} (h : okFb w = true) : Carrier.okF w := of_decide_eq_true h

/-- the opened columns' words, as a test over all positions -/
def chkC (π : Prf) : Bool :=
  (allA.all fun q => (col₁ π q).all okFb) && (allB.all fun q => (col₂ π q).all okFb) &&
    (allC.all fun q => (col₃ π q).all okFb)

/-- the outer tree at place p, as a test: at all places, read or not. c: the start of the salts with
which the tree was made -/
def chkX (c : ByteArray) (p : Fin (2 ^ D.a)) : Bool :=
  decide (((xt c 0).inp p.val).salt.take 256 = bytesToBits cfg) &&
    whole (((xt c 0).inp p.val).salt.drop 256) && decide ((y p).1 = p.val) &&
    (y p).2.all okFb && decide ((y p).2.length < 2 ^ 64) &&
    decide (((xt c 0).inp p.val).salt.length ≤ 256 + 8 * 64) &&
    decide ((pathOf (xt c 0).lv p.val).length < 2 ^ 64)

theorem good_F : (match run r1 r2 cfg with
    | .ok z => decide (GoodF z)
    | _ => false) = true := by decide +kernel
theorem good_W : (match run r1 r2 cfg with
    | .ok z => decide (GoodW z)
    | _ => false) = true := by decide +kernel
theorem good_C : (match run r1 r2 cfg with
    | .ok z => chkC z.1
    | _ => false) = true := by decide +kernel
theorem good_X : (List.finRange (2 ^ D.a)).all (chkX cfg) = true := by decide +kernel

/-- the tests can say no: at a tree whose leaves are salted from run1; at the prime as a word -/
theorem bad_X : (List.finRange (2 ^ D.a)).any (chkX r1) = false := by decide +kernel
theorem bad_word : okFb (UInt64.ofNat _root_.Fmt.Fld.two.p) = false := by decide +kernel

theorem owes_of_good (z : Prf × Tr Q.loc.shape) (hF : GoodF z) (hW : GoodW z)
    (hC : chkC z.1 = true) :
    WholeOwes Ct D tF tJ t3 sil rn () y (xt cfg) (bc r1) cfg z.1 z.2 := by
  simp only [chkC, Bool.and_eq_true, List.all_eq_true] at hC
  obtain ⟨⟨cA, cB⟩, cC⟩ := hC
  exact
    { run2 := hF.1
      run3 := hF.2.1
      again := hF.2.2.1
      answers := hF.2.2.2.1
      count := hF.2.2.2.2.1
      copy := hF.2.2.2.2.2
      words₁ := hW.1
      words₂ := hW.2.1
      words₃ := hW.2.2
      cols₁ := fun q op e w hw => okF_of (cA q (memA q) w (by unfold col₁; rw [e]; exact hw))
      cols₂ := fun q op e w hw => okF_of (cB q (memB q) w (by unfold col₂; rw [e]; exact hw))
      cols₃ := fun q op e w hw => okF_of (cC q (memC q) w (by unfold col₃; rw [e]; exact hw))
      outer := fun p _ => by
        have h := List.all_eq_true.1 good_X p (List.mem_finRange p)
        simp only [chkX, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
        exact ⟨⟨h1, h2⟩, h3, fun w hw => okF_of (h4 w hw), h5, h6, h7⟩ }

/-- **A MEMBER: the prover's own value, with WholeOwes and all that whole_prints concludes.** -/
theorem bites : ∃ z, run r1 r2 cfg = .ok z ∧
    WholeOwes Ct D tF tJ t3 sil rn () y (xt cfg) (bc r1) cfg z.1 z.2 ∧
    Printable Ct D tF tJ t3 sil rn cfg sB z.1 ∧ Canon Ct D tF tJ t3 sil rn z.1 ∧
    (_root_.Fmt.runOk (bitsToBytes z.1.salt) = true ∧
      _root_.Fmt.runOk (pls₂ (wholeDesc Ct D tF tJ t3 sil rn) z.1).1.run = true ∧
      _root_.Fmt.runOk (pls₃ (wholeDesc Ct D tF tJ t3 sil rn) z.1).1 = true) := by
  have hF := good_F
  have hW := good_W
  have hC := good_C
  cases hz : run r1 r2 cfg with
  | ok z =>
    rw [hz] at hF hW hC
    have ho := owes_of_good z (of_decide_eq_true hF) (of_decide_eq_true hW) hC
    exact ⟨z, rfl, ho, whole_prints Ct D tF tJ t3 sil rn L 1 chal Tag.onl embS (fun z => z) some
      (cms cfg) () y (xt cfg) (σ r2) (bc r1) (fun _ => 40) g cfg 2 sB z.1 z.2 hz coins_toy fewJ_toy
      few0_toy okg_toy (fun _ => by show (40 : ℕ) < 2 ^ 64; decide) (by decide +kernel)
      (by decide) ho⟩
  | noFormat => rw [hz] at hF; cases hF
  | ranOut j => rw [hz] at hF; cases hF

end Johnson.Prover.Print.ToyRun

#print axioms Johnson.Prover.Print.ToyRun.coins_toy
#print axioms Johnson.Prover.Print.ToyRun.okg_toy
#print axioms Johnson.Prover.Print.ToyRun.fewJ_toy
#print axioms Johnson.Prover.Print.ToyRun.few0_toy
#print axioms Johnson.Prover.Print.ToyRun.good_F
#print axioms Johnson.Prover.Print.ToyRun.good_W
#print axioms Johnson.Prover.Print.ToyRun.good_C
#print axioms Johnson.Prover.Print.ToyRun.good_X
#print axioms Johnson.Prover.Print.ToyRun.bad_X
#print axioms Johnson.Prover.Print.ToyRun.bad_word
#print axioms Johnson.Prover.Print.ToyRun.owes_of_good
#print axioms Johnson.Prover.Print.ToyRun.bites
