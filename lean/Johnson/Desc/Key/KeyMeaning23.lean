-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/KeyMeaning23.lean (the three readers of a message's entries go through KRead.of; the reader g sees the pair, not what was handed alone: so that the last chain can read the row weights where its own block reads them: off its own record; a sentence typed as an equation of the program's WORDS cannot be closed by a count in the field, which gives «reads as», never «the words are
equal»: EVERY «IS» BETWEEN TWO ELEMENTS IS THE LETTER same (KRead.same, Johnson/Desc/Key/KeyWords.lean: «they read as one element of the field»; meant as ρ a = ρ b); NearUAt compares no words; the two lemmas stand under SameLaws: same is an
equivalence that the program's sum and product respect): WHAT THE NAMED CLAIMS OF THE KEY FILE's SHARED AND LAST CHAIN SAY (Johnson/Desc/Key/KeyBorders23.lean's rows), as definitions, in the form of Johnson/Desc/Key/KeyMeaning.lean:
of what was handed to the chain (P), the chain's own state (S, through readers that are letters), the oracles and ONE witness. Definitions; two small lemmas that try them; no law of a block.
  § 1  the sentences on plain vectors u | om | v : Nat → E (the folded row's entries · Omega's · V's), in the program's own arithmetic (addE · mulE · Tensor.eq): evalEq · readU · DotUAt · DotOmAt · FoldAt · RecRowAt · NearUAt
       EACH IS MEANT TO BE THE LIBRARY's: Cb/Ld/LdLin.lean:253 DotU · :335-340 Dot | FoldR · Cb/Ld/LdFoldEq.lean:145 RecRow · :161 NearW: THAT IT IS, UNDER THE READING OF WORDS AS FIELD ELEMENTS, IS OWED.
  § 2  sumE_congr · dotOm_iff_dotU: WHERE Omega IS WHAT IS READ OFF u AT psi_lo, «DotOm» IS «DotU»: the half without chance of LIN zeta's row: so the two sentences are cut to each other
  § 3  KReaders23 · claim₂ | claim₃: the claims at the shared | the last chain's borders. A ROW «AS IT LIES» IS FOUND BY ITS PLACE IN ITS GROUP's LIST: G_u: the record's rows first (as many as the record has answers), then the columns' (as many
       as positions are drawn), then (Fold)'s part; G_omega: (Fold)'s part alone; the own group: (Eval), then (Dot): the book-keeping Bools (shape₂ | shape₃) hold the counts.
Limits. enc (the code's encoding of the whole folded message) and the radius are letters. A claim under a name that is none of these is False. The sums and products are still the program's machine operations: that these read as the field's at words that are not below the prime is owed by whoever fills same
(SameLaws says what is asked).
(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness.

-/
import Johnson.Desc.Key.KeyMeaning
import Johnson.Desc.Key.KeyBorders23

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open OnBytes.Params (LinShape IndexShape)

/-! ## 1 The sentences on plain vectors -/

/-- The multilinear extension of the first n entries of f, at a point. -/
def evalEq (pt : List E) (n : Nat) (f : Nat → E) : E := sumE n fun c => mulE ((Tensor.eq pt).entry c) (f c)

/-- What is read off the folded row for the matrix's row y, at psi_lo. -/
def readU (S : LinShape) (psi : List E) (u : Nat → E) (y : Nat) : E := evalEq (psi.take S.kLo) (2 ^ S.kLo) fun j => u (j + 2 ^ S.kLo * y)

/-- ⟨g, what is read off u⟩ = V at the shared point. -/
def DotUAt (same : E → E → Prop) (S : LinShape) (g : List Tensor) (psi : List E) (u v : Nat → E) : Prop :=
  same (sumE S.matrixRows fun y => mulE (weightAt g y) (readU S psi u y)) (evalEq psi (2 ^ S.kCol) v)

/-- ⟨g, Omega⟩ = V at the shared point. -/
def DotOmAt (same : E → E → Prop) (S : LinShape) (g : List Tensor) (psi : List E) (om v : Nat → E) : Prop :=
  same (sumE S.matrixRows fun y => mulE (weightAt g y) (om y)) (evalEq psi (2 ^ S.kCol) v)

/-- Omega at zeta is what u gives at (psi_lo, zeta), over the real rows. -/
def FoldAt (same : E → E → Prop) (S : LinShape) (psi zeta : List E) (u om : Nat → E) : Prop :=
  same (evalEq zeta S.matrixRows om) (sumE S.matrixRows fun y => mulE ((Tensor.eq zeta).entry y) (readU S psi u y))

/-- The sample of u's message part at each of the record's seeds is the record's answers folded at gamma. -/
def RecRowAt (same : E → E → Prop) (s : IndexShape) (key : TableKey) (gamma : List E) (u : Nat → E) : Prop :=
  ∀ i, i < s.answers → ∃ seed, key.seeds[i]? = some seed ∧
    same (addE (sumE s.plain fun p => mulE ((Tensor.eq seed.z).entry p) (u p)) (sumE 3 fun t => mulE (mulE seed.beta (thetaE t)) (u (s.padPlace i t))))
      (sumE s.rows fun r => mulE ((Tensor.eq gamma).entry r) (key.record.getD (r * s.answers + i) zeroE))

/-- u's codeword is within e positions of the stored words' fold at gamma: but for a list of at most e positions the stored table shows a column at x, and u's codeword at x reads as that column's fold. enc: the code's encoding of the whole folded
message. A position at which the stored table shows nothing is among the e. -/
def NearUAt (same : E → E → Prop) (logN e : Nat) (enc : (Nat → E) → Nat → E) (gamma : List E) (y : Strs) (u : Nat → E) : Prop :=
  ∃ B : List Nat, B.length ≤ e ∧ ∀ x, x < 2 ^ logN → x ∉ B → ∃ c, y.cell x = some c ∧ same (enc u x) (foldeqSymbol (foldeqWeights gamma) c.2.toArray)

/-! ## 2 Two lemmas that try the sentences -/

theorem sumE_succ (n : Nat) (f : Nat → E) : sumE (n + 1) f = addE (sumE n f) (f n) := by
  show (List.range (n + 1)).foldl _ zeroE = _
  rw [List.range_succ, List.foldl_append]
  rfl

theorem sumE_congr (n : Nat) (f g : Nat → E) (h : ∀ i, i < n → f i = g i) : sumE n f = sumE n g := by
  induction n with
  | zero => simp only [sumE, List.range_zero, List.foldl_nil]
  | succ n ih => rw [sumE_succ, sumE_succ, ih fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)]

/-- What is asked of «read as one element»: an equivalence that the program's sum and product respect. AT same := Eq it holds outright (sameLaws_eq). -/
structure SameLaws (same : E → E → Prop) : Prop where
  refl : ∀ a, same a a
  symm : ∀ {a b}, same a b → same b a
  trans : ∀ {a b c}, same a b → same b c → same a c
  add : ∀ {a a' b b'}, same a a' → same b b' → same (addE a b) (addE a' b')
  mul : ∀ {a a' b b'}, same a a' → same b b' → same (mulE a b) (mulE a' b')

theorem sameLaws_eq : SameLaws (· = ·) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k, fun h k => by rw [h, k], fun h k => by rw [h, k]⟩

theorem sumE_same {same : E → E → Prop} (L : SameLaws same) (n : Nat) (f g : Nat → E) (h : ∀ i, i < n → same (f i) (g i)) : same (sumE n f) (sumE n g) := by
  induction n with
  | zero =>
    simp only [sumE, List.range_zero, List.foldl_nil]
    exact L.refl _
  | succ n ih =>
    rw [sumE_succ, sumE_succ]
    exact L.add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

/-- **Where Omega READS AS what is read off u, «DotOm» is «DotU».** -/
theorem dotOm_iff_dotU {same : E → E → Prop} (L : SameLaws same) (S : LinShape) (g : List Tensor) (psi : List E) (u om v : Nat → E)
    (h : ∀ y, y < S.matrixRows → same (om y) (readU S psi u y)) : DotOmAt same S g psi om v ↔ DotUAt same S g psi u v := by
  have e : same (sumE S.matrixRows fun y => mulE (weightAt g y) (om y)) (sumE S.matrixRows fun y => mulE (weightAt g y) (readU S psi u y)) :=
    sumE_same L _ _ _ fun y hy => L.mul (L.refl _) (h y hy)
  exact ⟨fun hd => L.trans (L.symm e) hd, fun hd => L.trans e hd⟩

/-- And there (Fold) holds at every zeta. -/
theorem fold_of_readU {same : E → E → Prop} (L : SameLaws same) (S : LinShape) (psi zeta : List E) (u om : Nat → E)
    (h : ∀ y, y < S.matrixRows → same (om y) (readU S psi u y)) : FoldAt same S psi zeta u om :=
  sumE_same L _ _ _ fun y hy => L.mul (L.refl _) (h y hy)

/-! ## 3 The claims at the borders -/

/-- **What must be readable at a later chain's border.** P: what was handed to the chain. -/
structure KReaders23 (P S : Type) where
  st : S → Statement
  /-- the numbers of G_u, G_omega (the shared chain) and of the own group (the last chain) -/
  gU : S → Nat
  gO : S → Nat
  own : S → Nat
  /-- the shared point: the shared chain's own; at the last chain: off what was handed over -/
  psi : P × S → List E
  zeta : S → List E
  key : P × S → TableKey
  /-- the first chain's last statement and its row (Eval); the claim's row weights (off the pair) -/
  st₁ : P → Statement
  eval : P → Option OnBytes.Row
  g : P × S → Option (List Tensor)

section
variable {P S Cells M : Type} (K₁ K : KPlan) (R : KRead Cells M) (X : KReaders23 P S)
  (enc : (Nat → E) → Nat → E) (rad : Nat)

/-- The folded row's, Omega's and V's entries, read off the witness at the places where the program's layouts put them: THROUGH KRead.of, THE TABLE THAT PIN PINS (nobody reads w.msg k bare). -/
def uOf (codes : Codes) (w : Wit Cells Unit M) (i : Nat) : E := R.val (R.of w 3) .main ((vectorLay codes K.lin.fold.u K.lin.fold.rowsHigh).index i)
def omOf (codes : Codes) (w : Wit Cells Unit M) (y : Nat) : E := R.val (R.of w 4) .main ((linLayOmega codes K.lin).index y)
def vOf' (codes : Codes) (w : Wit Cells Unit M) (c : Nat) : E := R.val (R.of w 2) .main ((linLayW codes K.lin).index c)

/-- The rows number lo … lo + n − 1 of group g's open list are there and hold. -/
def rowsHold (same : E → E → Prop) (St : Statement) (val : Nat → Part → Nat → E) (g lo n : Nat) : Prop :=
  ∃ G, St.groups[g]? = some G ∧ lo + n ≤ G.rows.size ∧ n ≠ 0 ∧ ∀ r ∈ (G.rows.toList.drop lo).take n, RowHolds same St val r

/-- **The claims at the shared chain's borders.** K₁: the first chain's plan's numbers; K: the shared chain's. -/
def claim₂ (c : Nat) (n : String) (a : P × S) (y : Strs) (w : Wit Cells Unit M) : Prop :=
  let St := X.st a.2
  let cd := St.codes
  let rec_ := K.lin.fold.index.answers
  let t := K.lin.fold.columns
  let gamma := (X.psi a).drop K.lin.kLo
  if c = 1 ∧ n = "Eval" then ∃ r, X.eval a.1 = some r ∧ RowHolds R.same (X.st₁ a.1) (valOf K₁ R w) r
  else if c = 2 ∧ n = "NearU" then NearUAt R.same K.lin.fold.index.code.logN rad enc gamma y (uOf K R cd w)
  else if c = 2 ∧ n = "RecRow" then RecRowAt R.same K.lin.fold.index (X.key a) gamma (uOf K R cd w)
  else if c = 2 ∧ n = "DotU" then ∃ g, X.g a = some g ∧ DotUAt R.same K.lin g (X.psi a) (uOf K R cd w) (vOf' K R cd w)
  else if c = 2 ∧ n = "record" then rowsHold R.same St (valOf K R w) (X.gU a.2) 0 rec_
  else if c = 2 ∧ n = "columns" then rowsHold R.same St (valOf K R w) (X.gU a.2) rec_ t
  else if c = 2 ∧ n = "Fold" then FoldAt R.same K.lin (X.psi a) (X.zeta a.2) (uOf K R cd w) (omOf K R cd w)
  else if c = 2 ∧ n = "DotOm" then ∃ g, X.g a = some g ∧ DotOmAt R.same K.lin g (X.psi a) (omOf K R cd w) (vOf' K R cd w)
  else if c = 2 ∧ n = "FoldU" then rowsHold R.same St (valOf K R w) (X.gU a.2) (rec_ + t) 1
  else if c = 2 ∧ n = "FoldO" then rowsHold R.same St (valOf K R w) (X.gO a.2) 0 1
  else False

/-- **The claims at the last chain's borders.** K: the last chain's plan's numbers. (Eval) lies there as the own group's first open row, (Dot) as its second. -/
def claim₃ (c : Nat) (n : String) (a : P × S) (_ : Strs) (w : Wit Cells Unit M) : Prop :=
  let St := X.st a.2
  let cd := St.codes
  if c = 1 ∧ n = "Eval" then rowsHold R.same St (valOf K R w) (X.own a.2) 0 1
  else if c = 2 ∧ n = "DotOm" then ∃ g, X.g a = some g ∧ DotOmAt R.same K.lin g (X.psi a) (omOf K R cd w) (vOf' K R cd w)
  else if c = 3 ∧ n = "Dot" then rowsHold R.same St (valOf K R w) (X.own a.2) 1 1
  else False

end

/-- Every claim that the two chains' rows name has a sentence: no name falls to «False» by a slip of spelling. -/
def namedIn (rs : List KRow) : List (Nat × String) :=
  (rs.flatMap fun r => r.ins ++ r.outs ++ r.ctx).filterMap fun i => match i with | .claim c n => some (c, n) | _ => none

def known₂ : List (Nat × String) := [(1, "Eval"), (2, "NearU"), (2, "RecRow"), (2, "DotU"), (2, "record"), (2, "columns"), (2, "Fold"), (2, "DotOm"), (2, "FoldU"), (2, "FoldO")]
def known₃ : List (Nat × String) := [(1, "Eval"), (2, "DotOm"), (3, "Dot")]

#eval (namedIn rows₂).all known₂.contains && known₂.all (namedIn rows₂).contains
#eval (namedIn rows₃).all known₃.contains && known₃.all (namedIn rows₃).contains
-- a control: due «false»
#eval (namedIn rows₂).all (known₂.erase (2, "DotU")).contains

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.dotOm_iff_dotU
#print axioms VerifiableInference.Desc.Key.fold_of_readU
