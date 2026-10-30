-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyMemberTable.lean: DEFINITIONS AND THEOREMS. **A decoder for the third part of KeyLetters.lean's letters (the committed matrix) with a member**: the library's decoder of a stored table WITH A RECORD (DecR.dcd, OnBytes/Slice/DecoderRec.lean), the record read off a public part Q that no block writes.
OBJECT: DecR.dcd | DecR.coll at letters D; dec₃ | cond₃ (here): dec₂ | cond₂ with the third part's decoder handed the public part. USER: Johnson/RunOne/KeyMemberTableFull.lean calls member_three_has | dcd_stored | coll_share (meant beyond it: the links' laws once their letters are dec | cond : (Q × the riding part) × strings; the lift of their rows into the chain must then hand the public part on: as it stands it drops it). LETTERS: D · Q · recOf · tb (how a frame's strings hold the stored table: by LowDec it has one admissible value: the strings' first part) · A | rd (the frame's own reading of a decoded table as a matrix, and of a matrix by row and column), and those of KeyLetters.lean.
WHY A RECORD. The radius of the stored table's decoder lies beyond unique decoding: without the record there is a list. The key file's language is «the table has a collision at the record's seed, or decodes WITH THE RECORD». So a decoder of the matrix that is to be what the key file's later places establish must see the record.
  upM | stored    a table of full messages over the base field, read over the extension field; the stored table of its code words (each symbol: its position and the rows' words)
  tab_stored      the decoder's reading of that stored table is the table of the code words
  recOfM          the true record at a seed: the seed and every row's answers
  dcd_stored      **at the stored table of M with its true record, the radius below the distance: the decoder returns the message parts of M, AT EVERY SEED** (the library's ldFe_honest)
  not_coll_stored **at that stored table NO seed is a collision**: below the distance the list of a table of code words holds that table alone
  not_dcd_of_wrong_rec   the control: what has not the record's answers is not returned, at any table
  list_over_base  every member of the list of ANY stored table is over the base field (the library's ldFc_overF): so «M over the base field» shuts out nothing
  coll_share      the seeds at which the record does not single one out are at most a share 2^-K, at every FIXED table (the library's coll_count), from one inequality on numbers. FOR WHOM: soundness pays it at a table that an adversary picks; the member does not need it. ITS LIMIT, in the library's own words (OnBytes/Slice/DecoderRec.lean): the seed follows from the table's name by the hash, and «whoever tries many roots for a seed at which a record does not single one table out pays one try a root, without a factor for work»
  dec₃ | cond₃    the letters with a public part; dec₃_blind | cond₃_blind | dec₃_low | cond₃_low. cond₃ ASKS «no collision at the record's seed» of the third part: not for the member (the decoder returns M at every seed) but for the law's user: whoever extracts a table from a later test must show that it IS the decoder's value, and that wants the record to single one out; the frame's first row is handed just that
  mxA | mxA_cut   the matrix of what is decoded is THE FRAME's OWN reading of a decoded table (DecR.Claims.mat), so that «the keys lie in their tables» and the language's «inRange (A.mat u)» speak of one matrix; it reads no pad
  member_three | member_three_every   **cond₃ holds and dec₃ returns (m₀, m₁, the message parts of M)**; the second at every three seeds
  member_three_has    for every three seeds there is such a point, at the plainest letters
What is not claimed. That the keys which the matrix holds lie in their range tables: that is a property of M (an honest matrix), a premise of whoever needs it. That A.inRange is «the keys lie in their tables» at rd: a tie that whoever names A owes. That tb reads a frame's stored table. Nothing on soundness or on hiding.

-/
import Johnson.RunOne.KeyMemberEvery
import OnBytes.Slice.RecordColl
import OnBytes.Slice.RecordPriceGlue
import OnBytes.Slice.BlkProxGp
import Cb.Ld.LdFoldEqProofs

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob Blocks
open VerifiableInference.Desc VerifiableInference.Desc.K1

/-! ## The honest stored table -/

section table
variable (D : DecR)

/-- A table of full messages (tail and message) over the base field, read over the extension field. -/
def upM (M : (Fin D.v → Bool) → Fin (D.T.r + D.T.l) → GF) : D.ix.Row → D.toDec.Co → GE := fun r k => algebraMap GF GE (M r k)

/-- The stored table of its code words: the symbol at a position holds the position and, row by row in the order of the rows' numbers, the row's code word's symbol there. -/
def stored (M : (Fin D.v → Bool) → Fin (D.T.r + D.T.l) → GF) : D.toDec.Pos → Run.PQ.SgX := fun j =>
  (j.val, List.ofFn fun b : Fin (2 ^ D.v) => OnBytes.Slice.ofF (∑ k : Fin (D.T.r + D.T.l), ptOf D.T.a j ^ k.val * M (vtx D.v b.val) k))

theorem vtx_rowNo {k : Nat} (r : Fin k → Bool) : vtx k (Sz.rowNo r) = r :=
  OnBytes.Slice.ProxRun.vtx_rowNo k r

theorem tab_stored (M : (Fin D.v → Bool) → Fin (D.T.r + D.T.l) → GF) :
    D.tab (stored D M) = fun r => (genOf D.T).mulVec (upM D M r) := by
  funext r j
  show algebraMap GF GE (toF ((stored D M j).2.getD (Sz.rowNo r) 0)) = _
  have h : (stored D M j).2.getD (Sz.rowNo r) 0 = OnBytes.Slice.ofF (∑ k : Fin (D.T.r + D.T.l), ptOf D.T.a j ^ k.val * M r k) := by
    simp [stored, List.getD_eq_getElem?_getD, List.getElem?_ofFn, rowNo_lt r, vtx_rowNo]
  rw [h, toF_ofF, map_sum]
  simp only [Matrix.mulVec, dotProduct, genOf, upM, map_mul]

/-- The true record of M at a seed. -/
def recOfM (M : (Fin D.v → Bool) → Fin (D.T.r + D.T.l) → GF) (ρ : D.Z.D) : D.Rec := (ρ, D.ix.ZR.val ρ (D.ix.view (upM D M)))

/-- **At the stored table of M with its true record the decoder returns the message parts of M, at every seed.** -/
theorem dcd_stored (ha : D.T.a ≤ 32) (hk : D.T.r + D.T.l ≤ 2 ^ D.T.a) (he : D.eM < 2 ^ D.T.a - (D.T.r + D.T.l) + 1)
    (M : (Fin D.v → Bool) → Fin (D.T.r + D.T.l) → GF) (ρ : D.Z.D) :
    D.dcd (stored D M) (recOfM D M ρ) = some (D.ix.view (upM D M)) := by
  unfold DecR.dcd
  rw [tab_stored]
  exact Cb.ldFe_honest D.ix _ (upM D M) ρ (hasDist_genOf D.T ha hk) he

/-- **At the stored table of M no seed is a collision**: the radius is below the distance, so the list of a table of code words holds that table alone. -/
theorem not_coll_stored (ha : D.T.a ≤ 32) (hk : D.T.r + D.T.l ≤ 2 ^ D.T.a) (he : D.eM < 2 ^ D.T.a - (D.T.r + D.T.l) + 1)
    (M : (Fin D.v → Bool) → Fin (D.T.r + D.T.l) → GF) (ρ : D.Z.D) : ¬ D.coll (stored D M) ρ := by
  unfold DecR.coll
  rw [tab_stored]
  have hd := hasDist_genOf D.T ha hk
  have hall : ∀ u, InList (genOf D.T) D.eM D.ix.view (fun r => (genOf D.T).mulVec (upM D M r)) u → u = D.ix.view (upM D M) := by
    rintro u ⟨M', h1, rfl⟩
    exact congrArg D.ix.view (funext fun _ => DecodesTo.row_unique hd (by rw [Nat.add_zero]; exact he) h1 (decodesTo_mulVec (genOf D.T) 0 (upM D M)) rfl)
  rintro ⟨u, u', hu, hu', hne, -⟩
  exact hne ((hall u hu).trans (hall u' hu').symm)

/-- **The control**: a table of message parts that has not the record's answers is not returned. -/
theorem not_dcd_of_wrong_rec (f : D.toDec.Pos → Run.PQ.SgX) (rec : D.Rec) (U : D.ix.Row × D.toDec.En → GE)
    (h : D.ix.ZR.val rec.1 U ≠ rec.2) : D.dcd f rec ≠ some U := fun hd =>
  h (Cb.ood_decMin_cand _ _ _ _ _ _ _ _ _ _ _ _ hd).2

end table

/-! ## At the programs' sample map -/

section rec
variable (T : Fmt.M1.Code) (v eM lg s : Nat)

/-- **Every member of the list of any stored table is over the base field.** -/
theorem list_over_base (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a) (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (f : Fin (2 ^ T.a) → Run.PQ.SgX) (M : (Fin v → Bool) → Fin (T.r + T.l) → GE)
    (hM : DecodesTo (genOf T) eM ((decRec T v eM lg s).tab f) M) :
    ∃ M₀ : (Fin v → Bool) → Fin (T.r + T.l) → GF, M = upM (decRec T v eM lg s) M₀ := by
  rw [genOf_eq_GE, tab_lift] at hM
  obtain ⟨M₀, -, rfl⟩ := ldFc_overF GF GE (rsCode T) eM (hasDist_rsCode T ha hk) he _ (baseTab T v f) M hM
  exact ⟨M₀, rfl⟩

/-- **The share of the seeds at which the record does not single one table out**, at a FIXED table: the seed ranges. A count of typed seeds: no proof of work enters. -/
theorem coll_share (K : Nat) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a) (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l) (hl : T.l - 3 * s ≤ 2 ^ lg)
    (hK : (listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * clashSeeds (Fmt.Fld.two.p ^ 3) lg ^ s * 2 ^ K ≤ allSeeds (Fmt.Fld.two.p ^ 3) lg ^ s)
    (f : Fin (2 ^ T.a) → Run.PQ.SgX) :
    cnt ((decRec T v eM lg s).coll f) * 2 ^ K ≤ Fintype.card (recZ T.l lg s).D := by
  have c := coll_count T v eM lg s ha hk he hJ h3 hl f
  rw [recZ_err_clash, OnBytes.Slice.card_GE] at c
  rw [recZ_card_all, OnBytes.Slice.card_GE]
  exact le_trans (Nat.mul_le_mul_right _ c) hK

end rec

/-! ## The letters with a public part -/

section three
variable (cs : Codes) (s₀ s₁ : OracleShape) (e₀ e₁ o₀ o₁ : Nat) {Q X Y MW : Type} (stOf : X → Statement)
  (f₀ : Y → (portOmZ cs s₀ e₀).Str) (f₁ : Y → (portOmZ cs s₁ e₁).Str) (decW : Q → Y → Option MW) (condW : Q → Y → Prop)

/-- dec₂, the third part's decoder handed the public part. -/
def dec₃ (a : (Q × X) × Y) : Option (Two cs s₀ s₁ MW) := dec₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (decW a.1.1) (a.1.2, a.2)

/-- cond₂, and the third part's own condition. -/
def cond₃ (a : (Q × X) × Y) : Prop := cond₂ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (a.1.2, a.2) ∧ condW a.1.1 a.2

/-- The matrix of what is decoded: the frame's own reading of a decoded table, read by row and column. -/
def mxA {D : DecR} {Xc : Type} (A : D.Claims Xc) (rd : A.Mat → Nat → Nat → GE) (u : Two cs s₀ s₁ (D.ix.Row × D.toDec.En → GE)) : Nat → Nat → GE := rd (A.mat u.2.2)

/-- It reads no pad. -/
theorem mxA_cut {D : DecR} {Xc : Type} (A : D.Claims Xc) (rd : A.Mat → Nat → Nat → GE) {u u' : Two cs s₀ s₁ (D.ix.Row × D.toDec.En → GE)} (h : D.Agree u.2.2 u'.2.2) :
    mxA cs s₀ s₁ A rd u = mxA cs s₀ s₁ A rd u' := by
  unfold mxA
  rw [A.mat_cut _ _ h]

variable {cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW condW}

theorem dec₃_blind (q : Q) {x x' : X} (y : Y) (h : stOf x = stOf x') :
    dec₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW ((q, x), y) = dec₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW ((q, x'), y) :=
  dec₂_blind y h

theorem cond₃_blind (q : Q) {x x' : X} (y : Y) (h : stOf x = stOf x') :
    cond₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ condW ((q, x), y) ↔ cond₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ condW ((q, x'), y) :=
  and_congr_left' (cond₂_blind y h)

theorem dec₃_low (q : Q) (x : X) {y y' : Y} (h₀ : f₀ y = f₀ y') (h₁ : f₁ y = f₁ y') (hW : decW q y = decW q y') :
    dec₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW ((q, x), y) = dec₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ decW ((q, x), y') :=
  dec₂_low x h₀ h₁ hW

theorem cond₃_low (q : Q) (x : X) {y y' : Y} (h₀ : f₀ y = f₀ y') (h₁ : f₁ y = f₁ y') (hW : condW q y ↔ condW q y') :
    cond₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ condW ((q, x), y) ↔ cond₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ condW ((q, x), y') :=
  and_congr (cond₂_low x h₀ h₁) hW

/-- **The member, the stored table's decoder in the third place.** cond₃ packs the premises on the records and the seeds again; the content is dec₃'s value. -/
theorem member_three (D : DecR) (recOf : Q → D.Rec) (tb : Y → D.toDec.Pos → Run.PQ.SgX)
    (ha : D.T.a ≤ 32) (hk : D.T.r + D.T.l ≤ 2 ^ D.T.a) (he : D.eM < 2 ^ D.T.a - (D.T.r + D.T.l) + 1)
    (hT₀ : Tie cs s₀) (hT₁ : Tie cs s₁) {m₀ : (portCode cs s₀).J → GE} {r₀ : (portCode cs s₀).Q → GE} {m₁ : (portCode cs s₁).J → GE} {r₁ : (portCode cs s₁).Q → GE}
    (h₀ : Sendable cs s₀ m₀ r₀) (h₁ : Sendable cs s₁ m₁ r₁) {a : (Q × X) × Y} (M : (Fin D.v → Bool) → Fin (D.T.r + D.T.l) → GF) (ρ : D.Z.D)
    (hf₀ : f₀ a.2 = sent cs s₀ e₀ m₀ r₀) (hf₁ : f₁ a.2 = sent cs s₁ e₁ m₁ r₁) (htb : tb a.2 = stored D M) (hrec : recOf a.1.1 = recOfM D M ρ)
    {ρ₀ : (Fin (bitsZ cs s₀) → GE) × GEˣ} {ρ₁ : (Fin (bitsZ cs s₁) → GE) × GEˣ}
    (hI₀ : SeedIs cs s₀ (stOf a.1.2) o₀ ρ₀ ((portZ cs s₀).val ρ₀ m₀ ())) (hI₁ : SeedIs cs s₁ (stOf a.1.2) o₁ ρ₁ ((portZ cs s₁).val ρ₁ m₁ ()))
    (hn₀ : ¬ (portOmZ cs s₀ e₀).Clash (sent cs s₀ e₀ m₀ r₀) ρ₀) (hn₁ : ¬ (portOmZ cs s₁ e₁).Clash (sent cs s₁ e₁ m₁ r₁) ρ₁)
    (hn : ¬ D.coll (stored D M) ρ) :
    cond₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (fun q y => ¬ D.coll (tb y) (recOf q).1) a ∧
      dec₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (fun q y => D.dcd (tb y) (recOf q)) a = some (m₀, m₁, D.ix.view (upM D M)) := by
  have hW : (fun q y => D.dcd (tb y) (recOf q)) a.1.1 a.2 = some (D.ix.view (upM D M)) := by
    show D.dcd (tb a.2) (recOf a.1.1) = _
    rw [htb, hrec]
    exact dcd_stored D ha hk he M ρ
  have t := member_two (a := (a.1.2, a.2)) (decW := (fun q y => D.dcd (tb y) (recOf q)) a.1.1) hT₀ hT₁ h₀ h₁ hf₀ hf₁ hW hI₀ hI₁ hn₀ hn₁
  refine ⟨⟨t.1, ?_⟩, t.2⟩
  show ¬ D.coll (tb a.2) (recOf a.1.1).1
  rw [htb, hrec]
  exact hn

/-- **The same at every three seeds.** -/
theorem member_three_every (D : DecR) (recOf : Q → D.Rec) (tb : Y → D.toDec.Pos → Run.PQ.SgX)
    (ha : D.T.a ≤ 32) (hk : D.T.r + D.T.l ≤ 2 ^ D.T.a) (he : D.eM < 2 ^ D.T.a - (D.T.r + D.T.l) + 1)
    (hT₀ : Tie cs s₀) (hT₁ : Tie cs s₁) (hm₀ : meetsB cs s₀ e₀ = true) (hm₁ : meetsB cs s₁ e₁ = true)
    {m₀ : (portCode cs s₀).J → GE} {r₀ : (portCode cs s₀).Q → GE} {m₁ : (portCode cs s₁).J → GE} {r₁ : (portCode cs s₁).Q → GE}
    (h₀ : Sendable cs s₀ m₀ r₀) (h₁ : Sendable cs s₁ m₁ r₁) {a : (Q × X) × Y} (M : (Fin D.v → Bool) → Fin (D.T.r + D.T.l) → GF) (ρ : D.Z.D)
    (hf₀ : f₀ a.2 = sent cs s₀ e₀ m₀ r₀) (hf₁ : f₁ a.2 = sent cs s₁ e₁ m₁ r₁) (htb : tb a.2 = stored D M) (hrec : recOf a.1.1 = recOfM D M ρ)
    {ρ₀ : (Fin (bitsZ cs s₀) → GE) × GEˣ} {ρ₁ : (Fin (bitsZ cs s₁) → GE) × GEˣ}
    (hI₀ : SeedIs cs s₀ (stOf a.1.2) o₀ ρ₀ ((portZ cs s₀).val ρ₀ m₀ ())) (hI₁ : SeedIs cs s₁ (stOf a.1.2) o₁ ρ₁ ((portZ cs s₁).val ρ₁ m₁ ())) :
    cond₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (fun q y => ¬ D.coll (tb y) (recOf q).1) a ∧
      dec₃ cs s₀ s₁ e₀ e₁ o₀ o₁ stOf f₀ f₁ (fun q y => D.dcd (tb y) (recOf q)) a = some (m₀, m₁, D.ix.view (upM D M)) :=
  member_three D recOf tb ha hk he hT₀ hT₁ h₀ h₁ M ρ hf₀ hf₁ htb hrec hI₀ hI₁
    (no_clash_sent (base_of_meets hm₀).1 (base_of_meets hm₀).2.1 (base_of_meets hm₀).2.2 h₀ ρ₀)
    (no_clash_sent (base_of_meets hm₁).1 (base_of_meets hm₁).2.1 (base_of_meets hm₁).2.2 h₁ ρ₁)
    (not_coll_stored D ha hk he M ρ)

end three

attribute [local irreducible] DecR.dcd DecR.coll stored sent recOfM upM decAt Sealed SeedIs

/-- **For every three seeds there is such a point**, at the plainest letters: the public part is the record, the riding part the statement, the strings the two words and the stored table. -/
theorem member_three_has {cs : Codes} {s₀ s₁ : OracleShape} {e₀ e₁ : Nat} (D : DecR)
    (ha : D.T.a ≤ 32) (hk : D.T.r + D.T.l ≤ 2 ^ D.T.a) (he : D.eM < 2 ^ D.T.a - (D.T.r + D.T.l) + 1)
    (hT₀ : Tie cs s₀) (hT₁ : Tie cs s₁) (hm₀ : meetsB cs s₀ e₀ = true) (hm₁ : meetsB cs s₁ e₁ = true)
    {m₀ : (portCode cs s₀).J → GE} {r₀ : (portCode cs s₀).Q → GE} {m₁ : (portCode cs s₁).J → GE} {r₁ : (portCode cs s₁).Q → GE}
    (h₀ : Sendable cs s₀ m₀ r₀) (h₁ : Sendable cs s₁ m₁ r₁) (M : (Fin D.v → Bool) → Fin (D.T.r + D.T.l) → GF)
    (ρ₀ : (Fin (bitsZ cs s₀) → GE) × GEˣ) (ρ₁ : (Fin (bitsZ cs s₁) → GE) × GEˣ) (ρ : D.Z.D) :
    ∃ a : (D.Rec × Statement) × ((portOmZ cs s₀ e₀).Str × (portOmZ cs s₁ e₁).Str × (D.toDec.Pos → Run.PQ.SgX)),
      a.1.1 = recOfM D M ρ ∧ a.2 = (sent cs s₀ e₀ m₀ r₀, sent cs s₁ e₁ m₁ r₁, stored D M) ∧
      cond₃ cs s₀ s₁ e₀ e₁ 0 1 id (fun y => y.1) (fun y => y.2.1) (fun q y => ¬ D.coll y.2.2 (id q : D.Rec).1) a ∧
        dec₃ cs s₀ s₁ e₀ e₁ 0 1 id (fun y => y.1) (fun y => y.2.1) (fun q y => D.dcd y.2.2 (id q)) a = some (m₀, m₁, D.ix.view (upM D M)) := by
  obtain ⟨St, i₀, i₁⟩ := seedIs_two cs s₀ s₁ ρ₀ ((portZ cs s₀).val ρ₀ m₀ ()) ρ₁ ((portZ cs s₁).val ρ₁ m₁ ())
  refine ⟨((recOfM D M ρ, St), (sent cs s₀ e₀ m₀ r₀, sent cs s₁ e₁ m₁ r₁, stored D M)), rfl, rfl, ?_⟩
  exact member_three_every (Q := D.Rec) (X := Statement) (Y := (portOmZ cs s₀ e₀).Str × (portOmZ cs s₁ e₁).Str × (D.toDec.Pos → Run.PQ.SgX))
    (o₀ := 0) (o₁ := 1) (stOf := id) (f₀ := fun y => y.1) (f₁ := fun y => y.2.1)
    (a := ((recOfM D M ρ, St), (sent cs s₀ e₀ m₀ r₀, sent cs s₁ e₁ m₁ r₁, stored D M)))
    D id (fun y => y.2.2) ha hk he hT₀ hT₁ hm₀ hm₁ h₀ h₁ M ρ rfl rfl rfl rfl i₀ i₁

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.tab_stored
#print axioms Johnson.RunOne.KeyLetters.dcd_stored
#print axioms Johnson.RunOne.KeyLetters.not_dcd_of_wrong_rec
#print axioms Johnson.RunOne.KeyLetters.list_over_base
#print axioms Johnson.RunOne.KeyLetters.coll_share
#print axioms Johnson.RunOne.KeyLetters.dec₃_blind
#print axioms Johnson.RunOne.KeyLetters.cond₃_blind
#print axioms Johnson.RunOne.KeyLetters.dec₃_low
#print axioms Johnson.RunOne.KeyLetters.cond₃_low
#print axioms Johnson.RunOne.KeyLetters.member_three
#print axioms Johnson.RunOne.KeyLetters.not_coll_stored
#print axioms Johnson.RunOne.KeyLetters.mxA_cut
#print axioms Johnson.RunOne.KeyLetters.member_three_every
#print axioms Johnson.RunOne.KeyLetters.member_three_has
