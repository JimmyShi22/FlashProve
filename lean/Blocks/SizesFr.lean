-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/SizesFr.lean: the sums in which bounds on proof sizes are written, for a protocol that is
built from blocks, from sums over its vectors and its rounds.

The two sums run over the rounds of a protocol: the bits of the lists of opened positions (`entSum`,
Iop/Sizes.lean) and the bits of the plain parts (`BitsS.plainBits`, Iop/SerS.lean). Here, for the
encoded rounds, at the widths `bitsE` and the numbers of opened positions `opensE` of
Blocks/StageData.lean, where E has at most 2^e elements and F at most 2^f:
 * `REnc.entB`, `EncData.entB`, `entSum_enc_le'`: the opened positions, round by round.
 * `entSum_enc_le` (f = e): the same from two sums and two bounds, for parameters that are
   variables: one bit for each round, and for each position that is read in a vector an opening in a
   tree of depth at most Dm with a symbol of at most Rm entries; Dm bounds the logarithm of the sum
   of the lengths of all codewords, Rm the number of rows of every vector. Two more bits for each
   position come from the lengths of the lists. (Crude: every vector is counted with the largest
   number of rows and e bits for an entry, over F or over E, and every tree with the depth Dm.)
 * `Shape.plainLog`, `plainBits_enc`: the plain parts; their bits do not depend on the encoding.
 * `SNum.plainK`, `plainLog_le`, `plainBits_enc_le`: e bits for each scalar of a plain part, by the
   small numbers that the data of the rounds carry (Blocks/StageData.lean: `RNum.plainK`).
 * `EncData.entB_app`, `SNum.plainK_app`: two protocols in a row: sums; for protocols too long for
   the kernel to evaluate in one piece.
The sums over all vectors of a block are of the form `EncData.sum` of Blocks/StageCount.lean (`lenN`
of Blocks/PfrCounts.lean), so that they can be computed along the stages, or evaluated by the
kernel.
-/
import Blocks.StageData
import Blocks.PfrCounts
import Blocks.StageSide
import Blocks.ChalBits
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks
open Iop
open Ser (gam)

/-! ## Lemmas -/

theorem B2.mono {α : Type} {a b : ℕ} (h : B2 α a) (hab : a ≤ b) : B2 α b :=
  le_trans h (Nat.pow_le_pow_right (by decide) hab)

/-- pairs (position, symbol) of a message of words whose symbols have at most 2^t values each -/
theorem B2.wordsDep {A : Type} [Fintype A] (n : A → ℕ) (Sy : A → Type) [∀ a, Finite (Sy a)]
    {d t : ℕ} (hn : ∑ a, n a ≤ 2 ^ d) (hT : ∀ a, B2 (Sy a) t) :
    B2 (Σ p : (Σ a, Fin (n a)), Sy p.1) (d + t) := by
  unfold B2 at *
  rw [Nat.card_sigma, pow_add]
  refine le_trans (Finset.sum_le_sum fun p _ => hT p.1) ?_
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
  refine Nat.mul_le_mul_right _ ?_
  simpa using hn

unseal wordsBits in
theorem wordsBits_fst_le' (A : Type) [FinEnum A] [Fintype A] (n : A → ℕ) (Sy : A → Type)
    [∀ a, FinEnum (Sy a)] (Plain : Type) [FinEnum Plain] {d t : ℕ}
    (hn : ∑ a, n a ≤ 2 ^ d) (hT : ∀ a, B2 (Sy a) t) :
    (wordsBits A n Sy Plain).1 ≤ d + t :=
  haveI : ∀ a, Finite (Sy a) := fun a => Finite.of_equiv _ (FinEnum.equiv (α := Sy a)).symm
  clog_le_of_B2 (B2.wordsDep n Sy hn hT)

unseal wordsBits in
theorem wordsBits_snd_eq (A : Type) [FinEnum A] (n : A → ℕ) (Sy : A → Type) [∀ a, FinEnum (Sy a)]
    (Plain : Type) [FinEnum Plain] :
    (wordsBits A n Sy Plain).2 = Nat.clog 2 (Nat.card Plain) := by
  show Nat.clog 2 (FinEnum.card Plain) = _
  rw [finEnum_card_eq]

theorem gam_le (n : ℕ) : gam n ≤ 2 * n + 1 := by
  have h : Nat.log 2 (n + 1) ≤ n := Nat.lt_succ_iff.1 (Nat.log_lt_self 2 (Nat.succ_ne_zero n))
  unfold Ser.gam
  omega

theorem B2.kf {F E : Type} {e : ℕ} (hF : B2 F e) (hE : B2 E e) : ∀ b : Bool, B2 (Kf F E b) e
  | true => hF
  | false => hE

end Blocks

/-! ## The plain parts -/

namespace Iop

/-- The bits of the plain parts of some rounds: for each round the logarithm of the number of values
that its plain part can take. -/
def Shape.plainLog : Shape → ℕ
  | [] => 0
  | r :: s => Nat.clog 2 (Nat.card r.Plain) + Shape.plainLog s

end Iop

namespace Blocks
open Iop
open Ser (gam)

theorem plainLog_app :
    ∀ (s t : Shape), Shape.plainLog (s ++ t) = Shape.plainLog s + Shape.plainLog t
  | [], _ => (Nat.zero_add _).symm
  | r :: s, t => by
      show _ + Shape.plainLog (s ++ t) = _ + Shape.plainLog s + _
      rw [plainLog_app s t, Nat.add_assoc]

section Enc
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FinEnum F] [FinEnum E]

omit [Algebra F E] in
/-- The plain parts of the encoded rounds are those of the rounds. -/
theorem plainBits_enc :
    ∀ (s : Shape) (d : EncData F E s) (n : SNum s d),
      BitsS.plainBits (encShape s d) (bitsE s d n) = s.plainLog
  | [], _, _ => rfl
  | r :: s, (e, d), (a, as) => by
      letI := a.enumA
      letI := a.enumPlain
      show (wordsBits e.A (fun v => (e.code v).n)
            (fun v => Fin (e.rows v) → Kf F E (e.overF v)) r.Plain).2 +
          BitsS.plainBits (encShape s d) (bitsE s d as) = _
      rw [wordsBits_snd_eq, plainBits_enc s d as]
      rfl

/-- A bound for the number of scalars of all plain parts, from the data of the rounds. A recursion
on numbers, which the kernel can evaluate for fixed parameters. -/
def SNum.plainK : (s : Shape) → (d : EncData F E s) → SNum s d → ℕ
  | [], _, _ => 0
  | _ :: s, (_, d), (a, as) => a.plainK + SNum.plainK s d as

omit [Field F] [Field E] [Algebra F E] [FinEnum F] [FinEnum E] in
theorem SNum.plainK_app :
    ∀ {s t : Shape} {d : EncData F E s} {d' : EncData F E t} (n : SNum s d) (n' : SNum t d'),
      SNum.plainK (s ++ t) (d.app d') (SNum.app n n') = SNum.plainK s d n + SNum.plainK t d' n'
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (_, _), _, (a, as), n' => by
      show a.plainK + SNum.plainK _ _ (SNum.app as n') = a.plainK + SNum.plainK _ _ as + _
      rw [SNum.plainK_app as n', Nat.add_assoc]

omit [Field E] [FinEnum E] in
theorem B2.of_card_le {α : Type} {e k b : ℕ} (hE : B2 E e)
    (h : Nat.card α ≤ Nat.card E ^ k * 2 ^ b) : B2 α (k * e + b) := by
  unfold B2 at *
  refine le_trans h ?_
  rw [pow_add, Nat.mul_comm k e, pow_mul]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hE k)

omit [Field F] [Field E] [Algebra F E] [FinEnum F] [FinEnum E] in
/-- Under hE, the plain parts have at most e bits for each scalar. -/
theorem plainLog_le {e : ℕ} (hE : B2 E e) :
    ∀ (s : Shape) (d : EncData F E s) (n : SNum s d), s.plainLog ≤ SNum.plainK s d n * e
  | [], _, _ => Nat.zero_le _
  | r :: s, (_, d), (a, as) => by
      show Nat.clog 2 (Nat.card r.Plain) + Shape.plainLog s ≤ (a.plainK + SNum.plainK s d as) * e
      rw [Nat.add_mul]
      refine Nat.add_le_add ((Nat.clog_le_iff_le_pow (by decide)).2 ?_) (plainLog_le hE s d as)
      have := B2.of_card_le (b := 0) hE (by simpa using a.plainK_le)
      simpa [B2] using this

omit [Algebra F E] in
/-- Under hE, the plain parts of the encoded rounds are serialized in at most e bits for each
scalar. -/
theorem plainBits_enc_le {e : ℕ} (hE : B2 E e) (s : Shape) (d : EncData F E s) (n : SNum s d) :
    BitsS.plainBits (encShape s d) (bitsE s d n) ≤ SNum.plainK s d n * e :=
  le_trans (le_of_eq (plainBits_enc s d n)) (plainLog_le hE s d n)

/-! ## The opened positions -/

omit [Algebra F E] in
/-- A bound, in bits, for the lists of opened positions of the encoded rounds. Hypotheses: hF, hE (F
and E have at most 2^e elements); the sum of the lengths of all codewords is at most 2^Dm; every
vector has at most Rm rows. The bound: one bit for each round, and for each position that is read in
a vector two bits and an opening in a tree of depth at most Dm with a symbol of at most Rm entries
(`entBits`, Iop/Sizes.lean). -/
theorem entSum_enc_le (lam sMT : ℕ) {e Dm Rm : ℕ} (hF : B2 F e) (hE : B2 E e) :
    ∀ (s : Shape) (d : EncData F E s) (n : SNum s d), EncData.sum lenN s d ≤ 2 ^ Dm →
      EncData.All (fun _ rows _ _ _ => rows ≤ Rm) s d →
      entSum lam sMT (encShape s d) (depthList _ (encPoint s d)) (bitsE s d n) (opensE s d) ≤
        s.length + EncData.sum (fun _ _ _ _ q => q) s d * (2 + entBits lam sMT Dm (Dm + Rm * e))
  | [], _, _, _, _ => Nat.zero_le _
  | r :: s, (en, d), (a, as), hD, hR => by
      letI := a.enumA
      letI := a.enumPlain
      have hD1 : ∑ v, (en.code v).n ≤ 2 ^ Dm := le_trans (Nat.le_add_right _ _) hD
      have ih := entSum_enc_le lam sMT hF hE s d as (le_trans (Nat.le_add_left _ _) hD) hR.2
      have h1 := entSum_cons_le lam sMT (r := en.round) (s := encShape s d)
        (depthList _ (encPoint (r :: s) (en, d))) (bitsE (r :: s) (en, d) (a, as))
        (opensE (r :: s) (en, d)) (d' := Dm) (x' := Dm + Rm * e) (by
          show depthR (wordsPoint en.A (fun a => (en.code a).n)
                (fun a => Fin (en.rows a) → Kf F E (en.overF a)) r.Plain r.Chal
                (fun _ _ => 0) r.dPlain) ≤ Dm
          rw [depthR_enc]
          exact (Nat.clog_le_iff_le_pow (by decide)).2 hD1) (by
          show (wordsBits en.A (fun v => (en.code v).n)
              (fun v => Fin (en.rows v) → Kf F E (en.overF v)) r.Plain).1 ≤ _
          exact wordsBits_fst_le' _ _ _ _ hD1 fun v => ((B2.kf hF hE (en.overF v)).vec (en.rows v)).mono (Nat.mul_le_mul_right e (hR.1 v))) ih
      refine le_trans h1 ?_
      show (gam (∑ v, en.q v) + (∑ v, en.q v) * entBits lam sMT Dm (Dm + Rm * e)) +
          (s.length +
            EncData.sum (fun _ _ _ _ q => q) s d * (2 + entBits lam sMT Dm (Dm + Rm * e))) ≤
        (s.length + 1) +
          ((∑ v, en.q v) + EncData.sum (fun _ _ _ _ q => q) s d) *
            (2 + entBits lam sMT Dm (Dm + Rm * e))
      have hg := gam_le (∑ v, en.q v)
      rw [Nat.add_mul, Nat.mul_add (∑ v, en.q v)]
      omega

/-- one round: the bound for its list of opened positions: the positions read in its vectors, each
with an opening in the tree over all its codewords and a symbol of the widest of its vectors (f bits
for an entry over F, e bits for an entry over E) -/
def REnc.entB (lam sMT f e : ℕ) {r : Round} (en : REnc F E r) : ℕ :=
  gam (∑ a, en.q a) +
    (∑ a, en.q a) *
      entBits lam sMT (Nat.clog 2 (∑ a, (en.code a).n))
        (Nat.clog 2 (∑ a, (en.code a).n) +
          Finset.univ.sup fun a => en.rows a * (if en.overF a then f else e))

/-- The bound for the lists of opened positions of the encoded rounds, round by round. A recursion
on numbers, which the kernel can evaluate for fixed parameters. -/
def EncData.entB (lam sMT f e : ℕ) : (s : Shape) → EncData F E s → ℕ
  | [], _ => 0
  | _ :: s, (en, d) => en.entB lam sMT f e + EncData.entB lam sMT f e s d

omit [Field F] [Field E] [Algebra F E] [FinEnum F] [FinEnum E] in
theorem EncData.entB_app (lam sMT f e : ℕ) :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t),
      EncData.entB lam sMT f e (s ++ t) (d.app d') =
        EncData.entB lam sMT f e s d + EncData.entB lam sMT f e t d'
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (en, d), d' => by
      show en.entB lam sMT f e + EncData.entB lam sMT f e _ (d.app d') =
        en.entB lam sMT f e + EncData.entB lam sMT f e _ d + _
      rw [EncData.entB_app lam sMT f e d d', Nat.add_assoc]

omit [Algebra F E] in
theorem entSum_enc_le' (lam sMT : ℕ) {f e : ℕ} (hF : B2 F f) (hE : B2 E e) :
    ∀ (s : Shape) (d : EncData F E s) (n : SNum s d),
      entSum lam sMT (encShape s d) (depthList _ (encPoint s d)) (bitsE s d n) (opensE s d) ≤
        EncData.entB lam sMT f e s d
  | [], _, _ => Nat.le_refl _
  | r :: s, (en, d), (a, as) => by
      letI := a.enumA
      letI := a.enumPlain
      refine entSum_cons_le lam sMT (r := en.round) (s := encShape s d)
        (depthList _ (encPoint (r :: s) (en, d))) (bitsE (r :: s) (en, d) (a, as))
        (opensE (r :: s) (en, d)) ?_ ?_ (entSum_enc_le' lam sMT hF hE s d as)
      · show depthR (wordsPoint en.A (fun a => (en.code a).n)
              (fun a => Fin (en.rows a) → Kf F E (en.overF a)) r.Plain r.Chal
              (fun _ _ => 0) r.dPlain) ≤ _
        rw [depthR_enc]
      · show (wordsBits en.A (fun v => (en.code v).n)
            (fun v => Fin (en.rows v) → Kf F E (en.overF v)) r.Plain).1 ≤ _
        refine wordsBits_fst_le' _ _ _ _ (Nat.le_pow_clog (by decide) _) fun v => ?_
        refine B2.mono ?_
          (Finset.le_sup (f := fun a => en.rows a * (if en.overF a then f else e))
            (Finset.mem_univ v))
        show B2 (Fin (en.rows v) → Kf F E (en.overF v)) (en.rows v * (if en.overF v then f else e))
        cases en.overF v with
        | true => exact hF.vec (en.rows v)
        | false => exact hE.vec (en.rows v)

end Enc

end Blocks
