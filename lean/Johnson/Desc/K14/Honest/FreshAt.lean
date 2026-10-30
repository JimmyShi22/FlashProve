--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/FreshAt.lean: the mask message o_sp of the linear claim's shared rounds, as
Johnson/Desc/K14/Honest/SendMoves.lean lays it, has the form of Code/FreshCore.lean: its symbols,
its out-of-domain (OOD) answer and the scalar at "SPLIT" are the affine functions of that file, of
the row's tail, its pad and its other entries. First the three equations; then that file's
statement, called once; then where the shared sending writes these values.

The message: one mask row of n + 1 entries under the mask code Z, with one OOD answer. Its last
entry is the pad p; its entries 0 to n - 1 are k; its tail is t.

  pointE, pointE_inj   a position's point, in the extension field; different positions have
                  different points, for a code of at most 2 ^ 32 positions
  tailShare, tailShare_onto   what the tail adds to the symbols; on at most as many positions as the
                  tail has entries it takes all patterns, for a code of at most 2 ^ 32 positions
  maskRowOf, maskTailOf, spCoins   the row's entries, its tail, and the message's coins, of
                  (t, p, k)
  sym_form        the symbol at a position: the tail's share, plus p times a power of the point,
                  plus the sum of k i times a power of the point
  sampleValue_target, sampleValue_form   the left side of a message's sample row at words, in closed
                  form: says_iff (Johnson/Desc/K1/Law/SaysTie.lean) without the target
  weight_lastEntry, answer_form   the answer: beta p plus the sum of ak i k i, where ak i is the
                  sample row's weight on entry i
  mu_form         the scalar: omega_col at z_fd plus the entry kappa
  fresh_words     the statement of Code/FreshCore.lean at these values, at free words that hold the
                  row
  held_row, fresh_rows   the same at the rows that sendsOmega lays, at the held words, with the
                  scalar muSent in the place of the entry kappa; the code, the statement and its
                  entry still free
  spSymCode, spTriple, fresh_sent   **the statement**: the code is the mask code that o_sp's own
                  shape names; the statement T has the codes and, at the second new number, an entry
                  X of o_sp's shape (T, X and the number first stay parameters, under these
                  premises)
  sp_written, sp_answer   where the shared sending (Johnson/Prover/Send/Core.lean) writes these
                  values, if its parameters have the same codes: the mask symbols of its second
                  message at a position are the three words of the symbol at that position modulo
                  the mask code's length; the answer stands in its list of answers, written, behind
                  the answers of the first message

HOW FAR IT REACHES. One row, one pad, one answer. z_fd, the seed (z, beta) and the set S of
positions are the verifier's, sampled after the message has gone out; here they are fixed parameters
bound outside the distribution, as are the codes, the shape, the sending's parameters, the number
first, the words in front, psi_lo, the folded row, o_omega's coins, the statement and its entry, the
idle target, n, kappa and the function f; the step from fixed to sampled is not made here. The
statement T is meant as the one that has received the messages and not yet the answers. S counts
DISTINCT positions of the mask code's word, over all lists at which the row is read, each taken
modulo the mask code's length. Where S has as many positions as the tail has entries, the triple has
as many components as there are coins (by counting; no theorem here says that the map is one to
one). The triple's third component holds all n entries, not the scalar alone. maskRowOf lays the pad
at every place from n on, where the shared sending asks 0 of its caller beyond the code's message
length: no such place is read. In Johnson/Desc/K14/Honest/FreshAtChain.lean stand: the statement at
the row with 0 there (fresh_zero); at the shared chain's own parameters (fresh_chain); at both
(fresh_chain_zero); joins of the triple to what the shared sending writes and to the verifier's
constraint at "SPLIT"; and send_enc, called at free rows and a free position.

What is assumed. The mask code has at most 2 ^ 32 positions, and n + 1 message entries, which is 2
to its logEll; o_sp's shape has no main row, one mask row and one OOD answer; S has at most as many
positions as the tail has entries; the seed's factor does not read as 0; the seed's point has AT
LEAST the message's number of coordinates; the statement T has the codes and, at the number
first + 1, an entry of o_sp's shape; the sending has a second message, of o_sp's shape.
What is not claimed. That an honest prover samples t, p and k uniformly: no distribution of a
prover's coins occurs but the uniform one that is assumed. That kappa is the entry that the verifier
takes at "SPLIT": kappa is any entry but the pad. That the column of a tree holds the mask symbols
at a stated place. That symG is the symbol that a program's encoder has; what the IOP as written in
Lean reads of the written column is the shared sending's send_enc, called in FreshAtChain.lean.
Nothing on roots and paths, on any other value that is shown, or on a verifier's view. No property
of a protocol is claimed.

-/
import Code.FreshCore
import Code.RS
import OnBytes.Slice.Points
import Johnson.Desc.K1.Law.SaysTie
import Johnson.Desc.K14.Honest.SendMoves
import Johnson.Prover.Send.Held
import Johnson.Prover.Send.Says
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (K1.Msg K1.Msg.of K1.sampleRow)
open Johnson.Prover.Link (symG)

/-! ## The values at which Code/FreshCore.lean is called -/

/-- A position's point, in the extension field. -/
def pointE (a : ℕ) (x : Fin (2 ^ a)) : GE := algebraMap GF GE (ptOf a x)

theorem pointE_inj (a : ℕ) (ha : a ≤ 32) : Function.Injective (pointE a) :=
  (algebraMap GF GE).injective.comp (ptOf_inj a ha)

/-- What a row's tail adds to its symbols: the tail's entries are the lowest coefficients. -/
def tailShare (Z : Fmt.M1.Code) : (Fin Z.r → GE) →ₗ[GE] (Fin (2 ^ Z.a) → GE) :=
  Code.RS.gen (pointE Z.a) fun t : Fin Z.r => (t : ℕ)

/-- On at most as many positions as the tail has entries, the tail's share takes all patterns, for a
code of at most 2 ^ 32 positions. -/
theorem tailShare_onto (Z : Fmt.M1.Code) (ha : Z.a ≤ 32) : Code.OntoUpTo (tailShare Z) Z.r :=
  Code.RS.ontoUpTo_gen (pointE_inj Z.a ha) Z.r

/-- The row's entries: k below n, the pad p from n on. -/
def maskRowOf (n : ℕ) (p : GE) (k : Fin n → GE) (j : ℕ) : GE := if h : j < n then k ⟨j, h⟩ else p

/-- The row's tail. -/
def maskTailOf (r : ℕ) (t : Fin r → GE) (q : ℕ) : GE := if h : q < r then t ⟨q, h⟩ else 0

/-- The coins of the mask message, of (t, p, k). -/
def spCoins (r n : ℕ) (x : (Fin r → GE) × GE × (Fin n → GE)) : MsgCoins :=
  ⟨fun _ _ => 0, fun _ => 0, fun _ j => maskRowOf n x.2.1 x.2.2 j, fun _ q => maskTailOf r x.1 q⟩

/-! ## The symbols -/

/-- **The symbol at a position.** -/
theorem sym_form (Z : Fmt.M1.Code) (n : ℕ) (hl : Z.l = n + 1) (x : Fin (2 ^ Z.a))
    (t : Fin Z.r → GE) (p : GE) (k : Fin n → GE) :
    symG Z x.val (maskRowOf n p k) (maskTailOf Z.r t) =
      tailShare Z t x + p * pointE Z.a x ^ (Z.r + n) +
        ∑ i : Fin n, k i * pointE Z.a x ^ (Z.r + i.val) := by
  have e1 : ∑ q ∈ Finset.range Z.r,
      algebraMap GF GE (toF (Fmt.M1.point Z.a x.val) ^ q) * maskTailOf Z.r t q =
      ∑ i : Fin Z.r, t i * pointE Z.a x ^ (i : ℕ) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun q => algebraMap GF GE (toF (Fmt.M1.point Z.a x.val) ^ q) * maskTailOf Z.r t q) Z.r]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold maskTailOf
    rw [dif_pos i.isLt, map_pow, mul_comm]
    rfl
  have e2 : ∑ j ∈ Finset.range n,
      algebraMap GF GE (toF (Fmt.M1.point Z.a x.val) ^ (Z.r + j)) * maskRowOf n p k j =
      ∑ i : Fin n, k i * pointE Z.a x ^ (Z.r + i.val) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => algebraMap GF GE (toF (Fmt.M1.point Z.a x.val) ^ (Z.r + j)) * maskRowOf n p k j) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold maskRowOf
    rw [dif_pos i.isLt, map_pow, mul_comm]
    rfl
  have e3 : algebraMap GF GE (toF (Fmt.M1.point Z.a x.val) ^ (Z.r + n)) * maskRowOf n p k n =
      p * pointE Z.a x ^ (Z.r + n) := by
    unfold maskRowOf
    rw [dif_neg (Nat.lt_irrefl n), map_pow, mul_comm]
    rfl
  unfold symG tailShare
  rw [Code.RS.gen_apply, hl, Finset.sum_range_succ, e1, e2, e3]
  ring

/-! ## The answer -/

/-- A sample row's left side does not read the row's target. -/
theorem sampleValue_target (T : Statement) (m : K1.Msg) (o : ℕ) (z : List E) (β : E) (i : ℕ)
    (y y' : E) (w : Words GE) :
    Means.value rdE T (K1.sampleRow m o z β i y) w =
      Means.value rdE T (K1.sampleRow m o z β i y') w := by
  unfold Means.value Means.onTable
  rw [VerifiableInference.Desc.K1.sampleRow_eq m o z β i y,
    VerifiableInference.Desc.K1.sampleRow_eq m o z β i y']
  rfl

/-- The left side of a message's sample row at words, in closed form. -/
theorem sampleValue_form (T : Statement) (o : ℕ) (X : OnBytes.Oracle) (hX : T.oracles[o]? = some X)
    (z : List E) (β : E) (i : ℕ) (y : E) (w : Words GE)
    (hne : ((K1.Msg.of T.codes X.shape).K != 0 || (K1.Msg.of T.codes X.shape).Kzk != 0) = true)
    (hz : (K1.Msg.of T.codes X.shape).v ≤ z.length) :
    Means.value rdE T (K1.sampleRow (K1.Msg.of T.codes X.shape) o z β i y) w =
      (K1.Msg.of T.codes X.shape).form (readL z) (readE β) i (w o) := by
  generalize hv : Means.value rdE T (K1.sampleRow (K1.Msg.of T.codes X.shape) o z β i y) w = v
  have hs : Means.Says rdE T
      (K1.sampleRow (K1.Msg.of T.codes X.shape) o z β i (E.ofTriple (ofE v))) w := by
    show Means.value rdE T _ w = rdE.val (E.ofTriple (ofE v))
    rw [rdE_val, readE_ofTriple, toE_ofE, ← hv]
    exact sampleValue_target T _ o z β i _ y w
  have h := (VerifiableInference.Desc.K1.says_iff T o X hX z β i (E.ofTriple (ofE v)) w hne hz).1 hs
  rw [readE_ofTriple, toE_ofE] at h
  exact h.symm

/-- The sample row's weight on the pad of a message of one mask row with one answer: the factor. -/
theorem weight_lastEntry (m : K1.Msg) (z : ℕ → GE) (β : GE) (hZ : m.Kzk = 1)
    (hA : m.answers = 1) : m.weight z β 0 .mask (2 ^ m.logEllZk - 1) = β := by
  have h := m.weight_pad z β 0 0 0 (by rw [hA]; exact Nat.one_pos) (by simp [K1.Msg.e, hZ])
  have hp : m.padPart = .mask := by simp [K1.Msg.padPart, hZ]
  have hi : m.padIdx 0 0 = 2 ^ m.logEllZk - 1 := by
    simp [K1.Msg.padIdx, K1.Msg.padRows, K1.Msg.padLen, K1.Msg.e, hZ, hA,
      VerifiableInference.Desc.K1.clog]
  have h1 : readE (thetaE 0) = 1 := by
    have e : thetaE 0 = oneE := rfl
    rw [e]
    exact rdE.one
  rw [hp, hi, if_pos rfl, h1, mul_one] at h
  exact h

/-- **The answer**: the factor times the pad, plus the sum of the sample row's weights times the
other entries. u: the message's two tables; its mask table holds the row. -/
theorem answer_form (m : K1.Msg) (n : ℕ) (z : ℕ → GE) (β : GE) (hK : m.K = 0) (hZ : m.Kzk = 1)
    (hA : m.answers = 1) (hn : 2 ^ m.logEllZk = n + 1) (p : GE) (k : Fin n → GE)
    (u : Part → ℕ → GE) (hu : ∀ j, j < n + 1 → u .mask j = maskRowOf n p k j) :
    m.form z β 0 u = β * p + ∑ i : Fin n, m.weight z β 0 .mask i.val * k i := by
  have hb : m.bits .mask = m.logEllZk := by
    simp [K1.Msg.bits, K1.Msg.maskBits, hZ, VerifiableInference.Desc.K1.clog]
  have h1 : m.has .main = false := by simp [K1.Msg.has, hK]
  have h2 : m.has .mask = true := by simp [K1.Msg.has, hZ]
  have hp : n = 2 ^ m.logEllZk - 1 := by omega
  unfold K1.Msg.form
  rw [h1, h2, if_neg Bool.false_ne_true, if_pos rfl, Finset.range_zero, Finset.sum_empty, zero_add,
    hb, hn, Finset.sum_range_succ, hu n (Nat.lt_succ_self n)]
  have e1 : maskRowOf n p k n = p := by
    unfold maskRowOf
    rw [dif_neg (Nat.lt_irrefl n)]
  have e2 : m.weight z β 0 .mask n = β := by
    rw [hp]
    exact weight_lastEntry m z β hZ hA
  have e3 : ∑ j ∈ Finset.range n, m.weight z β 0 .mask j * u .mask j =
      ∑ i : Fin n, m.weight z β 0 .mask i.val * k i := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => m.weight z β 0 .mask j * u .mask j) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu i.val (Nat.lt_succ_of_lt i.isLt)]
    unfold maskRowOf
    rw [dif_pos i.isLt]
  rw [e1, e2, e3]
  ring

/-! ## The scalar -/

/-- **The scalar at "SPLIT"**: omega_col at z_fd, plus the entry kappa of the row. -/
theorem mu_form (S : LinShape) (psiLo z : List GE) (u : ℕ → GE) (r n : ℕ)
    (x : (Fin r → GE) × GE × (Fin n → GE)) (hm : S.sharedSplit.maskRows = 1) (kappa : Fin n) :
    muSent S psiLo z u (spCoins r n x) kappa.val =
      (∑ j ∈ Finset.range S.matrixRows, Law.eqK z j * omegaHon S psiLo u j) + x.2.2 kappa := by
  unfold muSent muHon kappaOf spCoins
  rw [hm]
  show _ + maskRowOf n x.2.1 x.2.2 (kappa.val / 2 ^ ceilLog2 1) = _
  have e : kappa.val / 2 ^ ceilLog2 1 = kappa.val := by
    have : ceilLog2 1 = 0 := rfl
    rw [this, Nat.pow_zero, Nat.div_one]
  rw [e]
  unfold maskRowOf
  rw [dif_pos kappa.isLt]

/-! ## The statement -/

/-- **Over uniform (tail, pad, entries) of the mask message, whatever is made of (its symbols on S,
its OOD answer, c + its entries) has the distribution of the same made of a uniform triple.** T, o,
X: the statement, the message's number and its entry there; w: words, as a function of the coins,
whose mask table at o holds the row. -/
theorem fresh_words {γ : Type} (Z : Fmt.M1.Code) (n : ℕ) (hl : Z.l = n + 1) (ha : Z.a ≤ 32)
    (S : Finset (Fin (2 ^ Z.a))) (hS : S.card ≤ Z.r) (T : Statement) (o : ℕ) (X : OnBytes.Oracle)
    (hX : T.oracles[o]? = some X) (hK : (K1.Msg.of T.codes X.shape).K = 0)
    (hZ : (K1.Msg.of T.codes X.shape).Kzk = 1) (hA : (K1.Msg.of T.codes X.shape).answers = 1)
    (hn : 2 ^ (K1.Msg.of T.codes X.shape).logEllZk = n + 1) (z : List E) (β y : E)
    (hz : (K1.Msg.of T.codes X.shape).v ≤ z.length) (hβ : readE β ≠ 0) (c : Fin n → GE)
    (w : (Fin Z.r → GE) × GE × (Fin n → GE) → Words GE)
    (hw : ∀ x j, j < n + 1 → w x o .mask j = maskRowOf n x.2.1 x.2.2 j)
    (f : (S → GE) × GE × (Fin n → GE) → γ) :
    (Prob.unif ((Fin Z.r → GE) × GE × (Fin n → GE))).map (fun x => f
        (fun j => symG Z j.1.val (maskRowOf n x.2.1 x.2.2) (maskTailOf Z.r x.1),
          Means.value rdE T (K1.sampleRow (K1.Msg.of T.codes X.shape) o z β 0 y) (w x),
          fun i => c i + x.2.2 i)) =
      (Prob.unif ((S → GE) × GE × (Fin n → GE))).map f := by
  have hne : ((K1.Msg.of T.codes X.shape).K != 0 || (K1.Msg.of T.codes X.shape).Kzk != 0) =
      true := by
    simp [hZ]
  have h := Code.fresh_core (tailShare Z) S (tailShare_onto Z ha S hS)
    (fun j => pointE Z.a j.1 ^ (Z.r + n)) (fun _ => 0) (fun i j => pointE Z.a j.1 ^ (Z.r + i.val))
    (fun i => (K1.Msg.of T.codes X.shape).weight (readL z) (readE β) 0 .mask i.val) c 0 (readE β)
    hβ f
  have e : (fun x : (Fin Z.r → GE) × GE × (Fin n → GE) => f
        (fun j : S => symG Z j.1.val (maskRowOf n x.2.1 x.2.2) (maskTailOf Z.r x.1),
          Means.value rdE T (K1.sampleRow (K1.Msg.of T.codes X.shape) o z β 0 y) (w x),
          fun i => c i + x.2.2 i)) =
      fun x => f
        (fun j : S => 0 + (tailShare Z x.1 j.1 + x.2.1 * pointE Z.a j.1 ^ (Z.r + n) +
            ∑ i : Fin n, x.2.2 i * pointE Z.a j.1 ^ (Z.r + i.val)),
          0 + (readE β * x.2.1 + ∑ i : Fin n,
            (K1.Msg.of T.codes X.shape).weight (readL z) (readE β) 0 .mask i.val * x.2.2 i),
          fun i => c i + x.2.2 i) := by
    funext x
    have e1 : (fun j : S => symG Z j.1.val (maskRowOf n x.2.1 x.2.2) (maskTailOf Z.r x.1)) =
        fun j : S => 0 + (tailShare Z x.1 j.1 + x.2.1 * pointE Z.a j.1 ^ (Z.r + n) +
          ∑ i : Fin n, x.2.2 i * pointE Z.a j.1 ^ (Z.r + i.val)) := by
      funext j
      rw [sym_form Z n hl j.1 x.1 x.2.1 x.2.2, zero_add]
    have e2 : Means.value rdE T (K1.sampleRow (K1.Msg.of T.codes X.shape) o z β 0 y) (w x) =
        0 + (readE β * x.2.1 + ∑ i : Fin n,
          (K1.Msg.of T.codes X.shape).weight (readL z) (readE β) 0 .mask i.val * x.2.2 i) := by
      rw [sampleValue_form T o X hX z β 0 y (w x) hne hz,
        answer_form _ n (readL z) (readE β) hK hZ hA hn x.2.1 x.2.2 (w x o) (hw x), zero_add]
    rw [e1, e2]
  rw [e]
  exact h

/-- The held words hold the row: at the number of the second message of "send o_omega", whose shape
has one mask row. -/
theorem held_row (codes : Codes) (S : LinShape) (Q : VerifiableInference.Desc.K1.Par) (first : ℕ)
    (w₀ : Words GE) (psiLo : List GE) (u : ℕ → GE) (cOmega : MsgCoins) (r n : ℕ)
    (x : (Fin r → GE) × GE × (Fin n → GE)) (h2 : 1 < Q.sent.size)
    (hm : (Johnson.Prover.Send.shapeAt Q 1).maskRows = 1) (j : ℕ) :
    Johnson.Prover.Send.held w₀ first Q (sendsOmega codes S psiLo u cOmega (spCoins r n x))
      (first + 1) .mask j = maskRowOf n x.2.1 x.2.2 j := by
  rw [Johnson.Prover.Send.held_new w₀ first Q _ 1 h2]
  have h := Johnson.Prover.Send.word_mask (sendsOmega codes S psiLo u cOmega (spCoins r n x) 1)
    (Johnson.Prover.Send.shapeAt Q 1) 0 j (by rw [hm]; exact Nat.one_pos)
  have e : 0 + j * 2 ^ VerifiableInference.Desc.K1.clog (Johnson.Prover.Send.shapeAt Q 1).maskRows =
      j := by
    rw [hm]
    have : VerifiableInference.Desc.K1.clog 1 = 0 := rfl
    rw [this, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  rw [e] at h
  rw [h]
  rfl

/-- The statement at the rows that sendsOmega lays for its second message. THE CODE Z, THE STATEMENT
T AND ITS ENTRY X ARE STILL FREE HERE: fresh_sent ties them to the shape. -/
theorem fresh_rows {γ : Type} (codes : Codes) (Sh : LinShape)
    (Q : VerifiableInference.Desc.K1.Par) (first : ℕ) (w₀ : Words GE) (psiLo zfd : List GE)
    (u : ℕ → GE) (cOmega : MsgCoins) (Z : Fmt.M1.Code) (n : ℕ) (hl : Z.l = n + 1) (ha : Z.a ≤ 32)
    (S : Finset (Fin (2 ^ Z.a))) (hS : S.card ≤ Z.r) (T : Statement) (X : OnBytes.Oracle)
    (hX : T.oracles[first + 1]? = some X) (hK : (K1.Msg.of T.codes X.shape).K = 0)
    (hZ : (K1.Msg.of T.codes X.shape).Kzk = 1) (hA : (K1.Msg.of T.codes X.shape).answers = 1)
    (hn : 2 ^ (K1.Msg.of T.codes X.shape).logEllZk = n + 1) (z : List E) (β y : E)
    (hz : (K1.Msg.of T.codes X.shape).v ≤ z.length) (hβ : readE β ≠ 0) (h2 : 1 < Q.sent.size)
    (hm : (Johnson.Prover.Send.shapeAt Q 1).maskRows = 1) (hm' : Sh.sharedSplit.maskRows = 1)
    (kappa : Fin n) (f : (S → GE) × GE × (Fin n → GE) → γ) :
    (Prob.unif ((Fin Z.r → GE) × GE × (Fin n → GE))).map (fun x => f
        (fun j => symG Z j.1.val
            ((sendsOmega codes Sh psiLo u cOmega (spCoins Z.r n x) 1).mask 0)
            ((sendsOmega codes Sh psiLo u cOmega (spCoins Z.r n x) 1).maskTl 0),
          Means.value rdE T (K1.sampleRow (K1.Msg.of T.codes X.shape) (first + 1) z β 0 y)
            (Johnson.Prover.Send.held w₀ first Q
              (sendsOmega codes Sh psiLo u cOmega (spCoins Z.r n x))),
          fun i => if i = kappa then muSent Sh psiLo zfd u (spCoins Z.r n x) kappa.val
            else x.2.2 i)) =
      (Prob.unif ((S → GE) × GE × (Fin n → GE))).map f := by
  have h := fresh_words Z n hl ha S hS T (first + 1) X hX hK hZ hA hn z β y hz hβ
    (fun i => if i = kappa then
      ∑ j ∈ Finset.range Sh.matrixRows, Law.eqK zfd j * omegaHon Sh psiLo u j else 0)
    (fun x => Johnson.Prover.Send.held w₀ first Q
      (sendsOmega codes Sh psiLo u cOmega (spCoins Z.r n x)))
    (fun x j _ => held_row codes Sh Q first w₀ psiLo u cOmega Z.r n x h2 hm j) f
  rw [← h]
  congr 1
  funext x
  have e : (fun i : Fin n => if i = kappa then muSent Sh psiLo zfd u (spCoins Z.r n x) kappa.val
      else x.2.2 i) = fun i => (if i = kappa then
        ∑ j ∈ Finset.range Sh.matrixRows, Law.eqK zfd j * omegaHon Sh psiLo u j else 0) +
          x.2.2 i := by
    funext i
    by_cases hi : i = kappa
    · rw [if_pos hi, if_pos hi, mu_form Sh psiLo zfd u Z.r n x hm' kappa, hi]
    · rw [if_neg hi, if_neg hi, zero_add]
  rw [e]
  rfl

/-- The mask code that o_sp's own shape names, in the form in which a symbol is computed. -/
def spSymCode (codes : Codes) (Sh : LinShape) : Fmt.M1.Code :=
  OnBytes.Slice.codeOf (codes.mask.getD Sh.sharedSplit.maskCode default)

/-- **The triple**, of o_sp's coins x = (tail, pad, entries), all else fixed: o_sp's symbols at the
positions of S; the left side of its sample row number 0 at the held words (y, the row's target, is
not read); its n entries that are no pad, with the scalar muSent in the place of the entry kappa. -/
def spTriple (codes : Codes) (Sh : LinShape) (Q : VerifiableInference.Desc.K1.Par) (first : ℕ)
    (w₀ : Words GE) (psiLo zfd : List GE) (u : ℕ → GE) (cOmega : MsgCoins) (n : ℕ)
    (S : Finset (Fin (2 ^ (spSymCode codes Sh).a))) (T : Statement) (z : List E) (β y : E)
    (kappa : Fin n) (x : (Fin (spSymCode codes Sh).r → GE) × GE × (Fin n → GE)) :
    (S → GE) × GE × (Fin n → GE) :=
  (fun j => symG (spSymCode codes Sh) j.1.val
      ((sendsOmega codes Sh psiLo u cOmega (spCoins (spSymCode codes Sh).r n x) 1).mask 0)
      ((sendsOmega codes Sh psiLo u cOmega (spCoins (spSymCode codes Sh).r n x) 1).maskTl 0),
    Means.value rdE T (K1.sampleRow (K1.Msg.of codes Sh.sharedSplit) (first + 1) z β 0 y)
      (Johnson.Prover.Send.held w₀ first Q
        (sendsOmega codes Sh psiLo u cOmega (spCoins (spSymCode codes Sh).r n x))),
    fun i => if i = kappa then muSent Sh psiLo zfd u (spCoins (spSymCode codes Sh).r n x) kappa.val
      else x.2.2 i)

/-- **The statement at "send o_omega"'s own o_sp.** Over uniform (tail, pad, entries) of o_sp, all
else fixed, whatever is made of the triple has the distribution of the same made of a uniform
triple. -/
theorem fresh_sent {γ : Type} (codes : Codes) (Sh : LinShape)
    (Q : VerifiableInference.Desc.K1.Par) (first : ℕ) (w₀ : Words GE) (psiLo zfd : List GE)
    (u : ℕ → GE) (cOmega : MsgCoins) (n : ℕ) (hl : (spSymCode codes Sh).l = n + 1)
    (hpow : 2 ^ (codes.mask.getD Sh.sharedSplit.maskCode default).logEll = (spSymCode codes Sh).l)
    (ha : (spSymCode codes Sh).a ≤ 32) (h0 : Sh.sharedSplit.mainRows = 0)
    (hm : Sh.sharedSplit.maskRows = 1) (hA : Sh.sharedSplit.answers = 1)
    (S : Finset (Fin (2 ^ (spSymCode codes Sh).a))) (hS : S.card ≤ (spSymCode codes Sh).r)
    (T : Statement) (X : OnBytes.Oracle) (hX : T.oracles[first + 1]? = some X)
    (hXs : X.shape = Sh.sharedSplit) (hT : T.codes = codes) (h2 : 1 < Q.sent.size)
    (hQ : Johnson.Prover.Send.shapeAt Q 1 = Sh.sharedSplit) (z : List E) (β y : E)
    (hz : (K1.Msg.of codes Sh.sharedSplit).v ≤ z.length) (hβ : readE β ≠ 0) (kappa : Fin n)
    (f : (S → GE) × GE × (Fin n → GE) → γ) :
    (Prob.unif ((Fin (spSymCode codes Sh).r → GE) × GE × (Fin n → GE))).map (fun x =>
        f (spTriple codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa x)) =
      (Prob.unif ((S → GE) × GE × (Fin n → GE))).map f := by
  have e : K1.Msg.of T.codes X.shape = K1.Msg.of codes Sh.sharedSplit := by rw [hT, hXs]
  have h := fresh_rows codes Sh Q first w₀ psiLo zfd u cOmega (spSymCode codes Sh) n hl ha S hS T X
    hX (by rw [e]; exact h0) (by rw [e]; exact hm) (by rw [e]; exact hA)
    (by rw [e]; exact hpow.trans hl) z β y (by rw [e]; exact hz) hβ h2 (by rw [hQ]; exact hm) hm
    kappa f
  rw [e] at h
  exact h

/-! ## Where the shared sending writes these values -/

/-- The mask symbols that the shared sending writes for its second message at a position x are the
three words of the symbol at x modulo the mask code's length, if its parameters have the codes. -/
theorem sp_written (codes : Codes) (Sh : LinShape) (Q : VerifiableInference.Desc.K1.Par)
    (V : ℕ → Johnson.Prover.Send.Rows) (x : ℕ) (hQc : Q.codes = codes)
    (hQ : Johnson.Prover.Send.shapeAt Q 1 = Sh.sharedSplit) (hm : Sh.sharedSplit.maskRows = 1) :
    Johnson.Prover.Send.maskSyms Q V 1 x =
      Johnson.Prover.Link.words3 (ofE (symG (spSymCode codes Sh)
        (x % 2 ^ (spSymCode codes Sh).a) ((V 1).mask 0) ((V 1).maskTl 0))) := by
  unfold Johnson.Prover.Send.maskSyms
  simp only [hQ, hm, hQc, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

/-- The answer stands, written, in the shared sending's list of answers, behind the answers of the
first message, if its parameters have the codes and its first seed is (z, beta). -/
theorem sp_answer (codes : Codes) (Sh : LinShape) (Q : VerifiableInference.Desc.K1.Par)
    (T : Statement) (first : ℕ) (w : Words GE) (seeds : List (List E × E)) (z : List E) (β : E)
    (hQc : Q.codes = codes) (h2 : 1 < Q.sent.size)
    (hQ : Johnson.Prover.Send.shapeAt Q 1 = Sh.sharedSplit) (hA : Sh.sharedSplit.answers = 1)
    (h0 : seeds.getD 0 default = (z, β)) :
    (Johnson.Prover.Send.answers Q T first w seeds)[VerifiableInference.Desc.K1.offset Q 1 + 0]? =
      some (ofE (Means.value rdE T
        (K1.sampleRow (K1.Msg.of codes Sh.sharedSplit) (first + 1) z β 0 zeroE) w)) := by
  have h := Johnson.Prover.Send.answers_at Q T first w seeds 1 0 h2
    (by rw [hQ, hA]; exact Nat.one_pos)
  rw [hQc, hQ, h0] at h
  exact h

end Desc.K14.Honest

#print axioms Desc.K14.Honest.pointE_inj
#print axioms Desc.K14.Honest.tailShare_onto
#print axioms Desc.K14.Honest.sym_form
#print axioms Desc.K14.Honest.sampleValue_target
#print axioms Desc.K14.Honest.sampleValue_form
#print axioms Desc.K14.Honest.weight_lastEntry
#print axioms Desc.K14.Honest.answer_form
#print axioms Desc.K14.Honest.mu_form
#print axioms Desc.K14.Honest.fresh_words
#print axioms Desc.K14.Honest.held_row
#print axioms Desc.K14.Honest.fresh_rows
#print axioms Desc.K14.Honest.fresh_sent
#print axioms Desc.K14.Honest.sp_written
#print axioms Desc.K14.Honest.sp_answer
